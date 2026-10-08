-- Prove2me | solution 1 for ConicQuadIPM.Complementarity.rot_quad_transform
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:07:23.820305+00:00
-- url     : https://prove2.me/submissions/08474a71-69f5-4d42-9619-b13610a98bd2

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting
open Matrix ConicQuadIPM.Complementarity
set_option maxRecDepth 4000

private lemma coordinate {d : ℕ} (v : Fin d → ℝ) (r : ℕ) (hr : r < d) : coord v r = v ⟨r, hr⟩ := by
  unfold coord
  rw [Finset.sum_eq_single ⟨r, hr⟩]
  · simp
  · intro j hj h; simp [show j.val ≠ r by intro he; apply h; exact Fin.ext he]
  · simp

private lemma taction (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) (a : Fin d) :
    (Tmat .rot d *ᵥ v) a =
    if a.val = 0 then (coord v 0 + coord v 1) / Real.sqrt 2
    else if a.val = 1 then (coord v 0 - coord v 1) / Real.sqrt 2 else v a := by
  let z : Fin d := ⟨0, by omega⟩
  let o : Fin d := ⟨1, by omega⟩
  change (∑ j : Fin d, Tmat .rot d a j * v j) = _
  simp only [Tmat]
  by_cases ha : a.val < 2
  · have he : ∀ j : Fin d, (if a.val < 2 ∧ j.val < 2 then (if a.val = 1 ∧ j.val = 1 then -(1 / Real.sqrt 2) else 1 / Real.sqrt 2) else if a = j then 1 else 0) =
          (if j = z then 1 / Real.sqrt 2 else 0) + (if j = o then (if a.val = 1 then -(1 / Real.sqrt 2) else 1 / Real.sqrt 2) else 0) := by
        intro j; simp [ha, z, o, Fin.ext_iff]; split_ifs <;> simp_all <;> omega
    simp_rw [he, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [coordinate v 0 (by omega), coordinate v 1 (by omega)]
    dsimp [z, o]
    split_ifs <;> try omega
    all_goals simp [div_eq_mul_inv, mul_add, add_mul, sub_mul, mul_comm, neg_mul, sub_eq_add_neg]
  · rw [Finset.sum_eq_single a]
    · simp [ha, show a.val ≠ 0 by omega, show a.val ≠ 1 by omega]
    · intro j hj hja; simp [ha, Ne.symm hja]
    · simp

private lemma tail_split (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) :
    tailSq v 1 = coord v 1 ^ 2 + tailSq v 2 := by
  rw [coordinate v 1 (by omega)]
  unfold tailSq
  have he : ∀ j : Fin d, (if 1 ≤ j.val then v j ^ 2 else 0) =
      (if j = (⟨1, by omega⟩ : Fin d) then v j ^ 2 else 0) + (if 2 ≤ j.val then v j ^ 2 else 0) := by
    intro j; simp [Fin.ext_iff]; split_ifs <;> simp_all <;> omega
  simp_rw [he, Finset.sum_add_distrib]
  simp

private lemma tail_nonneg {d : ℕ} (v : Fin d → ℝ) (r : ℕ) : 0 ≤ tailSq v r := by
  apply Finset.sum_nonneg
  intro j hj; split_ifs <;> positivity

private lemma tcoords (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) :
    coord (Tmat .rot d *ᵥ v) 0 = (coord v 0 + coord v 1) / Real.sqrt 2 ∧
    coord (Tmat .rot d *ᵥ v) 1 = (coord v 0 - coord v 1) / Real.sqrt 2 ∧
    tailSq (Tmat .rot d *ᵥ v) 2 = tailSq v 2 := by
  constructor
  · rw [coordinate _ 0 (by omega), taction d hd]; simp
  constructor
  · rw [coordinate _ 1 (by omega), taction d hd]; simp
  · unfold tailSq
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : 2 ≤ j.val
    · simp [h, taction d hd, show j.val ≠ 0 by omega, show j.val ≠ 1 by omega]
    · simp [h]

theorem solution (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) :
    inQuad v ↔ inRot (Tmat .rot d *ᵥ v) := by
  obtain ⟨h0, h1, ht⟩ := tcoords d hd v
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hn := tail_nonneg v 2
  have hv := tail_split d hd v
  unfold inQuad inRot
  rw [h0, h1, ht]
  constructor
  · rintro ⟨hq, hq0⟩
    have hplus : 0 ≤ coord v 0 + coord v 1 := by nlinarith
    have hminus : 0 ≤ coord v 0 - coord v 1 := by nlinarith
    refine ⟨?_, div_nonneg hplus hp.le, div_nonneg hminus hp.le⟩
    have he : 2 * ((coord v 0 + coord v 1) / Real.sqrt 2) * ((coord v 0 - coord v 1) / Real.sqrt 2) = coord v 0 ^ 2 - coord v 1 ^ 2 := by
      field_simp
      nlinarith [hs]
    rw [he]; linarith
  · rintro ⟨hr, hp0, hp1⟩
    have hplus : 0 ≤ coord v 0 + coord v 1 := by
      simpa [div_nonneg_iff, hp.le, not_le_of_gt hp] using hp0
    have hminus : 0 ≤ coord v 0 - coord v 1 := by
      simpa [div_nonneg_iff, hp.le, not_le_of_gt hp] using hp1
    have he : 2 * ((coord v 0 + coord v 1) / Real.sqrt 2) * ((coord v 0 - coord v 1) / Real.sqrt 2) = coord v 0 ^ 2 - coord v 1 ^ 2 := by
      field_simp
      nlinarith [hs]
    rw [he] at hr
    constructor <;> linarith

#print axioms solution
