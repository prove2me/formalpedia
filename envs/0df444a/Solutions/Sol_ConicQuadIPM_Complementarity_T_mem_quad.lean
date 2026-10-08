-- Prove2me | solution 1 for ConicQuadIPM.Complementarity.T_mem_quad
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:11:11.921281+00:00
-- url     : https://prove2.me/submissions/22a03ddd-e492-4f50-9bc2-112c56b23019

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

private theorem rot_equiv (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) :
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


private lemma tsq (c : ConeKind) (d : ℕ) (hwf : BlockWF c d) : Tmat c d * Tmat c d = 1 := by
  cases c
  · simp [Tmat]
  · simp [Tmat]
  · have hd := hwf.2.2 rfl
    have hs : (1 / Real.sqrt 2) ^ 2 = (1 : ℝ) / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    let z : Fin d := ⟨0, by omega⟩
    let o : Fin d := ⟨1, by omega⟩
    ext a b
    change (∑ j : Fin d, Tmat .rot d a j * Tmat .rot d j b) = if a = b then 1 else 0
    simp only [Tmat]
    by_cases ha : a.val < 2
    · have he : ∀ j : Fin d, (if a.val < 2 ∧ j.val < 2 then (if a.val = 1 ∧ j.val = 1 then -(1 / Real.sqrt 2) else 1 / Real.sqrt 2) else if a = j then 1 else 0) =
          (if j = z then 1 / Real.sqrt 2 else 0) + (if j = o then (if a.val = 1 then -(1 / Real.sqrt 2) else 1 / Real.sqrt 2) else 0) := by
        intro j; simp [ha, z, o, Fin.ext_iff]; split_ifs <;> simp_all <;> omega
      simp_rw [he, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp [z, o, ha]
      split_ifs <;> simp_all [Fin.ext_iff] <;> try omega
      all_goals
        have hi : (Real.sqrt (2 : ℝ))⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
          rw [← mul_inv, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
        rw [hi]
        norm_num
    · rw [Finset.sum_eq_single a]
      · simp [ha]
      · intro j hj hja; simp [ha, Ne.symm hja]
      · simp

theorem solution {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ)
    (hwf : WellFormed kind n) (x : (i : Fin k) → Fin (n i) → ℝ) (hx : inK kind x) :
    ∀ i, inQuad (Tmat (kind i) (n i) *ᵥ x i) := by
  intro i
  have hi := hx i
  have hw := hwf i
  cases hc : kind i
  · have hn : n i = 1 := hw.1 hc
    simp only [hc, inCone, inNonneg] at hi
    simp only [Tmat, one_mulVec]
    constructor
    · have ht : tailSq (x i) 1 = 0 := by
        unfold tailSq
        apply Finset.sum_eq_zero
        intro j hj
        simp [show ¬1 ≤ j.val by have := j.isLt; omega]
      rw [ht]; positivity
    · exact hi
  · simpa [hc, inCone, Tmat] using hi
  · have hd : 2 ≤ n i := hw.2.2 hc
    have hsq := tsq .rot (n i) (by simpa [hc] using hw)
    have he : Tmat .rot (n i) *ᵥ (Tmat .rot (n i) *ᵥ x i) = x i := by
      rw [mulVec_mulVec, hsq, one_mulVec]
    apply (rot_equiv (n i) hd _).2
    rw [he]
    simpa [hc, inCone] using hi

#print axioms solution
