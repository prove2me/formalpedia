-- Prove2me | solution 1 for ConicQuadIPM.Complementarity.starting_point
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:15:52.52911+00:00
-- url     : https://prove2.me/submissions/c2c77c08-4b48-402f-bfa9-a85e704b7023

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

private lemma qrot_action (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) (a : Fin d) :
    (Qmat .rot d *ᵥ v) a = if a.val = 0 then coord v 1 else if a.val = 1 then coord v 0 else -v a := by
  let z : Fin d := ⟨0, by omega⟩
  let o : Fin d := ⟨1, by omega⟩
  change (∑ j : Fin d, Qmat .rot d a j * v j) = _
  by_cases h0 : a.val = 0
  · rw [Finset.sum_eq_single o]
    · simp [Qmat, h0, z, o, coordinate v 1 (by omega)]
    · intro j hj hjo
      have hn : j.val ≠ 1 := by intro he; apply hjo; exact Fin.ext he
      simp [Qmat, h0, hn]; split_ifs <;> simp_all [Fin.ext_iff] <;> omega
    · simp
  · by_cases h1 : a.val = 1
    · rw [Finset.sum_eq_single z]
      · simp [Qmat, h1, z, o, coordinate v 0 (by omega)]
      · intro j hj hjz
        have hn : j.val ≠ 0 := by intro he; apply hjz; exact Fin.ext he
        simp [Qmat, h1, hn]; split_ifs <;> simp_all [Fin.ext_iff] <;> omega
      · simp
    · rw [Finset.sum_eq_single a]
      · simp [Qmat, h0, h1, show ¬ a.val < 2 by omega]
      · intro j hj hja
        simp [Qmat, show ¬ a.val < 2 by omega, Ne.symm hja]
      · simp

private lemma quad_form (d : ℕ) (v : Fin d → ℝ) :
    v ⬝ᵥ (Qmat .quad d *ᵥ v) = coord v 0 ^ 2 - tailSq v 1 := by
  have hhead : (∑ j : Fin d, if j.val = 0 then v j ^ 2 else 0) = coord v 0 ^ 2 := by
    cases d with
    | zero => simp [coord]
    | succ d =>
      rw [coordinate v 0 (by omega), Finset.sum_eq_single ⟨0, by omega⟩]
      · simp
      · intro j hj h; simp [show j.val ≠ 0 by intro he; apply h; exact Fin.ext he]
      · simp
  change (∑ j : Fin d, v j * (Qmat .quad d *ᵥ v) j) = _
  have he : ∀ j : Fin d, v j * (Qmat .quad d *ᵥ v) j =
      (if j.val = 0 then v j ^ 2 else 0) - (if 1 ≤ j.val then v j ^ 2 else 0) := by
    intro j
    simp only [Qmat, Matrix.mulVec_diagonal]
    split_ifs <;> simp_all [pow_two] <;> try omega <;> ring
  simp_rw [he, Finset.sum_sub_distrib]
  rw [hhead]; rfl

private lemma rot_form (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) :
    v ⬝ᵥ (Qmat .rot d *ᵥ v) = 2 * coord v 0 * coord v 1 - tailSq v 2 := by
  have he : ∀ j : Fin d, v j * (Qmat .rot d *ᵥ v) j =
      (if j = (⟨0, by omega⟩ : Fin d) then v j * coord v 1 else 0) +
      (if j = (⟨1, by omega⟩ : Fin d) then v j * coord v 0 else 0) -
      (if 2 ≤ j.val then v j ^ 2 else 0) := by
    intro j
    rw [qrot_action d hd]
    simp only [Fin.ext_iff, Fin.val_mk]
    split_ifs <;> simp_all [pow_two] <;> try omega <;> ring
  change (∑ j : Fin d, v j * (Qmat .rot d *ᵥ v) j) = _
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← coordinate v 0 (by omega), ← coordinate v 1 (by omega)]
  unfold tailSq; ring


private lemma ehead (d : ℕ) (hd : 1 ≤ d) : coord (e1 : Fin d → ℝ) 0 = 1 := by
  rw [coordinate _ 0 (by omega)]; simp [e1]

private lemma etail (d : ℕ) (r : ℕ) (hr : 1 ≤ r) : tailSq (e1 : Fin d → ℝ) r = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  simp only [e1]
  split_ifs <;> simp_all <;> omega

private lemma edot (d : ℕ) (hd : 1 ≤ d) : (e1 : Fin d → ℝ) ⬝ᵥ e1 = 1 := by
  change (∑ j : Fin d, e1 j * e1 j) = 1
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · simp [e1]
  · intro j hj h; simp [e1, show j.val ≠ 0 by intro he; apply h; exact Fin.ext he]
  · simp

private lemma block_start (c : ConeKind) (d : ℕ) (hw : BlockWF c d) :
    inCone c (Tmat c d *ᵥ e1) ∧
    (Tmat c d *ᵥ e1) ⬝ᵥ (Tmat c d *ᵥ e1) = 1 ∧
    (Tmat c d *ᵥ e1) ⬝ᵥ (Qmat c d *ᵥ (Tmat c d *ᵥ e1)) = 1 := by
  cases c
  · have hd : 1 ≤ d := by have := hw.1 rfl; omega
    simp only [Tmat, Qmat, one_mulVec, inCone, inNonneg]
    rw [ehead d hd, edot d hd]; norm_num
  · have hd : 1 ≤ d := hw.2.1 rfl
    simp only [Tmat, one_mulVec, inCone, inQuad]
    rw [ehead d hd, etail d 1 (by omega), edot d hd, quad_form, ehead d hd, etail d 1 (by omega)]
    norm_num
  · have hd : 2 ≤ d := hw.2.2 rfl
    let v := Tmat .rot d *ᵥ (e1 : Fin d → ℝ)
    obtain ⟨h0, h1, ht⟩ := tcoords d hd (e1 : Fin d → ℝ)
    have he1 : coord (e1 : Fin d → ℝ) 1 = 0 := by rw [coordinate _ 1 (by omega)]; simp [e1]
    rw [ehead d (by omega), he1] at h0 h1
    rw [etail d 2 (by omega)] at ht
    simp only [add_zero, sub_zero] at h0 h1
    have hs : (1 / Real.sqrt (2 : ℝ)) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    have hvdot : v ⬝ᵥ v = 1 := by
      have he : ∀ a : Fin d, v a = if a.val = 0 ∨ a.val = 1 then 1 / Real.sqrt 2 else 0 := by
        intro a
        dsimp [v]
        rw [taction d hd, ehead d (by omega), he1]
        simp [e1]; split_ifs <;> simp_all <;> omega
      change (∑ a : Fin d, v a * v a) = 1
      have he' : ∀ a : Fin d, v a * v a =
          (if a = (⟨0, by omega⟩ : Fin d) then (1 / Real.sqrt 2)^2 else 0) +
          (if a = (⟨1, by omega⟩ : Fin d) then (1 / Real.sqrt 2)^2 else 0) := by
        intro a; rw [he]; simp [Fin.ext_iff, pow_two]; split_ifs <;> simp_all <;> omega
      simp_rw [he', Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hs]; norm_num
    refine ⟨?_, hvdot, ?_⟩
    · change inRot v
      unfold inRot
      change tailSq (Tmat .rot d *ᵥ e1) 2 ≤ _ ∧ _
      rw [ht, h0, h1]
      constructor
      · positivity
      · constructor <;> positivity
    · rw [rot_form d hd, h0, h1, ht]
      nlinarith [hs]

theorem solution {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ)
    (hwf : WellFormed kind n) :
    Nbhd kind n 1
      (fun i => Tmat (kind i) (n i) *ᵥ (e1 : Fin (n i) → ℝ)) 1
      (fun i => Tmat (kind i) (n i) *ᵥ (e1 : Fin (n i) → ℝ)) 1 := by
  have hb := fun i => block_start (kind i) (n i) (hwf i)
  have hm : mu (fun i => Tmat (kind i) (n i) *ᵥ e1)
      (fun i => Tmat (kind i) (n i) *ᵥ e1) 1 1 = 1 := by
    unfold mu
    simp_rw [(hb _).2.1]
    simp
    positivity
  unfold Nbhd
  rw [hm]
  refine ⟨fun i => (hb i).1, by norm_num, fun i => (hb i).1, by norm_num, ?_, by norm_num⟩
  intro i
  rw [(hb i).2.2]
  norm_num

#print axioms solution
