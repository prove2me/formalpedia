-- Prove2me | solution 1 for ConicQuadIPM.NTScaling.rot_scaling_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:15:54.381685+00:00
-- url     : https://prove2.me/submissions/ef8d5f3a-8c56-4242-8642-343adfdede5b

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
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

private lemma tsym (c : ConeKind) (d : ℕ) : (Tmat c d)ᵀ = Tmat c d := by
  cases c
  · simp [Tmat]
  · simp [Tmat]
  · ext a b
    change Tmat .rot d b a = Tmat .rot d a b
    simp only [Tmat]
    simp [and_comm, eq_comm]

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

private lemma conjugateQ (d : ℕ) (hd : 2 ≤ d) :
    Tmat .rot d * Qmat .rot d * Tmat .rot d = Qmat .quad d := by
  have ht : Tmat .rot d * Tmat .rot d = 1 := tsq .rot d ⟨by simp, by simp, by simpa⟩
  have hc : Tmat .rot d * Qmat .rot d = Qmat .quad d * Tmat .rot d := by
    apply Matrix.ext_iff_mulVec.2
    intro v
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    ext a
    rw [taction d hd]
    have h0 : coord (Qmat .rot d *ᵥ v) 0 = coord v 1 := by
      rw [coordinate _ 0 (by omega), qrot_action d hd]; simp
    have h1 : coord (Qmat .rot d *ᵥ v) 1 = coord v 0 := by
      rw [coordinate _ 1 (by omega), qrot_action d hd]; simp
    rw [h0, h1]
    have hq : ∀ u : Fin d → ℝ, (Qmat .quad d *ᵥ u) a = (if a.val = 0 then 1 else -1) * u a := by
      intro u; simp [Qmat, mulVec_diagonal]
    rw [hq]
    rw [taction d hd, qrot_action d hd]
    split_ifs <;> simp_all <;> ring
  rw [hc, mul_assoc, ht, mul_one]

private lemma ntQmatch (c : ConeKind) (d : ℕ) :
    ConicQuadIPM.NTScaling.Qmat c d = Qmat c d := by
  cases c
  · rfl
  · ext a b
    simp [ConicQuadIPM.NTScaling.Qmat, Qmat, diagonal_apply]
  · ext a b
    change (if (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0) then (1 : ℝ)
      else if a = b ∧ 2 ≤ a.val then -1 else 0) =
      (if a.val < 2 ∧ b.val < 2 then (if a.val ≠ b.val then 1 else 0) else if a = b then -1 else 0)
    split_ifs <;> simp_all [Fin.ext_iff] <;> omega

theorem solution (d : ℕ) (hd : 2 ≤ d) (w : Fin d → ℝ) :
    ConicQuadIPM.NTScaling.Tmat .rot d * ConicQuadIPM.NTScaling.Wrot d w * ConicQuadIPM.NTScaling.Tmat .rot d = ConicQuadIPM.NTScaling.WquadOuter d (ConicQuadIPM.NTScaling.Tmat .rot d *ᵥ w) := by
  have htm : ConicQuadIPM.NTScaling.Tmat .rot d = Tmat .rot d := rfl
  have ht : Tmat .rot d * Tmat .rot d = 1 := tsq .rot d ⟨by simp, by simp, by simpa⟩
  have hts := tsym .rot d
  unfold ConicQuadIPM.NTScaling.Wrot ConicQuadIPM.NTScaling.WquadOuter
  rw [htm, ntQmatch, ntQmatch]
  rw [mul_add, add_mul, mul_neg, neg_mul, conjugateQ d hd, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul]
  have hv : Tmat .rot d *ᵥ (Tmat .rot d *ᵥ e1 + w) = e1 + Tmat .rot d *ᵥ w := by
    rw [mulVec_add, mulVec_mulVec, ht, one_mulVec]
  have hr : (Tmat .rot d *ᵥ e1 + w) ᵥ* Tmat .rot d = e1 + Tmat .rot d *ᵥ w := by
    calc
      (Tmat .rot d *ᵥ e1 + w) ᵥ* Tmat .rot d = (Tmat .rot d *ᵥ e1 + w) ᵥ* (Tmat .rot d)ᵀ := by rw [hts]
      _ = _ := by rw [vecMul_transpose, hv]
  rw [hv, hr]

#print axioms solution
