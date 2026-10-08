-- Prove2me | solution 1 for ConicQuadIPM.NTScaling.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:11:15.846622+00:00
-- url     : https://prove2.me/submissions/4312deeb-284a-44c0-b31c-5823993249a5

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix ConicQuadIPM.Complementarity
set_option maxRecDepth 4000
private lemma comp_qsq (c : ConeKind) (d : ℕ) (hwf : BlockWF c d) : Qmat c d * Qmat c d = 1 := by
  cases c
  · simp [Qmat]
  · simp only [Qmat, diagonal_mul_diagonal]
    ext a b
    by_cases h : a.val = 0 <;> simp [h, diagonal_apply, one_apply]
  · have hd := hwf.2.2 rfl
    let z : Fin d := ⟨0, by omega⟩
    let o : Fin d := ⟨1, by omega⟩
    ext a b
    change (∑ j : Fin d, Qmat .rot d a j * Qmat .rot d j b) = if a = b then 1 else 0
    simp only [Qmat]
    by_cases ha : a.val < 2
    · have ha' : a = z ∨ a = o := by dsimp [z, o]; rcases (by omega : a.val = 0 ∨ a.val = 1) with h | h <;> [left; right] <;> apply Fin.ext <;> exact h
      rcases ha' with rfl | rfl
      · rw [Finset.sum_eq_single o]
        · by_cases hb : b = z <;> simp_all [z, o, Fin.ext_iff] <;> split_ifs <;> simp_all <;> omega
        · intro j hj hjo
          have : j.val ≠ 1 := by intro h; apply hjo; apply Fin.ext; exact h
          simp [z, o, this]; split_ifs <;> simp_all <;> omega
        · simp
      · rw [Finset.sum_eq_single z]
        · by_cases hb : b = o <;> simp_all [z, o, Fin.ext_iff] <;> split_ifs <;> simp_all <;> omega
        · intro j hj hjz
          have : j.val ≠ 0 := by intro h; apply hjz; apply Fin.ext; exact h
          simp [z, o, this]; split_ifs <;> simp_all <;> omega
        · simp
    · rw [Finset.sum_eq_single a]
      · simp [ha]
      · intro j hj hja; simp [ha, Ne.symm hja]
      · simp


private lemma qmatch (c : ConeKind) (d : ℕ) :
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

open ConicQuadIPM.NTScaling in
theorem solution (kind : ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d)
    (θ : ℝ) (hθ : 0 < θ) (W : Matrix (Fin d) (Fin d) ℝ) (hW : IsScaling kind d W) :
    (θ • W)⁻¹ * (θ • W)⁻¹ = (θ ^ 2)⁻¹ • (ConicQuadIPM.NTScaling.Qmat kind d * (W * W) * ConicQuadIPM.NTScaling.Qmat kind d) := by
  let Q := ConicQuadIPM.NTScaling.Qmat kind d
  have hQ : Q * Q = 1 := by
    dsimp [Q]; rw [qmatch]; exact comp_qsq kind d hwf
  have hsc : W * Q * W = Q := hW.2
  have hi : (θ • W)⁻¹ = θ⁻¹ • (Q * W * Q) := by
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_smul, mul_inv_cancel₀ hθ.ne', one_smul]
    calc
      W * (Q * W * Q) = (W * Q * W) * Q := by noncomm_ring
      _ = 1 := by rw [hsc, hQ]
  rw [hi, smul_mul_smul, ← pow_two, ← inv_pow]
  congr 1
  calc
    (Q * W * Q) * (Q * W * Q) = Q * W * (Q * Q) * W * Q := by noncomm_ring
    _ = Q * (W * W) * Q := by rw [hQ]; simp [mul_assoc]

#print axioms solution

