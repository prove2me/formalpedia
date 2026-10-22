-- Prove2me | solution 1 for ContJRP.Align.claim_1_1_eoq_properties
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:01:24.547049+00:00
-- url     : https://prove2.me/submissions/069247a3-88d1-4dce-8c53-9a30798925be

import Mathlib
import Definitions.Def_ContJRP_Align_Model

set_option autoImplicit false
open ContJRP.Align

theorem solution (K H : ℝ) (hK : 0 < K) (hH : 0 < H) :
    (∀ T, 0 < T → 0 < eoqCost K H T) ∧
    StrictConvexOn ℝ (Set.Ioi 0) (eoqCost K H) ∧
    (0 < Real.sqrt (K / H) ∧ ∀ T, 0 < T → eoqCost K H (Real.sqrt (K / H)) ≤ eoqCost K H T) ∧
    (∀ T, 0 < T → eoqCost K H T = eoqCost K H (Real.sqrt (K / H)) → T = Real.sqrt (K / H)) ∧
    ∀ θ, 0 < θ → eoqCost K H (θ * Real.sqrt (K / H)) =
      1 / 2 * (θ + 1 / θ) * eoqCost K H (Real.sqrt (K / H)) := by
  have hs0 : 0 < Real.sqrt (K / H) := Real.sqrt_pos.mpr (div_pos hK hH)
  have hs2 : Real.sqrt (K / H) ^ 2 = K / H := Real.sq_sqrt (div_pos hK hH).le
  set s := Real.sqrt (K / H) with hs
  have hKs : K = H * s ^ 2 := by rw [hs2]; field_simp
  have hCs : eoqCost K H s = 2 * H * s := by
    unfold eoqCost; rw [hKs]; field_simp; ring
  have hdiff : ∀ T : ℝ, 0 < T → eoqCost K H T - eoqCost K H s = H * (s - T) ^ 2 / T := by
    intro T hT
    unfold eoqCost; rw [hKs]; field_simp; ring
  refine ⟨?_, ?_, ⟨hs0, ?_⟩, ?_, ?_⟩
  · intro T hT; unfold eoqCost; positivity
  · refine ⟨convex_Ioi 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have h := (strictConvexOn_zpow (m := -1) (by norm_num) (by norm_num)).2 hx hy hxy ha hb hab
    simp only [zpow_neg_one, smul_eq_mul] at h ⊢
    unfold eoqCost
    have h2 : K * (a * x + b * y)⁻¹ < K * (a * x⁻¹ + b * y⁻¹) := mul_lt_mul_of_pos_left h hK
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    have e : a * (K * x⁻¹ + H * x) + b * (K * y⁻¹ + H * y) =
        K * (a * x⁻¹ + b * y⁻¹) + H * (a * x + b * y) := by ring
    rw [e]
    linarith
  · intro T hT
    have := hdiff T hT
    have : 0 ≤ H * (s - T) ^ 2 / T := by positivity
    linarith
  · intro T hT heq
    have := hdiff T hT
    rw [heq, sub_self] at this
    have h0 : H * (s - T) ^ 2 / T = 0 := this.symm
    have h1 : (s - T) ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp h0 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hH.ne'
        · exact h
      · exact absurd h hT.ne'
    have : s - T = 0 := by simpa using h1
    linarith
  · intro θ hθ
    unfold eoqCost
    rw [hKs]
    field_simp
    ring
