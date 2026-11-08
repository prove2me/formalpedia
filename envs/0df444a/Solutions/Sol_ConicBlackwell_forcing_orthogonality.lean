-- Prove2me | solution 1 for ConicBlackwell.forcing_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:44:42.588809+00:00
-- url     : https://prove2.me/submissions/a2220a77-b94c-4e0f-b0f4-3b9f9d4cf4c6

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne
import Definitions.Def_ConicBlackwell_chooseDecision
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace Aux_CBFO

open ConicBlackwell

theorem lift_zero {d : ℕ} (a : ℝ) (x : E d) : lift a x 0 = a := rfl

theorem lift_succ {d : ℕ} (a : ℝ) (x : E d) (j : Fin d) : lift a x j.succ = x j := rfl

theorem inner_lift {d : ℕ} (a b : ℝ) (x y : E d) :
    ⟪lift a x, lift b y⟫ = a * b + ⟪x, y⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succ, lift_zero, lift_zero]
  simp only [lift_succ]
  simp only [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
  ring

end Aux_CBFO

open ConicBlackwell Aux_CBFO in
theorem solution {n : ℕ} (X : Set (E n)) (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (x₀ : E n) (hx₀ : x₀ ∈ X) (u : E (n + 1)) (hu : u ∈ cone (lift (kappa X) '' X))
    (f : E n) :
    ⟪u, payoff X (chooseDecision X x₀ u) f⟫ = 0 := by
  obtain ⟨α, hα, _, ⟨x, hx, rfl⟩, rfl⟩ := hu
  have hbdd : BddAbove ((fun x : E n => ‖x‖) '' X) := (hXc.image continuous_norm).bddAbove
  have hxκ : ‖x‖ ≤ kappa X := le_csSup hbdd ⟨x, hx, rfl⟩
  have hu0 : (α • lift (kappa X) x : E (n + 1)) 0 = α * kappa X := by
    rw [PiLp.smul_apply, lift_zero, smul_eq_mul]
  unfold payoff chooseDecision
  by_cases h0 : (α • lift (kappa X) x : E (n + 1)) 0 = 0
  · rw [if_pos h0]
    rw [hu0] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · rw [h, zero_smul, inner_zero_left]
    · have hx0 : x = 0 := norm_le_zero_iff.mp (h ▸ hxκ)
      rw [hx0, real_inner_smul_left, inner_lift, h]
      simp
  · rw [if_neg h0]
    rw [hu0] at h0
    have hα0 : α ≠ 0 := left_ne_zero_of_mul h0
    have hκ0 : kappa X ≠ 0 := right_ne_zero_of_mul h0
    have ht : tail (α • lift (kappa X) x) = α • x := by
      apply PiLp.ext
      intro j
      rw [PiLp.smul_apply]
      show (α • lift (kappa X) x) j.succ = _
      rw [PiLp.smul_apply, lift_succ]
    have hc : kappa X / (α * kappa X) * α = 1 := by field_simp
    rw [hu0, ht, smul_smul, hc, one_smul, real_inner_smul_left, inner_lift, inner_neg_right,
      real_inner_comm x f]
    have hk : kappa X * (⟪x, f⟫ / kappa X) = ⟪x, f⟫ := by field_simp
    rw [hk]
    ring
