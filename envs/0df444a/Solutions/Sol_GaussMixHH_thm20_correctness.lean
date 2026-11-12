-- Prove2me | solution 1 for GaussMixHH.thm20_correctness
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T23:51:59.342581+00:00
-- url     : https://prove2.me/submissions/ce3cfd79-e7cd-4032-8777-96f793ff824b

import Mathlib
import Definitions.Def_GaussMixHH_GridFit
import Definitions.Def_GaussMixHH_Gapped

open MeasureTheory Complex

open GaussMixHH in
theorem solution (n : ℕ) (R η Γ θ₀ q : ℝ) (ρ : MeasureTheory.Measure ℝ) (G : Finset ℝ)
    (H : ℕ) (θs : Fin H → ℝ) (Φhat : Fin H → ℂ) (xstar : ℝ → ℝ) (hΓ : 0 < Γ) (hH : 0 < H)
    (hx : IsProbVec G xstar) (hnm : nearMassVec R G xstar = nearMass R ρ)
    (hgrid : ∀ t, ‖PhiRad n ρ (θs t) - PhiVec n G xstar (θs t)‖ ≤ Γ / 1000)
    (h9 : ∀ t, ‖Φhat t - PhiRad n ρ (θs t)‖ ≤ Γ / 1000)
    (h8 : ∀ x y : ℝ → ℝ, IsProbVec G x → IsProbVec G y →
      |empSqDiff n G θs x y - avgSqDiff n G θ₀ q x y| ≤ Γ ^ 2 / 25)
    (hsep : ∀ x : ℝ → ℝ, IsProbVec G x →
      η ≤ |nearMassVec R G x - nearMassVec R G xstar| → 16 * Γ ^ 2 ≤ avgSqDiff n G θ₀ q x xstar) :
    ∀ x : ℝ → ℝ, IsProbVec G x →
      fitObjective n G θs Φhat x ≤
        sInf (fitObjective n G θs Φhat '' {y | IsProbVec G y}) + Γ ^ 2 / 100 →
      |nearMassVec R G x - nearMass R ρ| < η := by
  intro x hxp hfit
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hHinv : (0 : ℝ) ≤ (H : ℝ)⁻¹ := inv_nonneg.2 hHpos.le
  have hstar : ∀ t, ‖PhiVec n G xstar (θs t) - Φhat t‖ ≤ Γ / 500 := by
    intro t
    have h1 := norm_sub_le_norm_sub_add_norm_sub (PhiVec n G xstar (θs t)) (PhiRad n ρ (θs t))
      (Φhat t)
    have h2 := hgrid t
    have h3 := h9 t
    rw [norm_sub_rev] at h2
    rw [norm_sub_rev] at h3
    linarith
  have hfitstar : fitObjective n G θs Φhat xstar ≤ (Γ / 500) ^ 2 := by
    unfold fitObjective
    have hs : ∑ t, ‖PhiVec n G xstar (θs t) - Φhat t‖ ^ 2 ≤ ∑ _t : Fin H, (Γ / 500) ^ 2 :=
      Finset.sum_le_sum (fun t _ => pow_le_pow_left₀ (norm_nonneg _) (hstar t) 2)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    calc (H : ℝ)⁻¹ * ∑ t, ‖PhiVec n G xstar (θs t) - Φhat t‖ ^ 2
        ≤ (H : ℝ)⁻¹ * ((H : ℝ) * (Γ / 500) ^ 2) := mul_le_mul_of_nonneg_left hs hHinv
      _ = (Γ / 500) ^ 2 := by rw [← mul_assoc, inv_mul_cancel₀ hHpos.ne', one_mul]
  have hbdd : BddBelow (fitObjective n G θs Φhat '' {y | IsProbVec G y}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, _, rfl⟩
    unfold fitObjective
    positivity
  have hinf : sInf (fitObjective n G θs Φhat '' {y | IsProbVec G y}) ≤
      fitObjective n G θs Φhat xstar := csInf_le hbdd ⟨xstar, hx, rfl⟩
  have hemp : empSqDiff n G θs x xstar ≤
      2 * fitObjective n G θs Φhat x + 2 * fitObjective n G θs Φhat xstar := by
    unfold empSqDiff fitObjective
    have hs : ∑ t, ‖PhiVec n G x (θs t) - PhiVec n G xstar (θs t)‖ ^ 2 ≤
        ∑ t, (2 * ‖PhiVec n G x (θs t) - Φhat t‖ ^ 2 +
          2 * ‖PhiVec n G xstar (θs t) - Φhat t‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro t _
      have h1 := norm_sub_le_norm_sub_add_norm_sub (PhiVec n G x (θs t)) (Φhat t)
        (PhiVec n G xstar (θs t))
      rw [norm_sub_rev (Φhat t)] at h1
      have h0 := norm_nonneg (PhiVec n G x (θs t) - PhiVec n G xstar (θs t))
      nlinarith [sq_nonneg (‖PhiVec n G x (θs t) - Φhat t‖ -
        ‖PhiVec n G xstar (θs t) - Φhat t‖), norm_nonneg (PhiVec n G x (θs t) - Φhat t),
        norm_nonneg (PhiVec n G xstar (θs t) - Φhat t)]
    have hm := mul_le_mul_of_nonneg_left hs hHinv
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hm
    linarith
  have habs := h8 x xstar hxp hx
  have havg : avgSqDiff n G θ₀ q x xstar ≤ empSqDiff n G θs x xstar + Γ ^ 2 / 25 := by
    have := (abs_le.1 habs).1
    linarith
  by_contra hc
  push_neg at hc
  rw [← hnm] at hc
  have hsep' := hsep x hxp hc
  have hG2 : 0 < Γ ^ 2 := pow_pos hΓ 2
  nlinarith
