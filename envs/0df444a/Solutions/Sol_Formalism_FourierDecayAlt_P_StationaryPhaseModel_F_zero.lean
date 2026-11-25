-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:46:18.760183+00:00
-- url     : https://prove2.me/submissions/e22ef5e8-62fe-4308-ad72-f92c187185cc

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_zero_small
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_norm_psi_alt
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_bump_cutoff_spec
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_bump_cutoff_deriv_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_oscillatory_integral_trivial_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (d : ℕ) (hd : 0 < d) (β : ℂ) (hβ : β ≠ 0) (r Λ : ℝ) (hr : 0 < r) (hΛ : 0 < Λ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (g : (Fin d → ℂ) → ℂ) (dg : (Fin d → ℂ) → Fin d → ℂ) (H : Matrix (Fin d) (Fin d) ℂ),
      DifferentiableOn ℂ g (Metric.ball 0 (2 * r)) → (∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ‖g x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
        HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k)) →
      (∀ k, dg 0 k = 0) →
      (∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0) →
      (∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ‖x‖ ≤ Λ * ‖dg x‖) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (a : (Fin d → ℂ) → V) (S : ℝ),
        ContDiff ℝ (2 * d + 2 : ℕ) a → Function.support a ⊆ Metric.closedBall 0 r →
        (∀ j ≤ 2 * d + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) →
        ∀ t : ℂ, t ≠ 0 →
          ‖∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d)) -
              (psi β (g 0 / t) * ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ)) • a 0‖ ≤ C * S * ‖t‖ ^ (d + 1) := by
  obtain ⟨C₀, hC₀, h₀⟩ := F_zero_small d hd β hβ r Λ hr hΛ
  obtain ⟨Sχ, hSχ⟩ := bump_cutoff_deriv_bound d r hr (2 * d + 2)
  obtain ⟨hχc, -, hχs, hχ0⟩ := bump_cutoff_spec d r hr (2 * d + 2)
  set M : ℝ := (muPi β (Fin d) (Metric.closedBall 0 r)).toReal with hM
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hSχ0 : 0 ≤ Sχ := (norm_nonneg _).trans (hSχ 0 (Nat.zero_le _) 0)
  set D₁ : ℝ := Sχ * M + C₀ * Sχ with hD₁
  have hD₁0 : 0 ≤ D₁ := by positivity
  refine ⟨max C₀ (M + D₁), le_max_of_le_left hC₀, ?_⟩
  intro g dg H hg hb hdg hdg0 hH hgrad V _ _ _ a S ha hsupp hS t ht
  have haS : ∀ x, ‖a x‖ ≤ S := fun x => by
    have := hS 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (haS 0)
  have hτ : 0 < ‖t‖ := norm_pos_iff.2 ht
  rcases le_total ‖t‖ 1 with h1 | h1
  · refine (h₀ g dg H hg hb hdg hdg0 hH hgrad V a S ha hsupp hS t ht h1).trans ?_
    gcongr
    exact le_max_left _ _
  ·
    have hdet : 1 / ‖H.det‖ ≤ D₁ := by
      have h2 := h₀ g dg H hg hb hdg hdg0 hH hgrad ℂ (fun x : Fin d → ℂ => ((cutB d r x : ℝ) : ℂ)) Sχ hχc hχs hSχ 1
        one_ne_zero (by simp)
      have h3 := oscillatory_integral_trivial_bound d β hβ r (fun x => psi β (g x / 1)) (fun x => norm_psi_alt β _)
        (fun x : Fin d → ℂ => ((cutB d r x : ℝ) : ℂ)) Sχ hχs (fun x => by
          have := hSχ 0 (Nat.zero_le _) x
          rwa [norm_iteratedFDeriv_zero] at this)
      have h4 : ‖(psi β (g 0 / 1) * ((‖(1 : ℂ)‖ ^ d / ‖H.det‖ : ℝ) : ℂ)) • ((cutB d r (0 : Fin d → ℂ) : ℝ) : ℂ)‖ =
          1 / ‖H.det‖ := by
        rw [hχ0, norm_smul, norm_mul, norm_psi_alt, norm_one, one_pow, Complex.norm_real, mul_one, one_mul,
          Real.norm_of_nonneg (by positivity)]
      rw [← h4]
      have h5 := norm_sub_norm_le
        ((psi β (g 0 / 1) * ((‖(1 : ℂ)‖ ^ d / ‖H.det‖ : ℝ) : ℂ)) • ((cutB d r (0 : Fin d → ℂ) : ℝ) : ℂ))
        (∫ x : Fin d → ℂ, psi β (g x / 1) • ((cutB d r x : ℝ) : ℂ) ∂(muPi β (Fin d)))
      rw [norm_sub_rev] at h5
      simp only [norm_one, one_pow, mul_one] at h2 h5 ⊢
      linarith
    have h6 := oscillatory_integral_trivial_bound d β hβ r (fun x => psi β (g x / t)) (fun x => norm_psi_alt β _) a S hsupp haS
    have h7 : ‖(psi β (g 0 / t) * ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ)) • a 0‖ ≤ ‖t‖ ^ d * D₁ * S := by
      rw [norm_smul, norm_mul, norm_psi_alt, one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have : ‖t‖ ^ d / ‖H.det‖ = ‖t‖ ^ d * (1 / ‖H.det‖) := by ring
      rw [this]
      gcongr
      exact haS 0
    have h8 : ‖t‖ ^ d ≤ ‖t‖ ^ (d + 1) := pow_le_pow_right₀ h1 (Nat.le_succ d)
    have h9 : (1 : ℝ) ≤ ‖t‖ ^ (d + 1) := one_le_pow₀ h1
    calc _ ≤ S * M + ‖t‖ ^ d * D₁ * S := (norm_sub_le _ _).trans (add_le_add h6 h7)
      _ ≤ S * M * ‖t‖ ^ (d + 1) + ‖t‖ ^ (d + 1) * D₁ * S := by
          refine add_le_add (le_mul_of_one_le_right (by positivity) h9) ?_
          gcongr
      _ = (M + D₁) * S * ‖t‖ ^ (d + 1) := by ring
      _ ≤ max C₀ (M + D₁) * S * ‖t‖ ^ (d + 1) := by
          gcongr
          exact le_max_right _ _
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
