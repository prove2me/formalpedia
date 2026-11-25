-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.schur_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:13:31.874488+00:00
-- url     : https://prove2.me/submissions/9515c6dd-f42f-401b-bdcb-8126738ae451

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsSchur
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_norm_sq_eq_re_mul_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} (hS : IsSchur μ σ d) (a b : HH) :
    Integrable (fun γ => ‖⟪a, σ γ b⟫_ℂ‖ ^ 2) μ ∧
      ∫ γ, ‖⟪a, σ γ b⟫_ℂ‖ ^ 2 ∂μ = ‖a‖ ^ 2 * ‖b‖ ^ 2 / d := by
  obtain ⟨hI, hE⟩ := hS.2 b a b a
  have hfun : (fun γ => ‖⟪a, σ γ b⟫_ℂ‖ ^ 2) =
      fun γ => RCLike.re (⟪a, σ γ b⟫_ℂ * conj ⟪a, σ γ b⟫_ℂ) := by
    funext γ
    exact norm_sq_eq_re_mul_conj _
  have h2 : ∫ γ, RCLike.re (⟪a, σ γ b⟫_ℂ * conj ⟪a, σ γ b⟫_ℂ) ∂μ =
      RCLike.re (⟪b, b⟫_ℂ * ⟪a, a⟫_ℂ / (d : ℂ)) := by
    rw [← hE]
    exact integral_re hI
  have hsq : ∀ x : HH, ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hI.re
  · rw [hfun, h2, hsq a, hsq b, ← Complex.ofReal_mul, ← Complex.ofReal_div]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    ring
end Formalism.L2.S.Pv.EnergyAbs
