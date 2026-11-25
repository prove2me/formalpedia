-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.small_of_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:16:52.953782+00:00
-- url     : https://prove2.me/submissions/3a604316-d858-4f28-a5e2-b454ebd711dd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
variable {K : Type} [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}
namespace Formalism.L2.S.Pv.SchurTens
theorem _root_.solution (c : ℝ) (hc : 0 ≤ c) (hD : 0 < D) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 ≤ t → t < δ → ENNReal.ofReal (t ^ 2 * c / D) ≤ ε := by
  rcases eq_or_ne ε ⊤ with hte | hne
  · exact ⟨1, one_pos, fun _ _ _ => by rw [hte]; exact le_top⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hne
  have hc1 : (0 : ℝ) < c + 1 := by linarith
  refine ⟨min 1 (ε.toReal * D / (c + 1)), lt_min one_pos (div_pos (mul_pos he hD) hc1),
    fun t ht0 htδ => ?_⟩
  rw [← ENNReal.ofReal_toReal hne]
  apply ENNReal.ofReal_le_ofReal
  have h1 : t < 1 := lt_of_lt_of_le htδ (min_le_left _ _)
  have h2 : t < ε.toReal * D / (c + 1) := lt_of_lt_of_le htδ (min_le_right _ _)
  have h4 : t * (c + 1) ≤ ε.toReal * D := by
    have h5 : t * (c + 1) < ε.toReal * D / (c + 1) * (c + 1) := mul_lt_mul_of_pos_right h2 hc1
    rw [div_mul_cancel₀ _ hc1.ne'] at h5
    exact h5.le
  have h3 : t ^ 2 ≤ t := by nlinarith
  have h6 : t ^ 2 * c ≤ t * c := mul_le_mul_of_nonneg_right h3 hc
  have h7 : t ^ 2 * c ≤ ε.toReal * D := by nlinarith
  have h8 : t ^ 2 * c / D ≤ ε.toReal * D / D := by
    exact div_le_div_of_nonneg_right h7 hD.le
  rwa [mul_div_cancel_right₀ _ hD.ne'] at h8
end Formalism.L2.S.Pv.SchurTens
