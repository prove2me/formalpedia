-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBB.K8.bound_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:09.593712+00:00
-- url     : https://prove2.me/submissions/1b90cd4d-2115-4114-b4e4-182814cbd319

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramLocTendsto
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBB_K8_dw_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Real NumberField
open scoped FourierTransform RealInnerProductSpace ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBB Formalism.FourierDecayAlt.P.PBB.K8
noncomputable section
namespace Formalism.FourierDecayAlt.P.PBB.K8
theorem _root_.solution {f : ℂ → ℂ} (hf : Continuous f) {C : ℝ} (h : ∀ c, c ≠ 0 → ‖f c‖ ≤ C * dw c) (c : ℂ) :
    ‖f c‖ ≤ C * dw c := by
  have hs : IsClosed {c : ℂ | ‖f c‖ ≤ C * dw c} :=
    isClosed_le (continuous_norm.comp hf) (continuous_const.mul dw_cont)
  have hsub : ({0}ᶜ : Set ℂ) ⊆ {c | ‖f c‖ ≤ C * dw c} := fun c hc => h c hc
  have := hs.closure_subset_iff.mpr hsub
  rw [(dense_compl_singleton (0 : ℂ)).closure_eq] at this
  exact this (Set.mem_univ c)
end Formalism.FourierDecayAlt.P.PBB.K8
