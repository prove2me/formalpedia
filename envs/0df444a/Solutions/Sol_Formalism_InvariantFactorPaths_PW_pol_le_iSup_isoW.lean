-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.pol_le_iSup_isoW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:50:23.615833+00:00
-- url     : https://prove2.me/submissions/a5c03261-40c0-4591-bac5-fa8ccd14a890

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_PolLeISupIsoW
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_span_hw
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_subset_gS
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_pol_finW
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_pol_stable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL L2 : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) :
    Pol p r L2 ≤ ⨆ μ, IsoW (GAe p LL j e) (Pol p r L2) μ := by
  classical
  obtain ⟨S, hS⟩ := GAe_pol_finW (p := p) LL L2 j e
  have key := Formalism.CountingSumsFrames.GlX.span_hw (GAe p LL j e) (GAe_pol_stable LL L2 j e) hS
    (ι := {v : MvPolynomial (Fin N × Fin r) ℚ_[p] // v ∈ Pol p r L2 ∧ v ≠ 0 ∧
      ∃ μ, (GAe p LL j e).IsHW μ v})
    (fun i => i.1) (fun i => i.2.2.2.choose) (fun i => i.2.2.2.choose_spec) (fun i => i.2.1) (fun i => i.2.2.1)
    (by
      intro μ v hv hw
      by_cases h0 : v = 0
      · rw [h0]; exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨v, hv, h0, μ, hw⟩, rfl⟩)
  refine key.trans (iSup_le fun i => ?_)
  refine le_trans ?_ (le_iSup _ i.2.2.2.choose)
  refine GlW.gS_le _ ?_ (GlW.gS_stable _ _)
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  subst hv
  exact GlW.subset_gS _ _ ⟨i.2.2.2.choose_spec, i.2.1⟩
end Formalism.InvariantFactorPaths.PW
