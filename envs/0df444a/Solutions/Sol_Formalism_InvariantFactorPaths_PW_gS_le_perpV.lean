-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.gS_le_perpV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:22:37.613725+00:00
-- url     : https://prove2.me/submissions/451f2def-ab4f-4230-9afb-0f5c931ae10b

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_mem_perpV
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_fock_wt_ne
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Lw_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le_Lw
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_E
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_fischerAdjointness_holds
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_zero_right__1016718d7644


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
theorem _root_.solution (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) {μ ν : Fin n → ℤ} (hne : μ ≠ ν)
    {h h' : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hh : (GAe p LL j e).IsHW μ h) (hh' : (GAe p LL j e).IsHW ν h') :
    (GAe p LL j e).gS {h} ≤ perpV h' := by
  refine le_trans ((GAe p LL j e).gS_le_Lw hh) ?_
  refine (GAe p LL j e).Lw_le h ?_ ?_
  · rw [mem_perpV]
    exact fock_wt_ne LL j e hne hh.1 hh'.1
  · intro a b hba x _
    rw [mem_perpV]
    have hk : (GAe p LL j e).E b a h' = 0 := hh'.2 b a hba
    rw [GAe_E] at hk ⊢
    rw [fischerAdjointness_holds p N r LL j (e a) (e b) x h', hk, fock_zero_right']
end Formalism.InvariantFactorPaths.PW
