-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.gSall_le_perpV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:30:54.443503+00:00
-- url     : https://prove2.me/submissions/e7b28879-5ddf-4917-8b7b-b56107aa2643

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_mem_perpV
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_mem_perpS
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_gS_le_perpV
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_subset_gS
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_E
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_fischerAdjointness_holds
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_symm__e96ddd2ea090


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
    {h' : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hh' : (GAe p LL j e).IsHW ν h') :
    (GAe p LL j e).gS {v | (GAe p LL j e).IsHW μ v} ≤ perpV h' := by
  have hA : (GAe p LL j e).Stable ((GAe p LL j e).gS {h'}) := (GAe p LL j e).gS_stable _
  have hst : (GAe p LL j e).Stable (perpS ((GAe p LL j e).gS {h'})) := by
    intro a b y hy
    rw [mem_perpS] at hy ⊢
    intro x hx
    have hmem := hA b a x hx
    rw [GAe_E] at hmem ⊢
    rw [← fischerAdjointness_holds p N r LL j (e b) (e a) x y]
    exact hy _ hmem
  refine le_trans ((GAe p LL j e).gS_le ?_ hst) ?_
  · intro v hv
    rw [SetLike.mem_coe, mem_perpS]
    intro y hy
    have hy' := gS_le_perpV LL j e (Ne.symm hne) hh' hv hy
    rw [mem_perpV] at hy'
    exact hy'
  · intro y hy
    rw [mem_perpS] at hy
    rw [mem_perpV, fock_symm']
    exact hy h' ((GAe p LL j e).subset_gS {h'} (Set.mem_singleton h'))
end Formalism.InvariantFactorPaths.PW
