-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G9.tprod_nat_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:42:58.610869+00:00
-- url     : https://prove2.me/submissions/88dd63bd-453e-4174-9841-af0edab4c231

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G9
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
namespace Formalism.L2.SG.Pf.G9
theorem _root_.solution {ι : Type*} (f : ι → ℕ) (hf : ∀ i, f i ≠ 0) : ∏' i, f i ≠ 0 := by
  by_cases hm : Multipliable f
  · have e := hm.hasProd.eventually_mem (IsOpen.mem_nhds (isOpen_discrete {∏' i, f i}) rfl)
    obtain ⟨s, hs⟩ := e.exists
    rw [← Set.mem_singleton_iff.mp hs]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hf i
  · rw [tprod_eq_one_of_not_multipliable hm]
    exact one_ne_zero
end Formalism.L2.SG.Pf.G9
