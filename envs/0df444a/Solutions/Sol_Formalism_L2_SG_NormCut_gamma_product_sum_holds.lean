-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.gamma_product_sum_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:20.117835+00:00
-- url     : https://prove2.me/submissions/bcc0502b-aa2d-46ab-a285-2ade30efc203

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCoreGamProdSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
open Formalism.L2.SG.GGMirabolic
namespace Formalism.L2.SG.NormCut
theorem _root_.solution : Formalism.L2.SG.NormCut.GamProdSum := by
  intro ι _ Fq _ _ k ψ x
  refine ⟨?_, ?_⟩
  · unfold gamProd gam
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    congr 1
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rfl
  · rw [Nat.card_congr (Equiv.subtypePiEquivPi), Nat.card_pi]
    rfl
end Formalism.L2.SG.NormCut
