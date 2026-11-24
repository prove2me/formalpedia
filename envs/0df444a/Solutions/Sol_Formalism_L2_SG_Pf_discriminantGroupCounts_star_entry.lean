-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantGroupCounts.star_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:18:39.209821+00:00
-- url     : https://prove2.me/submissions/592807bd-98dd-4e68-99be-4fbf20a7d905

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_OneAddFormEqIff
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.HermitianLattices.Ext.L3
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantGroupCounts
variable {A : Type*} [CommRing A] [StarRing A]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {d : m → A}
namespace Formalism.L2.SG.Pf.discriminantGroupCounts
theorem _root_.solution (hd : ∀ i, star (d i) = d i) {a : A} {i j : m} (h : d i * a * d j = 0) :
    d j * star a * d i = 0 := by
  have h' := congrArg star h
  simpa [star_mul, hd, mul_assoc] using h'
end Formalism.L2.SG.Pf.discriminantGroupCounts
