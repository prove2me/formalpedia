-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.HatData.Good.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:37:54.297117+00:00
-- url     : https://prove2.me/submissions/b75f0127-9330-47e1-856a-de8e97ec0c95

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.FourierDecayAlt.P.Qx6.HatData
variable {X : Type*} [AddCommGroup X] [Module ℂ X] (H : HatData X)
variable {H}
variable (H)
variable {H}
namespace Formalism.FourierDecayAlt.P.Qx6.HatData
namespace Good
theorem _root_.solution {T S : X → X} (hT : H.Good T) (hS : H.Good S) : H.Good (fun x => T (S x)) where
  mem := fun x hx => hT.mem _ (hS.mem x hx)
  congr := fun x hx y hy h => hT.congr _ (hS.mem x hx) _ (hS.mem y hy) (hS.congr x hx y hy h)
  lin := fun x hx y hy s => by
    have h1 : H.N (S (x + s • y)) = H.N (S x + s • S y) := by
      rw [hS.lin x hx y hy s, _root_.map_add, _root_.map_smul]
    rw [hT.congr _ (hS.mem _ (H.G.add_mem hx (H.G.smul_mem s hy))) _
      (H.G.add_mem (hS.mem x hx) (H.G.smul_mem s (hS.mem y hy))) h1]
    exact hT.lin _ (hS.mem x hx) _ (hS.mem y hy) s
end Good
end Formalism.FourierDecayAlt.P.Qx6.HatData
