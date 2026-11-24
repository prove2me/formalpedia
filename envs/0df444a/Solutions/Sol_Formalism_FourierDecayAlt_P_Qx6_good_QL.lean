-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.good_QL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:26:01.396995+00:00
-- url     : https://prove2.me/submissions/643c90f0-a7ea-428a-b6c5-3126d8bc2f25

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_RS_QL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_good_of

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
variable {L : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hTP : TPreservesFF) (hLL : TLinLoc) (hz : inWb k r z) (hz' : inWb k r z')
    (hS : SData z z' L Dc Dc (OmX r)) (Y : ℂ) (a b : Fin 2) : (famData π π' hS).Good (QL k r z z' L Y a b) :=
  good_of hS (RS_QL hTP hLL hz hz' hS Y a b) (fun Φ Ψ h h' s c hc g hg hgD =>
    (hLL _ k r z z' L (Dc c) Y a b (Φ c) (Ψ c) s (hS.d c hc).1 (h.2 c hc).1 (h'.2 c hc).1 g ⟨hg, hgD⟩).1)
end Formalism.FourierDecayAlt.P.Qx6
