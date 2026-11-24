-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.fam_QL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:43:56.393886+00:00
-- url     : https://prove2.me/submissions/6c67d0d7-b9da-4ad2-9ee6-62bfa0a8523a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_pres_tL


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
variable {L : Fin (r + 1)} {Dc Dc₀ : (Fin r → ℂ) → Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hTP : TPreservesFF) (hz : inWb k r z) (hz' : inWb k r z')
    (hd : ∀ c ∈ OmX r, IsDom k r z z' L (Dc c)) (Y : ℂ) (a b : Fin 2) {Φ : Fn k r (Wq →L[ℂ] Wp)}
    (h : FamFF k r z z' π π' L Dc Φ) : FamFF k r z z' π π' L Dc (QL k r z z' L Y a b Φ) :=
  ⟨Qx3.pres_tL z z' Y a b Φ h.1,
    fun c hc => hTP Wp Wq k r z z' π π' L (Dc c) Y a b hz hz' (hd c hc) (Φ c) (h.2 c hc)⟩
end Formalism.FourierDecayAlt.P.Qx6
