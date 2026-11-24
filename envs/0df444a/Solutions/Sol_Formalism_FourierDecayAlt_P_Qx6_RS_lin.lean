-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.RS_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:42:18.740281+00:00
-- url     : https://prove2.me/submissions/d6d45b49-c384-4375-885f-bba01cab7363

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul


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
variable {S : Set (Fin r → ℂ)}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution : LinRel (RS z z' π π' L Dc Dc₀ S) where
  zero := ⟨fam_zero, fam_zero, fun _ _ _ _ _ => rfl⟩
  add := fun h h' => ⟨fam_add h.1 h'.1, fam_add h.2.1 h'.2.1, fun c hc g hg hgD => by
    simp only [Pi.add_apply, h.2.2 c hc g hg hgD, h'.2.2 c hc g hg hgD]⟩
  smul := fun s _ _ h => ⟨fam_smul s h.1, fam_smul s h.2.1, fun c hc g hg hgD => by
    simp only [Pi.smul_apply, h.2.2 c hc g hg hgD]⟩
end Formalism.FourierDecayAlt.P.Qx6
