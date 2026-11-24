-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.kcls_Psc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:50:19.647072+00:00
-- url     : https://prove2.me/submissions/5f697e74-50cc-492d-88e8-4a89425b584e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_supp_bounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_isCompact_Sset
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_gI_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_contDiff_Psc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBJ Formalism.FourierDecayAlt.P.PBJ.Frz
open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open scoped Convolution
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.PBJ.Frz
theorem _root_.solution [CompleteSpace V] (β c : ℂ) {p : ℕ} {Ψ : G.Mat (p + 1) → V} (hΨ : KCls Ψ) (hc : c ≠ 0) :
    KCls (Psc β c Ψ) := by
  obtain ⟨R, δ, hR, hδ, hb⟩ := supp_bounds hΨ
  have hpos : 0 < δ / ‖c‖ := div_pos hδ (norm_pos_iff.2 hc)
  have hsupp : Function.support (Psc β c Ψ) ⊆ Sset p R (δ / ‖c‖) := by
    intro H hH
    by_contra hS
    apply hH
    have h0 : ∀ y, gI β c Ψ H y = 0 := fun y => by
      by_contra hne
      exact hS (gI_ne hR hδ hb hne).1
    show ∫ y, gI β c Ψ H y = 0
    simp [h0]
  have hcl : IsClosed (Sset p R (δ / ‖c‖)) := (isCompact_Sset p R _).isClosed
  have hts : tsupport (Psc β c Ψ) ⊆ Sset p R (δ / ‖c‖) := closure_minimal hsupp hcl
  refine ⟨contDiff_Psc β c hΨ hc, ?_, fun H hH => ?_⟩
  · exact (isCompact_Sset p R _).of_isClosed_subset (isClosed_tsupport _) hts
  · exact norm_pos_iff.1 (lt_of_lt_of_le hpos (hts hH).2)
end Formalism.FourierDecayAlt.P.PBJ.Frz
