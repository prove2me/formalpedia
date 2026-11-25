-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBL.nnS_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:13:20.762435+00:00
-- url     : https://prove2.me/submissions/c0c38d18-cc95-43fc-b009-a9680ff03007

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormPos
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeNeZeroComplex
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_weight_product_append
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_weight_product_indep_of_real_parameter


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBL
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBL
theorem _root_.solution (S : C.HidaSetting E Wp Wq) (j : ℕ) (hj : j ≤ S.G.r) (H : C.LPt) (c : ℂ) (hH : D.ptSize H = j) :
    nnS S (H ++ [(1, c)]) = nnS S H *
      C.nAux S.G.k S.G.r (Complex.normSq c - S.T * S.T') S.fr (j + 1) [(1, c)] := by
  simp only [nnS, C.nLoc]
  rw [weight_product_append, hH, show 1 + j = j + 1 by omega]
  have hG : D.ptGG (S.T * S.T') (H ++ [(1, c)]) = Complex.normSq c - S.T * S.T' := by simp [D.ptGG, D.ptLast]
  rw [hG, weight_product_indep_of_real_parameter _ _ _ (D.ptGG (S.T * S.T') H) _ H 1 le_rfl (by omega)]
end Formalism.FourierDecayAlt.P.PBL
