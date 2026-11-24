-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Cx2.inner_dm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:15:40.252908+00:00
-- url     : https://prove2.me/submissions/7cd59824-1153-40e6-b97a-d6aa2f95e124

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstNormRealNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C NumberField MeasureTheory
open scoped ComplexOrder ComplexConjugate RealInnerProductSpace
noncomputable section
open Formalism.FourierDecayAlt.P.Cx2
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.Cx2
theorem _root_.solution (g : ℕ) (l : E) (c : J.CV E) :
    inner ℝ c (J.dm E g 1 (-l)) = -((∑ w : InfinitePlace E, 2 * (w.embedding l * c w).re) / g) := by
  rw [PiLp.inner_apply, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hd : (J.dm E g 1 (-l)) w = ((2 / ((g : ℝ) * 1) : ℝ) : ℂ) * conj (w.embedding (-l)) := rfl
  rw [hd, Complex.inner]
  simp only [map_neg, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, mul_one]
  ring
end Formalism.FourierDecayAlt.P.Cx2
