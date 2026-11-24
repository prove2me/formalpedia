-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.weight_coordinate_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:34:43.224348+00:00
-- url     : https://prove2.me/submissions/fff7384c-cf9c-4c82-be85-c54f10aca267

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P5_coordinate_split_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_coordinate_split_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (l : Fin r) (a : Cf r l.castSucc) :
    (∏ j, ‖a j‖ ^ (-2 : ℤ)) = ‖(coordinateSplit l a).1‖ ^ (-2 : ℤ) * ∏ j, ‖(coordinateSplit l a).2 j‖ ^ (-2 : ℤ) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun j : {j : Fin r // l.castSucc.val ≤ j.val} => j.1 = l)]
  congr 1
  · rw [Fintype.prod_unique, coordinate_split_fst]; rfl
  · rw [← (coordinateRestEquiv l).prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [coordinate_split_snd]; rfl
end Formalism.FourierDecayAlt.P5
