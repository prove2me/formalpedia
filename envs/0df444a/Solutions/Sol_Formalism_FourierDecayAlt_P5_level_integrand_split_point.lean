-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.level_integrand_split_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:48:03.360162+00:00
-- url     : https://prove2.me/submissions/9148c6e6-56ef-49d2-a6c9-ee5f57d01484

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSplitAssocMeasurePreserving
import Theorems.Thm_Formalism_FourierDecayAlt_P5_level_product_act_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P5_glue_coordinate_split
import Theorems.Thm_Formalism_FourierDecayAlt_P5_weight_coordinate_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (w : List (Letter ℂ S)) (l : Fin r) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ)
    (q : Cf r l.succ × Mt k r) :
    levelIntegrand L st w l.castSucc x y c ((coordinateSplitAssoc l).symm (t, q)) =
      ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * levelIntegrand L st w l.succ (act (bTl L l w) x) (act (bTl L l w) y)
        (Function.update c l t) q := by
  have hq : (coordinateSplitAssoc l).symm (t, q) = ((coordinateSplit l).symm (t, q.1), q.2) := rfl
  rw [hq]
  simp only [levelIntegrand]
  rw [weight_coordinate_split l ((coordinateSplit l).symm (t, q.1)), glue_coordinate_split l c]
  simp only [MeasurableEquiv.apply_symm_apply, Fin.coe_castSucc, Fin.val_succ, level_product_act_succ]
  push_cast
  ring
end Formalism.FourierDecayAlt.P5
