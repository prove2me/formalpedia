-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.top_density_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:47:50.08882+00:00
-- url     : https://prove2.me/submissions/44286b58-e1f1-4c6a-8bd1-d4ad372e19e9

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P5_act_add_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P5_hsInner_add_smul_right


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
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
  (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
  (w : List (Letter ℂ S))
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (x y y' : Ix S → RadSp k r z z' π π') (a : ℂ) (c : Fin r → ℂ) (g : Mx k r) :
    topDens L st w x (y + a • y') c g = topDens L st w x y c g + conj a * topDens L st w x y' c g := by
  simp only [topDens, act_add_smul, Pi.add_apply, Pi.smul_apply, Submodule.coe_add, Submodule.coe_smul,
    hsInner_add_smul_right, Finset.sum_add_distrib, Finset.mul_sum]
end Formalism.FourierDecayAlt.P5
