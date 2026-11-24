-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.act_one_hermitian_curvature
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:14:30.810995+00:00
-- url     : https://prove2.me/submissions/9ff45695-e96a-40df-9b21-f851ea35b53b

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable

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
theorem _root_.solution (x : Ix S → RadSp k r z z' π π') : act (1 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) x = x := by
  funext a
  simp only [act, Matrix.one_apply]
  rw [Finset.sum_eq_single a]
  · simp; rfl
  · intro b _ hb; rw [if_neg (Ne.symm hb)]; rfl
  · simp
end Formalism.FourierDecayAlt.P5
