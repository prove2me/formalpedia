-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_xi_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:45:31.245786+00:00
-- url     : https://prove2.me/submissions/1db492af-c1cb-4344-9615-09b8bac7cb91

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDensNonnegOfKappa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexOrder ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
open Formalism.FourierDecayAlt.P5.WordTransvectionCongruences
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P5.WordTransvectionCongruences
theorem _root_.solution (L : R.LevelData A r) (st st' : Fr.Start A) (w : List (Letter ℂ S)) (Y : ℂ)
    (hY : st'.xi Y = st.xi Y) : (Fr.ofWord L st' w).xi Y = (Fr.ofWord L st w).xi Y := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hY]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih, hY]
end Formalism.FourierDecayAlt.P5.WordTransvectionCongruences
