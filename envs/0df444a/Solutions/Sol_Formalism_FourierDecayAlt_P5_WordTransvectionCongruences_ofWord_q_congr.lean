-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_q_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:41:43.818414+00:00
-- url     : https://prove2.me/submissions/4899744c-f623-47df-a402-d52d31f12f60

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
theorem _root_.solution (L : R.LevelData A r) (st st' : Fr.Start A) (hq : st'.q = st.q) (w : List (Letter ℂ S)) :
    (Fr.ofWord L st' w).q = (Fr.ofWord L st w).q := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hq]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih, hq]
end Formalism.FourierDecayAlt.P5.WordTransvectionCongruences
