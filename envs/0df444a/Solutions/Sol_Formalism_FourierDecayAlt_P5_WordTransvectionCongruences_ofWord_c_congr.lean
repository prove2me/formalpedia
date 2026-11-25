-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_c_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:22:03.696993+00:00
-- url     : https://prove2.me/submissions/c44b1e32-7f70-4595-9410-c97b0734ef85

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDensNonnegOfKappa
import Theorems.Thm_Formalism_FourierDecayAlt_P5_WordTransvectionCongruences_ofWord_x_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P5_WordTransvectionCongruences_ofWord_q_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P5_WordTransvectionCongruences_ofWord_xi_congr

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
theorem _root_.solution (L : R.LevelData A r) (st st' : Fr.Start A) (hx : st'.x = st.x) (hq : st'.q = st.q)
    (w : List (Letter ℂ S))
    (hw : ∀ l ∈ w, st'.xi (l.pt + 1) = st.xi (l.pt + 1) ∧ st'.xi (l.pt - 1) = st.xi (l.pt - 1)) :
    (Fr.ofWord L st' w).c = (Fr.ofWord L st w).c := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hx, hq]
  | cons l w ih =>
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    have hl := hw l List.mem_cons_self
    have hxw := ofWord_x_congr L st st' hx w
    have hqw := ofWord_q_congr L st st' hq w
    have hxi1 := ofWord_xi_congr L st st' w (l.pt + 1) hl.1
    have hxi2 := ofWord_xi_congr L st st' w (l.pt - 1) hl.2
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih', hxw, hqw, hxi1, hxi2]
end Formalism.FourierDecayAlt.P5.WordTransvectionCongruences
