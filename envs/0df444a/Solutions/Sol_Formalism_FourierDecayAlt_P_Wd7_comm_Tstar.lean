-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.comm_Tstar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:49:03.990811+00:00
-- url     : https://prove2.me/submissions/56d91070-9cb5-431e-8d10-d354297e8429

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (σ : Site A) (Y : K) (z : A) (hz : ∀ x ∈ hol σ, Commute z (star x)) (i j : Fin 2) :
    Commute z (star (Ts σ Y i j)) := by
  have hp : Commute z (star σ.p) := hz _ (by simp [hol])
  have hc : Commute z (star σ.c) := hz _ (by simp [hol])
  have hci : Commute z (star σ.ci) := hz _ (by simp [hol])
  have ha : Commute z (star (algebraMap K A Y)) := by
    rw [← algebraMap_star_comm]
    exact (Algebra.commutes _ z).symm
  fin_cases i <;> fin_cases j <;> simp only [Ts, Tm] <;> simp
  · rw [← algebraMap_star_comm] at ha ⊢
    exact ha.add_right hp
  · exact hc
  · exact hci
end Formalism.FourierDecayAlt.P.Wd7
