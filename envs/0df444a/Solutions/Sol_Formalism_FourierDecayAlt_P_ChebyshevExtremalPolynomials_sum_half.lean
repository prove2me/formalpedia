-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.sum_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:27.028625+00:00
-- url     : https://prove2.me/submissions/73328e59-d6ab-4ff4-bd2a-752b79deb8ac

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
theorem _root_.solution (m : ℕ) :
    ∑ j : Fin (m + 2), (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1) = (m:ℝ) + 1 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have : ∀ i : Fin m, (if ((i.castSucc.succ : Fin (m + 2)) : ℕ) = 0 ∨
      ((i.castSucc.succ : Fin (m + 2)) : ℕ) = m + 1 then (1 / 2 : ℝ) else 1) = 1 := by
    intro i
    rw [if_neg]
    have := i.isLt
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  rw [sum_congr rfl (fun i _ => this i)]
  simp
  ring
end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
