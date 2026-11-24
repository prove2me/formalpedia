-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lehwShift_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:22.832823+00:00
-- url     : https://prove2.me/submissions/3f53791f-dbef-46e1-889e-ce5a0b037796

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ)
    (a b : Fin r) (hstep : ∀ s : Fin n, w (a, s) = w (b, s) + δ) (v : Fin r × Fin n) :
    LehwShift w (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (w v) δ := by
  obtain ⟨c, s⟩ := v
  intro k
  by_cases hc : c = b
  · subst hc
    rw [if_pos (show (c, s).1 = c from rfl)]
    rcases k with _ | _ | k
    · have e : (Polynomial.C (X (c, s)) + Polynomial.X * Polynomial.C (X (a, s)) :
          Polynomial (MvPolynomial (Fin r × Fin n) R)).coeff 0 = X (c, s) := by simp
      rw [e]
      simpa using isWeightedHomogeneous_X R w (c, s)
    · have e : (Polynomial.C (X (c, s)) + Polynomial.X * Polynomial.C (X (a, s)) :
          Polynomial (MvPolynomial (Fin r × Fin n) R)).coeff (0 + 1) = X (a, s) := by simp
      rw [e]
      convert isWeightedHomogeneous_X R w (a, s) using 1
      rw [hstep s]
      push_cast
      ring
    · have e : (Polynomial.C (X (c, s)) + Polynomial.X * Polynomial.C (X (a, s)) :
          Polynomial (MvPolynomial (Fin r × Fin n) R)).coeff (k + 1 + 1) = 0 := by
        simp [Polynomial.coeff_C]
      rw [e]
      intro d hd
      exact (hd (MvPolynomial.coeff_zero d)).elim
  · rw [if_neg (show ¬ (c, s).1 = b from hc), add_zero, Polynomial.coeff_C]
    split_ifs with hk
    · subst hk
      simpa using isWeightedHomogeneous_X R w (c, s)
    · intro d hd
      exact (hd (MvPolynomial.coeff_zero d)).elim
end Formalism.GradedWeylDivisibility
