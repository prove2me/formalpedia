-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwinShift_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:52.700111+00:00
-- url     : https://prove2.me/submissions/77b8b3cf-6940-455f-a2bb-c317e11b09c4

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    LhwinShift (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (lhwinHt r n v) ((a.val : ℤ) - b.val) := by
  intro k
  have hX : IsWeightedHomogeneous (lhwinHt r n) (X v : MvPolynomial (Fin r × Fin n) R)
      (lhwinHt r n v) := isWeightedHomogeneous_X R _ v
  have hXa : IsWeightedHomogeneous (lhwinHt r n) (X (a, v.2) : MvPolynomial (Fin r × Fin n) R)
      (lhwinHt r n (a, v.2)) := isWeightedHomogeneous_X R _ (a, v.2)
  rw [Polynomial.coeff_add]
  refine IsWeightedHomogeneous.add ?_ ?_
  · rw [Polynomial.coeff_C]
    split_ifs with h
    · subst h; simpa using hX
    · exact isWeightedHomogeneous_zero R _ _
  · split_ifs with hb
    · rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs with h
      · subst h
        have e : lhwinHt r n v + ((1 : ℕ) : ℤ) * ((a.val : ℤ) - b.val) = lhwinHt r n (a, v.2) := by
          simp [lhwinHt, hb]
        rw [e]; exact hXa
      · exact isWeightedHomogeneous_zero R _ _
    · rw [Polynomial.coeff_zero]
      exact isWeightedHomogeneous_zero R _ _
end Formalism.GradedWeylDivisibility
