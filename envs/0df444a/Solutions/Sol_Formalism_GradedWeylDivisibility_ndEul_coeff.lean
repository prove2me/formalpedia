-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ndEul_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:30:33.682778+00:00
-- url     : https://prove2.me/submissions/74d778ca-9c41-498b-9113-f3d454b11387

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas

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
set_option linter.unusedSimpArgs false
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (s : Fin n) (g : MvPolynomial (Fin r × Fin n) R) (m : Fin r × Fin n →₀ ℕ) :
    coeff m (ndEul R r n s g) =
      (Finsupp.weight (fun v => colW r n v s) m : R) * coeff m g := by
  classical
  induction g using MvPolynomial.induction_on generalizing m with
  | C a =>
    rw [derivation_C, coeff_zero, coeff_C]
    split_ifs with h
    · subst h; simp
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]
  | mul_X p v hp =>
    have hX : ndEul R r n s (X v) = colW r n v s • X v := mkDerivation_X _ _ _
    rw [Derivation.leibniz, hX, coeff_add, smul_eq_mul, smul_eq_mul,
      mul_smul_comm, coeff_smul, coeff_mul_X', coeff_X_mul']
    split_ifs with h
    · rw [hp]
      have hle : Finsupp.single v 1 ≤ m := by
        rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)
      have hm : m = (m - Finsupp.single v 1) + Finsupp.single v 1 := (tsub_add_cancel_of_le hle).symm
      have hw : Finsupp.weight (fun v => colW r n v s) m =
          Finsupp.weight (fun v => colW r n v s) (m - Finsupp.single v 1) + colW r n v s := by
        conv_lhs => rw [hm]
        rw [map_add, Finsupp.weight_single, one_smul]
      rw [hw, nsmul_eq_mul]; push_cast; ring
    · simp
end Formalism.GradedWeylDivisibility
