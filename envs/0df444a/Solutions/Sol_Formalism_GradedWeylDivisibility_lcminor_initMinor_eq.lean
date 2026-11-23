-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lcminor_initMinor_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:06.596099+00:00
-- url     : https://prove2.me/submissions/30189a1a-3665-443b-8b66-4767e9cceba0

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColLexInitMinor

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
open scoped MonomialOrder
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (R : Type) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    initMinor R I hs = ∑ σ : Equiv.Perm (Fin s),
      monomial (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1)
        (((Equiv.Perm.sign σ : ℤ) : R)) := by
  rw [initMinor, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.of_apply]
  rw [← mul_one (((Equiv.Perm.sign σ : ℤ) : R)), ← C_mul_monomial, monomial_sum_one,
    Units.smul_def, zsmul_eq_mul]
  congr 1
end Formalism.GradedWeylDivisibility
