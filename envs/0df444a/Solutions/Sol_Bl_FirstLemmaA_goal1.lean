-- Prove2me | solution 1 for Bl.FirstLemmaA.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:04.647183+00:00
-- url     : https://prove2.me/submissions/585e1c0c-97f3-4f42-b8fa-edbbc4e75a1b

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.FirstLemmaA
namespace Bl.FirstLemmaA
theorem _root_.solution :
  ∀ {B : Type u_1} [inst : CommRing.{u_1} B] {ι : Type u_2} (s : Finset.{u_2} ι) (v : ι → Polynomial.{u_1} B)
  (d : ι → Nat),
  (∀ (i : ι), LE.le.{0} (Polynomial.natDegree.{u_1} (v i)) 1) →
    And
      (LE.le.{0}
        (Polynomial.natDegree.{u_1} (Finset.prod.{u_2, u_1} s fun (i : ι) ↦ HPow.hPow.{u_1, 0, u_1} (v i) (d i)))
        (Finset.sum.{u_2, 0} s fun (i : ι) ↦ d i))
      (Eq.{u_1 + 1}
        (Polynomial.coeff.{u_1} (Finset.prod.{u_2, u_1} s fun (i : ι) ↦ HPow.hPow.{u_1, 0, u_1} (v i) (d i))
          (Finset.sum.{u_2, 0} s fun (i : ι) ↦ d i))
        (Finset.prod.{u_2, u_1} s fun (i : ι) ↦ HPow.hPow.{u_1, 0, u_1} (Polynomial.coeff.{u_1} (v i) 1) (d i))) := by
  intro B _ ι s v d hv
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih
    have hA : (v a ^ d a).natDegree ≤ d a := by
      simpa using Polynomial.natDegree_pow_le_of_le (d a) (hv a)
    have hc : (v a ^ d a).coeff (d a) = (v a).coeff 1 ^ d a := by
      simpa using Polynomial.coeff_pow_of_natDegree_le (m := d a) (hv a)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨Polynomial.natDegree_mul_le.trans (add_le_add hA h1), ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hA h1, hc, h2]
end Bl.FirstLemmaA
