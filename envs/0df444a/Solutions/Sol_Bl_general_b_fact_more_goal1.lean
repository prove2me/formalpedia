-- Prove2me | solution 1 for Bl.general_b_fact_more.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:15.343281+00:00
-- url     : https://prove2.me/submissions/b37f76ef-5e88-4921-8149-bb53b47f907a

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactMore_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u_2 u_3
namespace Bl.general_b_fact_more
private lemma aux {R : Type u_2} [CommRing R] (q : Polynomial R) (m : ℕ) (h : q.natDegree ≤ 1) :
    (q ^ m).natDegree ≤ m ∧ (q ^ m).coeff m = q.coeff 1 ^ m := by
  constructor
  · calc (q ^ m).natDegree ≤ m * q.natDegree := Polynomial.natDegree_pow_le
      _ ≤ m * 1 := Nat.mul_le_mul_left _ h
      _ = m := Nat.mul_one m
  · have h2 := Polynomial.coeff_pow_of_natDegree_le (m := m) h
    simpa only [Nat.mul_one] using h2
private lemma aux2 {R : Type u_2} {ι : Type u_3} [CommRing R] (s : Finset ι) (q : ι → Polynomial R)
    (e : ι → ℕ) (h : ∀ i, (q i).natDegree ≤ e i) :
    (s.prod q).natDegree ≤ s.sum e ∧
      (s.prod q).coeff (s.sum e) = s.prod (fun i => (q i).coeff (e i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨?_, ?_⟩
    · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (h a) ih.1)
    · rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (h a) ih.1, ih.2]
end Bl.general_b_fact_more
end

set_option autoImplicit false
universe u_2 u_3
open Bl Bl.general_b_fact_more
namespace Bl.general_b_fact_more
theorem _root_.solution :
  ∀ {R : Type u_2} {ι : Type u_3} [inst : CommRing.{u_2} R] (s : Finset.{u_3} ι) (p : ι → Polynomial.{u_2} R)
  (e : ι → Nat),
  (∀ (i : ι), LE.le.{0} (Polynomial.natDegree.{u_2} (p i)) 1) →
    And
      (LE.le.{0}
        (Polynomial.natDegree.{u_2} (Finset.prod.{u_3, u_2} s fun (i : ι) ↦ HPow.hPow.{u_2, 0, u_2} (p i) (e i)))
        (Finset.sum.{u_3, 0} s fun (i : ι) ↦ e i))
      (Eq.{u_2 + 1}
        (Polynomial.coeff.{u_2} (Finset.prod.{u_3, u_2} s fun (i : ι) ↦ HPow.hPow.{u_2, 0, u_2} (p i) (e i))
          (Finset.sum.{u_3, 0} s fun (i : ι) ↦ e i))
        (Finset.prod.{u_3, u_2} s fun (i : ι) ↦ HPow.hPow.{u_2, 0, u_2} (Polynomial.coeff.{u_2} (p i) 1) (e i))) := by
  intro R ι _ s p e hp
  have h := aux2 s (fun i => p i ^ e i) e (fun i => (aux (p i) (e i) (hp i)).1)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  exact Finset.prod_congr rfl (fun i _ => (aux (p i) (e i) (hp i)).2)
end Bl.general_b_fact_more
