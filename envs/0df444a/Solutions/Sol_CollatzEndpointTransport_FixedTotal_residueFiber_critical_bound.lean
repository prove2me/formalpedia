-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.residueFiber_critical_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:41.444979+00:00
-- url     : https://prove2.me/submissions/861e1962-a669-4015-a09b-abb4143b2815

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_mul_sqrt_card_le_four_sum_sqrt_succ
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_quotient_injective_on_residueFiber

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {α : Type*} [DecidableEq α]
    (W : Finset α) (A : α → ℕ) (m : ℕ) (a : Fin m)
    (hm : 0 < m) (hA : Set.InjOn A W) :
    Real.sqrt m *
        ((residueFiber W A m a).card : ℝ) *
        Real.sqrt (residueFiber W A m a).card ≤
      4 * ∑ x ∈ residueFiber W A m a,
        Real.sqrt (m + A x) := by
  let F := residueFiber W A m a
  let Q := F.image fun x => A x / m
  have hqinj :
      Set.InjOn (fun x => A x / m) F :=
    quotient_injective_on_residueFiber hA
  have hcardQ : Q.card = F.card := by
    exact Finset.card_image_iff.mpr hqinj
  have hbase :=
    card_mul_sqrt_card_le_four_sum_sqrt_succ Q
  rw [hcardQ] at hbase
  have hscaled :
      Real.sqrt m * (F.card : ℝ) * Real.sqrt F.card ≤
        4 * ∑ q ∈ Q, Real.sqrt ((m * (q + 1) : ℕ) : ℝ) := by
    have hm0 : (0 : ℝ) ≤ m := by positivity
    calc
      Real.sqrt m * (F.card : ℝ) * Real.sqrt F.card
          = Real.sqrt m * ((F.card : ℝ) * Real.sqrt F.card) := by ring
      _ ≤ Real.sqrt m *
          (4 * ∑ q ∈ Q, Real.sqrt (q + 1)) :=
        mul_le_mul_of_nonneg_left hbase (Real.sqrt_nonneg _)
      _ = 4 * ∑ q ∈ Q,
          (Real.sqrt m * Real.sqrt (q + 1)) := by
        calc
          Real.sqrt m * (4 * ∑ q ∈ Q, Real.sqrt (q + 1))
              = 4 * (Real.sqrt m * ∑ q ∈ Q, Real.sqrt (q + 1)) := by ring
          _ = 4 * ∑ q ∈ Q,
              (Real.sqrt m * Real.sqrt (q + 1)) := by
            rw [Finset.mul_sum]
      _ = 4 * ∑ q ∈ Q, Real.sqrt ((m * (q + 1) : ℕ) : ℝ) := by
        apply congrArg (fun x : ℝ => 4 * x)
        apply Finset.sum_congr rfl
        intro q hq
        rw [← Real.sqrt_mul hm0]
        norm_num [Nat.cast_mul, Nat.cast_add]
  have hrewrite :
      ∑ q ∈ Q, Real.sqrt ((m * (q + 1) : ℕ) : ℝ) =
        ∑ x ∈ F,
          Real.sqrt ((m * (A x / m + 1) : ℕ) : ℝ) := by
    rw [show Q = F.image (fun x => A x / m) by rfl]
    rw [Finset.sum_image hqinj]
  rw [hrewrite] at hscaled
  refine hscaled.trans ?_
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  apply Finset.sum_le_sum
  intro x hx
  apply Real.sqrt_le_sqrt
  have hdiv : m * (A x / m) ≤ A x := Nat.mul_div_le (A x) m
  have hnat : m * (A x / m + 1) ≤ m + A x := by
    calc
      m * (A x / m + 1) = m * (A x / m) + m := by
        rw [Nat.mul_add, Nat.mul_one]
      _ ≤ A x + m := Nat.add_le_add_right hdiv m
      _ = m + A x := Nat.add_comm _ _
  exact_mod_cast hnat
end CollatzEndpointTransport.FixedTotal
