-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.residueFiber_renyi_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:26.085182+00:00
-- url     : https://prove2.me/submissions/69d55bfe-7ad8-4b73-9bb9-efce3fac56be

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_mul_rpow_card_le_four_sum_rpow_succ
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_quotient_injective_on_residueFiber


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {alpha : Type*} [DecidableEq alpha]
    (W : Finset alpha) (A : alpha → ℕ) (m : ℕ) (a : Fin m)
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (hm : 0 < m) (hA : Set.InjOn A W) :
    (m : ℝ) ^ theta *
        ((residueFiber W A m a).card : ℝ) *
        ((residueFiber W A m a).card : ℝ) ^ theta ≤
      4 * ∑ x ∈ residueFiber W A m a,
        ((m + A x : ℕ) : ℝ) ^ theta := by
  let F := residueFiber W A m a
  let Q := F.image fun x => A x / m
  have hqinj : Set.InjOn (fun x => A x / m) F :=
    quotient_injective_on_residueFiber hA
  have hcardQ : Q.card = F.card := Finset.card_image_iff.mpr hqinj
  have hbase :=
    card_mul_rpow_card_le_four_sum_rpow_succ Q htheta0 htheta1
  rw [hcardQ] at hbase
  have hscaled :
      (m : ℝ) ^ theta * (F.card : ℝ) * (F.card : ℝ) ^ theta ≤
        4 * ∑ q ∈ Q, ((m * (q + 1) : ℕ) : ℝ) ^ theta := by
    calc
      (m : ℝ) ^ theta * (F.card : ℝ) * (F.card : ℝ) ^ theta =
          (m : ℝ) ^ theta *
            ((F.card : ℝ) * (F.card : ℝ) ^ theta) := by ring
      _ ≤ (m : ℝ) ^ theta *
          (4 * ∑ q ∈ Q, ((q + 1 : ℕ) : ℝ) ^ theta) :=
        mul_le_mul_of_nonneg_left hbase
          (Real.rpow_nonneg (by positivity) _)
      _ = 4 * ((m : ℝ) ^ theta *
          ∑ q ∈ Q, ((q + 1 : ℕ) : ℝ) ^ theta) := by ring
      _ = 4 * ∑ q ∈ Q,
          (m : ℝ) ^ theta * ((q + 1 : ℕ) : ℝ) ^ theta := by
        rw [Finset.mul_sum]
      _ = 4 * ∑ q ∈ Q, ((m * (q + 1) : ℕ) : ℝ) ^ theta := by
        apply congrArg (fun x : ℝ => 4 * x)
        apply Finset.sum_congr rfl
        intro q hq
        rw [show (((m * (q + 1) : ℕ) : ℝ)) =
            (m : ℝ) * ((q + 1 : ℕ) : ℝ) by norm_num [Nat.cast_mul]]
        rw [Real.mul_rpow] <;> positivity
  have hrewrite :
      ∑ q ∈ Q, ((m * (q + 1) : ℕ) : ℝ) ^ theta =
        ∑ x ∈ F, ((m * (A x / m + 1) : ℕ) : ℝ) ^ theta := by
    rw [show Q = F.image (fun x => A x / m) by rfl]
    rw [Finset.sum_image hqinj]
  rw [hrewrite] at hscaled
  refine hscaled.trans ?_
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  apply Finset.sum_le_sum
  intro x hx
  apply Real.rpow_le_rpow (by positivity) _ htheta0.le
  have hdiv : m * (A x / m) ≤ A x := Nat.mul_div_le (A x) m
  have hnat : m * (A x / m + 1) ≤ m + A x := by
    calc
      m * (A x / m + 1) = m * (A x / m) + m := by
        rw [Nat.mul_add, Nat.mul_one]
      _ ≤ A x + m := Nat.add_le_add_right hdiv m
      _ = m + A x := Nat.add_comm _ _
  exact_mod_cast hnat
end CollatzEndpointTransport.FixedTotal
