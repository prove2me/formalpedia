-- Prove2me | solution 1 for DerivativeChainContinuation.actual_tower_transverse_budget
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:39:57.529905+00:00
-- url     : https://prove2.me/submissions/1312557b-3412-49ce-80f4-c58c0ffbd61b

import Mathlib
import Definitions.Def_DerivativeChainContinuation_DeficitBudget
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_tower_holomorphic_rescaling
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators



theorem degreeDeficit_step (V : ℕ → ℝ) (k : ℕ) :
    degreeDeficit V (k+3) / ((k+2 : ℕ) * (k+1 : ℕ) : ℝ) =
      V (k+3) / (k+2 : ℕ) - V (k+2) / (k+1 : ℕ) := by
  have h1 : (k+1 : ℝ) ≠ 0 := by positivity
  have h2 : (k+2 : ℝ) ≠ 0 := by positivity
  simp only [degreeDeficit, show k+3-2=k+1 by omega, show k+3-1=k+2 by omega,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp

theorem degreeDeficit_telescope (V : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n,
      degreeDeficit V (k+3) / ((k+2 : ℕ) * (k+1 : ℕ) : ℝ)) =
      V (n+2) / (n+1 : ℕ) - V 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, degreeDeficit_step]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    ring

theorem transverse_budget (V : ℕ → ℝ) (H : ℝ) (n : ℕ)
    (hbase : V 2 = H / (n+1 : ℕ)) :
    (∑ k ∈ Finset.range n,
      degreeDeficit V (k+3) / ((k+2 : ℕ) * (k+1 : ℕ) : ℝ)) =
      (V (n+2) - H) / (n+1 : ℕ) := by
  rw [degreeDeficit_telescope, hbase]
  ring


end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial

theorem quadratic_variance_eq_holomorphic_norm (p : Polynomial ℂ)
    (hdeg : p.natDegree = 2) (hcenter : p.roots.sum = 0) :
    rootVariance p = ‖rootHolomorphicMoment p‖ := by
  have hcard : p.roots.card = 2 := by
    rw [(splits_iff_card_roots.mp (IsAlgClosed.splits p)), hdeg]
  obtain ⟨a,b,hab⟩ := Multiset.card_eq_two.mp hcard
  rw [hab] at hcenter
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hcenter
  have hb : b = -a := by linear_combination hcenter
  simp [rootVariance, rootHolomorphicMoment, hdeg, hab, hb,
    norm_pow, Complex.normSq_eq_norm_sq]


end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (P : ℕ → Polynomial ℂ) (n : ℕ)
    (hmonic : ∀ k ≤ n, (P (k+2)).Monic)
    (hdegree : ∀ k ≤ n, (P (k+2)).natDegree = k+2)
    (hcenter : ∀ k ≤ n, (P (k+2)).roots.sum = 0)
    (hstep : ∀ k < n, monicDerivative (P (k+3)) = P (k+2)) :
    (∑ k ∈ Finset.range n,
      schoenbergDeficit (P (k+3))/((k+2 : ℕ)*(k+1 : ℕ) : ℝ)) =
      (rootVariance (P (n+2)) - ‖rootHolomorphicMoment (P (n+2))‖)/(n+1 : ℕ) := by
  have ht := tower_holomorphic_rescaling P n hmonic hdegree hcenter hstep
  have hbase := quadratic_variance_eq_holomorphic_norm (P 2)
    (hdegree 0 (by omega)) (hcenter 0 (by omega))
  rw [ht, norm_div] at hbase
  have hnorm : ‖(n+1 : ℂ)‖ = (n+1 : ℝ) := by
    norm_cast
  rw [hnorm] at hbase
  have eqsum : (∑ k ∈ Finset.range n,
      schoenbergDeficit (P (k+3))/((k+2 : ℕ)*(k+1 : ℕ) : ℝ)) =
      ∑ k ∈ Finset.range n,
        degreeDeficit (fun m => rootVariance (P m)) (k+3)/
          ((k+2 : ℕ)*(k+1 : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [schoenbergDeficit, hdegree (k+1) (by omega), hstep k hk']
    simp [degreeDeficit, show k+3-1=k+2 by omega]
  rw [eqsum]
  apply transverse_budget
  simpa only [Nat.cast_add, Nat.cast_one] using hbase
