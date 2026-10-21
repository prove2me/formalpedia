-- Prove2me | solution 1 for FiniteFields.Dwork.frobenius_wittTraceTeichmuller
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:44:18.014983+00:00
-- url     : https://prove2.me/submissions/7bd85844-0498-461f-bb23-ddf52e03cc25

import Mathlib
import Definitions.Def_FiniteFields_Dwork_AdditiveCharacter
section
noncomputable section
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k]
variable [CharP k p]
@[simp]
theorem frobeniusLift_teichmuller (x : k) :
    frobeniusLift k p (teichmullerLift k p x) = teichmullerLift k p (x ^ p) := by
  change WittVector.frobenius (WittVector.teichmuller p x) = WittVector.teichmuller p (x ^ p)
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller]
  rfl
variable [Finite k]
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
omit [Finite k] in
theorem iterate_frobeniusLift_teichmullerLift (i : ℕ) (x : k) :
    (frobeniusLift k p)^[i] (teichmullerLift k p x) = teichmullerLift k p (x ^ p ^ i) := by
  induction i with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, frobeniusLift_teichmuller]
      congr 1
      rw [← pow_mul, pow_succ]
theorem wittVector_ext_of_ghostComponent {R : Type*} [CommRing R] [IsDomain R]
    (hp : (p : R) ≠ 0) {u v : WittVector p R}
    (h : ∀ n, WittVector.ghostComponent n u = WittVector.ghostComponent n v) : u = v := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hg := h n
    rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply,
      aeval_wittPolynomial p ℤ u.coeff n, aeval_wittPolynomial p ℤ v.coeff n,
      Finset.sum_range_succ, Finset.sum_range_succ] at hg
    have hrest : ∑ i ∈ Finset.range n, (p : R) ^ i * u.coeff i ^ p ^ (n - i)
        = ∑ i ∈ Finset.range n, (p : R) ^ i * v.coeff i ^ p ^ (n - i) :=
      Finset.sum_congr rfl fun i hi => by rw [ih i (Finset.mem_range.mp hi)]
    rw [hrest, Nat.sub_self, pow_zero, pow_one, pow_one] at hg
    exact mul_left_cancel₀ (pow_ne_zero n hp) (add_left_cancel hg)
theorem frobenius_teichmuller {R : Type*} [CommRing R] [IsDomain R] (hp : (p : R) ≠ 0) (a : R) :
    WittVector.frobenius (WittVector.teichmuller p a) = WittVector.teichmuller p (a ^ p) := by
  refine wittVector_ext_of_ghostComponent p hp fun n => ?_
  rw [WittVector.ghostComponent_frobenius, WittVector.ghostComponent_teichmuller,
    WittVector.ghostComponent_teichmuller, ← pow_mul, ← pow_succ']
omit [Finite k] in
theorem coefficientRing_p_ne_zero : (p : CoefficientRing k p) ≠ 0 :=
  WittVector.p_nonzero p k
end FiniteFields.Dwork
end
end
open PowerSeries IsUltrametricDist
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4e2TraceLimitResiduePrimeAlgebra
theorem solution (x : k) :
    WittVector.frobenius (wittTraceTeichmuller k p (teichmullerLift k p x))
      = wittTraceTeichmuller k p (teichmullerLift k p x) := by
  have hstep : ∀ i : ℕ,
      WittVector.frobenius
          (WittVector.teichmuller p ((frobeniusLift k p)^[i] (teichmullerLift k p x)))
        = WittVector.teichmuller p ((frobeniusLift k p)^[i + 1] (teichmullerLift k p x)) := by
    intro i
    rw [frobenius_teichmuller p (coefficientRing_p_ne_zero k p),
      iterate_frobeniusLift_teichmullerLift, iterate_frobeniusLift_teichmullerLift, ← map_pow]
    congr 2
    rw [← pow_mul, ← pow_succ]
  have hper : WittVector.teichmuller p
        ((frobeniusLift k p)^[Module.finrank (ZMod p) k] (teichmullerLift k p x))
      = WittVector.teichmuller p ((frobeniusLift k p)^[0] (teichmullerLift k p x)) := by
    rw [Function.iterate_zero_apply, iterate_frobeniusLift_finrank k p]
  have h1 : (∑ i ∈ Finset.range (Module.finrank (ZMod p) k + 1),
        WittVector.teichmuller p ((frobeniusLift k p)^[i] (teichmullerLift k p x)))
      = (∑ i ∈ Finset.range (Module.finrank (ZMod p) k),
          WittVector.teichmuller p ((frobeniusLift k p)^[i + 1] (teichmullerLift k p x)))
        + WittVector.teichmuller p ((frobeniusLift k p)^[0] (teichmullerLift k p x)) :=
    Finset.sum_range_succ' _ _
  have h2 : (∑ i ∈ Finset.range (Module.finrank (ZMod p) k + 1),
        WittVector.teichmuller p ((frobeniusLift k p)^[i] (teichmullerLift k p x)))
      = (∑ i ∈ Finset.range (Module.finrank (ZMod p) k),
          WittVector.teichmuller p ((frobeniusLift k p)^[i] (teichmullerLift k p x)))
        + WittVector.teichmuller p
            ((frobeniusLift k p)^[Module.finrank (ZMod p) k] (teichmullerLift k p x)) :=
    Finset.sum_range_succ _ _
  rw [hper] at h2
  have hsum : (∑ i ∈ Finset.range (Module.finrank (ZMod p) k),
        WittVector.teichmuller p ((frobeniusLift k p)^[i + 1] (teichmullerLift k p x)))
      = ∑ i ∈ Finset.range (Module.finrank (ZMod p) k),
        WittVector.teichmuller p ((frobeniusLift k p)^[i] (teichmullerLift k p x)) :=
    add_right_cancel (h1.symm.trans h2)
  rw [wittTraceTeichmuller, map_sum,
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range (Module.finrank (ZMod p) k)) => hstep i),
    hsum]
