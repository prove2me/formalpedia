-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_polynomial_ne_zero_forall_mul_mem_holOn_of_forall_exists_mem_holOn_mul_eq_of_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f3323cc1-ee56-5839-8af9-bcdbd01ef076

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_polynomial_ne_zero_forall_mul_mem_holOn_of_forall_exists_mem_holOn_mul_eq_of_polynomial

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_polynomial_ne_zero_forall_mul_mem_holOn_of_forall_exists_mem_holOn_mul_eq_of_polynomial.CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid mem_affinoid_iff' RatPair RatPair.evalAt IsHolOn isHolOn_ratPair IsHolOn.const holOn"
namespace PolyDenomAux
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem coord_mem_holOn (ϖ : PseudoUniformizer K₀ K) (n : ℕ) (S : Set K) (hS : S ⊆ affinoid ϖ n) :
    (fun z : ↥S => (z : K)) ∈ holOn K S := by
  have h := isHolOn_ratPair (S := S) ⟨Polynomial.X, 1⟩ (fun z _ => by simp)
    ⟨algebraMap K₀ K (ϖ.ϖ⁻¹ ^ n), fun z hz => by
      have := ((mem_affinoid_iff' ϖ n z).1 (hS hz)).1
      simpa [RatPair.evalAt, map_pow, map_inv₀] using this⟩
  rw [mem_holOn_iff]
  convert h using 1
  funext z
  simp [RatPair.evalAt]

theorem polynomial_eval_mem_holOn (ϖ : PseudoUniformizer K₀ K) (n : ℕ) (S : Set K) (hS : S ⊆ affinoid ϖ n)
    (Q : Polynomial K) : (fun z : ↥S => Q.eval (z : K)) ∈ holOn K S := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    have : (fun z : ↥S => (p + q).eval (z : K)) = (fun z : ↥S => p.eval (z : K)) + (fun z : ↥S => q.eval (z : K)) := by
      funext z; simp [Polynomial.eval_add]
    rw [this]
    exact (holOn K S).add_mem hp hq
  | monomial k c =>
    have : (fun z : ↥S => (Polynomial.monomial k c).eval (z : K)) = (fun _ : ↥S => c) * (fun z : ↥S => (z : K)) ^ k := by
      funext z; simp [Polynomial.eval_monomial]
    rw [this]
    exact (holOn K S).mul_mem (IsHolOn.const S c) ((holOn K S).pow_mem (coord_mem_holOn ϖ n S hS) k)

end CerednikDrinfeld.Omega.PolyDenomAux

open CerednikDrinfeld.Omega.PolyDenomAux in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) (n : ℕ)
    {ι : Type} [Fintype ι] (S : ι → Set K) (hS : ∀ i, S i ⊆ affinoid ϖ n)
    (F : ↥(affinoid ϖ n) → K)
    (P : ι → Polynomial K) (hP : ∀ i, P i ≠ 0)
    (f : (i : ι) → ↥(S i) → K) (hf : ∀ i, f i ∈ holOn K (S i))
    (hrep : ∀ (i : ι) (z : ↥(S i)), (P i).eval (z : K) ≠ 0 → (P i).eval (z : K) * F ⟨(z : K), hS i z.2⟩ = f i z) :
    ∃ g : Polynomial K, g ≠ 0 ∧
      ∀ i : ι, (fun z : ↥(S i) => g.eval (z : K) * F ⟨(z : K), hS i z.2⟩) ∈ holOn K (S i) := by
  classical
  refine ⟨∏ j, P j ^ 2, Finset.prod_ne_zero_iff.2 (fun j _ => pow_ne_zero 2 (hP j)), fun i => ?_⟩
  set Q : Polynomial K := P i * ∏ j ∈ Finset.univ.erase i, P j ^ 2 with hQdef
  have hg : ∏ j, P j ^ 2 = P i * Q := by
    rw [hQdef, ← Finset.mul_prod_erase Finset.univ (fun j => P j ^ 2) (Finset.mem_univ i), pow_two, mul_assoc]
  have heq : (fun z : ↥(S i) => (∏ j, P j ^ 2).eval (z : K) * F ⟨(z : K), hS i z.2⟩) =
      (fun z : ↥(S i) => Q.eval (z : K)) * f i := by
    funext z
    rw [Pi.mul_apply, hg, Polynomial.eval_mul]
    by_cases hz : (P i).eval (z : K) = 0
    · have hQ : Q.eval (z : K) = 0 := by rw [hQdef, Polynomial.eval_mul, hz, zero_mul]
      rw [hz, hQ, zero_mul, zero_mul, zero_mul]
    · rw [mul_comm ((P i).eval (z : K)) (Q.eval (z : K)), mul_assoc, hrep i z hz]
  rw [heq]
  exact (holOn K (S i)).mul_mem (polynomial_eval_mem_holOn ϖ n (S i) (hS i) Q) (hf i)

end S_CerednikDrinfeld_Omega_exists_polynomial_ne_zero_forall_mul_mem_holOn_of_forall_exists_mem_holOn_mul_eq_of_polynomial
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_polynomial_ne_zero_forall_mul_mem_holOn_of_forall_exists_mem_holOn_mul_eq_of_polynomial (solution)
