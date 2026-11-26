-- Prove2me | solution 1 for Erdos266.f_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:37:44.418934+00:00
-- url     : https://prove2.me/submissions/58728ec0-443a-4bab-83a1-62cd00a479e1

module
public import Definitions.Def_Erdos266_Enumeration
public import Definitions.Def_Erdos266_Defs
public import Theorems.Thm_Erdos266_tSeq_injective


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {i : ℕ} (hi : 1 ≤ i) {x : ℝ}
    (hx : ∀ j ∈ range i, x + (tSeq j : ℝ) ≠ 0) :
    f i x = ∑ j ∈ range i, (m i j : ℝ) * (x + (tSeq j : ℝ))⁻¹ := by
  classical
  set v : ℕ → ℝ := fun j => -(tSeq j : ℝ) with hv
  have hinj : Set.InjOn v (range i) := by
    intro p _ q _ hpq
    have : (tSeq p : ℚ) = tSeq q := by
      have := neg_injective hpq
      exact_mod_cast this
    exact tSeq_injective this
  have hne : (range i).Nonempty := ⟨0, mem_range.mpr hi⟩
  -- Lagrange: the basis polynomials at the nodes `-tⱼ` sum to 1
  have hsum := congrArg (Polynomial.eval x) (Lagrange.sum_basis hinj hne)
  rw [Polynomial.eval_finsetSum, Polynomial.eval_one] at hsum
  -- each basis polynomial evaluates to `m i j * ∏_{k≠j}(x + tₖ)`
  have hbasis : ∀ j ∈ range i, (Lagrange.basis (range i) v j).eval x
      = (m i j : ℝ) * ∏ k ∈ (range i).erase j, (x + (tSeq k : ℝ)) := by
    intro j hj
    rw [Lagrange.basis, Polynomial.eval_prod]
    have hfact : ∀ k ∈ (range i).erase j,
        (Lagrange.basisDivisor (v j) (v k)).eval x
          = ((tSeq k - tSeq j : ℚ) : ℝ)⁻¹ * (x + (tSeq k : ℝ)) := by
      intro k _
      have heval : (Lagrange.basisDivisor (v j) (v k)).eval x
          = (v j - v k)⁻¹ * (x - v k) := by
        simp [Lagrange.basisDivisor]
      rw [heval]
      simp only [hv]
      push_cast
      congr 1
      · congr 1
        ring
      · ring
    rw [prod_congr rfl hfact, prod_mul_distrib, prod_inv_distrib]
    congr 1
    rw [m]
    push_cast
    rfl
  rw [sum_congr rfl hbasis] at hsum
  -- divide the identity by the full product
  have step : ∀ j ∈ range i, (m i j : ℝ) * (x + (tSeq j : ℝ))⁻¹
      = ((m i j : ℝ) * ∏ k ∈ (range i).erase j, (x + (tSeq k : ℝ)))
        * (∏ k ∈ range i, (x + (tSeq k : ℝ)))⁻¹ := by
    intro j hj
    have he : (∏ k ∈ (range i).erase j, (x + (tSeq k : ℝ))) ≠ 0 :=
      prod_ne_zero_iff.mpr fun k hk => hx k (mem_of_mem_erase hk)
    rw [← mul_prod_erase _ _ hj, mul_inv]
    field_simp
  rw [sum_congr rfl step, ← sum_mul, hsum, one_mul, f]
end Erdos266
