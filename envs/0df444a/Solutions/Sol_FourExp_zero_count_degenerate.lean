-- Prove2me | solution 1 for FourExp.zero_count_degenerate
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-15T03:53:57.277881+00:00
-- url     : https://prove2.me/submissions/2e96f6c1-be0f-4cbf-9b5f-9de101d33f30

import Mathlib

open Polynomial Finset

namespace FourExpDeg

/-- A polynomial times an exponential has, at every point, the root multiplicity as its order. -/
theorem order_poly_mul_exp (P : ℂ[X]) (hP : P ≠ 0) (c z : ℂ) :
    analyticOrderNatAt (fun w : ℂ => P.eval w * Complex.exp (c * w)) z = P.rootMultiplicity z := by
  obtain ⟨Q, hPQ, hQ⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP z
  have hQz : Q.eval z ≠ 0 := fun h => hQ (dvd_iff_isRoot.mpr h)
  have hdiff : ∀ R : ℂ[X], Differentiable ℂ (fun w : ℂ => R.eval w * Complex.exp (c * w)) :=
    fun R => R.differentiable.mul ((differentiable_id.const_mul c).cexp)
  have h := ((hdiff P).analyticAt z).analyticOrderAt_eq_natCast (n := P.rootMultiplicity z)
  have hord : analyticOrderAt (fun w : ℂ => P.eval w * Complex.exp (c * w)) z
      = (P.rootMultiplicity z : ℕ∞) := by
    refine h.2 ⟨fun w => Q.eval w * Complex.exp (c * w), (hdiff Q).analyticAt z,
      mul_ne_zero hQz (Complex.exp_ne_zero _), Filter.Eventually.of_forall (fun w => ?_)⟩
    simp only [smul_eq_mul]
    conv_lhs => rw [hPQ]
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    ring
  simp [analyticOrderNatAt, hord]

/-- Summed over any finite set, the orders are at most the degree. -/
theorem sum_order_le (P : ℂ[X]) (hP : P ≠ 0) (c : ℂ) (S : Finset ℂ) :
    ∑ z ∈ S, analyticOrderNatAt (fun w : ℂ => P.eval w * Complex.exp (c * w)) z ≤ P.natDegree := by
  classical
  simp_rw [order_poly_mul_exp P hP c]
  calc ∑ z ∈ S, P.rootMultiplicity z
      ≤ ∑ z ∈ S ∪ P.roots.toFinset, P.rootMultiplicity z :=
        Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = ∑ z ∈ P.roots.toFinset, P.rootMultiplicity z := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro z _ hz
        rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def] at hz
        exact rootMultiplicity_eq_zero hz
    _ = ∑ z ∈ P.roots.toFinset, P.roots.count z := by
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [count_roots]
    _ = Multiset.card P.roots := Multiset.toFinset_sum_count_eq _
    _ ≤ P.natDegree := card_roots' P

end FourExpDeg

theorem solution
    {l : ℕ} (q : Fin l → ℕ) (ω : Fin l → ℂ) (hω : Function.Injective ω)
    (b : (j : Fin l) → Fin (q j) → ℂ) (hb : ∃ j i, b j i ≠ 0)
    (S : Finset ℂ) (hdeg : (∑ j, q j) ≤ 1 ∨ (⨆ j, ‖ω j‖) = 0) :
    (∑ z ∈ S, analyticOrderNatAt (fun w : ℂ => ∑ j, ∑ i : Fin (q j), b j i * w ^ (i : ℕ) * Complex.exp (ω j * w)) z) + 1 ≤ ∑ j, q j := by
  classical
  obtain ⟨j₀, i₀, hb₀⟩ := hb
  -- every other block is empty
  have hsingle : ∀ j, j ≠ j₀ → q j = 0 := by
    intro j hj
    rcases hdeg with h1 | hΩ
    · have hle : q j + q j₀ ≤ ∑ k, q k := by
        have := Finset.sum_le_sum_of_subset (f := q) (Finset.subset_univ ({j, j₀} : Finset (Fin l)))
        rwa [Finset.sum_pair hj] at this
      have := i₀.isLt
      omega
    · exfalso
      have hz : ∀ k, ω k = 0 := by
        intro k
        have hk : ‖ω k‖ ≤ ⨆ j, ‖ω j‖ :=
          le_ciSup (f := fun j => ‖ω j‖) (Finite.bddAbove_range _) k
        rw [hΩ] at hk
        exact norm_le_zero_iff.mp hk
      exact hj (hω (by rw [hz j, hz j₀]))
  let P : ℂ[X] := ∑ i : Fin (q j₀), C (b j₀ i) * X ^ (i : ℕ)
  have hfun : (fun w : ℂ => ∑ j, ∑ i : Fin (q j), b j i * w ^ (i : ℕ) * Complex.exp (ω j * w))
      = fun w : ℂ => P.eval w * Complex.exp (ω j₀ * w) := by
    funext w
    rw [Finset.sum_eq_single j₀ (fun j _ hj => Finset.sum_eq_zero
      (fun i _ => by
        have hi : (i : ℕ) < q j := i.isLt
        have hq := hsingle j hj
        omega)) (by simp)]
    simp only [P, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, Finset.sum_mul]
  have hP : P ≠ 0 := by
    intro h0
    have hc := congrArg (fun p => p.coeff (i₀ : ℕ)) h0
    simp only [P, finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc
    rw [Finset.sum_eq_single i₀ (fun k _ hk => if_neg (fun h => hk (Fin.ext h).symm)) (by simp)] at hc
    simp only [if_true] at hc
    exact hb₀ hc
  have hdegP : P.natDegree + 1 ≤ q j₀ := by
    have : P.natDegree ≤ q j₀ - 1 := by
      apply natDegree_sum_le_of_forall_le
      intro i _
      exact (natDegree_C_mul_X_pow_le _ _).trans (by have := i.isLt; omega)
    have := i₀.isLt
    omega
  rw [hfun]
  have h1 := FourExpDeg.sum_order_le P hP (ω j₀) S
  have h2 : q j₀ ≤ ∑ j, q j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j₀)
  omega
