-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.le_of_iterate_bounds_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:43:53.630992+00:00
-- url     : https://prove2.me/submissions/ffa746aa-7150-478c-b43e-bed92461a7cb

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_DyadicSummation
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Criterion
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_recursion_readable

section
section
open Finset
/-- Chaining the dyadic recursion `m` times: with `T(d) = x^(d-1) S(d)`,
`S(1) ≤ T(2^m) + A Σ_{j<m} 2^j y^(2^j)`. -/
private theorem FunctionalInequalities.Analysis.le_dyadic_chain {S : ℕ → ℝ} {x y A : ℝ}
    (hrec : ∀ d, 1 ≤ d → x ^ (d - 1) * S d ≤ x ^ (2 * d - 1) * S (2 * d) + A * d * y ^ d)
    (m : ℕ) :
    S 1 ≤ x ^ (2 ^ m - 1) * S (2 ^ m) +
      A * ∑ j ∈ range m, ((2 ^ j : ℕ) : ℝ) * y ^ (2 ^ j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := hrec (2 ^ m) (Nat.one_le_two_pow)
    rw [sum_range_succ, pow_succ' 2 m, mul_add]
    linarith [ih, h]
/-- The dyadic partial sums are bounded by `Σ_d d (1/100)^d = 100/9801 ≤ 1/90`. -/
private theorem FunctionalInequalities.Analysis.sum_dyadic_le {y : ℝ} (hy : 0 ≤ y) (hy1 : 100 * y ≤ 1) (m : ℕ) :
    ∑ j ∈ range m, ((2 ^ j : ℕ) : ℝ) * y ^ (2 ^ j) ≤ 1 / 90 := by
  set r : ℝ := 1 / 100 with hr
  have hyr : y ≤ r := by rw [hr]; linarith
  have hnorm : ‖r‖ < 1 := by rw [hr, Real.norm_eq_abs]; norm_num
  have hsum := hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have hinj : Set.InjOn (fun j : ℕ => 2 ^ j) (range m : Set ℕ) :=
    fun a _ b _ hab => Nat.pow_right_injective le_rfl hab
  calc ∑ j ∈ range m, ((2 ^ j : ℕ) : ℝ) * y ^ (2 ^ j)
      ≤ ∑ j ∈ range m, ((2 ^ j : ℕ) : ℝ) * r ^ (2 ^ j) := by
        gcongr
    _ = ∑ d ∈ (range m).image (fun j : ℕ => 2 ^ j), ((d : ℕ) : ℝ) * r ^ d :=
        (sum_image (f := fun d : ℕ => (d : ℝ) * r ^ d) hinj).symm
    _ ≤ ∑' d : ℕ, (d : ℝ) * r ^ d :=
        hsum.summable.sum_le_tsum _ (fun d _ => by positivity)
    _ = r / (1 - r) ^ 2 := hsum.tsum_eq
    _ ≤ 1 / 90 := by rw [hr]; norm_num
/-- **The dyadic summation of BKL Theorem 3.1** (arXiv:2610.05474v1, p. 17). If `S` vanishes
from `N` on, `0 ≤ x ≤ 1`, `0 ≤ A`, `0 ≤ y ≤ 1/100`, and
`x^(d-1) S(d) ≤ x^(2d-1) S(2d) + A d y^d` for all `d ≥ 1`, then `S(1) ≤ A / 90`. -/
theorem FunctionalInequalities.Analysis.le_of_dyadic_recursion {S : ℕ → ℝ} {x y A : ℝ} {N : ℕ}
    (hN : ∀ d, N ≤ d → S d = 0) (hA : 0 ≤ A) (hy : 0 ≤ y) (hy1 : 100 * y ≤ 1)
    (hrec : ∀ d, 1 ≤ d → x ^ (d - 1) * S d ≤ x ^ (2 * d - 1) * S (2 * d) + A * d * y ^ d) :
    S 1 ≤ A / 90 := by
  have hchain := le_dyadic_chain hrec N
  rw [hN (2 ^ N) (Nat.lt_two_pow_self).le, mul_zero, zero_add] at hchain
  have hsum := sum_dyadic_le hy hy1 N
  calc S 1 ≤ A * ∑ j ∈ range N, ((2 ^ j : ℕ) : ℝ) * y ^ (2 ^ j) := hchain
    _ ≤ A * (1 / 90) := mul_le_mul_of_nonneg_left hsum hA
    _ = A / 90 := by ring
end
end

noncomputable section
open MeasureTheory Filter Topology Finset
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff
section Scalar
/-- The first index `N` with `v_N < λ/2` (the source's (53), shifted by one). -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.exists_first_small {v : ℕ → ℝ} {l : ℝ} (hl : 0 < l)
    (hvlim : Tendsto v atTop (𝓝 0)) :
    ∃ N, v N < l / 2 ∧ ∀ k < N, l / 2 ≤ v k := by
  have hex : ∃ N, v N < l / 2 :=
    ((hvlim.eventually (gt_mem_nhds (half_pos hl))).exists)
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, fun k hk => ?_⟩
  exact not_lt.mp (Nat.find_min hex hk)
/-- The step bounds (54) for the steps before `N`: if `v_{j+1} ≥ λ/2` then `α_j > 0` and
`α_j² ≤ 3λ`, from (46), `‖L h‖² ≤ ‖L h₁‖² ≤ (1.1 λ)²` and `α_j ≥ 0`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale_bounds {C : ℝ} {v L α : ℕ → ℝ} (hC : 0 < C)
    (hL0 : L 0 ≤ (11 / 10 * C⁻¹) ^ 2) (hL : ∀ k, L (k + 1) ≤ L k)
    (h46 : ∀ k, L (k + 1) = α k ^ 2 * v (k + 1))
    (hα : ∀ k, 0 ≤ α k) (hα0 : ∀ k, α k = 0 → v (k + 1) = 0) {j : ℕ}
    (hvj : C⁻¹ / 2 ≤ v (j + 1)) : 0 < α j ∧ α j ^ 2 ≤ 3 / C := by
  have hl : 0 < C⁻¹ := inv_pos.mpr hC
  refine ⟨lt_of_le_of_ne (hα j) fun h => ?_, ?_⟩
  · have := hα0 j h.symm
    linarith
  · have hLj : L (j + 1) ≤ L 0 := antitone_nat_of_succ_le hL (Nat.zero_le _)
    have h1 : α j ^ 2 * (C⁻¹ / 2) ≤ (11 / 10 * C⁻¹) ^ 2 := by
      calc α j ^ 2 * (C⁻¹ / 2) ≤ α j ^ 2 * v (j + 1) :=
            mul_le_mul_of_nonneg_left hvj (sq_nonneg _)
        _ = L (j + 1) := (h46 j).symm
        _ ≤ _ := hLj.trans hL0
    rw [div_eq_mul_inv]
    by_contra hcon
    replace hcon := not_le.mp hcon
    have h2 := mul_lt_mul_of_pos_right hcon (half_pos hl)
    nlinarith
/-- `v_{k+1} ≤ 1.21 λ` for every `k`: by (32) and (46), `λ v_{k+1} ≤ α_k² v_{k+1} = ‖L h‖² ≤
(1.1 λ)²` when `α_k > 0`, and `v_{k+1} = 0` when `α_k = 0`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_succ_le {C : ℝ} {v L α : ℕ → ℝ} (hC : 0 < C) (hv : ∀ k, 0 ≤ v k)
    (hL0 : L 0 ≤ (11 / 10 * C⁻¹) ^ 2) (hL : ∀ k, L (k + 1) ≤ L k)
    (h46 : ∀ k, L (k + 1) = α k ^ 2 * v (k + 1))
    (hα : ∀ k, 0 ≤ α k) (hα0 : ∀ k, α k = 0 → v (k + 1) = 0)
    (h32 : ∀ k, 0 < α k → C⁻¹ ≤ α k ^ 2) (k : ℕ) :
    v (k + 1) ≤ 121 / 100 * C⁻¹ := by
  have hl : 0 < C⁻¹ := inv_pos.mpr hC
  rcases (hα k).eq_or_lt with h0 | hpos
  · rw [hα0 k h0.symm]
    positivity
  · have hLk : L (k + 1) ≤ L 0 := antitone_nat_of_succ_le hL (Nat.zero_le _)
    have h1 : C⁻¹ * v (k + 1) ≤ C⁻¹ * (121 / 100 * C⁻¹) := by
      calc C⁻¹ * v (k + 1) ≤ α k ^ 2 * v (k + 1) :=
            mul_le_mul_of_nonneg_right (h32 k hpos) (hv _)
        _ = L (k + 1) := (h46 k).symm
        _ ≤ (11 / 10 * C⁻¹) ^ 2 := hLk.trans hL0
        _ = C⁻¹ * (121 / 100 * C⁻¹) := by ring
    exact le_of_mul_le_mul_left h1 hl
/-- The recursion (63) multiplied by `(cλ)^{d-1}`, in the form of `le_of_dyadic_recursion` with
`x = cλ`, `y = c²λR²` and `A = 5`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.dyadic_step {C c R : ℝ} {S : ℕ → ℝ} (hC : 0 < C) (hc : 1 ≤ c) {d : ℕ}
    (hd : 1 ≤ d)
    (hrec : S d ≤ (c / C) ^ d * S (2 * d) + 5 * d * c ^ d * C⁻¹ * R ^ (2 * d)) :
    (c * C⁻¹) ^ (d - 1) * S d ≤ (c * C⁻¹) ^ (2 * d - 1) * S (2 * d) +
      5 * d * (c ^ 2 * C⁻¹ * R ^ 2) ^ d := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le' hd
  have hx : 0 ≤ (c * C⁻¹) ^ e := by have := inv_pos.mpr hC; positivity
  rw [div_eq_mul_inv] at hrec
  rw [Nat.add_sub_cancel, show 2 * (e + 1) - 1 = 2 * e + 1 by omega]
  have h1 := mul_le_mul_of_nonneg_left hrec hx
  have hY : 0 ≤ (c * C⁻¹) ^ e * c ^ (e + 1) * C⁻¹ * R ^ (2 * (e + 1)) := by
    have := inv_pos.mpr hC
    have : 0 ≤ c := by linarith
    have : 0 ≤ R ^ (2 * (e + 1)) := by rw [pow_mul]; positivity
    positivity
  have h2 : (c ^ 2 * C⁻¹ * R ^ 2) ^ (e + 1) =
      c * ((c * C⁻¹) ^ e * c ^ (e + 1) * C⁻¹ * R ^ (2 * (e + 1))) := by ring
  have h3 := mul_le_mul_of_nonneg_right hc hY
  have he : (0 : ℝ) ≤ (e + 1 : ℕ) := by positivity
  have h4 := mul_le_mul_of_nonneg_left h3 he
  calc (c * C⁻¹) ^ e * S (e + 1)
      ≤ (c * C⁻¹) ^ e * ((c * C⁻¹) ^ (e + 1) * S (2 * (e + 1)) +
          5 * ((e + 1 : ℕ) : ℝ) * c ^ (e + 1) * C⁻¹ * R ^ (2 * (e + 1))) := h1
    _ = (c * C⁻¹) ^ (2 * e + 1) * S (2 * (e + 1)) +
          5 * (((e + 1 : ℕ) : ℝ) * (1 * ((c * C⁻¹) ^ e * c ^ (e + 1) * C⁻¹ *
            R ^ (2 * (e + 1))))) := by ring
    _ ≤ (c * C⁻¹) ^ (2 * e + 1) * S (2 * (e + 1)) +
          5 * (((e + 1 : ℕ) : ℝ) * (c * ((c * C⁻¹) ^ e * c ^ (e + 1) * C⁻¹ *
            R ^ (2 * (e + 1))))) := by linarith
    _ = (c * C⁻¹) ^ (2 * e + 1) * S (2 * (e + 1)) +
          5 * ((e + 1 : ℕ) : ℝ) * (c ^ 2 * C⁻¹ * R ^ 2) ^ (e + 1) := by rw [h2]; ring
/-- **The final argument of BKL Theorem 3.1, for real sequences** (arXiv:2610.05474v1, p. 17,
in the operator route).

The sequences are the scalar quantities of the iterates `h_{k+1}` of one approximate
eigenfunction, `λ = 1/C`: `v k` the energy `‖∇h_{k+1}‖²`, `p k` the drop `|∫∇h_{k+1}|²`, `χ k` the
defect, `L k = ‖L h_{k+1}‖²`, `α k = α_{k+2}` and `t d k = |T_d(∇₀h_{k+1})|²`. The hypotheses are
(36), `v₀ ≥ λ`, `v_k → 0` and `Σ χ ≤ ‖L h₁‖² ≤ (1.1 λ)²` (Corollary 3.5), the monotonicity of
`‖L h‖²` (Lemma 3.4), (46), (32), `α ≥ 0` with `α_k = 0 ⇒ v_{k+1} = 0`, the Taylor bound
`t_d(k) ≤ R^{2d} v_{k+1}` ((29) and (33)), Lemma 3.8 with constant `c ≥ 1` and Lemma 3.9 (both
with `β = 3`, in the shapes of the route statements `J1`, `J2`). Then `C ≤ 100 c² R²`. -/
theorem solution {C c R : ℝ} {v p χ L α : ℕ → ℝ} {t : ℕ → ℕ → ℝ}
    (hC : 0 < C) (hc : 1 ≤ c) (hR : 1 ≤ R)
    (hv : ∀ k, 0 ≤ v k) (hv0 : C⁻¹ ≤ v 0) (hvlim : Tendsto v atTop (𝓝 0))
    (h36 : ∀ N, v 0 = v N + ∑ k ∈ range N, p k)
    (hχ : ∀ k, 0 ≤ χ k) (hχsum : ∀ N, ∑ k ∈ range N, χ k ≤ L 0)
    (hL0 : L 0 ≤ (11 / 10 * C⁻¹) ^ 2) (hL : ∀ k, L (k + 1) ≤ L k)
    (h46 : ∀ k, L (k + 1) = α k ^ 2 * v (k + 1))
    (hα : ∀ k, 0 ≤ α k) (hα0 : ∀ k, α k = 0 → v (k + 1) = 0)
    (h32 : ∀ k, 0 < α k → C⁻¹ ≤ α k ^ 2)
    (ht : ∀ d k, 0 ≤ t d k)
    (htaylor : ∀ d k, 1 ≤ d → t d k ≤ R ^ (2 * d) * v (k + 1))
    (hJ1 : ∀ k d, 1 ≤ d → 2 * d ≤ k + 1 → (∀ j < k, 0 < α j ∧ α j ^ 2 ≤ 3 / C) →
      t d k ≤ (c / C) ^ d * t (2 * d) (k - d) +
        c ^ d * R ^ (2 * d) * C * ∑ j ∈ Ico (k + 1 - 2 * d) k, χ j)
    (hJ2 : ∀ N, (∀ j, j + 1 < N → α j ^ 2 ≤ 3 / C) →
      ∑ k ∈ range N, p k ≤ L 0 + 3 / C * ∑ k ∈ range (N - 1), t 1 k) :
    C ≤ 100 * c ^ 2 * R ^ 2 := by
  have hl : 0 < C⁻¹ := inv_pos.mpr hC
  obtain ⟨N, hN, hmin⟩ := FunctionalInequalities.KLS.LogConcave.PoissonIterate.exists_first_small hl hvlim
  have hαN : ∀ j, j + 1 < N → 0 < α j ∧ α j ^ 2 ≤ 3 / C := fun j hj =>
    FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale_bounds hC hL0 hL h46 hα hα0 (hmin _ hj)
  have hvk := FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_succ_le hC hv hL0 hL h46 hα hα0 h32
  set S : ℕ → ℝ := fun d => ∑ k ∈ range (N - d), t d k with hS
  by_contra hcon
  replace hcon := not_le.mp hcon
  -- the contradiction hypothesis (64): `y = c²λR² < 1/100`
  have hc0 : 0 < c := by linarith
  have hy : c ^ 2 * C⁻¹ * R ^ 2 < 1 / 100 := by
    have h1 : c ^ 2 * C⁻¹ * R ^ 2 = (100 * c ^ 2 * R ^ 2) * C⁻¹ / 100 := by ring
    rw [h1, div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 100)]
    calc 100 * c ^ 2 * R ^ 2 * C⁻¹ < C * C⁻¹ := mul_lt_mul_of_pos_right hcon hl
      _ = 1 := mul_inv_cancel₀ hC.ne'
  have hy0 : 0 ≤ c ^ 2 * C⁻¹ * R ^ 2 := by positivity
  have hcR : 1 ≤ c ^ 2 * R ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hc)
    (one_le_pow₀ hR)
  have hlam : C⁻¹ ≤ 1 / 100 := by nlinarith
  -- the dyadic summation of (63) gives `S₁ ≤ 5/90`
  have hS1 : S 1 ≤ 5 / 90 := by
    refine FunctionalInequalities.Analysis.le_of_dyadic_recursion (N := N) (x := c * C⁻¹) (A := 5)
      (fun d hd => ?_) (by norm_num) hy0 (by linarith) fun d hd => ?_
    · simp only [hS, Nat.sub_eq_zero_of_le hd, range_zero, sum_empty]
    · exact FunctionalInequalities.KLS.LogConcave.PoissonIterate.dyadic_step hC hc hd
        (FunctionalInequalities.KLS.LogConcave.PoissonIterate.recursion_readable hC hc hR hd hvk hχ hχsum hL0 hαN ht htaylor hJ1)
  -- Lemma 3.9 against (36): `λ/2 < Σ p ≤ 1.21 λ² + 3 λ S₁ < λ/2`
  have hp := hJ2 N fun j hj => (hαN j hj).2
  have h36N := h36 N
  have hpS : 3 / C * S 1 ≤ 3 / C * (5 / 90) :=
    mul_le_mul_of_nonneg_left hS1 (by positivity)
  have hsq : (11 / 10 * C⁻¹) ^ 2 ≤ 121 / 100 * (C⁻¹ * (1 / 100)) := by
    have := mul_le_mul_of_nonneg_left hlam hl.le
    nlinarith
  rw [div_eq_mul_inv] at hpS
  change ∑ k ∈ range N, p k ≤ L 0 + 3 / C * S 1 at hp
  rw [div_eq_mul_inv] at hp
  linarith
