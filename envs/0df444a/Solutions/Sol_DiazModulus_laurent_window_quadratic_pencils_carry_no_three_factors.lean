-- Prove2me | solution 1 for DiazModulus.laurent_window_quadratic_pencils_carry_no_three_factors
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:46:43.254981+00:00
-- url     : https://prove2.me/submissions/44d59657-4f2f-43aa-9f85-18273afb72bb

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_laurent_window_factor_in_hull_plus_min_degree_line

open Complex ComplexConjugate

/-! # The pencils `(1, X² + αX)` and `(X + β, X² + γX)` carry no three free factors

Let `H = span(X^(N-1), X^N, X^(N+1))` and `W = H ⊔ M`, where every non-zero element of the plane
`M` has order at most `N - 2` and degree at least `N + 2` (so `N ≥ 2`).
Absorption: an element of `W` divisible by `X^(N-1)` lies in `H`, since its `M`-part is then
divisible by `X^(N-1)`, against the order bound.
Let `(p, q)` be one of the pencils and `b₀, b₁, b₂` free with `p b_j, q b_j ∈ W`. By
`laurent_window_factor_in_hull_plus_min_degree_line` (`deg p < deg q`), the 3-space
`Y = span(p b_j)` lies in `H + K n`, so `dim (Y ∩ H) ≥ 2` (dimension of sum and intersection).
On the other hand let `p y ∈ Y ∩ H`. Then `X^(N-1) ∣ y` (for `p = X + β`, `β ≠ 0`, because
`X^(N-1)` is coprime to `p`), so `X^(N-1) ∣ q y`; by absorption `q y ∈ H` has degree at most
`N + 1`, and `deg q = 2` forces `y ∈ K X^(N-1)`. So `Y ∩ H` is at most a line: a contradiction.
-/

open Polynomial

namespace R18_L3

open DiazModulus

variable {K : Type*} [Field K]

/-- Window elements are divisible by `X^(N-1)` and have degree at most `N + 1`. -/
theorem window_prop {N : ℕ} {h : K[X]}
    (hh : h ∈ Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X])) :
    X ^ (N - 1) ∣ h ∧ h.natDegree ≤ N + 1 := by
  induction hh using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨dvd_rfl, (natDegree_X_pow_le _).trans (by omega)⟩
    · exact ⟨pow_dvd_pow _ (by omega), (natDegree_X_pow_le _).trans (by omega)⟩
    · exact ⟨pow_dvd_pow _ (by omega), natDegree_X_pow_le _⟩
  | zero => exact ⟨dvd_zero _, by simp⟩
  | add x y _ _ hx hy => exact ⟨dvd_add hx.1 hy.1, natDegree_add_le_of_degree_le hx.2 hy.2⟩
  | smul a x _ hx =>
    refine ⟨?_, (natDegree_smul_le _ _).trans hx.2⟩
    rw [smul_eq_C_mul]; exact dvd_mul_of_dvd_right hx.1 _

/-- Absorption: an element of `H ⊔ M` divisible by `X^(N-1)` lies in `H`. -/
theorem absorb {N : ℕ} (hN : 2 ≤ N) {M : Submodule K K[X]}
    (hMo : ∀ f ∈ M, f ≠ 0 → f.natTrailingDegree + 2 ≤ N) {f : K[X]}
    (hf : f ∈ Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M)
    (hdvd : X ^ (N - 1) ∣ f) :
    f ∈ Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) := by
  obtain ⟨h, hh, m, hm, rfl⟩ := Submodule.mem_sup.mp hf
  by_cases hm0 : m = 0
  · rw [hm0, add_zero]; exact hh
  exfalso
  have hdm : X ^ (N - 1) ∣ m := by
    have := dvd_sub hdvd (window_prop hh).1
    rwa [add_sub_cancel_left] at this
  have hc := (X_pow_dvd_iff.mp hdm) m.natTrailingDegree (by have := hMo m hm hm0; omega)
  exact hm0 (trailingCoeff_eq_zero.mp hc)

/-- If `X^(N-1) ∣ y`, `deg q = 2` and `deg (q y) ≤ N + 1`, then `y ∈ K X^(N-1)`. -/
theorem small {N : ℕ} {q y : K[X]} (hq : q.natDegree = 2) (hdvd : X ^ (N - 1) ∣ y)
    (hd : (q * y).natDegree ≤ N + 1) : y ∈ K ∙ (X ^ (N - 1) : K[X]) := by
  obtain ⟨g, rfl⟩ := hdvd
  by_cases hg : g = 0
  · rw [hg, mul_zero]; exact Submodule.zero_mem _
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hX : (X ^ (N - 1) : K[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  rw [natDegree_mul hq0 (mul_ne_zero hX hg), natDegree_mul hX hg, natDegree_X_pow] at hd
  have hg0 : g.natDegree = 0 := by omega
  rw [eq_C_of_natDegree_eq_zero hg0, mul_comm, ← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- A 3-space inside `H + K n` meets `H` in at least a plane, so not inside a line. -/
theorem dim_contra {H Y : Submodule K K[X]} [FiniteDimensional K H] [FiniteDimensional K Y]
    {n e : K[X]} (hY : Module.finrank K Y = 3) (hYle : Y ≤ H ⊔ K ∙ n) (hYH : Y ⊓ H ≤ K ∙ e) :
    False := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq Y H
  have h2 : Module.finrank K ↥(Y ⊔ H) ≤ Module.finrank K ↥(H ⊔ K ∙ n) :=
    Submodule.finrank_mono (sup_le hYle le_sup_left)
  have h3 := Submodule.finrank_add_le_finrank_add_finrank H (K ∙ n)
  have h4 : Module.finrank K (K ∙ n) ≤ 1 := (finrank_span_le_card ({n} : Set K[X])).trans (by simp)
  have h5 : Module.finrank K ↥(Y ⊓ H) ≤ Module.finrank K (K ∙ e) := Submodule.finrank_mono hYH
  have h6 : Module.finrank K (K ∙ e) ≤ 1 := (finrank_span_le_card ({e} : Set K[X])).trans (by simp)
  omega

theorem isCoprime_X_add_C {β : K} (hβ : β ≠ 0) : IsCoprime (X : K[X]) (X + C β) := by
  refine ⟨-C β⁻¹, C β⁻¹, ?_⟩
  have h : C β⁻¹ * C β = 1 := by rw [← C_mul, inv_mul_cancel₀ hβ, C_1]
  linear_combination h

end R18_L3

open DiazModulus R18_L3 in
open Polynomial in
theorem solution (K : Type*) [Field K] (N : ℕ) (M : Submodule K K[X]) (hM2 : Module.finrank K M = 2)
    (hMo : ∀ f ∈ M, f ≠ 0 → f.natTrailingDegree + 2 ≤ N)
    (hMd : ∀ f ∈ M, f ≠ 0 → N + 2 ≤ f.natDegree) :
    (∀ α : K, ¬ ∃ b : Fin 3 → K[X], LinearIndependent K b ∧ ∀ j, b j ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) ∧
          (X ^ 2 + C α * X) * b j ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M)) ∧
    (∀ β γ : K, β ≠ 0 → ¬ ∃ b : Fin 3 → K[X], LinearIndependent K b ∧ ∀ j, (X + C β) * b j ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) ∧
          (X ^ 2 + C γ * X) * b j ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M)) := by
  set H := Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) with hH
  have : FiniteDimensional K H := FiniteDimensional.span_of_finite K (Set.toFinite _)
  have hN : 2 ≤ N := by
    have hMne : M ≠ ⊥ := by rintro rfl; simp at hM2
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hMne
    have := hMo f hf hf0; omega
  obtain ⟨n, -, -, -, hL2⟩ :=
    DiazModulus.laurent_window_factor_in_hull_plus_min_degree_line K N M hM2 hMd
  have hS : Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1), n} : Set K[X]) ≤ H ⊔ K ∙ n := by
    rw [Submodule.span_le]
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact Submodule.mem_sup_left (Submodule.subset_span (by simp))
    · exact Submodule.mem_sup_left (Submodule.subset_span (by simp))
    · exact Submodule.mem_sup_left (Submodule.subset_span (by simp))
    · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  -- the common dimension count
  have key : ∀ (c : Fin 3 → K[X]) (e : K[X]), LinearIndependent K c → (∀ j, c j ∈ H ⊔ K ∙ n) →
      Submodule.span K (Set.range c) ⊓ H ≤ K ∙ e → False := by
    intro c e hc hcS hle
    have : FiniteDimensional K (Submodule.span K (Set.range c)) :=
      FiniteDimensional.span_of_finite K (Set.finite_range c)
    refine dim_contra (n := n) ((finrank_span_eq_card hc).trans (by simp)) ?_ hle
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hcS j
  -- `q y ∈ W` for every `y` in the span of the factors
  have hcomap : ∀ (b : Fin 3 → K[X]) (q : K[X]), (∀ j, q * b j ∈ H ⊔ M) →
      ∀ y ∈ Submodule.span K (Set.range b), q * y ∈ H ⊔ M := by
    intro b q hb y hy
    have : Submodule.span K (Set.range b) ≤ (H ⊔ M).comap (LinearMap.mulLeft K q) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hb j
    exact this hy
  refine ⟨?_, ?_⟩
  · rintro α ⟨b, hb, hbW⟩
    have hq : (X ^ 2 + C α * X : K[X]).natDegree = 2 := by compute_degree!
    refine key b (X ^ (N - 1)) hb (fun j => hS ?_) ?_
    · have := hL2 1 (X ^ 2 + C α * X) (b j) (by rw [natDegree_one, hq]; norm_num)
        (by rw [one_mul]; exact (hbW j).1) (hbW j).2
      rwa [one_mul] at this
    · rintro y ⟨hyY, hyH⟩
      have hqy := hcomap b _ (fun j => (hbW j).2) y hyY
      have hyd := (window_prop hyH).1
      exact small hq hyd (window_prop (absorb hN hMo hqy (dvd_mul_of_dvd_right hyd _))).2
  · rintro β γ hβ ⟨b, hb, hbW⟩
    have hq : (X ^ 2 + C γ * X : K[X]).natDegree = 2 := by compute_degree!
    have hp0 : (X + C β : K[X]) ≠ 0 := X_add_C_ne_zero β
    have hc : LinearIndependent K (fun j => (X + C β) * b j) :=
      hb.map' (LinearMap.mulLeft K (X + C β))
        (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ hp0))
    refine key (fun j => (X + C β) * b j) ((X + C β) * X ^ (N - 1)) hc (fun j => hS ?_) ?_
    · exact hL2 (X + C β) (X ^ 2 + C γ * X) (b j) (by rw [natDegree_X_add_C, hq]; norm_num)
        (hbW j).1 (hbW j).2
    · rintro z ⟨hzY, hzH⟩
      have hmap : Submodule.span K (Set.range fun j => (X + C β) * b j) =
          (Submodule.span K (Set.range b)).map (LinearMap.mulLeft K (X + C β)) := by
        rw [Submodule.map_span, ← Set.range_comp]; rfl
      rw [hmap] at hzY
      obtain ⟨y, hyY, rfl⟩ := hzY
      rw [LinearMap.mulLeft_apply] at hzH ⊢
      have hqy := hcomap b _ (fun j => (hbW j).2) y hyY
      have hyd : X ^ (N - 1) ∣ y :=
        ((isCoprime_X_add_C hβ).pow_left).dvd_of_dvd_mul_left (window_prop hzH).1
      have := small hq hyd (window_prop (absorb hN hMo hqy (dvd_mul_of_dvd_right hyd _))).2
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp this
      exact Submodule.mem_span_singleton.mpr ⟨c, by rw [mul_smul_comm]⟩
