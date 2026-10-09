-- Prove2me | solution 1 for DiazModulus.candidate_power_pair_not_both_mem_logAlgTilde
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-08T16:36:09.516995+00:00
-- url     : https://prove2.me/submissions/68aa6365-5810-469e-bd6e-de856117f500

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_logAlgTilde_conj_stable
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate

/-! # Two powers `u^k, u^l` of a candidate are not both in `ℒ̃` (Diaz 2007)

Under Roy's strong six exponentials theorem, let `u` be a candidate, `4 ≤ k < l` with
`l ∈ {k+1, k+2, 2k−1, 2k, 2k+1, 3k}`. Suppose `u^k, u^l ∈ ℒ̃`.

At a candidate `ρ = u ū = |u|²` is algebraic and non-zero, and `u ∉ Q̄` by Hermite–Lindemann, so
`u` is transcendental over `Q̄`; hence powers `u^a` with distinct integer exponents are
`Q̄`-linearly independent. Since `ℒ̃` is stable under conjugation, `u^n ∈ ℒ̃` gives
`u^{−n} = ρ^{−n} ūⁿ ∈ ℒ̃`; with `1 ∈ ℒ̃` and `u ∈ ℒ` this puts `u^s ∈ ℒ̃` for every
`s ∈ S = {0, ±1, ±k, ±l}`. For each of the six cases a `2 × 3` configuration
`x = (u^a)_{a ∈ A}`, `y = (u^b)_{b ∈ B}` with `A + B ⊆ S` (Table 2 of the note) lies in `ℒ̃`:
`l = k+1`: `A = {0,1}, B = {−1,0,k}`; `l = k+2`: `A = {0,2}, B = {−1,k,−k−2}`;
`l = 2k−1`: `A = {0,k−1}, B = {1,−k,k}`; `l = 2k`: `A = {0,k}, B = {0,−k,k}`;
`l = 2k+1`: `A = {0,k+1}, B = {−1,−k,k}`; `l = 3k`: `A = {0,2k}, B = {−k,k,−3k}`.
This contradicts the strong six exponentials hypothesis.
-/

namespace R6_powerPair
open DiazModulus Polynomial

theorem transcendental_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental Qbar u := by
  have : Algebra.IsAlgebraic ℚ Qbar := ⟨fun x =>
    (isAlgebraic_algHom_iff (Qbar.subtype.toRatAlgHom) Subtype.val_injective).1
      (mem_Qbar_iff.1 x.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h => hu (mem_Qbar_iff.2 h)

/-- Distinct natural powers of a transcendental element are linearly independent. -/
theorem linInd_pow {u : ℂ} (hu : Transcendental Qbar u) {n : ℕ} (f : Fin n → ℕ)
    (hf : Function.Injective f) : LinearIndependent Qbar (fun i => u ^ f i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hp : (∑ j, C (g j) * X ^ f j : Qbar[X]) = 0 := by
    by_contra hne
    exact hu ⟨_, hne, by simpa [Polynomial.aeval_def, Polynomial.eval₂_finsetSum,
      Algebra.smul_def] using hg⟩
  have := congrArg (fun p : Qbar[X] => p.coeff (f i)) hp
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, hf.eq_iff] using this

/-- Distinct integer powers of a non-zero transcendental element are linearly independent. -/
theorem linInd_zpow {u : ℂ} (hu : Transcendental Qbar u) (hu0 : u ≠ 0) {n : ℕ} (e : Fin n → ℤ)
    (he : Function.Injective e) : LinearIndependent Qbar (fun i => u ^ e i) := by
  set N : ℕ := ∑ i, (e i).natAbs
  have hN : ∀ i, 0 ≤ e i + N := fun i => by
    have : (e i).natAbs ≤ N := Finset.single_le_sum (f := fun i => (e i).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hf : Function.Injective (fun i => (e i + N).toNat) := fun i j hij => by
    have := hN i; have := hN j
    exact he (by simp only at hij; omega)
  have hc : u ^ (-(N : ℤ)) ≠ 0 := zpow_ne_zero _ hu0
  have hker : LinearMap.ker (LinearMap.mulLeft Qbar (u ^ (-(N : ℤ)))) = ⊥ :=
    LinearMap.ker_eq_bot.2 (mul_right_injective₀ hc)
  have hmap := (linInd_pow hu _ hf).map' _ hker
  have heq : (fun i => u ^ e i) =
      (LinearMap.mulLeft Qbar (u ^ (-(N : ℤ)))) ∘ (fun i => u ^ (e i + N).toNat) := by
    funext i
    simp only [Function.comp_apply, LinearMap.mulLeft_apply]
    rw [← zpow_natCast, Int.toNat_of_nonneg (hN i), ← zpow_add₀ hu0]
    ring_nf
  rw [heq]
  exact hmap

theorem neg_mem {u : ℂ} (hu0 : u ≠ 0) (hρ : u * conj u ∈ Qbar) (n : ℕ)
    (h : u ^ n ∈ LogAlgTilde) : u ^ (-(n : ℤ)) ∈ LogAlgTilde := by
  have hc0 : conj u ≠ 0 := (_root_.map_ne_zero _).2 hu0
  have heq : u ^ (-(n : ℤ)) = ((u * conj u) ^ n)⁻¹ * conj (u ^ n) := by
    rw [zpow_neg, zpow_natCast, map_pow, mul_pow, mul_inv, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero n hc0), mul_one]
  rw [heq]
  exact Submodule.smul_mem LogAlgTilde (⟨_, Qbar.inv_mem (Qbar.pow_mem hρ n)⟩ : Qbar)
    (logAlgTilde_conj_stable _ h)

/-- The shared step: a `2 × 3` configuration of integer powers of `u` with all products in
`ℒ̃` contradicts the strong six exponentials hypothesis. -/
theorem config_false
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {u : ℂ} (hu : Transcendental Qbar u) (hu0 : u ≠ 0) (a : Fin 2 → ℤ) (b : Fin 3 → ℤ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hmem : ∀ i j, u ^ (a i + b j) ∈ LogAlgTilde) : False :=
  hSSE (fun i => u ^ a i) (fun j => u ^ b j) (linInd_zpow hu hu0 a ha) (linInd_zpow hu hu0 b hb)
    fun i j => by rw [← zpow_add₀ hu0]; exact hmem i j

end R6_powerPair

open DiazModulus R6_powerPair in
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {u : ℂ} (h : IsCandidate u) (k l : ℕ) (hk : 4 ≤ k) (hkl : k < l)
    (hl : l = k + 1 ∨ l = k + 2 ∨ l = 2 * k - 1 ∨ l = 2 * k ∨ l = 2 * k + 1 ∨ l = 3 * k) :
    ¬ (u ^ k ∈ LogAlgTilde ∧ u ^ l ∈ LogAlgTilde) := by
  rintro ⟨hkL, hlL⟩
  have hu0 : u ≠ 0 := h.1
  have hu : Transcendental Qbar u :=
    transcendental_of_not_mem fun hq => hermite_lindemann_holds u h.1 (mem_Qbar_iff.1 hq) h.2.2
  have hρ : u * conj u ∈ Qbar := by
    rw [Complex.mul_conj']
    exact Qbar.pow_mem (mem_Qbar_iff.2 h.2.1) 2
  have h1 : u ^ (1 : ℕ) ∈ LogAlgTilde := by
    rw [pow_one]; exact Submodule.subset_span (Set.mem_insert_of_mem _ h.2.2)
  have hS : ∀ s : ℤ, (s = 0 ∨ s = 1 ∨ s = -1 ∨ s = k ∨ s = -k ∨ s = l ∨ s = -l) →
      u ^ s ∈ LogAlgTilde := by
    rintro s (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · rw [zpow_zero]; exact Submodule.subset_span (Set.mem_insert _ _)
    · simpa using h1
    · simpa using neg_mem hu0 hρ 1 h1
    · rwa [zpow_natCast]
    · exact neg_mem hu0 hρ k hkL
    · rwa [zpow_natCast]
    · exact neg_mem hu0 hρ l hlL
  have key := config_false hSSE hu hu0
  rcases hl with hl | hl | hl | hl | hl | hl
  · refine key ![0, 1] ![-1, 0, k] ?_ ?_ ?_
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
    · intro i j; apply hS; fin_cases i <;> fin_cases j <;> simp; omega
  · refine key ![0, 2] ![-1, k, -k - 2] ?_ ?_ ?_
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
    · intro i j; apply hS; fin_cases i <;> fin_cases j <;> simp <;> omega
  · refine key ![0, k - 1] ![1, -k, k] ?_ ?_ ?_
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
    · intro i j; apply hS; fin_cases i <;> fin_cases j <;> simp <;> omega
  · refine key ![0, k] ![0, -k, k] ?_ ?_ ?_
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
    · intro i j; apply hS; fin_cases i <;> fin_cases j <;> simp; omega
  · refine key ![0, k + 1] ![-1, -k, k] ?_ ?_ ?_
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
    · intro i j; apply hS; fin_cases i <;> fin_cases j <;> simp; omega
  · refine key ![0, 2 * k] ![-k, k, -3 * k] ?_ ?_ ?_
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
    · intro i j; apply hS; fin_cases i <;> fin_cases j <;> simp <;> omega
