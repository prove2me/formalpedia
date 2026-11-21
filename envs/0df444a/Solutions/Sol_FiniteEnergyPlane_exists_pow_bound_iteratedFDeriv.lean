-- Prove2me | solution 1 for FiniteEnergyPlane.exists_pow_bound_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T19:15:58.846248+00:00
-- url     : https://prove2.me/submissions/8ce40f16-2ab0-432a-b9e1-745cd2672738

import Mathlib



/-!
# R′ generic helpers: derivative bounds on `ℝ × ℝ` (Mathlib only)
-/

namespace FiniteEnergyPlane

open Set
open scoped ContDiff

namespace DGA3R

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Derivatives of order `≥ 1` of a map with constant derivative. -/
lemma norm_iteratedFDeriv_le_of_hasFDerivAt_const {f : E → F} (L : E →L[ℝ] F)
    (hf : ∀ x, HasFDerivAt f L x) (k : ℕ) (hk : 1 ≤ k) (x : E) :
    ‖iteratedFDeriv ℝ k f x‖ ≤ ‖L‖ := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv]
  have e : fderiv ℝ f = fun _ => L := funext fun x => (hf x).fderiv
  rw [e]
  rcases j with _ | j
  · simp
  · rw [iteratedFDeriv_const_of_ne (by omega)]; simp

lemma periodic_int {G : ℝ × ℝ → F} (hper : ∀ q : ℝ × ℝ, G (q + (0, 1)) = G q) (n : ℤ)
    (q : ℝ × ℝ) : G (q + (0, (n : ℝ))) = G q := by
  induction n using Int.induction_on generalizing q with
  | zero => rw [Int.cast_zero, Prod.mk_zero_zero, add_zero]
  | succ n ih =>
    have e : q + (0, (((n : ℤ) + 1 : ℤ) : ℝ)) = (q + (0, (((n : ℤ) : ℤ) : ℝ))) + (0, 1) := by
      push_cast; ext <;> simp; ring
    rw [e, hper, ih]
  | pred n ih =>
    have e : (q + (0, ((-(n : ℤ) - 1 : ℤ) : ℝ))) + (0, 1) = q + (0, ((-(n : ℤ) : ℤ) : ℝ)) := by
      push_cast; ext <;> simp; ring
    rw [← ih q, ← e, hper]

/-- Smooth maps `1`-periodic in `t` have bounded derivatives on strips of bounded `s`. -/
lemma strip_bound {G : ℝ × ℝ → F} (hG : ContDiff ℝ ∞ G)
    (hper : ∀ q : ℝ × ℝ, G (q + (0, 1)) = G q) (lo hi : ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ a ∈ Icc lo hi, ∀ b : ℝ, ‖iteratedFDeriv ℝ k G (a, b)‖ ≤ C := by
  set K : Set (ℝ × ℝ) := Icc lo hi ×ˢ Icc (0 : ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (iteratedFDeriv ℝ k G) K :=
    (hG.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨C, fun a ha b => ?_⟩
  set v : ℝ × ℝ := (0, ((⌊b⌋ : ℤ) : ℝ)) with hv
  set x : ℝ × ℝ := (a, Int.fract b) with hx
  have hxK : x ∈ K := ⟨ha, ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩⟩
  have hxv : x + v = (a, b) := by
    simp only [hx, hv, Prod.mk_add_mk, add_zero, Int.fract_add_floor]
  have hfun : (fun z => G (z + v)) = G := funext fun z => periodic_int hper _ z
  have e : iteratedFDeriv ℝ k G (a, b) = iteratedFDeriv ℝ k G x := by
    rw [← hxv, ← iteratedFDeriv_comp_add_right, hfun]
  rw [e]
  exact hC x hxK

/-- Finitely many strip bounds combine into one. -/
lemma strip_bound_le {G : ℝ × ℝ → F} {lo hi : ℝ}
    (h : ∀ k : ℕ, ∃ C : ℝ, ∀ a ∈ Icc lo hi, ∀ b : ℝ, ‖iteratedFDeriv ℝ k G (a, b)‖ ≤ C)
    (n : ℕ) : ∃ C : ℝ, ∀ i ≤ n, ∀ a ∈ Icc lo hi, ∀ b : ℝ, ‖iteratedFDeriv ℝ i G (a, b)‖ ≤ C := by
  induction n with
  | zero =>
    obtain ⟨C, hC⟩ := h 0
    exact ⟨C, fun i hi a ha b => by
      obtain rfl : i = 0 := by omega
      exact hC a ha b⟩
  | succ n ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨C', hC'⟩ := h (n + 1)
    refine ⟨max C C', fun i hi a ha b => ?_⟩
    rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
    · exact (hC i (by omega) a ha b).trans (le_max_left _ _)
    · obtain rfl : i = n + 1 := by omega
      exact (hC' a ha b).trans (le_max_right _ _)

/-- Finitely many derivative bounds combine into bounds by powers `D ^ i` with `1 ≤ D`. -/
lemma pow_bounds {X : ℝ × ℝ → F}
    (h : ∀ m : ℕ, 1 ≤ m → ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖iteratedFDeriv ℝ m X (s, t)‖ ≤ C)
    (n : ℕ) : ∃ D s₁ : ℝ, 1 ≤ D ∧ ∀ i, 1 ≤ i → i ≤ n → ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ i X (s, t)‖ ≤ D ^ i := by
  induction n with
  | zero => exact ⟨1, 0, le_rfl, fun i h1 h2 => by omega⟩
  | succ n ih =>
    obtain ⟨D, s₁, hD1, hD⟩ := ih
    obtain ⟨C, s₂, hC⟩ := h (n + 1) (by omega)
    refine ⟨max D (max 1 C), max s₁ s₂, le_trans hD1 (le_max_left _ _), fun i h1 h2 s hs t => ?_⟩
    have hD0 : 0 ≤ D := by linarith
    have hs1 : s₁ ≤ s := le_trans (le_max_left _ _) hs
    have hs2 : s₂ ≤ s := le_trans (le_max_right _ _) hs
    have hM1 : 1 ≤ max D (max 1 C) := le_trans (le_max_left 1 C) (le_max_right _ _)
    rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
    · exact (hD i h1 (by omega) s hs1 t).trans
        (pow_le_pow_left₀ hD0 (le_max_left _ _) i)
    · obtain rfl : i = n + 1 := by omega
      calc ‖iteratedFDeriv ℝ (n + 1) X (s, t)‖ ≤ C := hC s hs2 t
        _ ≤ max D (max 1 C) := le_trans (le_max_right 1 C) (le_max_right _ _)
        _ ≤ max D (max 1 C) ^ (n + 1) := le_self_pow₀ hM1 (by omega)

end DGA3R

end FiniteEnergyPlane

open FiniteEnergyPlane

open scoped ContDiff

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {X : ℝ × ℝ → F}
    (h : ∀ m : ℕ, 1 ≤ m → ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖iteratedFDeriv ℝ m X (s, t)‖ ≤ C)
    (n : ℕ) : ∃ D s₁ : ℝ, 1 ≤ D ∧ ∀ i, 1 ≤ i → i ≤ n → ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ i X (s, t)‖ ≤ D ^ i :=
  FiniteEnergyPlane.DGA3R.pow_bounds h n
