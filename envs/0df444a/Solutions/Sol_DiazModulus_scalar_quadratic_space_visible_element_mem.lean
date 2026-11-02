-- Prove2me | solution 1 for DiazModulus.scalar_quadratic_space_visible_element_mem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:30:28.048701+00:00
-- url     : https://prove2.me/submissions/d340a589-1ab0-48ae-8387-81b5d316f0da

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_quadratic_fraction_extension_visible_element_mem_of_common_zero

open Complex ComplexConjugate

/-! # A scalar quadratic space contains a `t_x`

`W ⊇ H₀ = span(1, u, u⁻¹)` contains `Q(u) R(u)/(u P(u))` for every `R` of degree `≤ 2`. Pick `S` of
degree `≤ 2` with a common zero with `P` on `P¹` and `S ∉ Q̄·P`:
* `deg P = 2`: `P` has a root `x ∈ Q̄` (roots in `ℂ` of polynomials over `Q̄` are algebraic); `S = X − x`
  is not coprime to `P`, and has degree `1 ≠ 2`;
* `deg P = 1`: `S = 1` (common zero at `∞`: both `X²`-coefficients vanish);
* `deg P = 0`: `S = X` (same).
Then `quadratic_fraction_extension_visible_element_mem_of_common_zero` puts a `t_x` in
`H₀ + Q̄·Q(u) S(u)/(u P(u)) ≤ W`.
-/

namespace R21b_V5

open DiazModulus Polynomial

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

/-- A polynomial over `Q̄` of positive degree has a root in `Q̄`. -/
theorem exists_root {p : (↥Qbar)[X]} (hp : 0 < p.natDegree) : ∃ b : ↥Qbar, p.IsRoot b := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective (k := ℂ)
    (R := ↥Qbar) Subtype.val_injective p (by
      rw [degree_eq_natDegree (ne_zero_of_natDegree_gt hp)]; exact_mod_cast hp.ne')
  by_cases hzq : z ∈ Qbar
  · refine ⟨⟨z, hzq⟩, ?_⟩
    have : aeval (algebraMap (↥Qbar) ℂ ⟨z, hzq⟩) p = 0 := hz
    rw [aeval_algebraMap_apply, coe_aeval_eq_eval] at this
    exact Subtype.val_injective (by simpa using this)
  · exact absurd (transcendental_iff.1 (tr_of_not_mem hzq) p hz) (ne_zero_of_natDegree_gt hp)

theorem ne_smul {S P : (↥Qbar)[X]} (hS0 : S ≠ 0) (hd : S.natDegree ≠ P.natDegree) (k : ↥Qbar) :
    S ≠ C k * P := by
  intro h
  by_cases hk : k = 0
  · exact hS0 (by simpa [hk] using h)
  · exact hd (by rw [h, natDegree_C_mul hk])

end R21b_V5

open DiazModulus R21b_V5 in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (P Q : (↥Qbar)[X]) (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2)
    (hscal : ∀ R : (↥Qbar)[X], R.natDegree ≤ 2 → aeval u Q * aeval u R / (u * aeval u P) ∈ W) :
    (u ^ 2 ∈ W ∨ (u ^ 2)⁻¹ ∈ W ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ W) := by
  have hP2 : P.natDegree ≤ 2 := hdeg ▸ le_max_left _ _
  obtain ⟨S, hS, hSP, hz⟩ : ∃ S : (↥Qbar)[X], S.natDegree ≤ 2 ∧ (∀ k : ↥Qbar, S ≠ C k * P) ∧
      (¬ IsCoprime P S ∨ (P.coeff 2 = 0 ∧ S.coeff 2 = 0)) := by
    rcases (show P.natDegree = 2 ∨ P.natDegree = 1 ∨ P.natDegree = 0 by omega) with h | h | h
    · obtain ⟨x, hx⟩ := exists_root (show 0 < P.natDegree by omega)
      refine ⟨X - C x, by rw [natDegree_X_sub_C]; omega,
        ne_smul (X_sub_C_ne_zero x) (by rw [natDegree_X_sub_C]; omega), Or.inl fun ⟨a, b, e⟩ => ?_⟩
      simpa [hx.eq_zero] using congrArg (eval x) e
    · exact ⟨1, by simp, ne_smul one_ne_zero (by simp [h]),
        Or.inr ⟨coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by simp)⟩⟩
    · exact ⟨X, by simp, ne_smul X_ne_zero (by simp [h]),
        Or.inr ⟨coeff_eq_zero_of_natDegree_lt (by omega), by simp [coeff_X]⟩⟩
  have hle : Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S / (u * aeval u P)} : Set ℂ) ≤ W :=
    Submodule.span_le.2 (by
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      exact ⟨h1, hu1, hui, hscal S hS⟩)
  rcases quadratic_fraction_extension_visible_element_mem_of_common_zero u hu P Q S hcop hdeg hS hSP hz
    with h | h | ⟨a, ha, ha0, h⟩
  · exact Or.inl (hle h)
  · exact Or.inr (Or.inl (hle h))
  · exact Or.inr (Or.inr ⟨a, ha, ha0, hle h⟩)
