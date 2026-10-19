-- Prove2me | solution 1 for DiazModulus.degree_one_space_mem_square_or_reciprocal_of_cubic_over_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T09:52:03.74808+00:00
-- url     : https://prove2.me/submissions/2dc9a83f-9d83-45fe-b680-ce251fec6ca1

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Cubic over quadratic: a degree-one space contains a Theorem B element

Here `u ∉ Q̄`, so `u` is transcendental over `Q̄`, `u ≠ 0`, and `ρ = u ū ∈ Q̄` gives `ū = ρ/u`. As `R ≠ 0`,
`D = u R(u) ≠ 0`, and `φ(M) = M(u)/D` is a `Q̄`-linear map `Q̄[X] → ℂ`. The five generators of
`W = span(1, u, ū, g, ug)` are `φ(XR)`, `φ(X²R)`, `φ(ρR)`, `φ(N)` (by `u R(u) g = N(u)`) and `φ(XN)`, all of degree
at most 4. So `W ≤ φ(Q̄[X]_{<5})`, a space of dimension at most 5 (`Submodule.finrank_map_le`). Since
`1, u, ū, g, ug` are free, `W` has dimension 5, and the two spaces are equal
(`Submodule.eq_of_le_of_finrank_le`): every `φ(M)` with `deg M ≤ 4` lies in `W`. Three cases finish. If
`deg R ≤ 1` then `u² = φ(X³R)`. If `R(0) = 0` then `R = X R₁` and `ū² = ρ²/u² = φ(ρ² R₁)`. Otherwise `deg R = 2`
and `R(0) ≠ 0`; `R` has a root `b` in `ℂ` (`IsAlgClosed`), which is algebraic, so `b ∈ Q̄`, and `b ≠ 0`. Writing
`R = (X − b) R₁` gives `(u − b)⁻¹ = φ(X R₁)`.
-/

namespace R17_vis_b

open DiazModulus Polynomial

theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem exists_root {p : (↥Qbar)[X]} (hp : 0 < p.natDegree) : ∃ b : ↥Qbar, p.IsRoot b := by
  have hp0 : p ≠ 0 := ne_zero_of_natDegree_gt hp
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective (k := ℂ)
    (R := ↥Qbar) Subtype.val_injective p (by
      rw [degree_eq_natDegree hp0]; exact_mod_cast hp.ne')
  by_cases hzq : z ∈ Qbar
  · refine ⟨⟨z, hzq⟩, ?_⟩
    have : aeval (algebraMap (↥Qbar) ℂ ⟨z, hzq⟩) p = 0 := hz
    rw [aeval_algebraMap_apply, coe_aeval_eq_eval] at this
    exact Subtype.val_injective (by simpa using this)
  · exact absurd (aeval_eq_zero hzq hz) hp0

theorem mem_dLT {M : (↥Qbar)[X]} (h : M.natDegree ≤ 4) : M ∈ degreeLT (↥Qbar) 5 := by
  rw [mem_degreeLT]
  exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le h)

/-- The dimension count: `W = φ(Q̄[X]_{<5})`, so every `M(u)/(u R(u))` with `deg M ≤ 4` lies in `W`. -/
theorem key {u g : ℂ} (hu0 : u ≠ 0) (ρ : ↥Qbar) (hρ : (ρ : ℂ) = u * conj u)
    (hind : LinearIndependent (↥Qbar) ![1, u, conj u, g, u * g])
    (R N : (↥Qbar)[X]) (hRd : R.natDegree ≤ 2) (hNd : N.natDegree ≤ 3)
    (hD : u * aeval u R ≠ 0) (hRN : u * aeval u R * g = aeval u N)
    (M : (↥Qbar)[X]) (hM : M.natDegree ≤ 4) :
    (u * aeval u R)⁻¹ * aeval u M ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ) := by
  have hR0 : aeval u R ≠ 0 := right_ne_zero_of_mul hD
  set D := u * aeval u R with hDdef
  let φ : (↥Qbar)[X] →ₗ[↥Qbar] ℂ := (LinearMap.mulLeft (↥Qbar) D⁻¹).comp (aeval u).toLinearMap
  set V := (degreeLT (↥Qbar) 5).map φ
  set W := Submodule.span (↥Qbar) ({1, u, conj u, g, u * g} : Set ℂ) with hWdef
  have hmem : ∀ p : (↥Qbar)[X], p.natDegree ≤ 4 → D⁻¹ * aeval u p ∈ V := fun p hp =>
    Submodule.mem_map.2 ⟨p, mem_dLT hp, rfl⟩
  have hdeg : ∀ p : (↥Qbar)[X], ∀ n, p.natDegree ≤ n → (X * p).natDegree ≤ n + 1 := fun p n hp =>
    natDegree_mul_le.trans (by rw [natDegree_X]; omega)
  have hle : W ≤ V := by
    rw [hWdef, Submodule.span_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := hmem (X * R) ((hdeg R 2 hRd).trans (by norm_num))
      rwa [map_mul, aeval_X, ← hDdef, inv_mul_cancel₀ hD] at this
    · have := hmem (X * (X * R)) ((hdeg _ 3 (hdeg R 2 hRd)).trans (by norm_num))
      convert this using 1
      simp only [map_mul, aeval_X, hDdef]
      field_simp
    · have := hmem (C ρ * R) (natDegree_C_mul_le _ _ |>.trans (by omega))
      convert this using 1
      simp only [map_mul, aeval_C, am, hρ, hDdef]
      field_simp
    · have := hmem N (by omega)
      convert this using 1
      rw [← hRN]; field_simp
    · have := hmem (X * N) ((hdeg N 3 hNd).trans (by norm_num))
      convert this using 1
      rw [map_mul, aeval_X, ← hRN]; field_simp
  have hV : Module.finrank (↥Qbar) V ≤ 5 := by
    refine (Submodule.finrank_map_le φ _).trans (le_of_eq ?_)
    rw [Module.finrank_eq_card_basis (degreeLT.basis (↥Qbar) 5), Fintype.card_fin]
  have hW : Module.finrank (↥Qbar) W = 5 := by
    have := finrank_span_eq_card hind
    rw [show Set.range ![1, u, conj u, g, u * g] = ({1, u, conj u, g, u * g} : Set ℂ) by
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]]
      at this
    rw [hWdef, this, Fintype.card_fin]
  have hWV : W = V := Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [hWV]
  exact hmem M hM

end R17_vis_b

open DiazModulus R17_vis_b Polynomial in
theorem solution
    (u g : ℂ) (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (hind : LinearIndependent (↥Qbar) ![1, u, conj u, g, u * g])
    (R N : (↥Qbar)[X]) (hR : R ≠ 0) (hRd : R.natDegree ≤ 2) (hNd : N.natDegree ≤ 3)
    (hRN : u * aeval u R * g = aeval u N) :
    u ^ 2 ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ) ∨
      conj u ^ 2 ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ) ∨
      ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)
  set ρ : ↥Qbar := ⟨u * conj u, mem_Qbar_iff.2 hρ⟩
  have hρc : (ρ : ℂ) = u * conj u := rfl
  have hR0 : aeval u R ≠ 0 := fun h => hR (aeval_eq_zero hu h)
  have hD : u * aeval u R ≠ 0 := mul_ne_zero hu0 hR0
  have hK := key hu0 ρ hρc hind R N hRd hNd hD hRN
  by_cases h1 : R.natDegree ≤ 1
  · -- `u² = φ(X³ R)`
    left
    have := hK (X ^ 3 * R) (natDegree_mul_le.trans (by rw [natDegree_X_pow]; omega))
    convert this using 1
    simp only [map_mul, map_pow, aeval_X]
    field_simp
  by_cases h0 : R.coeff 0 = 0
  · -- `R = X R₁` and `ū² = φ(ρ² R₁)`
    right; left
    obtain ⟨R₁, hR₁⟩ := X_dvd_iff.2 h0
    have hR₁0 : aeval u R₁ ≠ 0 := by
      intro h; apply hR0; rw [hR₁, map_mul, h, mul_zero]
    have hdeg : R₁.natDegree ≤ 4 :=
      (natDegree_le_of_dvd ⟨X, by rw [hR₁, mul_comm]⟩ hR).trans (by omega)
    have := hK (C (ρ ^ 2) * R₁) ((natDegree_C_mul_le _ _).trans hdeg)
    convert this using 1
    rw [hR₁]
    simp only [map_mul, aeval_X, aeval_C, am, map_pow, hρc]
    field_simp
  · -- a non-zero root `b ∈ Q̄` of `R`: `R = (X − b) R₁` and `(u − b)⁻¹ = φ(X R₁)`
    right; right
    obtain ⟨b, hb⟩ := exists_root (p := R) (by omega)
    have hb0 : b ≠ 0 := by
      rintro rfl; apply h0; rw [coeff_zero_eq_eval_zero]; exact hb
    set R₁ := R /ₘ (X - C b)
    have hR₁ : (X - C b) * R₁ = R := mul_divByMonic_eq_iff_isRoot.2 hb
    have hdeg : (X * R₁).natDegree ≤ 4 := by
      have := natDegree_le_of_dvd ⟨X - C b, by rw [← hR₁, mul_comm]⟩ hR
      exact (natDegree_mul_le.trans (by rw [natDegree_X]; omega))
    refine ⟨b, b.2, fun h => hb0 (Subtype.val_injective (by simpa using h)), ?_⟩
    have hR' : aeval u R = (u - b) * aeval u R₁ := by
      rw [← hR₁, map_mul, map_sub, aeval_X, aeval_C, am]
    have hub : u - (b : ℂ) ≠ 0 := by
      intro h; apply hR0; rw [hR', h, zero_mul]
    have hR₁0 : aeval u R₁ ≠ 0 := by
      intro h; apply hR0; rw [hR', h, mul_zero]
    have := hK (X * R₁) hdeg
    convert this using 1
    rw [map_mul, aeval_X, hR']
    field_simp
