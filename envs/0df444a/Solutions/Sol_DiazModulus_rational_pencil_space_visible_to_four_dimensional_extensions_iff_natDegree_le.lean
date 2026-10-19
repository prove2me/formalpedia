-- Prove2me | solution 1 for DiazModulus.rational_pencil_space_visible_to_four_dimensional_extensions_iff_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T09:45:55.907111+00:00
-- url     : https://prove2.me/submissions/37b50aa2-d4e7-49b4-8f08-2872268df809

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_rational_degree_one_space_visible_to_four_dimensional_extensions_iff_natDegree_le

open Complex ComplexConjugate

/-! # Pencil spaces with rational f: the visibility criterion

Let `u ∉ Q̄`, `s ∈ Q̄` with `s² = u ū`, `λ ∈ Q̄` with `λ λ̄ = 1`, `f = P(u)/Q(u)` with `P, Q ∈ Q̄[X]`
coprime, and `g = f/(s + λu)`, with `1, u, ū, f, g` free over `Q̄`.

* `λ ≠ 0`, `λ̄ = λ⁻¹`, and `s ≠ 0` because `s² = u ū ≠ 0`. Put `a₀ = −s λ̄ ∈ Q̄ \ {0}`; then
  `s + λu = λ(u − a₀) ≠ 0`, and `f = s g + λ·ug`.
* Hence `span(1, u, ū, f, g) = span(1, u, ū, g, ug)` (`ug = λ⁻¹ f − λ⁻¹ s g`), and `1, u, ū, g, ug`
  are free: a relation among them becomes one among `1, u, ū, f, g`.
* Write `g` as a reduced fraction. If `P(a₀) ≠ 0`, `g = P(u)/Q̃(u)` with `Q̃ = λ·Q·(X − a₀)`, coprime to
  `P` (`X − a₀` is irreducible and does not divide `P`), `deg Q̃ = deg Q + 1`, and `Q̃(0) = 0` exactly
  when `Q(0) = 0`. If `P(a₀) = 0`, `P = (X − a₀) P₁` and `g = λ⁻¹ P₁(u)/Q(u)`, coprime, with
  `deg P₁ = deg P − 1` (`P ≠ 0`, since `f ≠ 0`).
* `rational_degree_one_space_visible_to_four_dimensional_extensions_iff_natDegree_le` applied to that
  fraction gives `max(deg P, deg Q + 1) ≤ 2 + [Q(0) = 0] + [P(a₀) = 0]` in both cases.
-/

namespace R17_vis3

open DiazModulus Polynomial

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem aeval_ne_zero {u : ℂ} (hu : u ∉ Qbar) {Q : (↥Qbar)[X]} (hQ : Q ≠ 0) : aeval u Q ≠ 0 :=
  fun h => hQ (transcendental_iff.1 (tr_of_not_mem hu) Q h)

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem smul_mem' {S : Set ℂ} (c : ↥Qbar) {v : ℂ} (hv : v ∈ Submodule.span Qbar S) :
    (c : ℂ) * v ∈ Submodule.span Qbar S :=
  Submodule.smul_mem _ c hv

/-- `span(1, u, ū, f, g) = span(1, u, ū, g, ug)` when `f = σ g + ℓ ug`, `ℓ ≠ 0`. -/
theorem span_eq {u cu f G : ℂ} {σ ℓ : ↥Qbar} (hℓ : ℓ ≠ 0) (hf : f = σ * G + ℓ * (u * G)) :
    Submodule.span Qbar ({1, u, cu, f, G} : Set ℂ) =
      Submodule.span Qbar ({1, u, cu, G, u * G} : Set ℂ) := by
  have hℓc : (ℓ : ℂ) ≠ 0 := fun e => hℓ (Subtype.ext e)
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨Submodule.subset_span (by simp), Submodule.subset_span (by simp),
      Submodule.subset_span (by simp), ?_, Submodule.subset_span (by simp)⟩
    rw [hf]
    exact Submodule.add_mem _ (smul_mem' σ (Submodule.subset_span (by simp)))
      (smul_mem' ℓ (Submodule.subset_span (by simp)))
  · refine Submodule.span_le.2 ?_
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨Submodule.subset_span (by simp), Submodule.subset_span (by simp),
      Submodule.subset_span (by simp), Submodule.subset_span (by simp), ?_⟩
    have e : u * G = ((ℓ⁻¹ : ↥Qbar) : ℂ) * f + ((-(ℓ⁻¹ * σ) : ↥Qbar) : ℂ) * G := by
      rw [hf]; push_cast; field_simp; ring
    rw [e]
    exact Submodule.add_mem _ (smul_mem' _ (Submodule.subset_span (by simp)))
      (smul_mem' _ (Submodule.subset_span (by simp)))

/-- Freeness passes from `1, u, ū, f, g` to `1, u, ū, g, ug`. -/
theorem indep {u cu f G : ℂ} {σ ℓ : ↥Qbar} (hℓ : ℓ ≠ 0) (hf : f = σ * G + ℓ * (u * G))
    (hind : LinearIndependent (↥Qbar) ![1, u, cu, f, G]) :
    LinearIndependent (↥Qbar) ![1, u, cu, G, u * G] := by
  have hℓc : (ℓ : ℂ) ≠ 0 := fun e => hℓ (Subtype.ext e)
  rw [Fintype.linearIndependent_iff] at hind ⊢
  intro c hc
  simp [Fin.sum_univ_five, Subfield.smul_def] at hc
  have h := hind ![c 0, c 1, c 2, c 4 * ℓ⁻¹, c 3 - c 4 * ℓ⁻¹ * σ] (by
    simp [Fin.sum_univ_five, Subfield.smul_def]
    linear_combination hc + ((c 4 : ℂ) * (ℓ : ℂ)⁻¹) * hf +
      ((c 4 : ℂ) * u * G) * (inv_mul_cancel₀ hℓc))
  have h4 : c 4 = 0 := by simpa [hℓ] using h 3
  have h3 : c 3 = 0 := by simpa [h4] using h 4
  intro i
  fin_cases i
  · simpa using h 0
  · simpa using h 1
  · simpa using h 2
  · exact h3
  · exact h4

end R17_vis3

open DiazModulus R17_vis3 Polynomial in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (lam : ℂ) (hlam : lam ∈ Qbar) (hlam1 : lam * conj lam = 1)
    (P Q : (↥Qbar)[X]) (hcop : IsCoprime P Q)
    (hind : LinearIndependent (↥Qbar) ![1, u, conj u, aeval u P / aeval u Q, aeval u P / aeval u Q / (s + lam * u)]) :
    (∃ w ∈ Submodule.span Qbar ({1, u, conj u, aeval u P / aeval u Q, aeval u P / aeval u Q / (s + lam * u)} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) ∧
        ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ)) ↔
      max P.natDegree (Q.natDegree + 1) ≤
        2 + (if Q.coeff 0 = 0 then 1 else 0) + (if aeval (-(s * conj lam)) P = 0 then 1 else 0) := by
  -- basic facts
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hρ : IsAlgebraic ℚ (u * conj u) := mem_Qbar_iff.1 (by rw [← hss]; exact mul_mem hs hs)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hu0 ((_root_.map_ne_zero _).2 hu0) (by rw [← hss]; ring)
  have hlam0 : lam ≠ 0 := by rintro rfl; simp at hlam1
  have hclam : conj lam = lam⁻¹ := eq_inv_of_mul_eq_one_right hlam1
  have hQ : Q ≠ 0 := by rintro rfl; exact hind.ne_zero 3 (by simp)
  have hP : P ≠ 0 := by rintro rfl; exact hind.ne_zero 3 (by simp)
  have hQu := aeval_ne_zero hu hQ
  set ℓ : ↥Qbar := ⟨lam, hlam⟩ with hℓdef
  set σ : ↥Qbar := ⟨s, hs⟩ with hσdef
  have hℓ0 : ℓ ≠ 0 := fun e => hlam0 (congrArg Subtype.val e)
  set α₀ : ↥Qbar := ⟨-(s * conj lam), by rw [hclam]; exact neg_mem (mul_mem hs (inv_mem hlam))⟩
    with hα₀def
  have hα₀c : (α₀ : ℂ) = -(s * conj lam) := rfl
  have hα0 : α₀ ≠ 0 := fun e => by
    have : -(s * conj lam) = 0 := by rw [← hα₀c, e]; rfl
    rw [hclam, neg_eq_zero] at this
    exact mul_ne_zero hs0 (inv_ne_zero hlam0) this
  have hkey : lam * (u - α₀) = s + lam * u := by rw [hα₀c]; linear_combination s * hlam1
  have hua : u - α₀ ≠ 0 := sub_ne_zero.2 fun e => hu (e ▸ α₀.2)
  have hden : s + lam * u ≠ 0 := by rw [← hkey]; exact mul_ne_zero hlam0 hua
  have hfG : aeval u P / aeval u Q = (σ : ℂ) * (aeval u P / aeval u Q / (s + lam * u)) +
      (ℓ : ℂ) * (u * (aeval u P / aeval u Q / (s + lam * u))) := by
    simp only [hσdef, hℓdef]
    field_simp
  have hroot : aeval (-(s * conj lam)) P = 0 ↔ P.IsRoot α₀ := by
    rw [← hα₀c, ← am α₀, aeval_algebraMap_apply_eq_algebraMap_eval, am, IsRoot.def]
    exact ZeroMemClass.coe_eq_zero
  rw [span_eq hℓ0 hfG]
  by_cases hP0 : aeval (-(s * conj lam)) P = 0
  · -- `P = (X − a₀) P₁`, and `g = λ⁻¹ P₁(u) / Q(u)`
    have hR := hroot.1 hP0
    set P₁ := P /ₘ (X - C α₀) with hP₁def
    have hPP : (X - C α₀) * P₁ = P := mul_divByMonic_eq_iff_isRoot.2 hR
    have hP₁ : P₁ ≠ 0 := by rintro h; rw [h, mul_zero] at hPP; exact hP hPP.symm
    have hcop' : IsCoprime (C ℓ⁻¹ * P₁) Q := by
      rw [isCoprime_mul_unit_left_left (isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero hℓ0)))]
      rw [← hPP] at hcop
      exact hcop.of_mul_left_right
    have hg : aeval u (C ℓ⁻¹ * P₁) / aeval u Q = aeval u P / aeval u Q / (s + lam * u) := by
      rw [← hPP, ← hkey]
      simp only [map_mul, map_sub, aeval_C, aeval_X, am, Subfield.coe_inv, hℓdef]
      field_simp
    have hdeg : P.natDegree = P₁.natDegree + 1 := by
      rw [← hPP, natDegree_mul (X_sub_C_ne_zero _) hP₁, natDegree_X_sub_C, add_comm]
    rw [← hg, DiazModulus.rational_degree_one_space_visible_to_four_dimensional_extensions_iff_natDegree_le
      u hu hρ _ _ hcop' (by rw [hg]; exact indep hℓ0 hfG hind),
      natDegree_C_mul (inv_ne_zero hℓ0), hdeg, if_pos hP0, max_le_iff, max_le_iff]
    split_ifs <;> omega
  · -- `g = P(u) / Q̃(u)` with `Q̃ = λ Q (X − a₀)`
    have hR : ¬ P.IsRoot α₀ := fun h => hP0 (hroot.2 h)
    have hcop' : IsCoprime P (C ℓ * (Q * (X - C α₀))) := by
      rw [isCoprime_mul_unit_left_right (isUnit_C.2 (isUnit_iff_ne_zero.2 hℓ0))]
      refine hcop.mul_right ((irreducible_X_sub_C α₀).coprime_iff_not_dvd.2 ?_).symm
      rwa [dvd_iff_isRoot]
    have hg : aeval u P / aeval u (C ℓ * (Q * (X - C α₀))) =
        aeval u P / aeval u Q / (s + lam * u) := by
      rw [← hkey]
      simp only [map_mul, map_sub, aeval_C, aeval_X, am, hℓdef]
      rw [div_div]
      ring
    have hdeg : (C ℓ * (Q * (X - C α₀))).natDegree = Q.natDegree + 1 := by
      rw [natDegree_C_mul hℓ0, natDegree_mul hQ (X_sub_C_ne_zero _), natDegree_X_sub_C]
    have hco : (C ℓ * (Q * (X - C α₀))).coeff 0 = 0 ↔ Q.coeff 0 = 0 := by
      rw [coeff_C_mul, mul_coeff_zero]
      simp [hℓ0, hα0]
    rw [← hg, DiazModulus.rational_degree_one_space_visible_to_four_dimensional_extensions_iff_natDegree_le
      u hu hρ _ _ hcop' (by rw [hg]; exact indep hℓ0 hfG hind), hdeg, if_neg hP0, add_zero]
    simp only [hco]
