-- Prove2me | solution 1 for DiazModulus.visible_to_four_dimensional_extensions_iff_visible_element_mem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:28:05.093194+00:00
-- url     : https://prove2.me/submissions/425710e0-1817-4179-a2f9-bee2398bed35

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_circle_point_extension_two_by_three_configuration_iff

open Complex ComplexConjugate

/-! # Visibility to four-dimensional extensions is membership of a `t_x`

Let `u ∉ Q̄` with `ρ = u ū ∈ Q̄`, and `H₀ = span(1, u, u⁻¹) ≤ W`. As `ū = ρ u⁻¹` with `ρ ≠ 0`,
`span(1, u, ū) = H₀` and `span(1, u, ū, z) = span(1, u, u⁻¹, z)` for every `z`; also `ū² = ρ² u⁻²`.
So `circle_point_extension_two_by_three_configuration_iff` (10.6) reads: for `z ∉ H₀`, the space
`H₀ + Q̄z` carries a configuration iff `z ∈ H₀ + Q̄t` for some `t ∈ {u², u⁻², (u − a)⁻¹ : a ∈ Q̄ ∖ 0}`.
* `⇒`: `w ∈ W ∖ H₀` has a configuration, so `w ∈ H₀ + Q̄t`; as `w ∉ H₀` the coefficient of `t` is
  non-zero, and `t ∈ W` by exchange.
* `⇐`: take `w = t`. Each `t` is outside `H₀` (clear denominators; `u` is transcendental), and
  `t ∈ H₀ + Q̄t`, so 10.6's "if" gives the configuration.
-/

namespace R21b_V0

open DiazModulus Polynomial

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem smul_def' (c : ↥Qbar) (z : ℂ) : c • z = (c : ℂ) * z := rfl

/-- `1, u, u², u³` are free over `Q̄`. -/
theorem cubic {u : ℂ} (hu : u ∉ Qbar) (a₀ a₁ a₂ a₃ : ↥Qbar)
    (h : (a₀ : ℂ) + a₁ * u + a₂ * u ^ 2 + a₃ * u ^ 3 = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 := by
  have hP := transcendental_iff.1 (tr_of_not_mem hu) (C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3)
    (by simpa only [map_add, map_mul, map_pow, aeval_C, aeval_X, am] using h)
  exact ⟨by simpa using congrArg (coeff · 0) hP, by simpa using congrArg (coeff · 1) hP,
    by simpa using congrArg (coeff · 2) hP, by simpa using congrArg (coeff · 3) hP⟩

theorem H_coeffs {u w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ)) :
    ∃ a b c : ↥Qbar, w = (a : ℂ) + b * u + c * u⁻¹ := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hw
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, rfl⟩ := Submodule.mem_span_singleton.1 hw₂
  exact ⟨c₁, c₂, c₃, by simp only [smul_def']; ring⟩

theorem le3 {V : Submodule (↥Qbar) ℂ} {a b c : ℂ} (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) :
    Submodule.span Qbar ({a, b, c} : Set ℂ) ≤ V :=
  Submodule.span_le.2 (by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]; exact ⟨ha, hb, hc⟩)

theorem le4 {V : Submodule (↥Qbar) ℂ} {a b c d : ℂ} (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V)
    (hd : d ∈ V) : Submodule.span Qbar ({a, b, c, d} : Set ℂ) ≤ V :=
  Submodule.span_le.2 (by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨ha, hb, hc, hd⟩)

/-- Exchange: `w ∈ (H₀ + Q̄t) ∖ H₀` and `H₀ + Q̄w ≤ W` give `t ∈ W`. -/
theorem exch {W : Submodule (↥Qbar) ℂ} {u w t : ℂ}
    (hH : Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ≤ W) (hw : w ∈ W)
    (hwH : w ∉ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ))
    (h : w ∈ Submodule.span Qbar ({1, u, u⁻¹, t} : Set ℂ)) : t ∈ W := by
  have e : ({1, u, u⁻¹, t} : Set ℂ) = {1, u, u⁻¹} ∪ {t} := by ext; simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]; tauto
  rw [e, Submodule.span_union, Submodule.mem_sup] at h
  obtain ⟨h₀, hh₀, z, hz, rfl⟩ := h
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
  by_cases hc : c = 0
  · exact absurd (by simpa [hc] using hh₀) hwH
  · have e' : t = c⁻¹ • ((h₀ + c • t) - h₀) := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [e']
    exact W.smul_mem _ (W.sub_mem hw (hH hh₀))

end R21b_V0

open DiazModulus R21b_V0 in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (W : Submodule (↥Qbar) ℂ) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W) :
    (∃ w ∈ W, w ∉ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ∧
        ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, u⁻¹, w} : Set ℂ)) ↔
    (u ^ 2 ∈ W ∨ (u ^ 2)⁻¹ ∈ W ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ W) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)
  set ρ : ↥Qbar := ⟨u * conj u, mem_Qbar_iff.2 hρ⟩
  have hρ0 : (ρ : ℂ) ≠ 0 := mul_ne_zero hu0 ((map_ne_zero _).2 hu0)
  have hconj : conj u = ρ • u⁻¹ := by
    rw [smul_def']; field_simp; show conj u * u = u * conj u; ring
  have hconj2 : conj u ^ 2 = (ρ ^ 2 : ↥Qbar) • (u ^ 2)⁻¹ := by
    rw [smul_def', hconj, smul_def']; push_cast; field_simp
  have hinv2 : (u ^ 2)⁻¹ = (ρ ^ 2 : ↥Qbar)⁻¹ • conj u ^ 2 := by
    rw [hconj2, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (fun h => hρ0 (by rw [h]; rfl))), one_smul]
  have hui' : u⁻¹ = ρ⁻¹ • conj u := by
    rw [hconj, smul_smul, inv_mul_cancel₀ (fun h => hρ0 (by rw [h]; rfl)), one_smul]
  have sub : ∀ {s : Set ℂ} {x : ℂ}, x ∈ s → x ∈ Submodule.span Qbar s :=
    fun hx => Submodule.subset_span hx
  have hH : Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ≤ W := le3 h1 hu1 hui
  have e0 : Submodule.span Qbar ({1, u, conj u} : Set ℂ) = Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) :=
    le_antisymm (le3 (sub (by simp)) (sub (by simp)) (by rw [hconj]; exact Submodule.smul_mem _ _ (sub (by simp))))
      (le3 (sub (by simp)) (sub (by simp)) (by rw [hui']; exact Submodule.smul_mem _ _ (sub (by simp))))
  have e1 : ∀ z, Submodule.span Qbar ({1, u, conj u, z} : Set ℂ) =
      Submodule.span Qbar ({1, u, u⁻¹, z} : Set ℂ) := fun z =>
    le_antisymm (le4 (sub (by simp)) (sub (by simp))
        (by rw [hconj]; exact Submodule.smul_mem _ _ (sub (by simp))) (sub (by simp)))
      (le4 (sub (by simp)) (sub (by simp))
        (by rw [hui']; exact Submodule.smul_mem _ _ (sub (by simp))) (sub (by simp)))
  have hsq : u ^ 2 ∉ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) := fun h => by
    obtain ⟨a, b, c, e⟩ := H_coeffs h
    have := (cubic hu c a b (-1) (by field_simp at e; push_cast; linear_combination -e)).2.2.2
    exact one_ne_zero (neg_eq_zero.1 this)
  have hisq : (u ^ 2)⁻¹ ∉ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) := fun h => by
    obtain ⟨a, b, c, e⟩ := H_coeffs h
    have := (cubic hu (-1) c a b (by field_simp at e; push_cast; linear_combination -e)).1
    exact one_ne_zero (neg_eq_zero.1 this)
  have hpole : ∀ x : ↥Qbar, (x : ℂ) ≠ 0 → (u - x)⁻¹ ∉ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) :=
    fun x hx h => by
    have hux : u - x ≠ 0 := fun h' => hu (by rw [sub_eq_zero.1 h']; exact x.2)
    obtain ⟨a, b, c, e⟩ := H_coeffs h
    obtain ⟨h0, h1, h2, h3⟩ := cubic hu (-x * c) (c - x * a - 1) (a - x * b) b
      (by field_simp at e; push_cast; linear_combination -e)
    subst h3
    have ha : a = 0 := by simpa using h2
    subst ha
    have hc : c = 1 := by linear_combination (by simpa using h1 : c - 1 = 0)
    subst hc
    exact hx (by simpa using h0)
  constructor
  · rintro ⟨w, hw, hwH, x, y, hx, hy, hxy⟩
    have hz : w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) := by rwa [e0]
    rcases (circle_point_extension_two_by_three_configuration_iff u w hu hρ hz).1
      ⟨x, y, hx, hy, fun i j => by rw [e1]; exact hxy i j⟩ with h | h | ⟨a, ha, ha0, h⟩
    · exact Or.inl (exch hH hw hwH (by rwa [e1] at h))
    · refine Or.inr (Or.inl (exch hH hw hwH (le4 (sub (by simp)) (sub (by simp))
        (by rw [hconj]; exact Submodule.smul_mem _ _ (sub (by simp)))
        (by rw [hconj2]; exact Submodule.smul_mem _ _ (sub (by simp))) h)))
    · exact Or.inr (Or.inr ⟨a, ha, ha0, exch hH hw hwH (by rwa [e1] at h)⟩)
  · intro hPT
    obtain ⟨t, htW, htH, ht⟩ : ∃ t ∈ W, t ∉ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ∧
        (t ∈ Submodule.span Qbar ({1, u, conj u, u ^ 2} : Set ℂ) ∨
          t ∈ Submodule.span Qbar ({1, u, conj u, conj u ^ 2} : Set ℂ) ∨
          ∃ a ∈ Qbar, a ≠ 0 ∧ t ∈ Submodule.span Qbar ({1, u, conj u, (u - a)⁻¹} : Set ℂ)) := by
      rcases hPT with h | h | ⟨a, ha, ha0, h⟩
      · exact ⟨_, h, hsq, Or.inl (sub (by simp))⟩
      · exact ⟨_, h, hisq, Or.inr (Or.inl (by rw [hinv2]; exact Submodule.smul_mem _ _ (sub (by simp))))⟩
      · exact ⟨_, h, hpole ⟨a, ha⟩ ha0, Or.inr (Or.inr ⟨a, ha, ha0, sub (by simp)⟩)⟩
    obtain ⟨x, y, hx, hy, hxy⟩ :=
      (circle_point_extension_two_by_three_configuration_iff u t hu hρ (by rwa [e0])).2 ht
    exact ⟨t, htW, htH, x, y, hx, hy, fun i j => by rw [← e1]; exact hxy i j⟩
