-- Prove2me | solution 1 for DiazModulus.conj_stable_real_pencil_space_carries_two_by_three_configuration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:09:57.740729+00:00
-- url     : https://prove2.me/submissions/4cd75100-2ae2-4e23-bf21-3164275380b4

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A conjugation-stable real-pencil space carries a two-by-three configuration

Let `u ∉ Q̄`, `s ∈ Q̄` real with `s² = u ū`, `λ ∈ Q̄` with `λ λ̄ = 1`, `f` real, and put
`g = f/(s + λu)`, `W = span_Q̄ {1, u, ū, f, g}`, the five numbers being `Q̄`-free.

Non-vanishing: `u ≠ 0`, so `s ≠ 0` (`s² = u ū`), `λ ≠ 0` (`λ λ̄ = 1`), and `s + λu ≠ 0`, since
otherwise `u = −s/λ ∈ Q̄`. From `g (s + λu) = f` we get `u g = λ⁻¹ f − λ⁻¹ s g ∈ W`.
Conjugation: `ū = s²/u`, `λ̄ = 1/λ`, `s̄ = s`, `f̄ = f`, so `ḡ = f/(s + λ̄ ū)` and
`(s + λ̄ ū) λ u = s (s + λu)`, which gives `ḡ = f/s − g ∈ W`. Conjugation is additive and maps
`q • w` to `q̄ • w̄` with `q̄ ∈ Q̄` (it is a `ℚ`-algebra map), so by induction on the span `W̄ ⊆ W`.
Configuration: `x = (1, u)`, `y = (u⁻¹, 1, g)`. The six products are `u⁻¹ = s⁻² ū`, `1`, `g`,
`1`, `u`, `u g`, all in `W`. Freeness of `x` and of `y` comes from the freeness of the five
generators: a relation `a u⁻¹ + b + c g = 0` is the relation `b + a s⁻² ū + c g = 0` among them.
-/

namespace R11_pencilConfig

open DiazModulus

/-- Complex conjugation as a `ℚ`-algebra map. -/
noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

/-- Conjugation maps `Q̄` to itself. -/
theorem conj_mem_Qbar {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar := by
  obtain ⟨p, hp0, hp⟩ := mem_Qbar_iff.1 ha
  refine mem_Qbar_iff.2 ⟨p, hp0, ?_⟩
  rw [show (conj a : ℂ) = cjQ a from rfl, Polynomial.aeval_algHom_apply, hp, map_zero]

theorem span_mul_mem {S : Set ℂ} {c v : ℂ} (hc : c ∈ Qbar) (hv : v ∈ Submodule.span Qbar S) :
    c * v ∈ Submodule.span Qbar S := by
  have := Submodule.smul_mem _ (⟨c, hc⟩ : ↥Qbar) hv
  rwa [Subfield.smul_def, smul_eq_mul] at this

theorem span_mem_of_eq {S : Set ℂ} {v z : ℂ} (h : v = z) (hz : z ∈ Submodule.span Qbar S) :
    v ∈ Submodule.span Qbar S := by
  rwa [h]

/-- A span whose generators have conjugates in it is conjugation-stable. -/
theorem span_conj_stable {S : Set ℂ} (hS : ∀ x ∈ S, conj x ∈ Submodule.span Qbar S) :
    ∀ w ∈ Submodule.span Qbar S, conj w ∈ Submodule.span Qbar S := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have hcx : conj (c • x) = (⟨conj (c : ℂ), conj_mem_Qbar c.2⟩ : ↥Qbar) • conj x :=
      map_mul conj (c : ℂ) x
    rw [hcx]
    exact Submodule.smul_mem _ _ hx

end R11_pencilConfig

open DiazModulus R11_pencilConfig in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u)
    (lam : ℂ) (hlam : lam ∈ Qbar) (hlam1 : lam * conj lam = 1) (f : ℂ) (hf : conj f = f)
    (hind : LinearIndependent (↥Qbar) ![1, u, conj u, f, f / (s + lam * u)]) :
    (∀ w ∈ Submodule.span Qbar ({1, u, conj u, f, f / (s + lam * u)} : Set ℂ), conj w ∈ Submodule.span Qbar ({1, u, conj u, f, f / (s + lam * u)} : Set ℂ)) ∧
      ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, f, f / (s + lam * u)} : Set ℂ) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hcu0 : conj u ≠ 0 := (map_ne_zero _).2 hu0
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hu0 hcu0 (by rw [← hss]; ring)
  have hlam0 : lam ≠ 0 := by rintro rfl; simp at hlam1
  have hD : s + lam * u ≠ 0 := by
    intro h
    apply hu
    have : u = -s / lam := by rw [eq_div_iff hlam0]; linear_combination h
    rw [this]; exact div_mem (neg_mem hs) hlam
  set g := f / (s + lam * u) with hg
  set W := Submodule.span Qbar ({1, u, conj u, f, g} : Set ℂ) with hW
  have m1 : (1 : ℂ) ∈ W := Submodule.subset_span (by simp)
  have mu : u ∈ W := Submodule.subset_span (by simp)
  have mcu : conj u ∈ W := Submodule.subset_span (by simp)
  have mf : f ∈ W := Submodule.subset_span (by simp)
  have mg : g ∈ W := Submodule.subset_span (by simp)
  have hgD : g * (s + lam * u) = f := div_mul_cancel₀ f hD
  have hli : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam0
  have hug : u * g = lam⁻¹ * f + (-(lam⁻¹ * s)) * g := by
    linear_combination lam⁻¹ * hgD - u * g * hli
  have mug : u * g ∈ W := span_mem_of_eq hug (Submodule.add_mem _ (span_mul_mem (inv_mem hlam) mf)
    (span_mul_mem (neg_mem (mul_mem (inv_mem hlam) hs)) mg))
  -- the conjugate of `g`
  have hD'id : (s + conj lam * conj u) * (lam * u) = s * (s + lam * u) := by
    linear_combination (u * conj u) * hlam1 - hss
  have hD' : s + conj lam * conj u ≠ 0 := by
    intro h
    rw [h, zero_mul] at hD'id
    exact mul_ne_zero hs0 hD hD'id.symm
  have hcg : conj g = s⁻¹ * f + (-1) * g := by
    have h1 : conj g = f / (s + conj lam * conj u) := by
      rw [hg, map_div₀, hf, map_add, map_mul, hsr]
    have hsi : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
    rw [h1, div_eq_iff hD', ← mul_right_inj' (mul_ne_zero hlam0 hu0)]
    linear_combination (-(s⁻¹ * f) + g) * hD'id + s * hgD - f * (s + lam * u) * hsi
  have mcg : conj g ∈ W := span_mem_of_eq hcg (Submodule.add_mem _
    (span_mul_mem (inv_mem hs) mf) (span_mul_mem (neg_mem (one_mem _)) mg))
  refine ⟨span_conj_stable ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · rw [map_one]; exact m1
    · exact mcu
    · rw [conj_conj]; exact mu
    · rw [hf]; exact mf
    · exact mcg
  -- the configuration
  have hinv : u⁻¹ = s⁻¹ * s⁻¹ * conj u := by
    field_simp
    linear_combination hss
  have minv : u⁻¹ ∈ W := span_mem_of_eq hinv
    (span_mul_mem (mul_mem (inv_mem hs) (inv_mem hs)) mcu)
  have hind' := Fintype.linearIndependent_iff.1 hind
  refine ⟨![1, u], ![u⁻¹, 1, g], ?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have := hind' ![c 0, c 1, 0, 0, 0] (by
      simp only [Fin.sum_univ_two] at hc
      simpa [Fin.sum_univ_five] using hc)
    intro i
    fin_cases i
    · exact this 0
    · exact this 1
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    set σ : ↥Qbar := ⟨s, hs⟩
    have := hind' ![c 1, 0, c 0 * σ⁻¹ * σ⁻¹, 0, c 2] (by
      simp only [Fin.sum_univ_three, Subfield.smul_def, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
      simp only [Fin.sum_univ_five, Subfield.smul_def, smul_eq_mul]
      simp [σ]
      linear_combination hc - (c 0 : ℂ) * hinv)
    have e0 := this 0
    have e2 := this 2
    have e4 := this 4
    simp at e0 e2 e4
    intro i
    fin_cases i
    · refine e2.resolve_right fun h => hs0 ?_
      simpa [σ] using congrArg Subtype.val h
    · exact e0
    · exact e4
  · intro i j
    fin_cases i <;> fin_cases j
    · simpa using minv
    · simpa using m1
    · simpa using mg
    · simpa [hu0] using m1
    · simpa using mu
    · simpa using mug
