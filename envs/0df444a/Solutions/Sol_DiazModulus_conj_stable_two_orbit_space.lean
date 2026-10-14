-- Prove2me | solution 1 for DiazModulus.conj_stable_two_orbit_space
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T07:31:21.258476+00:00
-- url     : https://prove2.me/submissions/6a182292-a6c5-4720-9650-29ad33ac1787

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The two-orbit space is conjugation-stable

Let `u ∉ Q̄`, `s ∈ Q̄` real with `s² = u ū`, and `a, b, α, β, γ, δ ∈ Q̄` non-zero with
`a ā = b b̄ = s²`, `β ᾱ = β̄ α`, `δ γ̄ = δ̄ γ`. Put `g₁ = α/(u − a) + β/(u + a)`,
`g₂ = γ/(u − b) + δ/(u + b)`, `W = span_Q̄ {1, u, u⁻¹, g₁, g₂}`. Then `W̄ = W`.

Since `u ≠ 0`, also `s ≠ 0`, and `ū = s²/u`, `ā = s²/a`, `β̄ = β ᾱ/α`. Hence `ū = s² u⁻¹`,
`conj u⁻¹ = s⁻² u`, and substituting into `ḡ₁ = ᾱ/(ū − ā) + β̄/(ū + ā)` gives the rational
identity (`conj_pair`) `ḡ₁ = a(β̄ − ᾱ)/s² − (a²ᾱ/(s²α)) g₁`: the two poles `±a` go to themselves,
and the reality condition `β ᾱ = β̄ α` makes the resulting residues proportional to `(α, β)`. The same
holds for `g₂`. All coefficients lie in `Q̄`, as conjugation maps `Q̄` to itself (it is a
`ℚ`-algebra map). Conjugation is additive and maps `q • w` to `q̄ • w̄`, so by induction on the
span, conjugates of all of `W` stay in `W`.
-/

namespace R14_orbitConj

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

/-- The conjugate of one pole pair `α/(u − a) + β/(u + a)` with `a ā = s² = u ū` and
`β ᾱ = β̄ α`. -/
theorem conj_pair {u s a α β : ℂ} (hu0 : u ≠ 0) (ha0 : a ≠ 0) (hα0 : α ≠ 0)
    (hua : u - a ≠ 0) (hua' : u + a ≠ 0) (hss : s * s = u * conj u) (haa : a * conj a = s * s)
    (hαβ : β * conj α = conj β * α) :
    conj (α / (u - a) + β / (u + a)) = a * (conj β - conj α) / (s * s) +
      (-(a * a * conj α / (s * s * α))) * (α / (u - a) + β / (u + a)) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hu0 ((map_ne_zero _).2 hu0) (by rw [← hss]; ring)
  have hU : conj u = s * s / u := by rw [eq_div_iff hu0]; linear_combination -hss
  have hA : conj a = s * s / a := by rw [eq_div_iff ha0]; linear_combination haa
  have hB : conj β = β * conj α / α := by rw [eq_div_iff hα0]; linear_combination -hαβ
  rw [map_add, map_div₀, map_div₀, map_sub, map_add, hU, hA, hB]
  have e1 : s * s / u - s * s / a = s * s * (a - u) / (u * a) := by field_simp
  have e2 : s * s / u + s * s / a = s * s * (a + u) / (u * a) := by field_simp
  rw [e1, e2]
  have hau : a - u ≠ 0 := fun h => hua (by linear_combination -h)
  have hau' : a + u ≠ 0 := fun h => hua' (by linear_combination h)
  field_simp
  ring

theorem sub_ne {u x : ℂ} (hu : u ∉ Qbar) (hx : x ∈ Qbar) : u - x ≠ 0 :=
  fun h => hu (by rw [sub_eq_zero.1 h]; exact hx)

theorem add_ne {u x : ℂ} (hu : u ∉ Qbar) (hx : x ∈ Qbar) : u + x ≠ 0 := by
  rw [← sub_neg_eq_add]; exact sub_ne hu (neg_mem hx)

end R14_orbitConj

open DiazModulus R14_orbitConj in
theorem solution
    (u : ℂ) (hu : u ∉ Qbar) (a b α β γ δ : ℂ) (ha : a ∈ Qbar) (hb : b ∈ Qbar) (hα : α ∈ Qbar) (hβ : β ∈ Qbar)
    (hγ : γ ∈ Qbar) (hδ : δ ∈ Qbar) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ^ 2 ≠ b ^ 2)
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (hγ0 : γ ≠ 0) (hδ0 : δ ≠ 0)
    (s : ℂ) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u)
    (haa : a * conj a = s * s) (hbb : b * conj b = s * s)
    (hαβ : β * conj α = conj β * α) (hγδ : δ * conj γ = conj δ * γ) :
    ∀ w ∈ Submodule.span Qbar ({1, u, u⁻¹, (α / (u - a) + β / (u + a)), (γ / (u - b) + δ / (u + b))} : Set ℂ), conj w ∈ Submodule.span Qbar ({1, u, u⁻¹, (α / (u - a) + β / (u + a)), (γ / (u - b) + δ / (u + b))} : Set ℂ) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hu0 ((map_ne_zero _).2 hu0) (by rw [← hss]; ring)
  set W := Submodule.span Qbar ({1, u, u⁻¹, (α / (u - a) + β / (u + a)),
    (γ / (u - b) + δ / (u + b))} : Set ℂ) with hW
  have m1 : (1 : ℂ) ∈ W := Submodule.subset_span (by simp)
  have mu : u ∈ W := Submodule.subset_span (by simp)
  have mi : u⁻¹ ∈ W := Submodule.subset_span (by simp)
  have mg₁ : α / (u - a) + β / (u + a) ∈ W := Submodule.subset_span (by simp)
  have mg₂ : γ / (u - b) + δ / (u + b) ∈ W := Submodule.subset_span (by simp)
  have hss' := mul_mem hs hs
  have cα := conj_mem_Qbar hα
  have cγ := conj_mem_Qbar hγ
  refine span_conj_stable ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · rw [map_one]; exact m1
  · -- `ū = s² u⁻¹`
    refine span_mem_of_eq ?_ (span_mul_mem hss' mi)
    field_simp
    linear_combination -hss
  · -- `conj u⁻¹ = s⁻² u`
    refine span_mem_of_eq ?_ (span_mul_mem (inv_mem hss') mu)
    have hcu0 : conj u ≠ 0 := (map_ne_zero _).2 hu0
    rw [map_inv₀]
    field_simp
    linear_combination hss
  · rw [conj_pair hu0 ha0 hα0 (sub_ne hu ha) (add_ne hu ha) hss haa hαβ]
    exact Submodule.add_mem _ (span_mem_of_eq (mul_one _).symm (span_mul_mem
        (div_mem (mul_mem ha (sub_mem (conj_mem_Qbar hβ) cα)) hss') m1))
      (span_mul_mem (neg_mem (div_mem (mul_mem (mul_mem ha ha) cα) (mul_mem hss' hα))) mg₁)
  · rw [conj_pair hu0 hb0 hγ0 (sub_ne hu hb) (add_ne hu hb) hss hbb hγδ]
    exact Submodule.add_mem _ (span_mem_of_eq (mul_one _).symm (span_mul_mem
        (div_mem (mul_mem hb (sub_mem (conj_mem_Qbar hδ) cγ)) hss') m1))
      (span_mul_mem (neg_mem (div_mem (mul_mem (mul_mem hb hb) cγ) (mul_mem hss' hγ))) mg₂)
