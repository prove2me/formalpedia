-- Prove2me | solution 1 for DiazModulus.laurent_real_pencil_space_contains_square_of_root
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T07:31:32.115566+00:00
-- url     : https://prove2.me/submissions/596885da-764d-4deb-9376-f28e6f569db1

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A width-two real pencil space vanishing at the pole contains both squares

Let `u ∉ Q̄`, `s ∈ Q̄` real with `s² = u ū`, `λλ̄ = 1`, `v = u/s`, `w = v⁻¹ = s/u`, so `u = sv`,
`ū = sw`. Take `f = Σ_{|j| ≤ 2} c_j v^j = c₋₂w² + c₋₁w + c₀ + c₁v + c₂v²` and `g = f/(s + λu)`.
The hypothesis `f(−λ̄) = 0`, multiplied by `λ²` (with `λ̄ = λ⁻¹`), reads
`c₂ − λc₁ + λ²c₀ − λ³c₋₁ + λ⁴c₋₂ = 0`. It is exactly the condition for synthetic division of
`v²f` by `1 + λv` to leave no remainder:
`f = (1 + λv)(c₋₂w² + q₋₁w + q₀ + q₁v)` with `q₋₁ = c₋₁ − λc₋₂`, `q₀ = c₀ − λq₋₁`,
`q₁ = c₁ − λq₀`. As `s + λu = s(1 + λv) ≠ 0`, this gives `sg = c₋₂w² + q₋₁w + q₀ + q₁v`.
Hence `c₋₂ū² = s²·c₋₂w² = s³g − sq₋₁ū − s²q₀ − sq₁u` and
`c₂u² = s²·c₂v² = s²f − s³g + s(q₋₁ − c₋₁)ū + s²(q₀ − c₀) + s(q₁ − c₁)u`, both in
`W = span_Q̄ {1, u, ū, f, g}`. Since `c₂ ≠ 0` and `c₋₂ = c̄₂ ≠ 0`, `u²` and `ū²` lie in `W`.
-/

namespace R14_laurentSquare

open DiazModulus

theorem sum_Icc_two (F : ℤ → ℂ) :
    ∑ j ∈ Finset.Icc (-2 : ℤ) 2, F j = F (-2) + F (-1) + F 0 + F 1 + F 2 := by
  have : Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [this]
  simp [Finset.sum_insert]
  ring

theorem mem5 {x₂ x₃ x₄ x₅ : ℂ} (a₁ a₂ a₃ a₄ a₅ : ↥Qbar) :
    (a₁ : ℂ) + a₂ * x₂ + a₃ * x₃ + a₄ * x₄ + a₅ * x₅ ∈
      Submodule.span Qbar ({1, x₂, x₃, x₄, x₅} : Set ℂ) := by
  have h : ∀ (a : ↥Qbar) (x : ℂ), x ∈ ({1, x₂, x₃, x₄, x₅} : Set ℂ) →
      (a : ℂ) * x ∈ Submodule.span Qbar ({1, x₂, x₃, x₄, x₅} : Set ℂ) :=
    fun a x hx => Submodule.smul_mem _ a (Submodule.subset_span hx)
  have h1 := h a₁ 1 (by simp)
  rw [mul_one] at h1
  exact add_mem (add_mem (add_mem (add_mem h1 (h a₂ _ (by simp))) (h a₃ _ (by simp)))
    (h a₄ _ (by simp))) (h a₅ _ (by simp))

/-- The two identities, for abstract `u, ū, v, w, f, g`. -/
theorem key {s u cu v w f g ℓ m2 m1 c0 c1 c2 : ℂ} (hD : s + ℓ * u ≠ 0)
    (hu : u = s * v) (hcu : cu = s * w) (hvw : v * w = 1)
    (hf : f = m2 * w ^ 2 + m1 * w + c0 + c1 * v + c2 * v ^ 2) (hg : g * (s + ℓ * u) = f)
    (hR : c2 - ℓ * c1 + ℓ ^ 2 * c0 - ℓ ^ 3 * m1 + ℓ ^ 4 * m2 = 0) :
    c2 * u ^ 2 = s ^ 2 * (c0 - ℓ * m1 + ℓ ^ 2 * m2 - c0) +
        s * (c1 - ℓ * c0 + ℓ ^ 2 * m1 - ℓ ^ 3 * m2 - c1) * u +
        s * (m1 - ℓ * m2 - m1) * cu + s ^ 2 * f + (-s ^ 3) * g ∧
      m2 * cu ^ 2 = -s ^ 2 * (c0 - ℓ * m1 + ℓ ^ 2 * m2) +
        (-s * (c1 - ℓ * c0 + ℓ ^ 2 * m1 - ℓ ^ 3 * m2)) * u + (-s * (m1 - ℓ * m2)) * cu +
        0 * f + s ^ 3 * g := by
  have h1 : (s * g - (m2 * w ^ 2 + (m1 - ℓ * m2) * w + (c0 - ℓ * m1 + ℓ ^ 2 * m2) +
      (c1 - ℓ * c0 + ℓ ^ 2 * m1 - ℓ ^ 3 * m2) * v)) * (s + ℓ * u) = 0 := by
    linear_combination s * hg + s * hf -
      (m2 * w ^ 2 + (m1 - ℓ * m2) * w + (c0 - ℓ * m1 + ℓ ^ 2 * m2) +
        (c1 - ℓ * c0 + ℓ ^ 2 * m1 - ℓ ^ 3 * m2) * v) * ℓ * hu + s * v ^ 2 * hR -
      s * ℓ * m2 * w * hvw - s * ℓ * (m1 - ℓ * m2) * hvw
  have hsg := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right hD)
  constructor
  · linear_combination c2 * (u + s * v) * hu -
      s * (c1 - ℓ * c0 + ℓ ^ 2 * m1 - ℓ ^ 3 * m2 - c1) * hu -
      s * (m1 - ℓ * m2 - m1) * hcu - s ^ 2 * hf + s ^ 2 * hsg
  · linear_combination m2 * (cu + s * w) * hcu + s * (c1 - ℓ * c0 + ℓ ^ 2 * m1 - ℓ ^ 3 * m2) * hu +
      s * (m1 - ℓ * m2) * hcu - s ^ 2 * hsg

end R14_laurentSquare

open DiazModulus R14_laurentSquare in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u)
    (lam : ℂ) (hlam : lam ∈ Qbar) (hlam1 : lam * conj lam = 1) (k : ℕ) (c : ℤ → ℂ)
    (hc : ∀ j, c j ∈ Qbar) (hcs : ∀ j, c (-j) = conj (c j)) (hck : c k ≠ 0)
    (hk : k = 2) (hroot : (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (-conj lam) ^ j) = 0) :
    u ^ 2 ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ) ∧ conj u ^ 2 ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) / (s + lam * u)} : Set ℂ) := by
  subst hk
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hu0 ((map_ne_zero _).2 hu0) (by rw [← hss]; ring)
  have hlam0 : lam ≠ 0 := by rintro rfl; simp at hlam1
  have hD : s + lam * u ≠ 0 := by
    intro h
    apply hu
    rw [show u = -s / lam by field_simp; linear_combination h]
    exact div_mem (neg_mem hs) hlam
  have hcu : conj u = s * (s / u) := by field_simp; linear_combination -hss
  have hinv : (conj lam)⁻¹ = lam := inv_eq_of_mul_eq_one_left hlam1
  simp only [Nat.cast_ofNat, sum_Icc_two] at hroot ⊢
  set f := c (-2) * (u / s) ^ (-2 : ℤ) + c (-1) * (u / s) ^ (-1 : ℤ) + c 0 * (u / s) ^ (0 : ℤ) +
    c 1 * (u / s) ^ (1 : ℤ) + c 2 * (u / s) ^ (2 : ℤ) with hfdef
  have hf : f = c (-2) * (s / u) ^ 2 + c (-1) * (s / u) + c 0 + c 1 * (u / s) +
      c 2 * (u / s) ^ 2 := by
    rw [hfdef]
    simp only [zpow_neg, zpow_ofNat, pow_zero, pow_one, mul_one, ← inv_pow, inv_div]
  have hR : c 2 - lam * c 1 + lam ^ 2 * c 0 - lam ^ 3 * c (-1) + lam ^ 4 * c (-2) = 0 := by
    simp only [zpow_neg, zpow_ofNat, pow_zero, pow_one, mul_one, neg_sq, ← inv_pow, inv_neg,
      hinv] at hroot
    linear_combination lam ^ 2 * hroot + (c 1 * lam - c 2 * (lam * conj lam + 1)) * hlam1
  obtain ⟨e1, e2⟩ := key (g := f / (s + lam * u)) hD (v := u / s) (w := s / u)
    (by field_simp) hcu (by field_simp) hf (div_mul_cancel₀ _ hD) hR
  -- lift the coefficients to `Q̄`
  let σ : ↥Qbar := ⟨s, hs⟩
  let ℓ : ↥Qbar := ⟨lam, hlam⟩
  let γ : ℤ → ↥Qbar := fun j => ⟨c j, hc j⟩
  have h2 : γ 2 ≠ 0 := fun h => hck (congrArg Subtype.val h)
  have hm2 : γ (-2) ≠ 0 := by
    intro h
    have : c (-2) = 0 := congrArg Subtype.val h
    rw [show (-2 : ℤ) = -(2 : ℤ) from rfl, hcs, map_eq_zero] at this
    exact hck this
  constructor
  · have hmem := mem5 (x₂ := u) (x₃ := conj u) (x₄ := f) (x₅ := f / (s + lam * u))
      (σ ^ 2 * (γ 0 - ℓ * γ (-1) + ℓ ^ 2 * γ (-2) - γ 0))
      (σ * (γ 1 - ℓ * γ 0 + ℓ ^ 2 * γ (-1) - ℓ ^ 3 * γ (-2) - γ 1))
      (σ * (γ (-1) - ℓ * γ (-2) - γ (-1))) (σ ^ 2) (-σ ^ 3)
    have e : (γ 2 : ℂ) * u ^ 2 = _ := e1
    push_cast at hmem
    rw [← e] at hmem
    exact (Submodule.smul_mem_iff _ h2).1 hmem
  · have hmem := mem5 (x₂ := u) (x₃ := conj u) (x₄ := f) (x₅ := f / (s + lam * u))
      (-σ ^ 2 * (γ 0 - ℓ * γ (-1) + ℓ ^ 2 * γ (-2)))
      (-σ * (γ 1 - ℓ * γ 0 + ℓ ^ 2 * γ (-1) - ℓ ^ 3 * γ (-2)))
      (-σ * (γ (-1) - ℓ * γ (-2))) 0 (σ ^ 3)
    push_cast at hmem
    rw [← e2] at hmem
    exact (Submodule.smul_mem_iff _ hm2).1 hmem
