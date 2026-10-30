-- Prove2me | solution 1 for DiazModulus.torus_hilbert_side
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:07:02.988563+00:00
-- url     : https://prove2.me/submissions/6a699ab4-c14c-45b1-bf38-1b011740688c

import Mathlib
import Definitions.Def_DiazHilbertBox
import Theorems.Thm_DiazModulus_boxHilb_hilbert_side
import Theorems.Thm_DiazModulus_restrictSupport_block_filtration
import Theorems.Thm_DiazModulus_boxHilb_torusIdeal
import Theorems.Thm_DiazModulus_isWeaklyRegular_torusList
import Theorems.Thm_DiazModulus_box_ray_upper_bound

open Complex ComplexConjugate

/-! # The Hilbert side of Th. 8.1★ in the torus model

We apply the abstract Hilbert side `boxHilb_hilbert_side` (A3) to the model
`R = K[X, Y, Z]`, the filtration `torusBox` of per-coordinate boxes, the base list
`ps₀ = torusList = (Y_i Z_i − 1)_i` (weakly regular by `isWeaklyRegular_torusList`, of
length `d₁`, generating `torusIdeal = J₀` by `torusIdeal_eq_ofList`), the ray
`D = boxD D₀ D₁ ≥ 1` and `n = d₀ + d₁`. The filtration hypotheses (monotone, multiplicative,
finite-dimensional) come from `blockBox_mono` and `restrictSupport_block_filtration`. The
upper count `h_{J₀}(vD) = (vD₀+1)^{d₀}(2vD₁+1)^{d₁}` is `boxHilb_torusIdeal`, and
`box_ray_upper_bound` bounds it by `κ (v+1)^d` with `κ = D₀^{d₀}(2D₁)^{d₁}`. A3's conclusion
`λ 2^{r(r−1)/2} ≤ κ 2^{rd}` is the statement up to commuting a product. No bound on `r` is
needed, since A3 has none. -/

namespace C11_A4
open DiazModulus

theorem boxD_pos {A₀ A₁ : Type*} (D₀ D₁ : ℕ) (h0 : 1 ≤ D₀) (h1 : 1 ≤ D₁) :
    ∀ b, 1 ≤ boxD A₀ A₁ D₀ D₁ b := by
  intro b
  cases b <;> simpa

end C11_A4

open DiazModulus C11_A4 in
theorem solution {K A₀ A₁ : Type*} [Field K] [Infinite K] [Fintype A₀] [Fintype A₁]
    (hU : UnmixedHeight (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K))
    (D₀ D₁ : ℕ) (h0 : 1 ≤ D₀) (h1 : 1 ≤ D₁) (V : Submodule K (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K))
    (hV : V ≤ torusBox K A₀ A₁ (boxD A₀ A₁ D₀ D₁)) (r : ℕ)
    (hH : ∀ p : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K), p.IsPrime → torusIdeal K A₀ A₁ ⊔ Ideal.span (V : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)) ≤ p →
      ((Fintype.card A₁ + r : ℕ) : ℕ∞) ≤ p.height)
    (lam : ℕ) (C : A₀ ⊕ A₁ → ℕ)
    (hlow : ∀ u : ℕ, 1 ≤ u → lam * u ^ ((Fintype.card A₀ + Fintype.card A₁) - r) ≤
      boxHilb (torusBox K A₀ A₁) (torusIdeal K A₀ A₁ ⊔ Ideal.span (V : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K))) (u • boxD A₀ A₁ D₀ D₁ + C)) :
    lam * 2 ^ (r * (r - 1) / 2)
      ≤ 2 ^ (r * (Fintype.card A₀ + Fintype.card A₁)) * (D₀ ^ Fintype.card A₀ * (2 * D₁) ^ Fintype.card A₁) := by
  obtain ⟨hmul, hfin, -⟩ :=
    DiazModulus.restrictSupport_block_filtration (K := K) (Sum.map (id : A₀ → A₀) (Prod.fst : A₁ × Bool → A₁))
  have hJ := torusIdeal_eq_ofList K A₀ A₁
  rw [mul_comm (2 ^ _)]
  refine DiazModulus.boxHilb_hilbert_side (torusBox K A₀ A₁) (blockBox_mono K _)
    (fun ha hb => hmul _ _ _ _ ha hb) hfin hU (torusList K A₀ A₁)
    (DiazModulus.isWeaklyRegular_torusList) (boxD A₀ A₁ D₀ D₁) (boxD_pos D₀ D₁ h0 h1) V hV r
    (Fintype.card A₀ + Fintype.card A₁) ?_ _ ?_ lam C ?_
  · intro p hp hle
    rw [torusList_length]
    exact hH p hp (hJ ▸ hle)
  · intro v
    rw [← hJ, DiazModulus.boxHilb_torusIdeal, mul_comm _ ((v + 1) ^ _)]
    simpa [Pi.smul_apply, smul_eq_mul, mul_left_comm] using
      DiazModulus.box_ray_upper_bound (A₀ := A₀) (A₁ := A₁) D₀ D₁ h0 h1 v
  · intro u hu
    rw [← hJ]
    exact hlow u hu
