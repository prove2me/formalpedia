-- Prove2me | solution 1 for DiazModulus.multiplicityEstimateElem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T09:56:14.351674+00:00
-- url     : https://prove2.me/submissions/88be809d-1f23-4052-bbbe-bd837f8a361d

import Mathlib
import Definitions.Def_MultiplicityEstimateElem
import Theorems.Thm_DiazModulus_eval_torusDerivList_eq_zero
import Theorems.Thm_DiazModulus_torus_coeff_poly
import Theorems.Thm_DiazModulus_hlow_le_boxHilb
import Theorems.Thm_DiazModulus_exists_obstruction
import Theorems.Thm_DiazModulus_torus_hilbert_side
import Theorems.Thm_DiazModulus_le_hME_constant
import Theorems.Thm_DiazModulus_unmixedHeight_mvPolynomial

open Complex ComplexConjugate

/-! # The elementary multiplicity estimate (DALAG Th. 8.1, `G⁻ = {e}`)

Assembly. Put `a j i = aₑ j i` as units and `P = torusCoeffPoly D₀ D₁ cₑ` (in the box, not in `J₀` since `cₑ ≠ 0`, by
`torus_coeff_poly`); the coordinate premise becomes the vanishing of `D_{w₁}⋯D_{w_t} P` at the points `g_s` of
`Σ[d]` (`eval_torusDerivList_eq_zero`). The obstruction node `exists_obstruction` returns the stabiliser `Γ`, its
coordinate sections `(H, ℓ)`, `(J, ψ)`, the subgroup `V × L` with `dim V + dim L < d`, and the ideal `A` with its
height bound and its vanishing to order `> M₀` along `W` on `Σ·Γ`. For a set `Rₑ` incongruent modulo `(V, ψ)`,
`hlow_le_boxHilb` bounds the Hilbert function of `A` from below on the rays `t·D + C`; `torus_hilbert_side`
(with Macaulay's unmixedness `unmixedHeight_mvPolynomial`) bounds it from above by the leading coefficient, and
`le_hME_constant` turns the comparison into hME's constant. The conclusion takes `φₑ = ψ ∘ e⁻¹` for an enumeration
`e : A₁ ≃ Fin |A₁|` and `ℓₑ = dim W − dim (W ⊓ V × L)`. -/

open DiazModulus MvPolynomial in
theorem solution :
    MultiplicityEstimateElem := by
  intro A₀ A₁ B₀ B₁ _ _ _ _ _ _ wₑ uₑ aₑ D₀ D₁ M₀ M₁ cₑ h0 h1 ha hc hprem
  classical
  let a : B₁ → A₁ → ℂˣ := fun j i => Units.mk0 (aₑ j i) (ha j i)
  have hvan := DiazModulus.eval_torusDerivList_eq_zero wₑ uₑ aₑ D₀ D₁ M₀ M₁ cₑ a (fun j i => rfl) hprem
  obtain ⟨hPbox, hP0, -⟩ := DiazModulus.torus_coeff_poly (K := ℂ) D₀ D₁ cₑ
  obtain ⟨r, 𝔭, Γ, H, J, ℓ, ψ, V, L, hcop, hHsec, hJsec, hV, hL, hΓ, hVH, hLJ, hprop, hFbox, hH, hFvan⟩ :=
    DiazModulus.exists_obstruction D₀ D₁ (torusCoeffPoly D₀ D₁ cₑ) hPbox (hP0 hc)
      (Submodule.span ℂ (Set.range wₑ)) uₑ a M₀ M₁ hvan
  have hn : (Module.finrank ℂ ↥(Submodule.span ℂ (Set.range wₑ)) -
      Module.finrank ℂ ↥(Submodule.span ℂ (Set.range wₑ) ⊓ V.prod L))
      + Module.finrank ℂ ↥(Submodule.span ℂ (Set.range wₑ) ⊓ V.prod L)
      = Module.finrank ℂ ↥(Submodule.span ℂ (Set.range wₑ)) :=
    Nat.sub_add_cancel (Submodule.finrank_mono inf_le_left)
  refine ⟨V, Fintype.card A₁, fun k => ψ ((Fintype.equivFin A₁).symm k), L, _, ?_, hn, hprop, ?_⟩
  · intro v
    rw [hL v]
    constructor
    · intro h k
      exact h _
    · intro h i
      simpa using h (Fintype.equivFin A₁ i)
  · intro Rₑ hR hRinc
    have hRinc' : ∀ s ∈ Rₑ, ∀ s' ∈ Rₑ, ((∑ b, ((s b - s' b : ℤ) : ℂ) • uₑ b) ∈ V ∧
        ∀ k, ∏ i, (∏ b, a b i ^ (s b - s' b)) ^ ψ k i = 1) → s = s' := by
      rintro s hs s' hs' ⟨hx, hy⟩
      refine hRinc s hs s' hs' ⟨hx, fun k => ?_⟩
      have := congrArg Units.val (hy ((Fintype.equivFin A₁).symm k))
      simpa [a, Units.coe_prod, Units.val_zpow_eq_zpow_val] using this
    obtain ⟨C, hlow⟩ := DiazModulus.hlow_le_boxHilb Γ hcop H J hHsec hJsec ℓ ψ V L hV hL hΓ hVH hLJ
      (Submodule.span ℂ (Set.range wₑ)) _ hn uₑ a M₀ M₁ _ hFvan D₀ D₁ Rₑ hR hRinc'
    have hU := DiazModulus.unmixedHeight_mvPolynomial (σ := A₀ ⊕ (A₁ × Bool)) (K := ℂ)
    have h4 := DiazModulus.torus_hilbert_side hU D₀ D₁ h0 h1 _ hFbox _ hH _ C hlow
    exact DiazModulus.le_hME_constant _ _ _ _ D₀ D₁ h4
