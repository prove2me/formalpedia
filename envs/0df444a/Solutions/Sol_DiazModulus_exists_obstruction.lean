-- Prove2me | solution 1 for DiazModulus.exists_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T09:57:57.232989+00:00
-- url     : https://prove2.me/submissions/85c6518e-fc89-4953-b253-6710219de2d6

import Mathlib
import Definitions.Def_DiazMultiplicity
import Theorems.Thm_DiazModulus_exists_chain_prime
import Theorems.Thm_DiazModulus_obstructionSpan_vanishOrd
import Theorems.Thm_DiazModulus_le_height_obstruction
import Theorems.Thm_DiazModulus_torusStab_subgroup
import Theorems.Thm_DiazModulus_exists_coordinate_section_add
import Theorems.Thm_DiazModulus_exists_coordinate_section_mul
import Theorems.Thm_DiazModulus_linearIndependent_on_subgroup
import Theorems.Thm_DiazModulus_torus_reduce_mem_restrictSupport
import Theorems.Thm_DiazModulus_torusVanishing_torusZero
import Theorems.Thm_DiazModulus_torusTransl_algEquiv

open Complex ComplexConjugate

/-! # The obstruction subgroup (DALAG §8.4.1)

Assembly of DALAG §8.4.1. The chain node `exists_chain_prime` gives the step `r < d` and a prime `𝔭 ⊇ J₀ + (P)` that
contains every translate `σ_{g_s} D_{w₁}⋯D_{w_t} P` of order `(r+1)` and is minimal over `I_r` up to translation. Its
stabiliser `Γ = Stab Z(𝔭)` is a subgroup with the coset coprimality (`torusStab_subgroup`); the coordinate sections of
the additive span of `Γ` and of the character group `Φ = {φ : y^φ = 1 on Γ}` (`exists_coordinate_section_add/_mul`)
give `(H, ℓ, V)` and `(J, ψ, L)` with `Γ ⊆ V × T_ψ`. The section ideal vanishes on `Γ` generator by generator
(`Y_iZ_i − 1` at `(y, y⁻¹)`, `Σ ℓ_{hh'} X_{h'}` because `x_g ∈ V`, `Y^{ψ⁺}Z^{ψ⁻} − 1` because `y_g^ψ = 1`), so
`le_height_obstruction` gives the height bound, and `obstructionSpan_vanishOrd` gives the box and the vanishing of `A`
on `Σ·Γ`. Properness `dim V + dim L < d`: otherwise `H` and `J` are everything; for `v ∈ Z(𝔭)` (nonempty since
`𝔭 ≠ ⊤`, `torusVanishing_torusZero`) the reduced form of `σ_v P` (`torus_reduce_mem_restrictSupport`, box kept by
`torusTransl_algEquiv`) vanishes on `Γ` because `Z(𝔭)·Γ ⊆ Z(𝔭)` and `P ∈ 𝔭`, hence is `0` by
`linearIndependent_on_subgroup`; then `σ_v P ∈ J₀`, so `P ∈ J₀`, a contradiction. -/

namespace C13_Z7
open DiazModulus MvPolynomial

variable {A₀ A₁ : Type*}

/-- Membership in `I(S)`: vanishing at every point of `S`. -/
theorem mem_torusVanishing_iff {S : Set (TorusGroup ℂ A₀ A₁)} {f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ} :
    f ∈ torusVanishing S ↔ ∀ g ∈ S, eval (torusPt g) f = 0 := by
  simp [torusVanishing, Submodule.mem_iInf, RingHom.mem_ker]

/-- `J₀` vanishes at every torus point. -/
theorem eval_torusIdeal (g : TorusGroup ℂ A₀ A₁) {f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ}
    (hf : f ∈ torusIdeal ℂ A₀ A₁) : eval (torusPt g) f = 0 := by
  have : torusIdeal ℂ A₀ A₁ ≤ RingHom.ker (eval (torusPt g)) := by
    rw [torusIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [torusPt, torusPoint]
  exact this hf

/-- The Laurent monomial `Y^{φ⁺} Z^{φ⁻}` evaluates to the character `y^φ`. -/
theorem eval_torusMono [Fintype A₁] (g : TorusGroup ℂ A₀ A₁) (φ : A₁ → ℤ) :
    eval (torusPt g) (torusMono (A₀ := A₀) φ) = ((∏ i, g.2 i ^ φ i : ℂˣ) : ℂ) := by
  simp only [torusMono, map_prod, map_mul, map_pow, eval_X, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [torusPt, torusPoint, Sum.elim_inr, if_true, Bool.false_eq_true, if_false]
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
  congr 1
  rw [← zpow_natCast, ← zpow_natCast, inv_zpow', ← zpow_add, ← sub_eq_add_neg, Int.toNat_sub_toNat_neg]

/-- The linear form `Σ a_h X_h` evaluates to `Σ a_h x_h`. -/
theorem eval_linForm [Fintype A₀] (g : TorusGroup ℂ A₀ A₁) (c : A₀ → ℂ) :
    eval (torusPt g) (linForm (A₁ := A₁) c) = ∑ h, c h * Multiplicative.toAdd g.1 h := by
  simp [linForm, torusPt, torusPoint]

end C13_Z7

open DiazModulus C13_Z7 MvPolynomial in
theorem solution {A₀ A₁ B₁ : Type*} [Fintype A₀] [Fintype A₁] [Fintype B₁] (D₀ D₁ : ℕ) (P : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)
    (hPbox : P ∈ torusBox ℂ A₀ A₁ (boxD A₀ A₁ D₀ D₁)) (hP0 : P ∉ torusIdeal ℂ A₀ A₁) (W : Submodule ℂ ((A₀ → ℂ) × (A₁ → ℂ)))
    (u : B₁ → A₀ → ℂ) (a : B₁ → A₁ → ℂˣ) (M₀ M₁ : ℕ)
    (hvan : ∀ l : List ((A₀ → ℂ) × (A₁ → ℂ)), l.length ≤ (Fintype.card A₀ + Fintype.card A₁) * M₀ → (∀ w ∈ l, w ∈ W) →
      ∀ s : B₁ → ℤ, (∀ b, |s b| ≤ (((Fintype.card A₀ + Fintype.card A₁) * M₁ : ℕ) : ℤ)) →
        MvPolynomial.eval (torusPt (hmePoint u a s)) (torusDerivList l P) = 0) :
    ∃ (r : ℕ) (𝔭 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (Γ : Subgroup (TorusGroup ℂ A₀ A₁)) (H : Finset A₀) (J : Finset A₁) (ℓ : A₀ → A₀ → ℂ)
      (ψ : A₁ → A₁ → ℤ) (V : Submodule ℂ (A₀ → ℂ)) (L : Submodule ℂ (A₁ → ℂ)),
      (∀ g g' : TorusGroup ℂ A₀ A₁, g * g'⁻¹ ∉ Γ →
      torusVanishing {z | z * g ∈ Γ} ⊔ torusVanishing {z | z * g' ∈ Γ} = ⊤) ∧
      (∀ x : A₀ → ℂ, ∃ v ∈ Submodule.span ℂ {v | ∃ g ∈ Γ, Multiplicative.toAdd g.1 = v}, ∀ h ∈ H, v h = x h) ∧ (∀ φ : A₁ → ℤ, (∀ i ∉ J, φ i = 0) → (∀ g ∈ Γ, ∏ i, g.2 i ^ φ i = 1) → φ = 0) ∧
      (∀ v, v ∈ V ↔ ∀ h, ∑ h', ℓ h h' * v h' = 0) ∧ (∀ v, v ∈ L ↔ ∀ i, ∑ i', (ψ i i' : ℂ) * v i' = 0) ∧ (Γ : Set (TorusGroup ℂ A₀ A₁)) ⊆ standardSet V ψ ∧
      Module.finrank ℂ ↥V = H.card ∧ Module.finrank ℂ ↥L = J.card ∧ Module.finrank ℂ ↥V + Module.finrank ℂ ↥L < (Fintype.card A₀ + Fintype.card A₁) ∧
      obstructionSpan P W u a (r * M₁) (r * M₀) (torusZero 𝔭) ≤ torusBox ℂ A₀ A₁ (boxD A₀ A₁ D₀ D₁) ∧
      (∀ p : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ), p.IsPrime → torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) (torusZero 𝔭) : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ≤ p →
        ((Fintype.card A₁ + ((Fintype.card A₀ + Fintype.card A₁) - (Module.finrank ℂ ↥V + Module.finrank ℂ ↥L)) : ℕ) : ℕ∞) ≤ p.height) ∧
      ((torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) (torusZero 𝔭) : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ⊆ vanishOrd (torusVanishing {z | ∃ s : B₁ → ℤ, (∀ b, |s b| ≤ (M₁ : ℤ)) ∧ ∃ γ ∈ Γ, z = hmePoint u a s * γ}) W M₀ := by
  classical
  obtain ⟨r, -, 𝔭, h𝔭, hJ𝔭, hP𝔭, hb, hc⟩ := exists_chain_prime P hP0 W u a M₀ M₁ hvan
  obtain ⟨Γ, hΓS, -, hcop⟩ := torusStab_subgroup 𝔭 h𝔭 hJ𝔭
  obtain ⟨H, ℓ, -, hℓ, hV, hHsec, hVH⟩ :=
    exists_coordinate_section_add (Submodule.span ℂ {v | ∃ g ∈ Γ, Multiplicative.toAdd g.1 = v})
  let Φ : AddSubgroup (A₁ → ℤ) :=
    { carrier := {φ | ∀ g ∈ Γ, ∏ i, g.2 i ^ φ i = 1}
      add_mem' := fun {φ φ'} hφ hφ' g hg => by
        simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib, hφ g hg, hφ' g hg, mul_one]
      zero_mem' := fun g _ => by simp
      neg_mem' := fun {φ} hφ g hg => by
        simp only [Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib, hφ g hg, inv_one] }
  obtain ⟨J, ψ, hJΦ, hψΦ, -, hψ, hLdim⟩ := exists_coordinate_section_mul Φ
  let L : Submodule ℂ (A₁ → ℂ) :=
    { carrier := {v | ∀ i, ∑ i', (ψ i i' : ℂ) * v i' = 0}
      add_mem' := fun {v v'} hv hv' i => by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hv i, hv' i, add_zero]
      zero_mem' := fun i => by simp
      smul_mem' := fun c v hv i => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum, hv i, mul_zero] }
  have hL : ∀ v, v ∈ L ↔ ∀ i, ∑ i', (ψ i i' : ℂ) * v i' = 0 := fun v => Iff.rfl
  have hLJ := hLdim L hL
  have hΓstd : (Γ : Set (TorusGroup ℂ A₀ A₁)) ⊆
      standardSet (Submodule.span ℂ {v | ∃ g ∈ Γ, Multiplicative.toAdd g.1 = v}) ψ :=
    fun g hg => ⟨Submodule.subset_span ⟨g, hg, rfl⟩, fun k => hψΦ k g hg⟩
  have h𝔞 : sectionIdeal ℓ ψ ≤ torusVanishing (torusStab 𝔭) := by
    rw [← hΓS]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro f hf
      exact mem_torusVanishing_iff.2 fun g _ => eval_torusIdeal g hf
    · rw [Ideal.span_le]
      rintro _ ⟨h, rfl⟩
      refine mem_torusVanishing_iff.2 fun g hg => ?_
      rw [eval_linForm]
      exact (hV _).1 (Submodule.subset_span ⟨g, hg, rfl⟩) h
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      refine mem_torusVanishing_iff.2 fun g hg => ?_
      have h1 : ∏ i, g.2 i ^ ψ k i = 1 := hψΦ k g hg
      rw [map_sub, eval_torusMono, h1]
      simp
  have hH := le_height_obstruction P W u a M₀ M₁ r 𝔭 h𝔭 hJ𝔭 hc H J ℓ ψ hℓ hψ h𝔞
  obtain ⟨hFbox, hFvan⟩ := obstructionSpan_vanishOrd D₀ D₁ P hPbox W u a M₀ M₁ r 𝔭 hb
    (Γ : Set (TorusGroup ℂ A₀ A₁)) (fun v hv γ hγ => by
      have hγ' : γ ∈ torusStab 𝔭 := by rw [← hΓS]; exact hγ
      exact hγ' v hv)
  have hprop : Module.finrank ℂ ↥(Submodule.span ℂ {v | ∃ g ∈ Γ, Multiplicative.toAdd g.1 = v})
      + Module.finrank ℂ ↥L < Fintype.card A₀ + Fintype.card A₁ := by
    by_contra hcon
    rw [not_lt] at hcon
    rw [hVH, hLJ] at hcon
    have hHc := Finset.card_le_univ H
    have hJc := Finset.card_le_univ J
    have hHu : H = Finset.univ := Finset.eq_univ_of_card H (by omega)
    have hJu : J = Finset.univ := Finset.eq_univ_of_card J (by omega)
    obtain ⟨v, hv⟩ : (torusZero 𝔭).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact h𝔭.ne_top ((torusVanishing_torusZero 𝔭 hJ𝔭).2 h)
    obtain ⟨⟨e, he, hebox, heJ, -, -⟩, -, -⟩ := torusTransl_algEquiv v
    have heP : e P ∈ torusBox ℂ A₀ A₁ (boxD A₀ A₁ D₀ D₁) := by
      rw [← hebox]
      exact Submodule.mem_map_of_mem hPbox
    obtain ⟨g, hg, hgJ⟩ := torus_reduce_mem_restrictSupport _ _ heP
    have hg0 : g = 0 := by
      refine linearIndependent_on_subgroup Γ H J hHsec (fun φ h1 h2 => hJΦ φ h2 h1) g hg.2 ?_ ?_
      · intro m _
        simp [hHu, hJu]
      · intro γ hγ
        have h1 : eval (torusPt γ) (e P) = 0 := by
          have hγ' : γ ∈ torusStab 𝔭 := by rw [← hΓS]; exact hγ
          rw [he, eval_torusTransl, mul_comm]
          exact hγ' v hv P hP𝔭
        have h2 := eval_torusIdeal γ hgJ
        rwa [map_sub, h1, zero_sub, neg_eq_zero] at h2
    rw [hg0, sub_zero, ← heJ, Ideal.mem_map_of_equiv] at hgJ
    obtain ⟨x, hx, hxe⟩ := hgJ
    exact hP0 (e.injective hxe ▸ hx)
  refine ⟨r, 𝔭, Γ, H, J, ℓ, ψ, _, L, hcop, hHsec, fun φ h1 h2 => hJΦ φ h2 h1, hV, hL, hΓstd, hVH, hLJ, hprop,
    hFbox, ?_, hFvan⟩
  intro p hp hle
  rw [hVH, hLJ]
  exact hH p hp hle
