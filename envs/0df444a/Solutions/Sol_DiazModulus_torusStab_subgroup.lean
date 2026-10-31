-- Prove2me | solution 1 for DiazModulus.torusStab_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:01:12.009715+00:00
-- url     : https://prove2.me/submissions/224cdfef-872f-445b-b8a4-559e95bf57bb

import Mathlib
import Definitions.Def_DiazMultiplicity
import Theorems.Thm_DiazModulus_torusVanishing_torusZero
import Theorems.Thm_DiazModulus_torusTransl_algEquiv

open Complex ComplexConjugate

/-! # The stabiliser of `Z(𝔭)` is a subgroup with closed, pairwise comaximal cosets

Let `Z = Z_G(𝔭)` for a prime `𝔭 ⊇ J₀`. `1` and products lie in `Stab` trivially. Inverses: for `g ∈ Stab`, take
`e = σ_g` from the imported node `torusTransl_algEquiv`; then `Z(e 𝔭) = Z·g⁻¹ ⊇ Z`, so by the torus
Nullstellensatz (imported `torusVanishing_torusZero`; `e 𝔭` is prime and contains `e J₀ = J₀`)
`e 𝔭 = I(Z(e 𝔭)) ≤ I(Z) = 𝔭`. Both are primes of the same finite height (`RingEquiv.height_map`, `R` Noetherian),
so `e 𝔭 = 𝔭` (`Ideal.height_add_one_le_of_lt_of_isPrime`), i.e. `Z·g⁻¹ = Z`, and `g⁻¹ ∈ Stab`.
Closedness: if `w` is a zero of `I(Γg⁻¹)`, then for `z ∈ Z`, `f ∈ 𝔭` the translate `σ_{zg} f` vanishes on `Γg⁻¹`
(`eval_torusTransl`, `G` commutative), hence at `w`, so `z·(wg) ∈ Z` and `wg ∈ Γ`. Comaximality: a common zero `w`
of `I(Γg⁻¹) ⊔ I(Γg'⁻¹)` lies in both cosets, so `g g'⁻¹ = (wg)(wg')⁻¹ ∈ Γ`; hence the sum (which contains `J₀`) has
no zero on `G` and is `⊤` by the second half of `torusVanishing_torusZero`. -/

namespace C13_G3
open DiazModulus MvPolynomial

theorem torusIdeal_le_torusVanishing {A₀ A₁ : Type*} (S : Set (TorusGroup ℂ A₀ A₁)) :
    torusIdeal ℂ A₀ A₁ ≤ torusVanishing S := by
  rw [torusIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simp only [SetLike.mem_coe, torusVanishing, Submodule.mem_iInf, RingHom.mem_ker]
  intro g _
  simp [torusPt, torusPoint]

theorem subset_torusZero_torusVanishing {A₀ A₁ : Type*} (S : Set (TorusGroup ℂ A₀ A₁)) :
    S ⊆ torusZero (torusVanishing S) := by
  intro g hg f hf
  simp only [torusVanishing, Submodule.mem_iInf, RingHom.mem_ker] at hf
  exact hf g hg

theorem torusVanishing_anti {A₀ A₁ : Type*} {S T : Set (TorusGroup ℂ A₀ A₁)} (h : S ⊆ T) :
    torusVanishing T ≤ torusVanishing S := by
  intro f hf
  simp only [torusVanishing, Submodule.mem_iInf, RingHom.mem_ker] at hf ⊢
  exact fun g hg => hf g (h hg)

/-- For `g ∈ Stab`, `Z·g⁻¹ = Z`. -/
theorem stab_preimage_eq {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁]
    (𝔭 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (h𝔭 : 𝔭.IsPrime) (hJ : torusIdeal ℂ A₀ A₁ ≤ 𝔭)
    (g : TorusGroup ℂ A₀ A₁) (hg : g ∈ torusStab 𝔭) :
    {z | z * g ∈ torusZero 𝔭} = torusZero 𝔭 := by
  have := h𝔭
  obtain ⟨⟨e, -, -, hJe, -, hZe⟩, -, -⟩ := DiazModulus.torusTransl_algEquiv g
  have hpe : (𝔭.map e).IsPrime := Ideal.map_isPrime_of_equiv e
  have hJpe : torusIdeal ℂ A₀ A₁ ≤ 𝔭.map e := hJe ▸ Ideal.map_mono hJ
  have hle : 𝔭.map e ≤ 𝔭 := by
    have hsub : torusZero 𝔭 ⊆ torusZero (𝔭.map e) := by
      rw [hZe]
      exact fun z hz => hg z hz
    calc 𝔭.map e = (𝔭.map e).radical := hpe.radical.symm
      _ = torusVanishing (torusZero (𝔭.map e)) := (DiazModulus.torusVanishing_torusZero _ hJpe).1.symm
      _ ≤ torusVanishing (torusZero 𝔭) := torusVanishing_anti hsub
      _ = 𝔭 := by rw [(DiazModulus.torusVanishing_torusZero 𝔭 hJ).1, h𝔭.radical]
  have heq : 𝔭.map e = 𝔭 := by
    by_contra hne
    have hlt := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
    have hh : (𝔭.map e).height = 𝔭.height := RingEquiv.height_map e.toRingEquiv 𝔭
    have hfin : (𝔭.map e).height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
    rw [ENat.add_one_le_iff hfin, hh] at hlt
    exact lt_irrefl _ hlt
  rw [← hZe, heq]

end C13_G3

open DiazModulus C13_G3 in
theorem solution {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (𝔭 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (h𝔭 : 𝔭.IsPrime)
    (hJ𝔭 : torusIdeal ℂ A₀ A₁ ≤ 𝔭) :
    ∃ Γ : Subgroup (TorusGroup ℂ A₀ A₁), (Γ : Set (TorusGroup ℂ A₀ A₁)) = torusStab 𝔭 ∧
      (∀ g : TorusGroup ℂ A₀ A₁, torusZero (torusVanishing {z | z * g ∈ Γ}) = {z | z * g ∈ Γ}) ∧
      ∀ g g' : TorusGroup ℂ A₀ A₁, g * g'⁻¹ ∉ Γ →
      torusVanishing {z | z * g ∈ Γ} ⊔ torusVanishing {z | z * g' ∈ Γ} = ⊤ := by
  let Γ : Subgroup (TorusGroup ℂ A₀ A₁) :=
    { carrier := torusStab 𝔭
      mul_mem' := fun {a b} ha hb z hz => by
        rw [← mul_assoc]
        exact hb _ (ha z hz)
      one_mem' := fun z hz => by
        rw [mul_one]
        exact hz
      inv_mem' := fun {g} hg z hz => by
        have h := stab_preimage_eq 𝔭 h𝔭 hJ𝔭 g hg
        have : z * g⁻¹ ∈ {w | w * g ∈ torusZero 𝔭} := by
          show z * g⁻¹ * g ∈ torusZero 𝔭
          rwa [inv_mul_cancel_right]
        rwa [h] at this }
  have hclosed : ∀ g, torusZero (torusVanishing {z | z * g ∈ Γ}) = {z | z * g ∈ Γ} := by
    intro g
    refine Set.Subset.antisymm ?_ (subset_torusZero_torusVanishing _)
    intro w hw
    show w * g ∈ torusStab 𝔭
    intro z hz f hf
    have hF : torusTransl (z * g) f ∈ torusVanishing {z | z * g ∈ Γ} := by
      simp only [torusVanishing, Submodule.mem_iInf, RingHom.mem_ker]
      intro t ht
      rw [eval_torusTransl, mul_left_comm]
      exact (ht : t * g ∈ torusStab 𝔭) z hz f hf
    have := hw _ hF
    rwa [eval_torusTransl, mul_left_comm] at this
  have hcomax : ∀ g g' : TorusGroup ℂ A₀ A₁, g * g'⁻¹ ∉ Γ →
      torusVanishing {z | z * g ∈ Γ} ⊔ torusVanishing {z | z * g' ∈ Γ} = ⊤ := by
    intro g g' hgg
    have hJ : torusIdeal ℂ A₀ A₁ ≤ torusVanishing {z | z * g ∈ Γ} ⊔ torusVanishing {z | z * g' ∈ Γ} :=
      le_sup_of_le_left (torusIdeal_le_torusVanishing _)
    refine (DiazModulus.torusVanishing_torusZero _ hJ).2 ?_
    ext w
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hw
    have h1 : w ∈ torusZero (torusVanishing {z | z * g ∈ Γ}) := fun f hf => hw f (Ideal.mem_sup_left hf)
    have h2 : w ∈ torusZero (torusVanishing {z | z * g' ∈ Γ}) := fun f hf => hw f (Ideal.mem_sup_right hf)
    rw [hclosed] at h1 h2
    apply hgg
    have := Γ.mul_mem h1 (Γ.inv_mem h2)
    rwa [mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul] at this
  exact ⟨Γ, rfl, hclosed, hcomax⟩
