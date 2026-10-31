-- Prove2me | solution 1 for DiazModulus.exists_le_translate_of_le_torusVanishing
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:03:47.783947+00:00
-- url     : https://prove2.me/submissions/dcecadca-24f5-47c4-9fcc-e406c6c91b10

import Mathlib
import Definitions.Def_DiazMultiplicity
import Theorems.Thm_DiazModulus_torusVanishing_torusZero
import Theorems.Thm_DiazModulus_torusTransl_algEquiv

open Complex ComplexConjugate

/-! # A prime over the obstruction ideal contains a translate of the section ideal

Write `I_r = J₀ + (σ_{g_s} D_l P)` and `A = J₀ + (σ_{g_s v} D_l P : v ∈ Z(𝔭))`. If `z ∈ Z(A)`, every generator
`f` of `I_r` satisfies `(σ_z f)(v) = f(v z) = 0` for `v ∈ Z(𝔭)`, so `σ_z f ∈ I(Z(𝔭)) = 𝔭` (V1, `𝔭` prime), and
`σ_z J₀ = J₀ ⊆ 𝔭` (V2): hence `I_r ≤ 𝔭.comap σ_z`, and by `hc` this prime is one of the finitely many minimal
primes of `I_r` (`Ideal.finite_minimalPrimes_of_isNoetherianRing`). For each such minimal prime `Q` reached in
this way pick one `z_Q ∈ Z(A)` with `𝔭.comap σ_{z_Q} = Q`. If `𝔭.comap σ_z = 𝔭.comap σ_{z'}` then `z z'⁻¹`
stabilises `Z(𝔭)` (V2's composition rule `σ_g σ_h = σ_{g h}`), so for `a ∈ 𝔞 ≤ I(Stab)`, `(σ_{z_Q⁻¹} a)(z) =
a(z z_Q⁻¹) = 0`: the finite intersection `⋂_Q σ_{z_Q⁻¹}(𝔞)` lies in `I(Z(A)) = √A ≤ 𝔮` (V1). Prime avoidance
for a finite intersection (`Ideal.IsPrime.inf_le'`) gives one `Q` with `σ_{z_Q⁻¹}(𝔞) ≤ 𝔮`, i.e.
`𝔞 ≤ 𝔮.comap σ_{z_Q⁻¹}`. (If no `Q` is reached the intersection is `⊤ ≤ 𝔮`, impossible for a prime.) -/

namespace C13_Z3
open DiazModulus MvPolynomial

/-- `σ_g(𝔞)` vanishes at `z` when `𝔞 ≤ I(S)` and `z g ∈ S`. -/
theorem map_le_ker {A₀ A₁ : Type*} {S : Set (TorusGroup ℂ A₀ A₁)}
    {𝔞 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)} (h𝔞 : 𝔞 ≤ torusVanishing S)
    (g z : TorusGroup ℂ A₀ A₁) (hz : z * g ∈ S) :
    𝔞.map (torusTransl g) ≤ RingHom.ker (eval (torusPt z)) := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  have := h𝔞 hf
  simp only [torusVanishing, Submodule.mem_iInf, RingHom.mem_ker] at this
  simp only [Ideal.mem_comap, RingHom.mem_ker, eval_torusTransl]
  exact this _ hz

/-- Equal pulled-back primes differ by an element of the stabiliser. -/
theorem mem_torusStab_of_comap_eq {A₀ A₁ : Type*} (𝔭 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))
    (z z' : TorusGroup ℂ A₀ A₁) (h : 𝔭.comap (torusTransl z') = 𝔭.comap (torusTransl z)) :
    z * z'⁻¹ ∈ torusStab 𝔭 := by
  intro v hv f hf
  have h1 : torusTransl z'⁻¹ f ∈ 𝔭.comap (torusTransl z') := by
    rw [Ideal.mem_comap, (torusTransl_algEquiv z').2.1, mul_inv_cancel, (torusTransl_algEquiv z').2.2]
    exact hf
  rw [h, Ideal.mem_comap] at h1
  have := hv _ h1
  rwa [eval_torusTransl, eval_torusTransl, mul_assoc] at this

/-- A zero of `A` pulls `𝔭` back to a prime containing `I_r`. -/
theorem le_comap_of_mem_torusZero {A₀ A₁ B₁ : Type*} [Fintype A₀] [Fintype A₁] [Fintype B₁]
    (P : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) (W : Submodule ℂ ((A₀ → ℂ) × (A₁ → ℂ)))
    (u : B₁ → A₀ → ℂ) (a : B₁ → A₁ → ℂˣ) (m n : ℕ) (𝔭 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))
    (h𝔭 : 𝔭.IsPrime) (hJ𝔭 : torusIdeal ℂ A₀ A₁ ≤ 𝔭) (z : TorusGroup ℂ A₀ A₁)
    (hz : z ∈ torusZero (torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a m n (torusZero 𝔭) :
      Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)))) :
    torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a m n {1} :
      Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ≤ 𝔭.comap (torusTransl z) := by
  obtain ⟨⟨e, he, -, hJ, -, -⟩, -, -⟩ := torusTransl_algEquiv z
  have hrad : torusVanishing (torusZero 𝔭) = 𝔭 := by
    rw [(torusVanishing_torusZero 𝔭 hJ𝔭).1, h𝔭.radical]
  refine sup_le ?_ ?_
  · intro f hf
    rw [Ideal.mem_comap, ← he]
    exact hJ𝔭 (hJ ▸ Ideal.mem_map_of_mem e hf)
  · have hle : obstructionSpan P W u a m n {1} ≤ (𝔭.comap (torusTransl z)).restrictScalars ℂ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨s, hs, v, hv, l, hl, hW, rfl⟩
      rw [Set.mem_singleton_iff] at hv
      subst hv
      simp only [SetLike.mem_coe, Submodule.restrictScalars_mem, Ideal.mem_comap]
      rw [← hrad]
      simp only [torusVanishing, Submodule.mem_iInf, RingHom.mem_ker]
      intro y hy
      have hgen : torusTransl (hmePoint u a s * y) (torusDerivList l P) ∈
          torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a m n (torusZero 𝔭) :
            Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) :=
        Ideal.mem_sup_right (Ideal.subset_span (Submodule.subset_span ⟨s, hs, y, hy, l, hl, hW, rfl⟩))
      have h0 := hz _ hgen
      rw [eval_torusTransl] at h0
      rw [eval_torusTransl, eval_torusTransl, mul_one, mul_comm y z, mul_assoc, mul_comm y]
      exact h0
    rw [Ideal.span_le]
    exact fun x hx => hle hx

end C13_Z3

open DiazModulus C13_Z3 in
theorem solution {A₀ A₁ B₁ : Type*} [Fintype A₀] [Fintype A₁] [Fintype B₁] (P : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) (W : Submodule ℂ ((A₀ → ℂ) × (A₁ → ℂ)))
    (u : B₁ → A₀ → ℂ) (a : B₁ → A₁ → ℂˣ) (M₀ M₁ r : ℕ) (𝔭 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (h𝔭 : 𝔭.IsPrime)
    (hJ𝔭 : torusIdeal ℂ A₀ A₁ ≤ 𝔭)
    (hc : ∀ z : TorusGroup ℂ A₀ A₁, torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) {1} : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ≤ 𝔭.comap (torusTransl z) →
        𝔭.comap (torusTransl z) ∈ (torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) {1} : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))).minimalPrimes)
    (𝔞 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (h𝔞 : 𝔞 ≤ torusVanishing (torusStab 𝔭)) (𝔮 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (h𝔮 : 𝔮.IsPrime)
    (hA𝔮 : torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) (torusZero 𝔭) : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ≤ 𝔮) :
    ∃ g : TorusGroup ℂ A₀ A₁, 𝔞 ≤ 𝔮.comap (torusTransl g) := by
  classical
  set I := torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) {1} :
    Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) with hI
  set A := torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) (torusZero 𝔭) :
    Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) with hA
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I
  let reach : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) → Prop := fun Q =>
    ∃ z ∈ torusZero A, 𝔭.comap (torusTransl z) = Q
  let wit : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) → TorusGroup ℂ A₀ A₁ := fun Q =>
    if h : reach Q then h.choose else 1
  let s := hfin.toFinset.filter reach
  let f : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) → Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) :=
    fun Q => 𝔞.map (torusTransl (wit Q)⁻¹)
  have h1 : s.inf f ≤ torusVanishing (torusZero A) := by
    intro x hx
    simp only [torusVanishing, Submodule.mem_iInf, RingHom.mem_ker]
    intro z hz
    have hQ : 𝔭.comap (torusTransl z) ∈ I.minimalPrimes :=
      hc z (le_comap_of_mem_torusZero P W u a _ _ 𝔭 h𝔭 hJ𝔭 z hz)
    have hex : reach (𝔭.comap (torusTransl z)) := ⟨z, hz, rfl⟩
    have hmem : 𝔭.comap (torusTransl z) ∈ s := Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hQ, hex⟩
    have hx' := Finset.inf_le (f := f) hmem hx
    have hw : 𝔭.comap (torusTransl (wit (𝔭.comap (torusTransl z)))) = 𝔭.comap (torusTransl z) := by
      simp only [wit, dif_pos hex]
      exact hex.choose_spec.2
    exact map_le_ker h𝔞 _ z (mem_torusStab_of_comap_eq 𝔭 z _ hw) hx'
  have h2 : torusVanishing (torusZero A) ≤ 𝔮 := by
    rw [(torusVanishing_torusZero A le_sup_left).1]
    exact (Ideal.IsPrime.radical_le_iff h𝔮).mpr hA𝔮
  obtain ⟨Q, -, hQ⟩ := (Ideal.IsPrime.inf_le' h𝔮).mp (h1.trans h2)
  exact ⟨(wit Q)⁻¹, Ideal.map_le_iff_le_comap.mp hQ⟩
