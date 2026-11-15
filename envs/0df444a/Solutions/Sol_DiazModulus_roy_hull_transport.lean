-- Prove2me | solution 1 for DiazModulus.roy_hull_transport
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:47:31.249707+00:00
-- url     : https://prove2.me/submissions/ff9012fd-b81c-4b30-9019-3885d3c564c2

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_rational_adapted_basis

open Complex ComplexConjugate

/-! # Transport to the coordinates of a minimal rational subspace

Let `S₀` be rational of dimension `s`, containing `U`, with no rational subspace of smaller dimension containing
`U`. An adapted basis of `S₀` gives a linear automorphism `g` of `ℂ^d`, preserving algebraic vectors and
`ℒ̃`-vectors in both directions, with `v ∈ S₀` exactly when the coordinates of `g v` of index `≥ s` vanish. Put
`ι = g⁻¹ ∘ pad`, where `pad` extends a vector of `ℂ^s` by zeros, and `ρ v` = the first `s` coordinates of `g v`.
Then `ι` is injective with image `S₀`, `ρ ∘ ι = id`, and `ι ∘ ρ = id` on `S₀`. Take `U' = ι⁻¹(U)` and
`z' = ρ ∘ z`. Since `ι` maps `U'` onto `U`, the dimensions agree; `ι` sends algebraic vectors to algebraic vectors,
so `U' ∩ Q̄^s = 0`; `ρ` preserves `ℒ̃`-coordinates; and `ι z' = z` gives `Q̄`-freeness. Finally a rational `T ⊇ U'`
maps to a rational `ι(T) ⊇ U` of the same dimension, so `dim T ≥ s` by minimality, and `T = ℂ^s`. -/

open DiazModulus in
theorem solution {d s ℓ : ℕ} (S₀ U : Submodule ℂ (Fin d → ℂ))
    (hS₀ : Submodule.span ℂ {v : Fin d → ℂ | v ∈ S₀ ∧ ∀ i, v i ∈ Qbar} = S₀)
    (hs : Module.finrank ℂ ↥S₀ = s) (hUS₀ : U ≤ S₀)
    (hUQ : ∀ v ∈ U, (∀ i, v i ∈ Qbar) → v = 0)
    (hmin : ∀ T : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T → U ≤ T → s ≤ Module.finrank ℂ ↥T)
    (z : Fin ℓ → Fin d → ℂ) (hzU : ∀ i, z i ∈ U) (hz : ∀ i j, z i j ∈ LogAlgTilde)
    (hzind : LinearIndependent (↥Qbar) z) :
    ∃ (U' : Submodule ℂ (Fin s → ℂ)) (z' : Fin ℓ → Fin s → ℂ),
      Module.finrank ℂ ↥U' = Module.finrank ℂ ↥U ∧
      (∀ v ∈ U', (∀ i, v i ∈ Qbar) → v = 0) ∧
      (∀ T : Submodule ℂ (Fin s → ℂ),
        Submodule.span ℂ {v : Fin s → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T → U' ≤ T → T = ⊤) ∧
      (∀ i, z' i ∈ U') ∧ (∀ i j, z' i j ∈ LogAlgTilde) ∧ LinearIndependent (↥Qbar) z' := by
  obtain ⟨g, hgQ, hgL, hgS⟩ := DiazModulus.roy_rational_adapted_basis S₀ hS₀
  rw [hs] at hgS
  have hsd : s ≤ d := by
    have := Submodule.finrank_le S₀
    simp only [Module.finrank_fin_fun] at this
    omega
  -- pad (low coordinates), ι = g⁻¹ ∘ pad, ρ = first s coordinates of g
  let pad : (Fin s → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
    { toFun := fun x i => if h : i.val < s then x ⟨i.val, h⟩ else 0
      map_add' := by
        intro x y; ext i; by_cases h : i.val < s <;> simp [h]
      map_smul' := by
        intro c x; ext i; by_cases h : i.val < s <;> simp [h] }
  let ι : (Fin s → ℂ) →ₗ[ℂ] (Fin d → ℂ) := g.symm.toLinearMap ∘ₗ pad
  let ρ : (Fin d → ℂ) →ₗ[ℂ] (Fin s → ℂ) :=
    { toFun := fun v j => g v (Fin.castLE hsd j)
      map_add' := by intro x y; ext j; simp
      map_smul' := by intro c x; ext j; simp }
  have hgι : ∀ x, g (ι x) = pad x := by intro x; simp [ι]
  have hρι : ∀ x, ρ (ι x) = x := by
    intro x; ext j
    show g (ι x) (Fin.castLE hsd j) = x j
    rw [hgι]
    simp [pad, Fin.castLE, j.isLt]
  have hιS : ∀ x, ι x ∈ S₀ := by
    intro x
    rw [hgS, hgι]
    intro i hi
    simp [pad, show ¬ i.val < s by omega]
  have hιρ : ∀ v ∈ S₀, ι (ρ v) = v := by
    intro v hv
    have h0 := (hgS v).1 hv
    apply g.injective
    rw [hgι]
    ext i
    by_cases h : i.val < s
    · simp [pad, ρ, h, Fin.castLE]
    · simp only [pad, LinearMap.coe_mk, AddHom.coe_mk, h, dite_false]
      exact (h0 i (by omega)).symm
  have hιinj : Function.Injective ι := by
    intro x y h
    have := congrArg ρ h
    rwa [hρι, hρι] at this
  have hιalg : ∀ x : Fin s → ℂ, (∀ i, x i ∈ Qbar) → ∀ i, ι x i ∈ Qbar := by
    intro x hx
    have hpad : ∀ i, pad x i ∈ Qbar := by
      intro i
      by_cases h : i.val < s
      · simpa [pad, h] using hx ⟨i.val, h⟩
      · simp [pad, h, Qbar.zero_mem]
    exact (hgQ (pad x) hpad).2
  have hρL : ∀ v : Fin d → ℂ, (∀ i, v i ∈ LogAlgTilde) → ∀ j, ρ v j ∈ LogAlgTilde := by
    intro v hv j
    exact (hgL v hv).1 (Fin.castLE hsd j)
  have hmap : (U.comap ι).map ι = U := by
    rw [Submodule.map_comap_eq]
    refine inf_eq_right.mpr ?_
    intro u hu
    exact ⟨ρ u, hιρ u (hUS₀ hu)⟩
  refine ⟨U.comap ι, ρ ∘ z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- dim U* = dim U
    conv_rhs => rw [← hmap]
    exact (Submodule.equivMapOfInjective ι hιinj _).finrank_eq
  · -- U* ∩ Q̄^s = 0
    intro x hx hxQ
    have h0 := hUQ (ι x) hx (hιalg x hxQ)
    exact hιinj (by rw [h0, map_zero])
  · -- hull of U* is ℂ^s
    intro T hT hUT
    have hTrat : Submodule.span ℂ {v : Fin d → ℂ | v ∈ T.map ι ∧ ∀ i, v i ∈ Qbar} = T.map ι := by
      apply le_antisymm
      · rw [Submodule.span_le]; intro v hv; exact hv.1
      · conv_lhs => rw [← hT]
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨x, ⟨hxT, hxQ⟩, rfl⟩
        exact ⟨⟨x, hxT, rfl⟩, hιalg x hxQ⟩
    have hUT' : U ≤ T.map ι := by
      intro u hu
      refine ⟨ρ u, hUT ?_, hιρ u (hUS₀ hu)⟩
      show ι (ρ u) ∈ U
      rw [hιρ u (hUS₀ hu)]; exact hu
    have h1 := hmin _ hTrat hUT'
    have h2 : Module.finrank ℂ ↥(T.map ι) = Module.finrank ℂ ↥T :=
      (Submodule.equivMapOfInjective ι hιinj T).finrank_eq.symm
    apply Submodule.eq_top_of_finrank_eq
    have h3 := Submodule.finrank_le T
    simp only [Module.finrank_fin_fun] at h3 ⊢
    omega
  · -- z* in U*
    intro i
    show ι (ρ (z i)) ∈ U
    rw [hιρ _ (hUS₀ (hzU i))]; exact hzU i
  · -- coordinates of z* in ℒ̃
    intro i j
    exact hρL (z i) (hz i) j
  · -- z* Q̄-free
    rw [Fintype.linearIndependent_iff] at hzind ⊢
    intro c hc
    apply hzind c
    have := congrArg ι hc
    simp only [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Function.comp_apply, Subfield.smul_def, map_smul, hιρ _ (hUS₀ (hzU i))]
