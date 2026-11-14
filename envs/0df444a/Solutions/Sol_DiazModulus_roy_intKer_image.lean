-- Prove2me | solution 1 for DiazModulus.roy_intKer_image
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-13T10:03:25.604397+00:00
-- url     : https://prove2.me/submissions/f3dd0055-1131-449f-bc39-257cf4b15455

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The kernel of an integer matrix and its image under `Υ₁`
Write `Υ₁(y)_i = Σ_k ω_k y_{(k,i)}` and let `L_ℚ ⊆ ℚ^{m×d}` be the rational kernel of `φ`.
(1) `L₁` is the ℂ-span of `L_ℚ`: for `y ∈ L₁`, expand its coordinates in a ℚ-basis `c_t` of
the ℚ-span of the coordinates, `y = Σ_t c_t r_t` with `r_t` rational; applying the
coordinate map of that basis to `Σ_i φ_{k,i} y_i = 0` gives `Σ_i φ_{k,i} (r_t)_i = 0`, so
`r_t ∈ L_ℚ`. Casts of a ℚ-basis of `L_ℚ` then span `L₁`, so `dim_ℂ L₁ ≤ dim_ℚ L_ℚ`.
(2) Put `W = Υ₁(L₁)`. The coordinate functionals restricted to `W` span its dual, so some
`w = dim W` of them, at coordinates `a_j`, already separate the points of `W`. The ℚ-linear
map `r ↦ (r_{(k, a_j)})_{j,k}` from `L_ℚ` to `ℚ^{w×m}` is injective: if it kills `r`, then
`Υ₁(r) ∈ W` vanishes at every `a_j`, so `Υ₁(r) = 0`, and the ℚ-independence of `ω` forces
`r = 0`. Hence `dim_ℚ L_ℚ ≤ m·w`, and with (1), `dim L₁ ≤ m·dim W`.
(3) `W = Υ₁(span L_ℚ) = span Υ₁(L_ℚ)`, and each `Υ₁(r)` with `r` rational has algebraic
coordinates `Σ_k ω_k r_{(k,i)}`; so `W` is spanned by its algebraic points. -/

namespace RC1_IK
open DiazModulus

/-- The map `Υ₁`, verbatim. -/
noncomputable def Ups1 (d m : ℕ) (ω : Fin m → ℂ) : (Fin m × Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  LinearMap.pi fun i : Fin d => ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ)

theorem Ups1_apply {d m : ℕ} (ω : Fin m → ℂ) (y : Fin m × Fin d → ℂ) (i : Fin d) :
    Ups1 d m ω y i = ∑ k, ω k * y (k, i) := by
  simp [Ups1, LinearMap.sum_apply]

/-- The rational kernel of `φ`. -/
def Lq {ι : Type} [Fintype ι] {q : ℕ} (φ : Fin q → ι → ℤ) : Submodule ℚ (ι → ℚ) where
  carrier := {r | ∀ k, ∑ i, (φ k i : ℚ) * r i = 0}
  add_mem' {r s} hr hs k := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib] at *
    rw [hr k, hs k, add_zero]
  zero_mem' k := by simp
  smul_mem' c r hr k := by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at *
    rw [← mul_zero c, ← hr k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- The coordinatewise cast `ℚ^ι → ℂ^ι`. -/
def castL {ι : Type} : (ι → ℚ) →ₗ[ℚ] (ι → ℂ) where
  toFun r i := (r i : ℂ)
  map_add' r s := by funext i; simp
  map_smul' c r := by funext i; simp [Rat.smul_def]

theorem castL_mem {ι : Type} [Fintype ι] {q : ℕ} (φ : Fin q → ι → ℤ) {r : ι → ℚ}
    (hr : r ∈ Lq φ) (k : Fin q) : ∑ i, (φ k i : ℂ) * castL r i = 0 := by
  have := congrArg (fun x : ℚ => (x : ℂ)) (hr k)
  simpa [castL] using this

/-- Every complex kernel vector is a ℂ-combination of rational kernel vectors. -/
theorem mem_span_of_ker {ι : Type} [Fintype ι] {q : ℕ} (φ : Fin q → ι → ℤ) (y : ι → ℂ)
    (hy : ∀ k, ∑ i, (φ k i : ℂ) * y i = 0) :
    y ∈ Submodule.span ℂ (castL '' (Lq φ : Set (ι → ℚ))) := by
  set C := Submodule.span ℚ (Set.range y)
  have : FiniteDimensional ℚ C := FiniteDimensional.span_of_finite ℚ (Set.finite_range y)
  set c := Module.finBasis ℚ C
  set e := c.equivFun
  let yC : ι → C := fun i => ⟨y i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hsum0 : ∀ k, ∑ i, (φ k i : ℚ) • yC i = 0 := by
    intro k
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, yC, Rat.smul_def,
      Rat.cast_intCast]
    exact hy k
  have hr : ∀ t, (fun i => e (yC i) t) ∈ Lq φ := by
    intro t k
    have := congrArg (fun x => e x t) (hsum0 k)
    simpa [map_sum, map_smul] using this
  have hyexp : y = ∑ t, ((c t : C) : ℂ) • castL (fun i => e (yC i) t) := by
    funext i
    have := congrArg Subtype.val (c.sum_equivFun (yC i))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Rat.smul_def, yC] at this
    rw [Finset.sum_apply]
    refine this.symm.trans (Finset.sum_congr rfl fun t _ => ?_)
    simp [castL, e, yC, mul_comm]
  rw [hyexp]
  exact Submodule.sum_mem _ fun t _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hr t, rfl⟩)

/-- The ℂ-span of the casts of `L_ℚ` has dimension at most `dim_ℚ L_ℚ`. -/
theorem finrank_span_cast_le {ι : Type} [Fintype ι] (L : Submodule ℚ (ι → ℚ)) :
    Module.finrank ℂ ↥(Submodule.span ℂ (castL '' (L : Set (ι → ℚ)))) ≤ Module.finrank ℚ L := by
  set b := Module.finBasis ℚ L
  have hle : Submodule.span ℂ (castL '' (L : Set (ι → ℚ))) ≤
      Submodule.span ℂ (Set.range fun j => castL ((b j : L) : ι → ℚ)) := by
    rw [Submodule.span_le]
    rintro _ ⟨r, hr, rfl⟩
    have h := congrArg (fun x : L => castL (x : ι → ℚ)) (b.sum_equivFun ⟨r, hr⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul] at h
    rw [← h]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  refine (Submodule.finrank_mono hle).trans ?_
  have := finrank_range_le_card (R := ℂ) (fun j => castL ((b j : L) : ι → ℚ))
  simpa [Set.finrank] using this

/-- Some `dim W` coordinates separate the points of `W`. -/
theorem exists_coords {d : ℕ} (W : Submodule ℂ (Fin d → ℂ)) :
    ∃ (κ : Type) (a : κ → Fin d) (_ : Fintype κ), Fintype.card κ ≤ Module.finrank ℂ W ∧
      ∀ x ∈ W, (∀ j, x (a j) = 0) → x = 0 := by
  let f : Fin d → Module.Dual ℂ W := fun i => (LinearMap.proj i).comp W.subtype
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℂ f
  have : Fintype κ := Fintype.ofInjective a ha
  refine ⟨κ, a, inferInstance, ?_, ?_⟩
  · have := hli.fintype_card_le_finrank
    rwa [Subspace.dual_finrank_eq] at this
  · intro x hx h0
    have hall : ∀ g ∈ Submodule.span ℂ (Set.range (f ∘ a)), g ⟨x, hx⟩ = 0 := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem g hg => obtain ⟨j, rfl⟩ := hg; exact h0 j
      | zero => rfl
      | add g h _ _ hg hh => simp [hg, hh]
      | smul c g _ hg => simp [hg]
    funext i
    have := hall (f i) (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
    simpa [f] using this

/-- The ℚ-dimension count. -/
theorem finrank_le_of_maps {d m : ℕ} (ω : Fin m → ℂ) (hω : LinearIndependent ℚ ω)
    (L : Submodule ℚ (Fin m × Fin d → ℚ)) (W : Submodule ℂ (Fin d → ℂ))
    (hW : ∀ r ∈ L, Ups1 d m ω (castL r) ∈ W) :
    Module.finrank ℚ L ≤ m * Module.finrank ℂ W := by
  obtain ⟨κ, a, _, hcard, hinj⟩ := exists_coords W
  let G : (Fin m × Fin d → ℚ) →ₗ[ℚ] (κ × Fin m → ℚ) :=
    { toFun := fun r p => r (p.2, a p.1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hG : Function.Injective (G ∘ₗ L.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have hr' : ∀ j k, (r : Fin m × Fin d → ℚ) (k, a j) = 0 := fun j k =>
      congrFun hr (j, k)
    have h1 : Ups1 d m ω (castL (r : Fin m × Fin d → ℚ)) = 0 := by
      refine hinj _ (hW r r.2) fun j => ?_
      rw [Ups1_apply]
      simp [castL, hr' j]
    apply Subtype.ext
    funext ⟨k, i⟩
    have h2 := congrFun h1 i
    rw [Ups1_apply] at h2
    have h3 := Fintype.linearIndependent_iff.mp hω (fun k => (r : Fin m × Fin d → ℚ) (k, i))
      (by simpa [Rat.smul_def, castL, mul_comm] using h2) k
    simpa using h3
  have := LinearMap.finrank_le_finrank_of_injective hG
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at this
  calc Module.finrank ℚ L ≤ Fintype.card κ * m := this
    _ ≤ Module.finrank ℂ W * m := Nat.mul_le_mul_right _ hcard
    _ = m * Module.finrank ℂ W := Nat.mul_comm _ _

end RC1_IK

open DiazModulus RC1_IK in
theorem solution {d m q : ℕ} (ω : Fin m → ℂ) (hωQ : LinearIndependent ℚ ω)
    (hωalg : ∀ a, ω a ∈ Qbar) (φ : Fin q → Fin m × Fin d → ℤ) (L₁ : Submodule ℂ (Fin m × Fin d → ℂ))
    (hL₁ : ∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0) :
    Module.finrank ℂ ↥(L₁) ≤ m * Module.finrank ℂ ↥(L₁.map (LinearMap.pi fun i : Fin d =>
        ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ))) ∧
    Submodule.span ℂ {v : Fin d → ℂ | v ∈ L₁.map (LinearMap.pi fun i : Fin d =>
        ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ)) ∧ ∀ i, v i ∈ Qbar} = L₁.map (LinearMap.pi fun i : Fin d =>
        ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ)) := by
  change Module.finrank ℂ ↥L₁ ≤ m * Module.finrank ℂ ↥(L₁.map (Ups1 d m ω)) ∧
    Submodule.span ℂ {v : Fin d → ℂ | v ∈ L₁.map (Ups1 d m ω) ∧ ∀ i, v i ∈ Qbar} =
      L₁.map (Ups1 d m ω)
  have hcastL : ∀ r ∈ Lq φ, castL r ∈ L₁ := fun r hr => (hL₁ _).mpr (castL_mem φ hr)
  have hspan : L₁ = Submodule.span ℂ (castL '' (Lq φ : Set (Fin m × Fin d → ℚ))) := by
    apply le_antisymm
    · intro y hy
      exact mem_span_of_ker φ y ((hL₁ y).mp hy)
    · rw [Submodule.span_le]
      rintro _ ⟨r, hr, rfl⟩
      exact hcastL r hr
  refine ⟨?_, ?_⟩
  · calc Module.finrank ℂ ↥L₁ ≤ Module.finrank ℚ (Lq φ) := by
          rw [hspan]; exact finrank_span_cast_le _
      _ ≤ m * Module.finrank ℂ ↥(L₁.map (Ups1 d m ω)) :=
          finrank_le_of_maps ω hωQ _ _ fun r hr => Submodule.mem_map_of_mem (hcastL r hr)
  · apply le_antisymm
    · rw [Submodule.span_le]
      exact fun v hv => hv.1
    · conv_lhs => rw [hspan]
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      refine ⟨Submodule.mem_map_of_mem (hcastL r hr), fun i => ?_⟩
      rw [Ups1_apply]
      exact Qbar.sum_mem fun k _ => Qbar.mul_mem (hωalg k) (SubfieldClass.ratCast_mem Qbar _)
