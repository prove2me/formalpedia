-- Prove2me | solution 1 for DiazModulus.roy_period_space
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-13T10:03:29.778618+00:00
-- url     : https://prove2.me/submissions/57c296eb-05a1-4f3e-b271-974d5e189b89

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The period space `R = T ⊔ span F`

Write `R := T ⊔ span_ℂ F`. (a) Every `x ∈ F` is `τ + c κ` with `τ ∈ T` and `κ` algebraic; then
`κ = c⁻¹ (x − τ) ∈ R`, so `R` is spanned by `T`'s algebraic vectors and these `κ`: `R` is rational.
(b) Let `P` be the `Q̄`-subspace of pairs `(x, κ)` with `x ∈ F`, `κ ∈ Q̄^d` and `x − c κ ∈ T`; it is
finite-dimensional. Its first projection is onto `F`, with kernel `{(0, κ) : κ ∈ T ∩ Q̄^d}`, whose
`ℂ`-span contains `T` (T is rational), so the kernel has `Q̄`-dimension `≥ dim T`. Its second
projection has kernel `≅` a subspace of `F ⊓ T` (via `x`), and image a `Q̄`-space of algebraic
vectors of `R`. Base change: `Q̄`-independent algebraic vectors are `ℂ`-independent (if
`Σ a_i v_i = 0` with `a_{i₀} ≠ 0`, apply a `Q̄`-linear form `φ : ℂ → Q̄` with `φ a_{i₀} ≠ 0`
coordinatewise to get a `Q̄`-relation), so the image has `Q̄`-dimension `≤ dim R`. Rank–nullity
twice gives `dim F + dim T ≤ dim P ≤ dim (F ⊓ T) + dim R`. (c) `span F ≤ U`, hence
`U ⊔ R = U ⊔ T`, and the dimension formula for `U, R` and for `U, T` gives the last identity. -/

namespace RC1_PER
open DiazModulus

/-- `Q̄`-linearly independent algebraic vectors of `ℂ^d` are `ℂ`-linearly independent. -/
theorem linearIndependent_complex {ι : Type*} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℂ)
    (hv : ∀ i j, v i j ∈ Qbar) (hli : LinearIndependent (↥Qbar) v) : LinearIndependent ℂ v := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro a ha i
  by_contra hai
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero (↥Qbar) hai
  refine hφ (hli (fun j => φ (a j)) ?_ i)
  funext m
  have hm := congr_fun ha m
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hm ⊢
  have key : ∀ j, (φ (a j) • v j m : ℂ) = ((φ ((⟨v j m, hv j m⟩ : ↥Qbar) • a j) : ↥Qbar) : ℂ) := by
    intro j
    rw [map_smul, smul_eq_mul, Subfield.coe_mul, Subfield.smul_def, smul_eq_mul, mul_comm]
  simp only [key]
  have hsum : ∑ j, ((φ ((⟨v j m, hv j m⟩ : ↥Qbar) • a j) : ↥Qbar) : ℂ) =
      ((φ (∑ j, (⟨v j m, hv j m⟩ : ↥Qbar) • a j) : ↥Qbar) : ℂ) := by
    rw [map_sum]; exact (map_sum Qbar.subtype _ _).symm
  have : ∑ j, ((⟨v j m, hv j m⟩ : ↥Qbar) • a j) = ∑ j, a j * v j m := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subfield.smul_def, smul_eq_mul, mul_comm]
  rw [hsum, this, hm, map_zero]
  rfl

/-- The `ℂ`-span of a finite-dimensional `Q̄`-subspace has `ℂ`-dimension at most its `Q̄`-dimension. -/
theorem finrank_span_le {d : ℕ} (N : Submodule (↥Qbar) (Fin d → ℂ)) [FiniteDimensional (↥Qbar) N] :
    Module.finrank ℂ (Submodule.span ℂ (N : Set (Fin d → ℂ))) ≤ Module.finrank (↥Qbar) N := by
  let b := Module.finBasis (↥Qbar) N
  have h : Submodule.span ℂ (N : Set (Fin d → ℂ)) ≤
      Submodule.span ℂ (Set.range (N.subtype ∘ b)) := by
    rw [Submodule.span_le]
    intro x hx
    have hx' : x = N.subtype (∑ i, b.repr ⟨x, hx⟩ i • b i) := by rw [b.sum_repr]; rfl
    rw [hx', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  calc Module.finrank ℂ (Submodule.span ℂ (N : Set (Fin d → ℂ)))
      ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range (N.subtype ∘ b))) := Submodule.finrank_mono h
    _ ≤ Fintype.card (Fin (Module.finrank (↥Qbar) N)) := finrank_range_le_card _
    _ = Module.finrank (↥Qbar) N := Fintype.card_fin _

/-- A finite-dimensional `Q̄`-space of algebraic vectors inside `R` has `Q̄`-dimension `≤ dim_ℂ R`. -/
theorem finrank_alg_le {d : ℕ} (N : Submodule (↥Qbar) (Fin d → ℂ)) [FiniteDimensional (↥Qbar) N]
    (R : Submodule ℂ (Fin d → ℂ)) (hN : ∀ v ∈ N, (∀ i, v i ∈ Qbar) ∧ v ∈ R) :
    Module.finrank (↥Qbar) N ≤ Module.finrank ℂ R := by
  let b := Module.finBasis (↥Qbar) N
  have hli : LinearIndependent ℂ (N.subtype ∘ b) :=
    linearIndependent_complex _ (fun i => (hN _ (b i).2).1)
      (b.linearIndependent.map' N.subtype (Submodule.ker_subtype N))
  have hle : Submodule.span ℂ (Set.range (N.subtype ∘ b)) ≤ R := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (hN _ (b i).2).2
  calc Module.finrank (↥Qbar) N = Fintype.card (Fin (Module.finrank (↥Qbar) N)) :=
        (Fintype.card_fin _).symm
    _ = Module.finrank ℂ (Submodule.span ℂ (Set.range (N.subtype ∘ b))) :=
        (finrank_span_eq_card hli).symm
    _ ≤ Module.finrank ℂ R := Submodule.finrank_mono hle

/-- The pairs `(x, κ)`, `x ∈ F`, `κ` algebraic, `x − c κ ∈ T`. -/
noncomputable def pairs {d : ℕ} (c : ℂ) (T : Submodule ℂ (Fin d → ℂ))
    (F : Submodule (↥Qbar) (Fin d → ℂ)) : Submodule (↥Qbar) ((Fin d → ℂ) × (Fin d → ℂ)) where
  carrier := {z | z.1 ∈ F ∧ (∀ i, z.2 i ∈ Qbar) ∧ z.1 - c • z.2 ∈ T}
  add_mem' := by
    rintro ⟨x, κ⟩ ⟨x', κ'⟩ ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨F.add_mem h1 h1', fun i => Qbar.add_mem (h2 i) (h2' i), ?_⟩
    have := T.add_mem h3 h3'
    convert this using 1
    simp only [Prod.fst_add, Prod.snd_add, smul_add]
    abel
  zero_mem' := ⟨F.zero_mem, fun i => Qbar.zero_mem, by simp⟩
  smul_mem' := by
    rintro a ⟨x, κ⟩ ⟨h1, h2, h3⟩
    refine ⟨F.smul_mem a h1, fun i => ?_, ?_⟩
    · show a • κ i ∈ Qbar
      rw [Subfield.smul_def, smul_eq_mul]
      exact Qbar.mul_mem a.2 (h2 i)
    · have := T.smul_of_tower_mem a h3
      convert this using 1
      simp only [Prod.smul_fst, Prod.smul_snd]
      rw [smul_sub, smul_comm a c κ]

/-- The two projections of the space of pairs. -/
noncomputable def pr1 {d : ℕ} (c : ℂ) (T : Submodule ℂ (Fin d → ℂ))
    (F : Submodule (↥Qbar) (Fin d → ℂ)) : pairs c T F →ₗ[↥Qbar] (Fin d → ℂ) :=
  (LinearMap.fst _ _ _).comp (pairs c T F).subtype

noncomputable def pr2 {d : ℕ} (c : ℂ) (T : Submodule ℂ (Fin d → ℂ))
    (F : Submodule (↥Qbar) (Fin d → ℂ)) : pairs c T F →ₗ[↥Qbar] (Fin d → ℂ) :=
  (LinearMap.snd _ _ _).comp (pairs c T F).subtype

theorem pairs_finiteDimensional {d : ℕ} (c : ℂ) (T : Submodule ℂ (Fin d → ℂ))
    (F : Submodule (↥Qbar) (Fin d → ℂ)) [FiniteDimensional (↥Qbar) F] :
    FiniteDimensional (↥Qbar) (pairs c T F) := by
  let f := LinearMap.prodMap F.subtype (LinearMap.compLeft (Algebra.linearMap (↥Qbar) ℂ) (Fin d))
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range f) ?_
  rintro ⟨x, κ⟩ ⟨h1, h2, _⟩
  exact ⟨(⟨x, h1⟩, fun i => ⟨κ i, h2 i⟩), rfl⟩

/-- The count: `dim F + dim T ≤ dim P ≤ dim (F ⊓ T) + dim R`. -/
theorem pairs_count {d : ℕ} (c : ℂ) (T R : Submodule ℂ (Fin d → ℂ))
    (hT : Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T)
    (F : Submodule (↥Qbar) (Fin d → ℂ)) [FiniteDimensional (↥Qbar) F]
    (hF : ∀ x ∈ F, ∃ κ : Fin d → ℂ, (∀ i, κ i ∈ Qbar) ∧ x - c • κ ∈ T)
    (hκR : ∀ x ∈ F, ∀ κ : Fin d → ℂ, x - c • κ ∈ T → κ ∈ R) :
    Module.finrank (↥Qbar) F + Module.finrank ℂ T ≤
      Module.finrank (↥Qbar) ↥(F ⊓ T.restrictScalars (↥Qbar)) + Module.finrank ℂ R := by
  have := pairs_finiteDimensional c T F
  have e1 := LinearMap.finrank_range_add_finrank_ker (pr1 c T F)
  have e2 := LinearMap.finrank_range_add_finrank_ker (pr2 c T F)
  -- the first projection is onto `F`
  have r1 : LinearMap.range (pr1 c T F) = F := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩; exact z.2.1
    · intro x hx
      obtain ⟨κ, hκ, hxκ⟩ := hF x hx
      exact ⟨⟨(x, κ), hx, hκ, hxκ⟩, rfl⟩
  -- its kernel `{(0, κ) : κ ∈ T ∩ Q̄^d}` spans `T`
  have k1 : Module.finrank ℂ T ≤ Module.finrank (↥Qbar) (LinearMap.ker (pr1 c T F)) := by
    have hle : T ≤ Submodule.span ℂ
        (((LinearMap.ker (pr1 c T F)).map (pr2 c T F) : Submodule (↥Qbar) (Fin d → ℂ)) :
          Set (Fin d → ℂ)) := by
      conv_lhs => rw [← hT]
      refine Submodule.span_mono ?_
      rintro v ⟨hvT, hva⟩
      have hz : ((0 : Fin d → ℂ), v) ∈ pairs c T F :=
        ⟨F.zero_mem, hva, by rw [zero_sub]; exact T.neg_mem (T.smul_mem c hvT)⟩
      exact ⟨⟨_, hz⟩, LinearMap.mem_ker.2 rfl, rfl⟩
    exact (Submodule.finrank_mono hle).trans
      ((finrank_span_le _).trans (Submodule.finrank_map_le _ _))
  -- the second projection lands in the algebraic vectors of `R`
  have k2 : Module.finrank (↥Qbar) (LinearMap.range (pr2 c T F)) ≤ Module.finrank ℂ R := by
    apply finrank_alg_le
    rintro _ ⟨z, rfl⟩
    exact ⟨z.2.2.1, hκR _ z.2.1 _ z.2.2.2⟩
  -- its kernel embeds into `F ⊓ T` via the first coordinate
  have k3 : Module.finrank (↥Qbar) (LinearMap.ker (pr2 c T F)) ≤
      Module.finrank (↥Qbar) ↥(F ⊓ T.restrictScalars (↥Qbar)) := by
    have hinj : Function.Injective ((pr1 c T F).comp (LinearMap.ker (pr2 c T F)).subtype) := by
      rintro ⟨z, hz⟩ ⟨z', hz'⟩ h
      have h2 : (z : (Fin d → ℂ) × (Fin d → ℂ)).2 = (z' : (Fin d → ℂ) × (Fin d → ℂ)).2 :=
        (LinearMap.mem_ker.1 hz).trans (LinearMap.mem_ker.1 hz').symm
      exact Subtype.ext (Subtype.ext (Prod.ext h h2))
    rw [← LinearMap.finrank_range_of_inj hinj]
    refine Submodule.finrank_mono ?_
    rintro _ ⟨⟨z, hz⟩, rfl⟩
    have hz2 : (z : (Fin d → ℂ) × (Fin d → ℂ)).2 = 0 := LinearMap.mem_ker.1 hz
    have h3 := z.2.2.2
    rw [hz2, smul_zero, sub_zero] at h3
    exact Submodule.mem_inf.2 ⟨z.2.1, h3⟩
  rw [r1] at e1
  omega

end RC1_PER

open DiazModulus RC1_PER in
theorem solution {d : ℕ} (c : ℂ) (hc : c ≠ 0) (T U : Submodule ℂ (Fin d → ℂ))
    (hT : Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T)
    (F : Submodule (↥Qbar) (Fin d → ℂ)) (hFfin : FiniteDimensional (↥Qbar) ↥F) (hFU : ∀ x ∈ F, x ∈ U)
    (hF : ∀ x ∈ F, ∃ τ ∈ T, ∃ κ : Fin d → ℂ, (∀ i, κ i ∈ Qbar) ∧ x = τ + c • κ) :
    Submodule.span ℂ {v : Fin d → ℂ | v ∈ (T ⊔ Submodule.span ℂ (F : Set (Fin d → ℂ))) ∧ ∀ i, v i ∈ Qbar} = (T ⊔ Submodule.span ℂ (F : Set (Fin d → ℂ))) ∧
    Module.finrank (↥Qbar) ↥F + Module.finrank ℂ ↥(T) ≤
      Module.finrank (↥Qbar) ↥(F ⊓ T.restrictScalars (↥Qbar)) + Module.finrank ℂ ↥(T ⊔ Submodule.span ℂ (F : Set (Fin d → ℂ))) ∧
    Module.finrank ℂ ↥(U ⊓ (T ⊔ Submodule.span ℂ (F : Set (Fin d → ℂ)))) + Module.finrank ℂ ↥(T) = Module.finrank ℂ ↥(U ⊓ T) + Module.finrank ℂ ↥(T ⊔ Submodule.span ℂ (F : Set (Fin d → ℂ))) := by
  classical
  have := hFfin
  set R := T ⊔ Submodule.span ℂ (F : Set (Fin d → ℂ)) with hR
  have hTR : T ≤ R := le_sup_left
  have hFR : ∀ x ∈ F, x ∈ R := fun x hx => Submodule.mem_sup_right (Submodule.subset_span hx)
  have hκR : ∀ x ∈ F, ∀ κ : Fin d → ℂ, x - c • κ ∈ T → κ ∈ R := by
    intro x hx κ hκ
    have h1 : c • κ ∈ R := by
      have := R.sub_mem (hFR x hx) (hTR hκ)
      rwa [sub_sub_cancel] at this
    have := R.smul_mem c⁻¹ h1
    rwa [inv_smul_smul₀ hc] at this
  refine ⟨?_, ?_, ?_⟩
  · -- (a) `R` is rational
    apply le_antisymm
    · rw [Submodule.span_le]; exact fun v hv => hv.1
    · have hTX : T ≤ Submodule.span ℂ {v : Fin d → ℂ | v ∈ R ∧ ∀ i, v i ∈ Qbar} := by
        conv_lhs => rw [← hT]
        exact Submodule.span_mono fun v hv => ⟨hTR hv.1, hv.2⟩
      refine sup_le hTX ?_
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨τ, hτ, κ, hκ, rfl⟩ := hF x hx
      refine Submodule.add_mem _ (hTX hτ) (Submodule.smul_mem _ c (Submodule.subset_span ⟨?_, hκ⟩))
      exact hκR _ hx κ (by rwa [add_sub_cancel_right])
  · -- (b) the dimension count through the space of pairs
    refine pairs_count c T R hT F (fun x hx => ?_) hκR
    obtain ⟨τ, hτ, κ, hκ, hx'⟩ := hF x hx
    exact ⟨κ, hκ, by rw [hx', add_sub_cancel_right]; exact hτ⟩
  · -- (c) `U ⊔ R = U ⊔ T` and the dimension formula
    have hUR : U ⊔ R = U ⊔ T := by
      apply le_antisymm
      · refine sup_le le_sup_left (sup_le le_sup_right ?_)
        exact (Submodule.span_le.2 fun x hx => hFU x hx).trans le_sup_left
      · exact sup_le le_sup_left (hTR.trans le_sup_right)
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U R
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq U T
    rw [hUR] at h1
    omega
