-- Prove2me | solution 1 for DiazModulus.roy_rat_theorem_five
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T17:33:44.283904+00:00
-- url     : https://prove2.me/submissions/fb418bd7-de37-4ce0-8a81-817951b3ce95

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_multiplicityEstimateElem
import Theorems.Thm_DiazModulus_roy_rat_slope_bound
import Theorems.Thm_DiazModulus_roy_rat_adapted_basis

open Complex ComplexConjugate

/-! # Roy's Theorem 5 over ℚ, Harder–Narasimhan form

Let `U ≤ ℂ^d` contain no nonzero rational vector and let `z` be `ℓ` vectors of `U`, `ℚ`-free, with coordinates
in `ℚ + ℒ`. We find a rational `S ⊇ U` and a decomposition `D` of `(dim U, dim S)` into pairs `0 < nᵢ < dᵢ`
with `ℓ ≤ Σ nᵢdᵢ/(dᵢ − nᵢ)`, by strong induction on `d`. If `U = 0` then `ℓ = 0`, and `S = 0`, `D = []`.
Otherwise pick a rational `S₁ ≠ 0` of maximal slope `u₁/s₁`, `u₁ = dim(U ⊓ S₁)`, `s₁ = dim S₁`. Then `u₁ ≥ 1`
(compare with `ℂ^d`) and `u₁ < s₁` (otherwise `S₁ ⊆ U` would contain a nonzero rational vector). A rational
adapted basis of `S₁` identifies `S₁` with `ℂ^{s₁}` and gives a projection `π : ℂ^d → ℂ^{d−s₁}` with kernel
`S₁` and a rational section. By maximality, `U ⊓ S₁ ⊂ ℂ^{s₁}` satisfies the slope hypothesis with
`(a, b) = (u₁, s₁)`, and the slope bound gives `dim_ℚ(Z ⊓ S₁) ≤ u₁s₁/(s₁ − u₁)`, `Z` the span of `z`. Also
`π(U)` satisfies `s₁·dim(π U ⊓ S') ≤ u₁·dim S'` for rational `S'`, so it has no nonzero rational vector, and
the induction hypothesis on a `ℚ`-basis of `π(Z)` gives `S'` and `D'`. Then `S = π⁻¹(S')` is rational,
contains `U`, has dimension `s₁ + dim S'`, and `(u₁, s₁) :: D'` bounds `ℓ = dim_ℚ(Z ⊓ S₁) + dim_ℚ π(Z)`. -/

namespace RC5_T5Q
open DiazModulus

/-- A rational subspace: spanned by its vectors with rational coordinates. -/
abbrev IsRat {d : ℕ} (S : Submodule ℂ (Fin d → ℂ)) : Prop :=
  Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S

/-- The rationals inside `ℂ`, as a `ℚ`-submodule. -/
noncomputable def Mq : Submodule ℚ ℂ := Submodule.span ℚ {(1 : ℂ)}

theorem mem_Mq (x : ℂ) : x ∈ Mq ↔ ∃ q : ℚ, x = (q : ℂ) := by
  rw [Mq, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨q, rfl⟩; exact ⟨q, Rat.smul_one_eq_cast ℂ q⟩
  · rintro ⟨q, rfl⟩; exact ⟨q, Rat.smul_one_eq_cast ℂ q⟩

theorem isRat_span {d : ℕ} (X : Set (Fin d → ℂ)) (hX : ∀ v ∈ X, ∀ i, ∃ q : ℚ, v i = (q : ℂ)) :
    IsRat (Submodule.span ℂ X) :=
  le_antisymm (Submodule.span_le.mpr fun _ hv => hv.1)
    (Submodule.span_le.mpr fun v hv => Submodule.subset_span ⟨Submodule.subset_span hv, hX v hv⟩)

theorem isRat_bot {d : ℕ} : IsRat (⊥ : Submodule ℂ (Fin d → ℂ)) := by
  rw [← Submodule.span_empty]; exact isRat_span _ (by simp)

theorem isRat_top {d : ℕ} : IsRat (⊤ : Submodule ℂ (Fin d → ℂ)) := by
  rw [← (Pi.basisFun ℂ (Fin d)).span_eq]
  refine isRat_span _ ?_
  rintro _ ⟨j, rfl⟩ i
  rw [Pi.basisFun_apply, Pi.single_apply]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem isRat_map {d e : ℕ} (f : (Fin d → ℂ) →ₗ[ℂ] (Fin e → ℂ))
    (hf : ∀ v, (∀ i, ∃ q : ℚ, v i = (q : ℂ)) → ∀ i, ∃ q : ℚ, f v i = (q : ℂ))
    {S : Submodule ℂ (Fin d → ℂ)} (hS : IsRat S) : IsRat (S.map f) := by
  obtain ⟨X, hX, rfl⟩ : ∃ X : Set (Fin d → ℂ), (∀ v ∈ X, ∀ i, ∃ q : ℚ, v i = (q : ℂ)) ∧
      Submodule.span ℂ X = S := ⟨_, fun _ hv => hv.2, hS⟩
  rw [Submodule.map_span]
  exact isRat_span _ (by rintro _ ⟨v, hv, rfl⟩; exact hf v (hX v hv))

theorem isRat_sup {d : ℕ} {S T : Submodule ℂ (Fin d → ℂ)} (hS : IsRat S) (hT : IsRat T) :
    IsRat (S ⊔ T) := by
  obtain ⟨X, hX, rfl⟩ : ∃ X : Set (Fin d → ℂ), (∀ v ∈ X, ∀ i, ∃ q : ℚ, v i = (q : ℂ)) ∧
      Submodule.span ℂ X = S := ⟨_, fun _ hv => hv.2, hS⟩
  obtain ⟨Y, hY, rfl⟩ : ∃ Y : Set (Fin d → ℂ), (∀ v ∈ Y, ∀ i, ∃ q : ℚ, v i = (q : ℂ)) ∧
      Submodule.span ℂ Y = T := ⟨_, fun _ hv => hv.2, hT⟩
  rw [← Submodule.span_union]
  exact isRat_span _ (by rintro v (hv | hv); exacts [hX v hv, hY v hv])

/-! ### Quotient transport: `π` with kernel `S₁` and a section `σ` -/

section quot
variable {d e : ℕ} (π : (Fin d → ℂ) →ₗ[ℂ] (Fin e → ℂ)) (σ : (Fin e → ℂ) →ₗ[ℂ] (Fin d → ℂ))
  (S₁ : Submodule ℂ (Fin d → ℂ)) (hπσ : ∀ w, π (σ w) = w) (hker : ∀ v, π v = 0 ↔ v ∈ S₁)
include hπσ hker

theorem q_comap_eq (T : Submodule ℂ (Fin e → ℂ)) : T.comap π = S₁ ⊔ T.map σ := by
  apply le_antisymm
  · intro v hv
    have h1 : v - σ (π v) ∈ S₁ := (hker _).mp (by simp [hπσ])
    have h2 : σ (π v) ∈ T.map σ := ⟨π v, hv, rfl⟩
    simpa using Submodule.add_mem_sup h1 h2
  · refine sup_le (fun v hv => ?_) ?_
    · show π v ∈ T
      rw [(hker v).mpr hv]; exact T.zero_mem
    · rintro _ ⟨w, hw, rfl⟩
      show π (σ w) ∈ T
      rw [hπσ]; exact hw

theorem q_finrank_comap (T : Submodule ℂ (Fin e → ℂ)) :
    Module.finrank ℂ ↥(T.comap π) = Module.finrank ℂ ↥S₁ + Module.finrank ℂ ↥T := by
  have hσ : Function.Injective σ := fun x y h => by rw [← hπσ x, ← hπσ y, h]
  have hinf : S₁ ⊓ T.map σ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hv1, ⟨w, -, rfl⟩⟩
    have : w = 0 := by rw [← hπσ w]; exact (hker _).mpr hv1
    simp [this]
  have h := Submodule.finrank_sup_add_finrank_inf_eq S₁ (T.map σ)
  rw [hinf, finrank_bot, add_zero] at h
  rw [q_comap_eq π σ S₁ hπσ hker, h, ← (Submodule.equivMapOfInjective σ hσ T).finrank_eq]

omit hπσ in
theorem q_modular (U : Submodule ℂ (Fin d → ℂ)) (T : Submodule ℂ (Fin e → ℂ)) :
    Module.finrank ℂ ↥(U.map π ⊓ T) + Module.finrank ℂ ↥(U ⊓ S₁) =
      Module.finrank ℂ ↥(U ⊓ T.comap π) := by
  have heq : U.map π ⊓ T = (U ⊓ T.comap π).map π := by
    apply le_antisymm
    · rintro _ ⟨⟨u, hu, rfl⟩, ht⟩; exact ⟨u, ⟨hu, ht⟩, rfl⟩
    · rintro _ ⟨u, ⟨hu, ht⟩, rfl⟩; exact ⟨⟨u, hu, rfl⟩, ht⟩
  have hle : U ⊓ S₁ ≤ U ⊓ T.comap π := inf_le_inf_left _ fun v hv => by
    show π v ∈ T
    rw [(hker v).mpr hv]; exact T.zero_mem
  have h := LinearMap.finrank_range_add_finrank_ker (π.domRestrict (U ⊓ T.comap π))
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have he : (LinearMap.ker π).comap (U ⊓ T.comap π).subtype
      = (U ⊓ S₁).comap (U ⊓ T.comap π).subtype := by
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, LinearMap.mem_ker, Submodule.subtype_apply, Submodule.mem_inf, hker]
    exact ⟨fun h => ⟨hx.1, h⟩, fun h => h.2⟩
  rw [he, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at h
  rw [heq]; exact h

omit hπσ in
theorem q_finrank_map (U : Submodule ℂ (Fin d → ℂ)) :
    Module.finrank ℂ ↥(U.map π) + Module.finrank ℂ ↥(U ⊓ S₁) = Module.finrank ℂ ↥U := by
  have h := q_modular π S₁ hker U ⊤
  rwa [inf_top_eq, Submodule.comap_top, inf_top_eq] at h

omit hπσ in
theorem q_finrankQ (Z : Submodule ℚ (Fin d → ℂ)) [FiniteDimensional ℚ ↥Z] :
    Module.finrank ℚ ↥(Z.map (π.restrictScalars ℚ)) +
      Module.finrank ℚ ↥(Z ⊓ S₁.restrictScalars ℚ) = Module.finrank ℚ ↥Z := by
  have h := LinearMap.finrank_range_add_finrank_ker ((π.restrictScalars ℚ).domRestrict Z)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have he : (LinearMap.ker (π.restrictScalars ℚ)).comap Z.subtype
      = (Z ⊓ S₁.restrictScalars ℚ).comap Z.subtype := by
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, LinearMap.mem_ker, Submodule.subtype_apply, Submodule.mem_inf,
      LinearMap.restrictScalars_apply, Submodule.restrictScalars_mem, hker]
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  rw [he, (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq] at h
  exact h

end quot

/-! ### Sub-object transport: `ι` onto `S₁` with a left inverse `θ` -/

section sub
variable {d s : ℕ} (ι : (Fin s → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (θ : (Fin d → ℂ) →ₗ[ℂ] (Fin s → ℂ))
  (S₁ : Submodule ℂ (Fin d → ℂ)) (hθι : ∀ w, θ (ι w) = w) (hιS : ∀ w, ι w ∈ S₁)
  (hιθ : ∀ v ∈ S₁, ι (θ v) = v)

theorem s_inj (hθι : ∀ w, θ (ι w) = w) : Function.Injective ι :=
  fun x y h => by rw [← hθι x, ← hθι y, h]

theorem s_finrank_inf (hθι : ∀ w, θ (ι w) = w) (U : Submodule ℂ (Fin d → ℂ))
    (T : Submodule ℂ (Fin s → ℂ)) :
    Module.finrank ℂ ↥(U.comap ι ⊓ T) = Module.finrank ℂ ↥(U ⊓ T.map ι) := by
  have : (U.comap ι ⊓ T).map ι = U ⊓ T.map ι := by
    apply le_antisymm
    · rintro _ ⟨w, ⟨hu, ht⟩, rfl⟩; exact ⟨hu, w, ht, rfl⟩
    · rintro _ ⟨hu, w, ht, rfl⟩; exact ⟨w, ⟨hu, ht⟩, rfl⟩
  rw [← this]; exact (Submodule.equivMapOfInjective ι (s_inj ι θ hθι) _).finrank_eq

theorem s_finrank_map (hθι : ∀ w, θ (ι w) = w) (T : Submodule ℂ (Fin s → ℂ)) :
    Module.finrank ℂ ↥(T.map ι) = Module.finrank ℂ ↥T :=
  (Submodule.equivMapOfInjective ι (s_inj ι θ hθι) _).finrank_eq.symm

include hθι hιS hιθ in
theorem s_finrank_comap (U : Submodule ℂ (Fin d → ℂ)) :
    Module.finrank ℂ ↥(U.comap ι) = Module.finrank ℂ ↥(U ⊓ S₁) := by
  have h := s_finrank_inf ι θ hθι U ⊤
  have hr : (⊤ : Submodule ℂ (Fin s → ℂ)).map ι = S₁ := by
    rw [Submodule.map_top]
    exact le_antisymm (by rintro _ ⟨w, rfl⟩; exact hιS w) (fun v hv => ⟨θ v, hιθ v hv⟩)
  rwa [inf_top_eq, hr] at h

end sub

/-! ### The coordinate maps of an adapted basis `g` -/

section coords
variable {d : ℕ} (g : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ)) (s : ℕ)

/-- Coordinates `≥ s` of `g v`. -/
noncomputable def piG : (Fin d → ℂ) →ₗ[ℂ] (Fin (d - s) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun j : Fin (d - s) => (⟨s + j.val, by have := j.isLt; omega⟩ : Fin d))
    ∘ₗ g.toLinearMap

/-- Put `w` in the coordinates `≥ s`. -/
noncomputable def padHi : (Fin (d - s) → ℂ) →ₗ[ℂ] (Fin d → ℂ) where
  toFun w i := if h : s ≤ i.val then w ⟨i.val - s, by have := i.isLt; omega⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c x := by ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

noncomputable def secG : (Fin (d - s) → ℂ) →ₗ[ℂ] (Fin d → ℂ) := g.symm.toLinearMap ∘ₗ padHi s

/-- Coordinates `< s` of `g v`. -/
noncomputable def resG (hs : s ≤ d) : (Fin d → ℂ) →ₗ[ℂ] (Fin s → ℂ) :=
  LinearMap.funLeft ℂ ℂ (Fin.castLE hs) ∘ₗ g.toLinearMap

/-- Put `w` in the coordinates `< s`. -/
noncomputable def padLo : (Fin s → ℂ) →ₗ[ℂ] (Fin d → ℂ) where
  toFun w i := if h : i.val < s then w ⟨i.val, h⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c x := by ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

noncomputable def incG : (Fin s → ℂ) →ₗ[ℂ] (Fin d → ℂ) :=
  g.symm.toLinearMap ∘ₗ padLo (d := d) s

theorem piG_apply (v : Fin d → ℂ) (j : Fin (d - s)) :
    piG g s v j = g v ⟨s + j.val, by have := j.isLt; omega⟩ := rfl

theorem resG_apply (hs : s ≤ d) (v : Fin d → ℂ) (i : Fin s) :
    resG g s hs v i = g v (Fin.castLE hs i) := rfl

theorem piG_secG (w : Fin (d - s) → ℂ) : piG g s (secG g s w) = w := by
  ext j
  simp only [piG_apply, secG, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, padHi, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos (by simp)]
  congr 1; ext; simp

theorem resG_incG (hs : s ≤ d) (w : Fin s → ℂ) : resG g s hs (incG g s w) = w := by
  ext i
  simp only [resG_apply, incG, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, padLo, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_castLE]
  rw [dif_pos i.isLt]

variable {S₁ : Submodule ℂ (Fin d → ℂ)} (hgS : ∀ v, v ∈ S₁ ↔ ∀ i : Fin d, s ≤ i.val → g v i = 0)
include hgS

theorem piG_ker (v : Fin d → ℂ) : piG g s v = 0 ↔ v ∈ S₁ := by
  rw [hgS, funext_iff]
  constructor
  · intro h i hi
    have := h ⟨i.val - s, by have := i.isLt; omega⟩
    rw [piG_apply, Pi.zero_apply] at this
    rw [← this]; exact congrArg (g v) (Fin.ext (by show i.val = s + (i.val - s); omega))
  · intro h j; rw [piG_apply]; exact h _ (by simp)

theorem incG_mem (w : Fin s → ℂ) : incG g s w ∈ S₁ := by
  rw [hgS]; intro i hi
  simp only [incG, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, padLo, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_neg (by omega)]

theorem incG_resG (hs : s ≤ d) (v : Fin d → ℂ) (hv : v ∈ S₁) : incG g s (resG g s hs v) = v := by
  rw [hgS] at hv
  apply g.injective
  ext i
  simp only [incG, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, padLo, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with h
  · rw [resG_apply]; rfl
  · exact (hv i (by omega)).symm

end coords

theorem padHi_rat {d : ℕ} (s : ℕ) (w : Fin (d - s) → ℂ) (hw : ∀ i, ∃ q : ℚ, w i = (q : ℂ))
    (i : Fin d) : padHi (d := d) s w i ∈ Mq := by
  simp only [padHi, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs
  · exact (mem_Mq _).mpr (hw _)
  · exact Mq.zero_mem

theorem padLo_rat {d : ℕ} (s : ℕ) (w : Fin s → ℂ) (hw : ∀ i, ∃ q : ℚ, w i = (q : ℂ)) (i : Fin d) :
    padLo (d := d) s w i ∈ Mq := by
  simp only [padLo, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs
  · exact (mem_Mq _).mpr (hw _)
  · exact Mq.zero_mem

/-! ### Choosing a subspace of maximal slope -/

theorem exists_max_ratio {α : Type*} (C : α → Prop) (x y : α → ℕ) (N : ℕ)
    (hx : ∀ a, C a → x a ≤ N) (hy : ∀ a, C a → y a ≤ N) (hpos : ∀ a, C a → 0 < y a)
    (hne : ∃ a, C a) : ∃ a₀, C a₀ ∧ ∀ a, C a → x a * y a₀ ≤ x a₀ * y a := by
  classical
  let F : Finset (ℕ × ℕ) := ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
    (fun p => ∃ a, C a ∧ x a = p.1 ∧ y a = p.2)
  have hmem : ∀ a, C a → (x a, y a) ∈ F := fun a ha =>
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by have := hx a ha; omega),
      Finset.mem_range.mpr (by have := hy a ha; omega)⟩, a, ha, rfl, rfl⟩
  obtain ⟨a, ha⟩ := hne
  obtain ⟨p, hpF, hpmax⟩ := F.exists_max_image (fun p => (p.1 : ℚ) / p.2) ⟨_, hmem a ha⟩
  obtain ⟨a₀, ha₀, hx₀, hy₀⟩ := (Finset.mem_filter.mp hpF).2
  refine ⟨a₀, ha₀, fun b hb => ?_⟩
  have h := hpmax _ (hmem b hb)
  simp only [← hx₀, ← hy₀] at h
  rw [div_le_div_iff₀ (by exact_mod_cast hpos b hb) (by exact_mod_cast hpos a₀ ha₀)] at h
  exact_mod_cast h

/-! ### The theorem, by strong induction on `d` -/

theorem main : ∀ (d : ℕ) {ℓ : ℕ} (U : Submodule ℂ (Fin d → ℂ)),
    (∀ v ∈ U, (∀ i, ∃ q : ℚ, v i = (q : ℂ)) → v = 0) →
    ∀ (z : Fin ℓ → Fin d → ℂ), (∀ i, z i ∈ U) →
    (∀ i j, z i j ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg)) → LinearIndependent ℚ z →
    ∃ (S : Submodule ℂ (Fin d → ℂ)) (D : List (ℕ × ℕ)),
      IsRat S ∧ U ≤ S ∧ (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧
      (D.map Prod.fst).sum = Module.finrank ℂ ↥U ∧ (D.map Prod.snd).sum = Module.finrank ℂ ↥S ∧
      (ℓ : ℚ) ≤ (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro ℓ U hUQ z hzU hz hzind
  by_cases hU0 : U = ⊥
  · subst hU0
    have hℓ : ℓ = 0 := by
      by_contra h
      exact hzind.ne_zero ⟨0, by omega⟩ ((Submodule.mem_bot ℂ).mp (hzU _))
    subst hℓ
    exact ⟨⊥, [], isRat_bot, le_rfl, by simp, by simp, by simp, by simp⟩
  have hfr : ∀ S : Submodule ℂ (Fin d → ℂ), Module.finrank ℂ ↥S ≤ d :=
    fun S => (Submodule.finrank_le S).trans_eq (Module.finrank_fin_fun ℂ)
  have hpos : ∀ T : Submodule ℂ (Fin d → ℂ), T ≠ ⊥ → 0 < Module.finrank ℂ ↥T :=
    fun T hT => Nat.pos_of_ne_zero (fun h => hT (Submodule.finrank_eq_zero.mp h))
  have htopne : (⊤ : Submodule ℂ (Fin d → ℂ)) ≠ ⊥ := fun h => hU0 (eq_bot_iff.mpr (h ▸ le_top))
  obtain ⟨S₁, ⟨hS₁r, hS₁ne⟩, hmax⟩ := exists_max_ratio
    (fun T : Submodule ℂ (Fin d → ℂ) => IsRat T ∧ T ≠ ⊥)
    (fun T => Module.finrank ℂ ↥(U ⊓ T)) (fun T => Module.finrank ℂ ↥T) d
    (fun T _ => hfr _) (fun T _ => hfr _) (fun T hT => hpos T hT.2) ⟨⊤, isRat_top, htopne⟩
  have hmax' : ∀ T : Submodule ℂ (Fin d → ℂ), IsRat T →
      Module.finrank ℂ ↥(U ⊓ T) * Module.finrank ℂ ↥S₁ ≤
        Module.finrank ℂ ↥(U ⊓ S₁) * Module.finrank ℂ ↥T := by
    intro T hT
    by_cases h0 : T = ⊥
    · subst h0; simp
    · exact hmax T ⟨hT, h0⟩
  have hs₁pos := hpos S₁ hS₁ne
  have hs₁le := hfr S₁
  have hnpos := hpos U hU0
  have hu₁pos : 0 < Module.finrank ℂ ↥(U ⊓ S₁) := by
    have h := hmax' ⊤ isRat_top
    rw [inf_top_eq, finrank_top, Module.finrank_fin_fun] at h
    rcases Nat.eq_zero_or_pos (Module.finrank ℂ ↥(U ⊓ S₁)) with h0 | h0
    · rw [h0, zero_mul] at h
      have := Nat.mul_pos hnpos hs₁pos
      omega
    · exact h0
  have hus : Module.finrank ℂ ↥(U ⊓ S₁) < Module.finrank ℂ ↥S₁ := by
    refine lt_of_le_of_ne (Submodule.finrank_mono inf_le_right) (fun heq => ?_)
    have hS₁U : U ⊓ S₁ = S₁ := Submodule.eq_of_le_of_finrank_eq inf_le_right heq
    by_cases hc : ∀ v ∈ S₁, (∀ i, ∃ q : ℚ, v i = (q : ℂ)) → v = 0
    · exact hS₁ne (by rw [← hS₁r]; exact Submodule.span_eq_bot.mpr (fun v hv => hc v hv.1 hv.2))
    · push Not at hc
      obtain ⟨v, hvS, hvQ, hv0⟩ := hc
      have hvU : v ∈ U ⊓ S₁ := by rw [hS₁U]; exact hvS
      exact hv0 (hUQ v hvU.1 hvQ)
  obtain ⟨g, hgM, hgS⟩ := DiazModulus.roy_rat_adapted_basis S₁ hS₁r
  have hgQ : ∀ v : Fin d → ℂ, (∀ i, v i ∈ Mq) → ∀ i, ∃ q : ℚ, g.symm v i = (q : ℂ) :=
    fun v hv i => (mem_Mq _).mp ((hgM Mq v hv).2 i)
  set s₁ := Module.finrank ℂ ↥S₁ with hs₁
  set u₁ := Module.finrank ℂ ↥(U ⊓ S₁) with hu₁
  -- the span of `z`
  set Zq : Submodule ℚ (Fin d → ℂ) := Submodule.span ℚ (Set.range z) with hZq
  have : FiniteDimensional ℚ ↥Zq := FiniteDimensional.span_of_finite _ (Set.finite_range z)
  have hZU : ∀ x ∈ Zq, x ∈ U := by
    have : Zq ≤ U.restrictScalars ℚ :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hzU i)
    exact fun x hx => this hx
  have hZL : ∀ x ∈ Zq, ∀ j, x j ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg) := by
    have : Zq ≤ Submodule.pi Set.univ (fun _ : Fin d => Submodule.span ℚ (insert (1 : ℂ) LogAlg)) :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact Submodule.mem_pi.mpr (fun j _ => hz i j))
    exact fun x hx j => Submodule.mem_pi.mp (this hx) j (Set.mem_univ j)
  have hℓ : Module.finrank ℚ ↥Zq = ℓ := by rw [finrank_span_eq_card hzind, Fintype.card_fin]
  -- (i) the sub-object `U ⊓ S₁` inside `S₁ ≅ ℂ^{s₁}`: the slope bound
  set ic := incG g s₁
  set rs := resG g s₁ hs₁le
  have hθι : ∀ w, rs (ic w) = w := resG_incG g s₁ hs₁le
  have hιS : ∀ w, ic w ∈ S₁ := incG_mem g s₁ hgS
  have hιθ : ∀ v ∈ S₁, ic (rs v) = v := incG_resG g s₁ hgS hs₁le
  have hicQ : ∀ w : Fin s₁ → ℂ, (∀ i, ∃ q : ℚ, w i = (q : ℂ)) → ∀ i, ∃ q : ℚ, ic w i = (q : ℂ) :=
    fun w hw i => hgQ _ (padLo_rat s₁ w hw) i
  set Z₁ := Zq ⊓ S₁.restrictScalars ℚ
  set b₁ := Module.finBasis ℚ ↥Z₁
  have IH1 : (s₁ - u₁) * Module.finrank ℚ ↥Z₁ ≤ s₁ * Module.finrank ℂ ↥(U.comap ic) := by
    refine DiazModulus.roy_rat_slope_bound DiazModulus.multiplicityEstimateElem (U.comap ic) u₁ s₁ _
      (fun k => rs (b₁ k : Fin d → ℂ)) hus ?_ ?_ ?_ ?_
    · intro T hT
      rw [s_finrank_inf ic rs hθι U T, ← s_finrank_map ic rs hθι T, mul_comm]
      exact hmax' _ (isRat_map ic hicQ hT)
    · intro k
      show ic (rs (b₁ k)) ∈ U
      rw [hιθ _ (b₁ k).2.2]; exact hZU _ (b₁ k).2.1
    · intro k j
      show rs (b₁ k) j ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg)
      rw [resG_apply]; exact (hgM _ _ (hZL _ (b₁ k).2.1)).1 _
    · apply LinearIndependent.of_comp (ic.restrictScalars ℚ)
      have : (ic.restrictScalars ℚ) ∘ (fun k => rs (b₁ k : Fin d → ℂ)) = Z₁.subtype ∘ b₁ := by
        funext k; simp only [Function.comp_apply, LinearMap.restrictScalars_apply]
        exact hιθ _ (b₁ k).2.2
      rw [this]; exact b₁.linearIndependent.map' _ (Submodule.ker_subtype _)
  rw [s_finrank_comap ic rs S₁ hθι hιS hιθ U, ← hu₁] at IH1
  -- (ii) the quotient `π(U)` inside `ℂ^{d - s₁}`: the induction hypothesis
  set pr := piG g s₁
  set sc := secG g s₁
  have hπσ : ∀ w, pr (sc w) = w := piG_secG g s₁
  have hker : ∀ v, pr v = 0 ↔ v ∈ S₁ := piG_ker g s₁ hgS
  have hscQ : ∀ w : Fin (d - s₁) → ℂ, (∀ i, ∃ q : ℚ, w i = (q : ℂ)) →
      ∀ i, ∃ q : ℚ, sc w i = (q : ℂ) :=
    fun w hw i => hgQ _ (padHi_rat s₁ w hw) i
  have hq : ∀ T : Submodule ℂ (Fin (d - s₁) → ℂ), IsRat T →
      s₁ * Module.finrank ℂ ↥(U.map pr ⊓ T) ≤ u₁ * Module.finrank ℂ ↥T := by
    intro T hT
    have hr : IsRat (T.comap pr) := by
      rw [q_comap_eq pr sc S₁ hπσ hker]
      exact isRat_sup hS₁r (isRat_map sc hscQ hT)
    have h := hmax' _ hr
    rw [q_finrank_comap pr sc S₁ hπσ hker, ← q_modular pr S₁ hker U T, ← hu₁, ← hs₁] at h
    nlinarith
  have hUQ' : ∀ v ∈ U.map pr, (∀ i, ∃ q : ℚ, v i = (q : ℂ)) → v = 0 := by
    intro v hv hvQ
    by_contra hv0
    have hT : IsRat (Submodule.span ℂ {v}) := isRat_span {v} (by
      intro w hw; rw [Set.mem_singleton_iff] at hw; subst hw; exact hvQ)
    have h := hq _ hT
    have hle : Submodule.span ℂ {v} ≤ U.map pr := (Submodule.span_singleton_le_iff_mem _ _).mpr hv
    rw [inf_eq_right.mpr hle, finrank_span_singleton hv0] at h
    omega
  set Z₂ := Zq.map (pr.restrictScalars ℚ)
  set b₂ := Module.finBasis ℚ ↥Z₂
  obtain ⟨S', D', hS'r, hUS', hD'p, hD'1, hD'2, hD'ℓ⟩ := IH (d - s₁) (by omega) (U.map pr) hUQ'
    (fun k => (b₂ k : Fin (d - s₁) → ℂ))
    (fun k => by obtain ⟨x, hx, hxe⟩ := (b₂ k).2; rw [← hxe]; exact ⟨x, hZU x hx, rfl⟩)
    (fun k j => by
      obtain ⟨x, hx, hxe⟩ := (b₂ k).2
      rw [← hxe]
      show pr x j ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg)
      rw [piG_apply]; exact (hgM _ _ (hZL x hx)).1 _)
    (b₂.linearIndependent.map' Z₂.subtype (Submodule.ker_subtype Z₂))
  have hmapU : Module.finrank ℂ ↥(U.map pr) + u₁ = Module.finrank ℂ ↥U := q_finrank_map pr S₁ hker U
  have hsplit : Module.finrank ℚ ↥Z₂ + Module.finrank ℚ ↥Z₁ = ℓ := by
    rw [← hℓ]; exact q_finrankQ pr S₁ hker Zq
  have hdimS : Module.finrank ℂ ↥(S'.comap pr) = s₁ + Module.finrank ℂ ↥S' := by
    rw [q_finrank_comap pr sc S₁ hπσ hker]
  -- assembling `S = π⁻¹(S')` and `D = (u₁, s₁) :: D'`
  refine ⟨S'.comap pr, (u₁, s₁) :: D', ?_, Submodule.map_le_iff_le_comap.mp hUS', ?_, ?_, ?_, ?_⟩
  · rw [q_comap_eq pr sc S₁ hπσ hker]; exact isRat_sup hS₁r (isRat_map sc hscQ hS'r)
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hu₁pos, hus⟩
    · exact hD'p p hp
  · simp only [List.map_cons, List.sum_cons, hD'1]; omega
  · simp only [List.map_cons, List.sum_cons, hD'2, hdimS]
  · simp only [List.map_cons, List.sum_cons]
    have hpos' : (0 : ℚ) < (s₁ : ℚ) - u₁ := by
      have : (u₁ : ℚ) < s₁ := by exact_mod_cast hus
      linarith
    have h5 : (Module.finrank ℚ ↥Z₁ : ℚ) ≤ (u₁ : ℚ) * s₁ / ((s₁ : ℚ) - u₁) := by
      rw [le_div_iff₀ hpos']
      have h' : (((s₁ - u₁) * Module.finrank ℚ ↥Z₁ : ℕ) : ℚ) ≤ ((s₁ * u₁ : ℕ) : ℚ) := by
        exact_mod_cast IH1
      push_cast [Nat.cast_sub hus.le] at h'
      linarith
    have hsplitQ : (ℓ : ℚ) = (Module.finrank ℚ ↥Z₂ : ℚ) + (Module.finrank ℚ ↥Z₁ : ℚ) := by
      rw [← hsplit]; push_cast; ring
    rw [hsplitQ]
    linarith

end RC5_T5Q

open DiazModulus RC5_T5Q in
theorem solution {d ℓ : ℕ} (U : Submodule ℂ (Fin d → ℂ))
    (hUQ : ∀ v ∈ U, (∀ i, ∃ q : ℚ, v i = (q : ℂ)) → v = 0)
    (z : Fin ℓ → Fin d → ℂ) (hzU : ∀ i, z i ∈ U)
    (hz : ∀ i j, z i j ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg)) (hzind : LinearIndependent ℚ z) :
    ∃ (S : Submodule ℂ (Fin d → ℂ)) (D : List (ℕ × ℕ)),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S ∧ U ≤ S ∧
      (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧
      (D.map Prod.fst).sum = Module.finrank ℂ ↥U ∧ (D.map Prod.snd).sum = Module.finrank ℂ ↥S ∧
      (ℓ : ℚ) ≤ (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum := by
  exact main d U hUQ z hzU hz hzind
