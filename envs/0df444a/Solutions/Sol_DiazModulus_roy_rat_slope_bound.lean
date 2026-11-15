-- Prove2me | solution 1 for DiazModulus.roy_rat_slope_bound
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T17:36:17.127532+00:00
-- url     : https://prove2.me/submissions/154e1c74-db4d-4d35-8623-2db1358555e6

import Mathlib
import Definitions.Def_DiazModulus
import Definitions.Def_MultiplicityEstimateElem
import Theorems.Thm_DiazModulus_roy_rat_semistable_node
import Theorems.Thm_DiazModulus_roy_rat_adapted_basis

open Complex ComplexConjugate

/-! # The slope bound `P(d)` over `ℚ`, by strong induction on `d`

`P(d)`: if `a < b` and `b·dim(U ⊓ S) ≤ a·dim S` for every rational `S ≤ ℂ^d`, then every `ℚ`-free family
`z` in `U` with coordinates in `ℚ + ℒ` has `(b − a)·ℓ ≤ b·dim U`. For `d = 0` the family is empty. If
`d·dim(U ⊓ S) ≤ n·dim S` for all rational `S` (semistable), the hypothesis at `S = ℂ^d` gives `b·n ≤ a·d`,
hence `n < d`, and the semistable case (with the induction hypothesis) gives `(d − n)ℓ ≤ dn`, which implies
the claim. Otherwise pick a rational `S₁ ≠ 0` of maximal slope `dim(U ⊓ S)/dim S` (finitely many values); it
has `0 < s₁ < d` and `u₁ < s₁`. A rational adapted basis `g` of `S₁` has a rational matrix, so it preserves
vectors with coordinates in any `ℚ`-subspace of `ℂ`. Its coordinates `< s₁` identify `S₁` with `ℂ^{s₁}`, and its
coordinates `≥ s₁` give `π : ℂ^d → ℂ^{d−s₁}` with kernel `S₁` and a rational section. Both `U ⊓ S₁ ⊂ ℂ^{s₁}`
and `π(U) ⊂ ℂ^{d−s₁}` satisfy the hypothesis with `(a, b) = (u₁, s₁)`, by maximality (for the quotient,
`dim(π U ⊓ S'') = dim(U ⊓ π⁻¹S'') − u₁`). The `ℚ`-span of `z` splits as `Z ⊓ S₁` (a basis moved to `ℂ^{s₁}`)
and `π(Z)`, of total dimension `ℓ`. The induction hypothesis on both pieces adds up to `(s₁ − u₁)ℓ ≤ s₁n`, and
`b·u₁ ≤ a·s₁` turns this into `(b − a)ℓ ≤ bn`. -/

namespace RC5_RSB
open DiazModulus

/-- A rational subspace: spanned by its vectors with rational coordinates. -/
abbrev IsRat {d : ℕ} (S : Submodule ℂ (Fin d → ℂ)) : Prop :=
  Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S

/-- The rationals inside `ℂ`, as a `ℚ`-submodule. -/
noncomputable abbrev Mq : Submodule ℚ ℂ := Submodule.span ℚ {(1 : ℂ)}

theorem mem_Mq {x : ℂ} : x ∈ Mq ↔ ∃ q : ℚ, x = (q : ℂ) := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨q, rfl⟩; exact ⟨q, by rw [Rat.smul_def, mul_one]⟩
  · rintro ⟨q, rfl⟩; exact ⟨q, by rw [Rat.smul_def, mul_one]⟩

theorem isRat_span {d : ℕ} (X : Set (Fin d → ℂ)) (hX : ∀ v ∈ X, ∀ i, ∃ q : ℚ, v i = (q : ℂ)) :
    IsRat (Submodule.span ℂ X) :=
  le_antisymm (Submodule.span_le.mpr fun _ hv => hv.1)
    (Submodule.span_le.mpr fun v hv => Submodule.subset_span ⟨Submodule.subset_span hv, hX v hv⟩)

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

theorem padHi_mem {d : ℕ} (M : Submodule ℚ ℂ) (s : ℕ) (w : Fin (d - s) → ℂ) (hw : ∀ i, w i ∈ M)
    (i : Fin d) : padHi (d := d) s w i ∈ M := by
  simp only [padHi, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs
  · exact hw _
  · exact M.zero_mem

theorem padLo_mem {d : ℕ} (M : Submodule ℚ ℂ) (s : ℕ) (w : Fin s → ℂ) (hw : ∀ i, w i ∈ M)
    (i : Fin d) : padLo (d := d) s w i ∈ M := by
  simp only [padLo, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs
  · exact hw _
  · exact M.zero_mem

/-! ### Choosing an extremal subspace, and the arithmetic -/

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

theorem arith_ss {a b d n ℓ : ℕ} (hab : a < b) (hnd : n < d) (h1 : (d - n) * ℓ ≤ d * n)
    (h2 : b * n ≤ a * d) : (b - a) * ℓ ≤ b * n := by
  have key : d * ((b - a) * ℓ) ≤ d * (b * n) := by
    zify [hab.le, hnd.le] at h1 h2 ⊢
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℤ) ≤ b),
      mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℤ) ≤ ℓ)]
  exact Nat.le_of_mul_le_mul_left key (by omega)

theorem arith_split {a b n u₁ s₁ ℓ₁ ℓ₂ n₂ : ℕ} (hab : a < b) (hus : u₁ < s₁)
    (h1 : (s₁ - u₁) * ℓ₁ ≤ s₁ * u₁) (h2 : (s₁ - u₁) * ℓ₂ ≤ s₁ * n₂) (hn : n₂ + u₁ = n)
    (h3 : b * u₁ ≤ a * s₁) : (b - a) * (ℓ₂ + ℓ₁) ≤ b * n := by
  subst hn
  have key : s₁ * ((b - a) * (ℓ₂ + ℓ₁)) ≤ s₁ * (b * (n₂ + u₁)) := by
    zify [hab.le, hus.le] at h1 h2 h3 ⊢
    nlinarith [mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℤ) ≤ ℓ₂ + ℓ₁),
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity : (0 : ℤ) ≤ b)]
  exact Nat.le_of_mul_le_mul_left key (by omega)

/-! ### `P(d)` by strong induction -/

theorem main_P (hME : MultiplicityEstimateElem) : ∀ (d : ℕ) (U : Submodule ℂ (Fin d → ℂ))
    (a b ℓ : ℕ) (z : Fin ℓ → Fin d → ℂ),
    a < b → (∀ S : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S →
        b * Module.finrank ℂ ↥(U ⊓ S) ≤ a * Module.finrank ℂ ↥S) →
      (∀ i, z i ∈ U) → (∀ i j, z i j ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg)) →
      LinearIndependent ℚ z → (b - a) * ℓ ≤ b * Module.finrank ℂ ↥U := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro U a b ℓ z hab hU hzU hz hzind
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : ℓ = 0 := by
      by_contra h
      exact hzind.ne_zero ⟨0, by omega⟩ (Subsingleton.elim _ _)
    simp [this]
  have hfr : ∀ S : Submodule ℂ (Fin d → ℂ), Module.finrank ℂ ↥S ≤ d :=
    fun S => (Submodule.finrank_le S).trans_eq (Module.finrank_fin_fun ℂ)
  by_cases hss : ∀ S : Submodule ℂ (Fin d → ℂ), IsRat S →
      d * Module.finrank ℂ ↥(U ⊓ S) ≤ Module.finrank ℂ ↥U * Module.finrank ℂ ↥S
  · -- the semistable case
    have htop := hU ⊤ isRat_top
    rw [inf_top_eq, finrank_top, Module.finrank_fin_fun] at htop
    have hnd : Module.finrank ℂ ↥U < d := by
      by_contra h
      have he : Module.finrank ℂ ↥U = d := le_antisymm (hfr U) (not_lt.mp h)
      rw [he] at htop
      exact absurd htop (not_le.mpr (Nat.mul_lt_mul_of_pos_right hab hd))
    exact arith_ss hab hnd (DiazModulus.roy_rat_semistable_node hME IH U hnd hss z hzU hz hzind) htop
  -- the split along a subspace of maximal slope
  push Not at hss
  obtain ⟨S, hSr, hSlt⟩ := hss
  have hSne : S ≠ ⊥ := by rintro rfl; rw [inf_bot_eq, finrank_bot] at hSlt; simp at hSlt
  have hpos : ∀ T : Submodule ℂ (Fin d → ℂ), T ≠ ⊥ → 0 < Module.finrank ℂ ↥T :=
    fun T hT => Nat.pos_of_ne_zero (fun h => hT (Submodule.finrank_eq_zero.mp h))
  obtain ⟨S₁, ⟨hS₁r, hS₁ne⟩, hmax⟩ := exists_max_ratio
    (fun T : Submodule ℂ (Fin d → ℂ) => IsRat T ∧ T ≠ ⊥)
    (fun T => Module.finrank ℂ ↥(U ⊓ T)) (fun T => Module.finrank ℂ ↥T) d
    (fun T _ => hfr _) (fun T _ => hfr _) (fun T hT => hpos T hT.2) ⟨S, hSr, hSne⟩
  have hmax' : ∀ T : Submodule ℂ (Fin d → ℂ), IsRat T →
      Module.finrank ℂ ↥(U ⊓ T) * Module.finrank ℂ ↥S₁ ≤
        Module.finrank ℂ ↥(U ⊓ S₁) * Module.finrank ℂ ↥T := by
    intro T hT
    by_cases h0 : T = ⊥
    · subst h0; simp
    · exact hmax T ⟨hT, h0⟩
  have hs₁pos := hpos S₁ hS₁ne
  have hs₁le := hfr S₁
  have hslope : Module.finrank ℂ ↥U * Module.finrank ℂ ↥S₁ < d * Module.finrank ℂ ↥(U ⊓ S₁) := by
    have h1 := hmax' S hSr
    by_contra hc; push Not at hc
    nlinarith [Nat.mul_le_mul_right (Module.finrank ℂ ↥S) hc, Nat.mul_le_mul_left d h1,
      Nat.mul_lt_mul_of_pos_right hSlt hs₁pos]
  have hs₁d : Module.finrank ℂ ↥S₁ < d := by
    by_contra h
    have he : Module.finrank ℂ ↥S₁ = d := le_antisymm hs₁le (not_lt.mp h)
    have htop : S₁ = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact he)
    rw [htop, inf_top_eq, finrank_top, Module.finrank_fin_fun, mul_comm] at hslope
    exact lt_irrefl _ hslope
  have hus : Module.finrank ℂ ↥(U ⊓ S₁) < Module.finrank ℂ ↥S₁ := by
    have h := hU S₁ hS₁r
    by_contra hc; push Not at hc
    nlinarith [Nat.mul_le_mul_left b hc, Nat.mul_lt_mul_of_pos_right hab hs₁pos]
  obtain ⟨g, hgM, hgS⟩ := DiazModulus.roy_rat_adapted_basis S₁ hS₁r
  set s₁ := Module.finrank ℂ ↥S₁ with hs₁
  set u₁ := Module.finrank ℂ ↥(U ⊓ S₁) with hu₁
  set L : Submodule ℚ ℂ := Submodule.span ℚ (insert (1 : ℂ) LogAlg) with hL
  -- the vectors `z` and their `ℚ`-span
  set Zq : Submodule ℚ (Fin d → ℂ) := Submodule.span ℚ (Set.range z) with hZq
  have : FiniteDimensional ℚ ↥Zq := FiniteDimensional.span_of_finite _ (Set.finite_range z)
  have hZU : ∀ x ∈ Zq, x ∈ U := by
    have : Zq ≤ U.restrictScalars ℚ :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hzU i)
    exact fun x hx => this hx
  have hZL : ∀ x ∈ Zq, ∀ j, x j ∈ L := by
    have : Zq ≤ Submodule.pi Set.univ (fun _ : Fin d => L) :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact Submodule.mem_pi.mpr (fun j _ => hz i j))
    exact fun x hx j => Submodule.mem_pi.mp (this hx) j (Set.mem_univ j)
  have hℓ : Module.finrank ℚ ↥Zq = ℓ := by rw [finrank_span_eq_card hzind, Fintype.card_fin]
  -- (i) the sub-object `U ⊓ S₁` inside `S₁ ≅ ℂ^{s₁}`
  set ic := incG g s₁
  set rs := resG g s₁ hs₁le
  have hθι : ∀ w, rs (ic w) = w := resG_incG g s₁ hs₁le
  have hιS : ∀ w, ic w ∈ S₁ := incG_mem g s₁ hgS
  have hιθ : ∀ v ∈ S₁, ic (rs v) = v := incG_resG g s₁ hgS hs₁le
  have hicQ : ∀ w : Fin s₁ → ℂ, (∀ i, ∃ q : ℚ, w i = (q : ℂ)) → ∀ i, ∃ q : ℚ, ic w i = (q : ℂ) :=
    fun w hw i => mem_Mq.mp ((hgM Mq _ (padLo_mem Mq s₁ w fun i => mem_Mq.mpr (hw i))).2 i)
  set Z₁ := Zq ⊓ S₁.restrictScalars ℚ
  set b₁ := Module.finBasis ℚ ↥Z₁
  have IH1 : (s₁ - u₁) * Module.finrank ℚ ↥Z₁ ≤ s₁ * Module.finrank ℂ ↥(U.comap ic) := by
    refine IH s₁ hs₁d (U.comap ic) u₁ s₁ _ (fun k => rs (b₁ k : Fin d → ℂ)) hus ?_ ?_ ?_ ?_
    · intro T hT
      rw [s_finrank_inf ic rs hθι U T, ← s_finrank_map ic rs hθι T, mul_comm]
      exact hmax' _ (isRat_map ic hicQ hT)
    · intro k
      show ic (rs (b₁ k)) ∈ U
      rw [hιθ _ (b₁ k).2.2]; exact hZU _ (b₁ k).2.1
    · intro k j
      show rs (b₁ k) j ∈ L
      rw [resG_apply]; exact (hgM L _ (hZL _ (b₁ k).2.1)).1 _
    · apply LinearIndependent.of_comp (ic.restrictScalars ℚ)
      have : (ic.restrictScalars ℚ) ∘ (fun k => rs (b₁ k : Fin d → ℂ)) = Z₁.subtype ∘ b₁ := by
        funext k; simp only [Function.comp_apply, LinearMap.restrictScalars_apply]
        exact hιθ _ (b₁ k).2.2
      rw [this]; exact b₁.linearIndependent.map' _ (Submodule.ker_subtype _)
  rw [s_finrank_comap ic rs S₁ hθι hιS hιθ U] at IH1
  -- (ii) the quotient `π(U)` inside `ℂ^{d - s₁}`
  set pr := piG g s₁
  set sc := secG g s₁
  have hπσ : ∀ w, pr (sc w) = w := piG_secG g s₁
  have hker : ∀ v, pr v = 0 ↔ v ∈ S₁ := piG_ker g s₁ hgS
  have hscQ : ∀ w : Fin (d - s₁) → ℂ, (∀ i, ∃ q : ℚ, w i = (q : ℂ)) →
      ∀ i, ∃ q : ℚ, sc w i = (q : ℂ) :=
    fun w hw i => mem_Mq.mp ((hgM Mq _ (padHi_mem Mq s₁ w fun i => mem_Mq.mpr (hw i))).2 i)
  set Z₂ := Zq.map (pr.restrictScalars ℚ)
  set b₂ := Module.finBasis ℚ ↥Z₂
  have IH2 : (s₁ - u₁) * Module.finrank ℚ ↥Z₂ ≤ s₁ * Module.finrank ℂ ↥(U.map pr) := by
    refine IH (d - s₁) (by omega) (U.map pr) u₁ s₁ _ (fun k => (b₂ k : Fin (d - s₁) → ℂ)) hus ?_ ?_ ?_ ?_
    · intro T hT
      have hr : IsRat (T.comap pr) := by
        rw [q_comap_eq pr sc S₁ hπσ hker]
        exact isRat_sup hS₁r (isRat_map sc hscQ hT)
      have h := hmax' _ hr
      rw [q_finrank_comap pr sc S₁ hπσ hker, ← q_modular pr S₁ hker U T, ← hu₁, ← hs₁] at h
      nlinarith
    · intro k
      obtain ⟨x, hx, hxe⟩ := (b₂ k).2
      rw [← hxe]; exact ⟨x, hZU x hx, rfl⟩
    · intro k j
      obtain ⟨x, hx, hxe⟩ := (b₂ k).2
      rw [← hxe]
      show pr x j ∈ L
      rw [piG_apply]; exact (hgM L _ (hZL x hx)).1 _
    · exact b₂.linearIndependent.map' Z₂.subtype (Submodule.ker_subtype Z₂)
  have hmapU : Module.finrank ℂ ↥(U.map pr) + u₁ = Module.finrank ℂ ↥U := q_finrank_map pr S₁ hker U
  have hsplit : Module.finrank ℚ ↥Z₂ + Module.finrank ℚ ↥Z₁ = ℓ := by
    rw [← hℓ]; exact q_finrankQ pr S₁ hker Zq
  rw [← hsplit]
  exact arith_split hab hus IH1 IH2 hmapU (hU S₁ hS₁r)

end RC5_RSB

open DiazModulus RC5_RSB in
theorem solution (hME : MultiplicityEstimateElem) {d : ℕ} (U : Submodule ℂ (Fin d → ℂ))
    (a b ℓ : ℕ) (z : Fin ℓ → Fin d → ℂ) :
    a < b → (∀ S : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S →
        b * Module.finrank ℂ ↥(U ⊓ S) ≤ a * Module.finrank ℂ ↥S) →
      (∀ i, z i ∈ U) → (∀ i j, z i j ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg)) →
      LinearIndependent ℚ z → (b - a) * ℓ ≤ b * Module.finrank ℂ ↥U := by
  exact main_P hME d U a b ℓ z
