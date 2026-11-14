-- Prove2me | solution 1 for DiazModulus.roy_theorem_four
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-13T09:54:59.384736+00:00
-- url     : https://prove2.me/submissions/6616d375-c3c4-49ac-8f53-fe0c0de3d203

import Mathlib
import Definitions.Def_DiazModulus
import Definitions.Def_MultiplicityEstimateElem
import Theorems.Thm_DiazModulus_roy_slope_bound
import Theorems.Thm_DiazModulus_roy_rational_adapted_basis

open Complex ComplexConjugate

/-! # Roy's Theorem 4 at a minimiser `S` of `(n − u_S)/(d − s)`

The second claim is the minimality at `S' = ⊥` (rational, and `≠ ⊤` because `S ≠ ⊤` forces `d > 0`).
For the first, take the adapted basis `g` of `S` (`roy_rational_adapted_basis`); its coordinates `≥ s` give
`π : ℂ^d → ℂ^{d'}`, `d' = d − s`, with kernel `S` and an algebraic section, mapping `ℒ̃^d` into `ℒ̃^{d'}`.
Put `U' = π(U)`, of dimension `n' = n − u_S`, and `Z' = π(span_Q̄ z)`, of dimension `ℓ' = ℓ − ℓ_S` (rank–nullity
over `Q̄`); a `Q̄`-basis of `Z'` is a `Q̄`-free family in `U' ⊓ ℒ̃^{d'}`. For a rational `S'' ≤ ℂ^{d'}` its
preimage `S' = S ⊔ σ(S'')` is rational of dimension `s + dim S''`, and `dim(U ⊓ S') = u_S + dim(U' ⊓ S'')`
(modular law). If `S'' ≠ ⊤` then `S' ≠ ⊤`, and the minimality of `S` at `S'` gives
`d'·dim(U' ⊓ S'') ≤ n'·dim S''`; at `S'' = ⊤` this is an equality. If `n' < d'`, `roy_slope_bound` with
`(a, b) = (n', d')` gives `(d' − n')ℓ' ≤ d'n'`, that is `ℓ'd' ≤ n'(d' + ℓ')`; if `n' ≥ d'` this is clear. -/

namespace RC1_T4
open DiazModulus

/-- A rational subspace: spanned by its vectors with algebraic coordinates. -/
abbrev IsRat {d : ℕ} (S : Submodule ℂ (Fin d → ℂ)) : Prop :=
  Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, v i ∈ Qbar} = S

theorem isRat_span {d : ℕ} (X : Set (Fin d → ℂ)) (hX : ∀ v ∈ X, ∀ i, v i ∈ Qbar) :
    IsRat (Submodule.span ℂ X) :=
  le_antisymm (Submodule.span_le.mpr fun _ hv => hv.1)
    (Submodule.span_le.mpr fun v hv => Submodule.subset_span ⟨Submodule.subset_span hv, hX v hv⟩)

theorem isRat_bot {d : ℕ} : IsRat (⊥ : Submodule ℂ (Fin d → ℂ)) := by
  rw [← Submodule.span_empty]; exact isRat_span _ (by simp)

theorem isRat_map {d e : ℕ} (f : (Fin d → ℂ) →ₗ[ℂ] (Fin e → ℂ))
    (hf : ∀ v, (∀ i, v i ∈ Qbar) → ∀ i, f v i ∈ Qbar) {S : Submodule ℂ (Fin d → ℂ)} (hS : IsRat S) :
    IsRat (S.map f) := by
  obtain ⟨X, hX, rfl⟩ : ∃ X : Set (Fin d → ℂ), (∀ v ∈ X, ∀ i, v i ∈ Qbar) ∧ Submodule.span ℂ X = S :=
    ⟨_, fun _ hv => hv.2, hS⟩
  rw [Submodule.map_span]
  exact isRat_span _ (by rintro _ ⟨v, hv, rfl⟩; exact hf v (hX v hv))

theorem isRat_sup {d : ℕ} {S T : Submodule ℂ (Fin d → ℂ)} (hS : IsRat S) (hT : IsRat T) :
    IsRat (S ⊔ T) := by
  obtain ⟨X, hX, rfl⟩ : ∃ X : Set (Fin d → ℂ), (∀ v ∈ X, ∀ i, v i ∈ Qbar) ∧ Submodule.span ℂ X = S :=
    ⟨_, fun _ hv => hv.2, hS⟩
  obtain ⟨Y, hY, rfl⟩ : ∃ Y : Set (Fin d → ℂ), (∀ v ∈ Y, ∀ i, v i ∈ Qbar) ∧ Submodule.span ℂ Y = T :=
    ⟨_, fun _ hv => hv.2, hT⟩
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
theorem q_finrankQ (Z : Submodule (↥Qbar) (Fin d → ℂ)) [FiniteDimensional (↥Qbar) ↥Z] :
    Module.finrank (↥Qbar) ↥(Z.map (π.restrictScalars (↥Qbar))) +
      Module.finrank (↥Qbar) ↥(Z ⊓ S₁.restrictScalars (↥Qbar)) = Module.finrank (↥Qbar) ↥Z := by
  have h := LinearMap.finrank_range_add_finrank_ker ((π.restrictScalars (↥Qbar)).domRestrict Z)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have he : (LinearMap.ker (π.restrictScalars (↥Qbar))).comap Z.subtype
      = (Z ⊓ S₁.restrictScalars (↥Qbar)).comap Z.subtype := by
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, LinearMap.mem_ker, Submodule.subtype_apply, Submodule.mem_inf,
      LinearMap.restrictScalars_apply, Submodule.restrictScalars_mem, hker]
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  rw [he, (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq] at h
  exact h

end quot

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

theorem piG_apply (v : Fin d → ℂ) (j : Fin (d - s)) :
    piG g s v j = g v ⟨s + j.val, by have := j.isLt; omega⟩ := rfl

theorem piG_secG (w : Fin (d - s) → ℂ) : piG g s (secG g s w) = w := by
  ext j
  simp only [piG_apply, secG, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, padHi, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos (by simp)]
  congr 1; ext; simp

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

end coords

theorem padHi_qbar {d : ℕ} (s : ℕ) (w : Fin (d - s) → ℂ) (hw : ∀ i, w i ∈ Qbar) (i : Fin d) :
    padHi (d := d) s w i ∈ Qbar := by
  simp only [padHi, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs
  · exact hw _
  · exact Qbar.zero_mem


theorem arith_hyp {n uS d s x t : ℕ} (hxn : x + uS ≤ n) (hts : s + t ≤ d)
    (h : (n - uS) * (d - (s + t)) ≤ (n - (x + uS)) * (d - s)) : (d - s) * x ≤ (n - uS) * t := by
  have h1 : uS ≤ n := by omega
  have h2 : s ≤ d := by omega
  zify [h1, h2, hxn, hts] at h ⊢
  nlinarith

theorem arith_end {n' D ℓ' : ℕ} (h : n' < D → (D - n') * ℓ' ≤ D * n') : ℓ' * D ≤ n' * (D + ℓ') := by
  by_cases hnD : n' < D
  · have h' := h hnD
    zify [hnD.le] at h' ⊢
    nlinarith
  · nlinarith [Nat.mul_le_mul_left ℓ' (not_lt.mp hnD)]

end RC1_T4

open DiazModulus RC1_T4 in
theorem solution (hME : MultiplicityEstimateElem) {d ℓ : ℕ} (U : Submodule ℂ (Fin d → ℂ))
    (z : Fin ℓ → Fin d → ℂ) (hzU : ∀ i, z i ∈ U) (hz : ∀ i j, z i j ∈ LogAlgTilde)
    (hzind : LinearIndependent (↥Qbar) z)
    (S : Submodule ℂ (Fin d → ℂ)) (hSrat : Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, v i ∈ Qbar} = S) (hStop : S ≠ ⊤)
    (hmin : ∀ S' : Submodule ℂ (Fin d → ℂ), Submodule.span ℂ {v : Fin d → ℂ | v ∈ S' ∧ ∀ i, v i ∈ Qbar} = S' → S' ≠ ⊤ →
      (Module.finrank ℂ ↥(U) - Module.finrank ℂ ↥(U ⊓ S)) * (d - Module.finrank ℂ ↥(S')) ≤
        (Module.finrank ℂ ↥(U) - Module.finrank ℂ ↥(U ⊓ S')) * (d - Module.finrank ℂ ↥(S))) :
    (ℓ - Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range z) ⊓ S.restrictScalars (↥Qbar))) * (d - Module.finrank ℂ ↥(S)) ≤
        (Module.finrank ℂ ↥(U) - Module.finrank ℂ ↥(U ⊓ S)) * ((d - Module.finrank ℂ ↥(S)) + (ℓ - Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range z) ⊓ S.restrictScalars (↥Qbar)))) ∧
      (Module.finrank ℂ ↥(U) - Module.finrank ℂ ↥(U ⊓ S)) * d ≤ Module.finrank ℂ ↥(U) * (d - Module.finrank ℂ ↥(S)) := by
  have hfr : ∀ {e : ℕ} (T : Submodule ℂ (Fin e → ℂ)), Module.finrank ℂ ↥T ≤ e :=
    fun T => (Submodule.finrank_le T).trans_eq (Module.finrank_fin_fun ℂ)
  have hlt : ∀ {e : ℕ} (T : Submodule ℂ (Fin e → ℂ)), T ≠ ⊤ → Module.finrank ℂ ↥T < e := by
    intro e T hT
    by_contra h
    exact hT (Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact (hfr T).antisymm (by omega)))
  have hs : Module.finrank ℂ ↥S < d := hlt S hStop
  -- the second claim: minimality at `⊥`
  have hB : (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S)) * d ≤
      Module.finrank ℂ ↥U * (d - Module.finrank ℂ ↥S) := by
    have hbot : (⊥ : Submodule ℂ (Fin d → ℂ)) ≠ ⊤ := by
      intro h
      have := congrArg (fun T : Submodule ℂ (Fin d → ℂ) => Module.finrank ℂ ↥T) h
      simp only [finrank_bot, finrank_top, Module.finrank_fin_fun] at this
      omega
    have := hmin ⊥ isRat_bot hbot
    rwa [inf_bot_eq, finrank_bot, Nat.sub_zero, Nat.sub_zero] at this
  refine ⟨?_, hB⟩
  -- the quotient by `S`
  obtain ⟨g, hgQ, hgL, hgS⟩ := DiazModulus.roy_rational_adapted_basis S hSrat
  set s := Module.finrank ℂ ↥S with hs_def
  set uS := Module.finrank ℂ ↥(U ⊓ S) with huS
  set pr := piG g s
  set sc := secG g s
  have hπσ : ∀ w, pr (sc w) = w := piG_secG g s
  have hker : ∀ v, pr v = 0 ↔ v ∈ S := piG_ker g s hgS
  have hscQ : ∀ w : Fin (d - s) → ℂ, (∀ i, w i ∈ Qbar) → ∀ i, sc w i ∈ Qbar :=
    fun w hw i => (hgQ _ (padHi_qbar s w hw)).2 i
  set Zq : Submodule (↥Qbar) (Fin d → ℂ) := Submodule.span (↥Qbar) (Set.range z) with hZq
  have : FiniteDimensional (↥Qbar) ↥Zq := FiniteDimensional.span_of_finite _ (Set.finite_range z)
  have hZU : ∀ x ∈ Zq, x ∈ U := by
    have : Zq ≤ U.restrictScalars (↥Qbar) :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hzU i)
    exact fun x hx => this hx
  have hZL : ∀ x ∈ Zq, ∀ j, x j ∈ LogAlgTilde := by
    have : Zq ≤ Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde) :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact Submodule.mem_pi.mpr (fun j _ => hz i j))
    exact fun x hx j => Submodule.mem_pi.mp (this hx) j (Set.mem_univ j)
  have hℓ : Module.finrank (↥Qbar) ↥Zq = ℓ := by rw [finrank_span_eq_card hzind, Fintype.card_fin]
  set Z₂ := Zq.map (pr.restrictScalars (↥Qbar))
  set b₂ := Module.finBasis (↥Qbar) ↥Z₂
  have hsplit : Module.finrank (↥Qbar) ↥Z₂ + Module.finrank (↥Qbar) ↥(Zq ⊓ S.restrictScalars (↥Qbar)) = ℓ := by
    rw [← hℓ]; exact q_finrankQ pr S hker Zq
  have hmapU : Module.finrank ℂ ↥(U.map pr) + uS = Module.finrank ℂ ↥U := q_finrank_map pr S hker U
  have e1 : ℓ - Module.finrank (↥Qbar) ↥(Zq ⊓ S.restrictScalars (↥Qbar)) = Module.finrank (↥Qbar) ↥Z₂ := by
    omega
  have e2 : Module.finrank ℂ ↥U - uS = Module.finrank ℂ ↥(U.map pr) := by omega
  rw [e1, e2]
  apply arith_end
  intro hnD
  refine DiazModulus.roy_slope_bound hME (U.map pr) _ (d - s) _ (fun k => (b₂ k : Fin (d - s) → ℂ)) hnD
    ?_ ?_ ?_ (b₂.linearIndependent.map' Z₂.subtype (Submodule.ker_subtype Z₂))
  · intro T hT
    by_cases hTtop : T = ⊤
    · rw [hTtop, inf_top_eq, finrank_top, Module.finrank_fin_fun, mul_comm]
    · have hr : IsRat (T.comap pr) := by
        rw [q_comap_eq pr sc S hπσ hker]
        exact isRat_sup hSrat (isRat_map sc hscQ hT)
      have hdim := q_finrank_comap pr sc S hπσ hker T
      have hTd := hlt T hTtop
      have hne : T.comap pr ≠ ⊤ := by
        intro h
        rw [h, finrank_top, Module.finrank_fin_fun] at hdim
        omega
      have hmod := q_modular pr S hker U T
      have hx : Module.finrank ℂ ↥(U.map pr ⊓ T) ≤ Module.finrank ℂ ↥(U.map pr) :=
        Submodule.finrank_mono inf_le_left
      have h := hmin _ hr hne
      rw [hdim, ← hmod, ← huS] at h
      rw [← e2]
      exact arith_hyp (by omega) (by omega) h
  · intro k
    obtain ⟨x, hx, hxe⟩ := (b₂ k).2
    rw [← hxe]; exact ⟨x, hZU x hx, rfl⟩
  · intro k j
    obtain ⟨x, hx, hxe⟩ := (b₂ k).2
    rw [← hxe]
    show pr x j ∈ LogAlgTilde
    rw [piG_apply]; exact (hgL _ (hZL x hx)).1 _
