-- Prove2me | solution 1 for ErschlerZheng.germAction_wellDefined_and_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-05T23:44:24.790212+00:00
-- url     : https://prove2.me/submissions/ade79c80-876d-47a3-a8e3-c97db2e41eb8

import Mathlib
import Definitions.Def_ErschlerZheng_Germs
import Theorems.Thm_ErschlerZheng_germEq_mul_and_germ_mul

section
/-!
# Germ calculus (helpers for B2, B5, B6)

Composition of germ equalities and multiplicativity of germs come from B1 (imported).
-/

open scoped RightActions

namespace ErschlerZheng

namespace GermBase

set_option linter.unusedSectionVars false

variable {H : Type*} [Group H] {X : Type*} [TopologicalSpace X] [MulAction Hᵐᵒᵖ X]
  [ContinuousConstSMul Hᵐᵒᵖ X]

theorem rsmul_mul (y : X) (g h : H) : y <• (g * h) = (y <• g) <• h := by
  rw [MulOpposite.op_mul, mul_smul]

theorem rsmul_one (y : X) : y <• (1 : H) = y := by rw [MulOpposite.op_one, one_smul]

theorem rsmul_inv_eq {x : X} {h : H} (hh : x <• h = x) : x <• h⁻¹ = x := by
  conv_lhs => rw [← hh]
  rw [← rsmul_mul, mul_inv_cancel, rsmul_one]

theorem rsmul_inv_smul (y : X) (h : H) : (y <• h) <• h⁻¹ = y := by
  rw [← rsmul_mul, mul_inv_cancel, rsmul_one]

theorem germEq_refl (x : X) (g : H) : GermEq x g g := Filter.Eventually.of_forall fun _ => rfl

theorem GermEq.symm' {x : X} {g h : H} (e : GermEq x g h) : GermEq x h g := e.mono fun _ h => h.symm

theorem germEq_comp {x : X} {g₁ g₂ h₁ h₂ : H} (hg : GermEq x g₁ g₂) (hh : GermEq (x <• g₁) h₁ h₂) :
    GermEq x (g₁ * h₁) (g₂ * h₂) :=
  (germEq_mul_and_germ_mul x).1 g₁ g₂ h₁ h₂ hg hh

theorem germ_mul {x : X} {g h : H} (hg : x <• g = x) (hh : x <• h = x) :
    germ x (g * h) = germ x g * germ x h :=
  (germEq_mul_and_germ_mul x).2 g h hg hh

theorem germ_def {x : X} {h : H} (hh : x <• h = x) :
    germ x h = QuotientGroup.mk ⟨h, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top h, hh⟩⟩ := by
  unfold germ; rw [dif_pos hh]

theorem germ_one (x : X) : germ x (1 : H) = 1 := by
  rw [germ_def (rsmul_one x)]
  rfl

theorem germ_inv {x : X} {h : H} (hh : x <• h = x) : germ x h⁻¹ = (germ x h)⁻¹ := by
  have := germ_mul hh (rsmul_inv_eq hh)
  rw [mul_inv_cancel, germ_one] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem germ_eq_iff {x : X} {h h' : H} (hh : x <• h = x) (hh' : x <• h' = x) :
    germ x h = germ x h' ↔ GermEq x h h' := by
  rw [germ_def hh, germ_def hh', QuotientGroup.eq]
  change GermEq x (h⁻¹ * h') 1 ↔ GermEq x h h'
  constructor
  · intro e
    have := germEq_comp (germEq_refl x h) (by rw [hh]; exact e)
    rw [mul_inv_cancel_left, mul_one] at this
    exact GermEq.symm' this
  · intro e
    have := germEq_comp (germEq_refl x h⁻¹) (by rw [rsmul_inv_eq hh]; exact e)
    rw [inv_mul_cancel] at this
    exact GermEq.symm' this

theorem germ_eq_one_of_isotropy {L : Subgroup H} {x : X} (hiso : isotropy L x = ⊥) {τ : H}
    (hτ : τ ∈ L) (hx : x <• τ = x) : germ x τ = 1 := by
  rw [germ_def hx]
  have hmem : (⟨τ, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top τ, hx⟩⟩ : pointStab (⊤ : Subgroup H) x)
      ∈ (pointStab L x).subgroupOf (pointStab ⊤ x) := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨hτ, hx⟩
  have := Subgroup.mem_map_of_mem (QuotientGroup.mk' (trivialNear (H := H) x)) hmem
  unfold isotropy at hiso
  rw [hiso, Subgroup.mem_bot] at this
  exact this

theorem conj_fix {o x : X} {σ h : H} (hσ : o <• σ = x) (hh : x <• h = x) :
    o <• (σ * h * σ⁻¹) = o := by
  rw [rsmul_mul, rsmul_mul, hσ, hh, ← hσ, rsmul_inv_smul]

theorem conj_germEq {o x : X} {σ h h' : H} (hσ : o <• σ = x) (e : GermEq x h h') :
    GermEq o (σ * h * σ⁻¹) (σ * h' * σ⁻¹) := by
  have e1 : GermEq o (σ * h) (σ * h') := germEq_comp (germEq_refl o σ) (by rw [hσ]; exact e)
  exact germEq_comp e1 (germEq_refl _ _)

theorem germ_conj_eq {o x : X} {σ h h' : H} (hσ : o <• σ = x) (hh : x <• h = x)
    (hh' : x <• h' = x) (e : germ x h = germ x h') :
    germ o (σ * h * σ⁻¹) = germ o (σ * h' * σ⁻¹) := by
  rw [germ_eq_iff (conj_fix hσ hh) (conj_fix hσ hh')]
  exact conj_germEq hσ ((germ_eq_iff hh hh').mp e)

theorem germ_conj_of_trivial {x : X} {τ k : H} (hτ : x <• τ = x) (hk : x <• k = x)
    (h1 : germ x τ = 1) : germ x (τ * k * τ⁻¹) = germ x k := by
  have hτk : x <• (τ * k) = x := by rw [rsmul_mul, hτ, hk]
  rw [germ_mul hτk (rsmul_inv_eq hτ), germ_mul hτ hk, germ_inv hτ, h1]
  simp

theorem transport_spec {L : Subgroup H} {x y : X} (h : ∃ σ ∈ L, x <• σ = y) :
    transport L x y ∈ L ∧ x <• transport L x y = y := by
  unfold transport
  exact Classical.epsilon_spec (p := fun σ => σ ∈ L ∧ x <• σ = y) (by
    obtain ⟨σ, h1, h2⟩ := h; exact ⟨σ, h1, h2⟩)

theorem exists_L_of_mem {G L : Subgroup H} (hL : IsAuxiliary (X := X) G L) (x : X) {g : H}
    (hg : g ∈ G) : ∃ σ ∈ L, x <• σ = x <• g := by
  have : x <• g ∈ rightOrbit L x := by
    rw [hL.1 x]; exact ⟨g, hg, rfl⟩
  obtain ⟨σ, hσ, e⟩ := this
  exact ⟨σ, hσ, e.symm⟩

theorem orbit_smul {G : Subgroup H} {o x : X} (hx : x ∈ rightOrbit G o) {g : H} (hg : g ∈ G) :
    x <• g ∈ rightOrbit G o := by
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨k * g, G.mul_mem hk hg, (rsmul_mul o k g).symm⟩

theorem germ_mem_isotropy {K : Subgroup H} {x : X} {h : H} (hK : h ∈ K) (hh : x <• h = x) :
    germ x h ∈ isotropy K x := by
  rw [germ_def hh]
  refine ⟨⟨h, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top h, hh⟩⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_inf.mpr ⟨hK, hh⟩

theorem exists_of_mem_isotropy {K : Subgroup H} {x : X} {γ : GermGroup (H := H) x}
    (hγ : γ ∈ isotropy K x) : ∃ h ∈ K, x <• h = x ∧ germ x h = γ := by
  obtain ⟨a, ha, rfl⟩ := hγ
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha
  obtain ⟨hK, hx⟩ := Subgroup.mem_inf.mp ha
  refine ⟨a, hK, hx, ?_⟩
  rw [germ_def hx]
  rfl

theorem germ_out {x : X} (γ : GermGroup (H := H) x) :
    x <• ((γ.out : pointStab (⊤ : Subgroup H) x) : H) = x ∧
      germ x ((γ.out : pointStab (⊤ : Subgroup H) x) : H) = γ := by
  have hx : x <• ((γ.out : pointStab (⊤ : Subgroup H) x) : H) = x :=
    (Subgroup.mem_inf.mp γ.out.2).2
  refine ⟨hx, ?_⟩
  rw [germ_def hx]
  exact QuotientGroup.out_eq' γ

end GermBase

end ErschlerZheng
end

section
/-!
# Transporting germs by conjugation (helpers for B2, B5, B6)
-/

open scoped RightActions

namespace ErschlerZheng

namespace GermConj

open GermBase

variable {H : Type*} [Group H] {X : Type*} [TopologicalSpace X] [MulAction Hᵐᵒᵖ X]
  [ContinuousConstSMul Hᵐᵒᵖ X]

set_option linter.unusedSectionVars false

theorem conj_mul_conj (ρ a b : H) : ρ * (a * b) * ρ⁻¹ = (ρ * a * ρ⁻¹) * (ρ * b * ρ⁻¹) := by group

theorem conjGerm_mul {o x : X} {ρ : H} (hρ : o <• ρ = x) {a b : H} (ha : x <• a = x)
    (hb : x <• b = x) : germ o (ρ * (a * b) * ρ⁻¹) = germ o (ρ * a * ρ⁻¹) * germ o (ρ * b * ρ⁻¹) := by
  rw [conj_mul_conj, germ_mul (conj_fix hρ ha) (conj_fix hρ hb)]

/-- The map does not depend on `σ ∈ L`. -/
theorem conjGerm_indep {G L : Subgroup H} (hL : IsAuxiliary (X := X) G L) {o x : X} {σ₁ σ₂ : H}
    (h1 : σ₁ ∈ L) (h2 : σ₂ ∈ L) (e1 : o <• σ₁ = x) (e2 : o <• σ₂ = x) {h : H}
    (hh : x <• h = x) : germ o (σ₁ * h * σ₁⁻¹) = germ o (σ₂ * h * σ₂⁻¹) := by
  set τ := σ₂ * σ₁⁻¹
  have hτL : τ ∈ L := L.mul_mem h2 (L.inv_mem h1)
  have hτo : o <• τ = o := by
    simp only [τ]; rw [rsmul_mul, e2, ← e1, rsmul_inv_smul]
  have hτ1 : germ o τ = 1 := germ_eq_one_of_isotropy (hL.2 o) hτL hτo
  have e : σ₂ * h * σ₂⁻¹ = τ * (σ₁ * h * σ₁⁻¹) * τ⁻¹ := by simp only [τ]; group
  rw [e, germ_conj_of_trivial hτo (conj_fix e1 hh) hτ1]

theorem transport_smul {G L : Subgroup H} (hL : IsAuxiliary (X := X) G L) (x : X) {g : H}
    (hg : g ∈ G) : transport L x (x <• g) ∈ L ∧ x <• transport L x (x <• g) = x <• g :=
  transport_spec (exists_L_of_mem hL x hg)

theorem le_sup_L {G L : Subgroup H} {σ : H} (h : σ ∈ L) : σ ∈ G ⊔ L :=
  (le_sup_right : L ≤ G ⊔ L) h

end GermConj

end ErschlerZheng
end

section
/-!
# B5: `τ` is a well-defined action (p. 19)

`(τ_g Φ)(x) = (σ h σ⁻¹, x)` for any `σ ∈ L` with `x·σ = x·g` and any representative `h` of
`Φ(x·g)`: the germ of `σ h σ⁻¹` at `x` depends only on the germ of `h` at `x·g`, and `σ` is
determined up to an element of `L` fixing `x`, whose germ is trivial.
-/

open scoped RightActions

namespace ErschlerZheng

namespace GermB5Dev

open GermBase GermConj

variable {H : Type*} [Group H] {X : Type*} [TopologicalSpace X] [MulAction Hᵐᵒᵖ X]
  [ContinuousConstSMul Hᵐᵒᵖ X]

theorem germAction_eq {G L : Subgroup H} (hL : IsAuxiliary (X := X) G L) {g : H} (hg : g ∈ G)
    (Φ : (x : X) → GermGroup (H := H) x) (x : X) {σ : H} (hσL : σ ∈ L) (hσ : x <• σ = x <• g)
    {h : H} (hh : (x <• g) <• h = x <• g) (hgerm : germ (x <• g) h = Φ (x <• g)) :
    germAction L g Φ x = germ x (σ * h * σ⁻¹) := by
  obtain ⟨hσ₀L, hσ₀⟩ := transport_smul hL x hg
  obtain ⟨hk, hkg⟩ := germ_out (Φ (x <• g))
  unfold germAction
  rw [germ_conj_eq hσ₀ hk hh (hkg.trans hgerm.symm)]
  exact conjGerm_indep hL hσ₀L hσL hσ₀ hσ hh

/-- Transport along an equality of points. -/
theorem germ_eq_of_eq (Φ : (x : X) → GermGroup (H := H) x) {y z : X} (e : y = z) {h : H}
    (hgerm : germ y h = Φ y) : germ z h = Φ z := by
  subst e; exact hgerm

end GermB5Dev

end ErschlerZheng
end

section
open scoped RightActions
open ErschlerZheng
open GermBase GermConj GermB5Dev in
theorem solution {H : Type*} [Group H] {X : Type*} [TopologicalSpace X]
    [MulAction Hᵐᵒᵖ X] [ContinuousConstSMul Hᵐᵒᵖ X] (G L : Subgroup H)
    (hL : IsAuxiliary (X := X) G L) (o : X) :
    (∀ g ∈ G, ∀ Φ : (x : X) → GermGroup (H := H) x, ∀ x ∈ rightOrbit G o, ∀ σ ∈ L,
        x <• σ = x <• g → ∀ h : H, (x <• g) <• h = x <• g → germ (x <• g) h = Φ (x <• g) →
          germAction L g Φ x = germ x (σ * h * σ⁻¹)) ∧
      (∀ g ∈ G, ∀ Φ : (x : X) → GermGroup (H := H) x,
        (∀ y ∈ rightOrbit G o, Φ y ∈ isotropy (G ⊔ L) y) →
          ∀ x ∈ rightOrbit G o, germAction L g Φ x ∈ isotropy (G ⊔ L) x) ∧
      (∀ g ∈ G, ∀ Φ Ψ : (x : X) → GermGroup (H := H) x, ∀ x ∈ rightOrbit G o,
        germAction L g (Φ * Ψ) x = germAction L g Φ x * germAction L g Ψ x) ∧
      (∀ Φ : (x : X) → GermGroup (H := H) x, ∀ x ∈ rightOrbit G o, germAction L 1 Φ x = Φ x) ∧
      ∀ g₁ ∈ G, ∀ g₂ ∈ G, ∀ Φ : (x : X) → GermGroup (H := H) x, ∀ x ∈ rightOrbit G o,
        germAction L (g₁ * g₂) Φ x = germAction L g₁ (germAction L g₂ Φ) x := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- (1)
  · intro g hg Φ x _ σ hσL hσ h hh hgerm
    exact germAction_eq hL hg Φ x hσL hσ hh hgerm
  -- (2)
  · intro g hg Φ hΦ x hx
    obtain ⟨hσL, hσ⟩ := transport_smul hL x hg
    obtain ⟨k, hkGL, hkx, hkg⟩ := exists_of_mem_isotropy (hΦ _ (orbit_smul hx hg))
    rw [germAction_eq hL hg Φ x hσL hσ hkx hkg]
    exact germ_mem_isotropy (Subgroup.mul_mem _ (Subgroup.mul_mem _ (le_sup_L hσL) hkGL)
      (le_sup_L (L.inv_mem hσL))) (conj_fix hσ hkx)
  -- (3)
  · intro g hg Φ Ψ x _
    obtain ⟨hσL, hσ⟩ := transport_smul hL x hg
    obtain ⟨h1, g1⟩ := germ_out (Φ (x <• g))
    obtain ⟨h2, g2⟩ := germ_out (Ψ (x <• g))
    set k1 := ((Φ (x <• g)).out : H)
    set k2 := ((Ψ (x <• g)).out : H)
    have h12 : (x <• g) <• (k1 * k2) = x <• g := by rw [rsmul_mul, h1, h2]
    have g12 : germ (x <• g) (k1 * k2) = (Φ * Ψ) (x <• g) := by
      rw [germ_mul h1 h2, g1, g2]; rfl
    rw [germAction_eq hL hg (Φ * Ψ) x hσL hσ h12 g12, germAction_eq hL hg Φ x hσL hσ h1 g1,
      germAction_eq hL hg Ψ x hσL hσ h2 g2, conjGerm_mul hσ h1 h2]
  -- (4)
  · intro Φ x _
    obtain ⟨h1, g1⟩ := germ_out (Φ (x <• (1 : H)))
    rw [germAction_eq hL G.one_mem Φ x L.one_mem rfl h1 g1, one_mul, inv_one, mul_one]
    exact germ_eq_of_eq Φ (rsmul_one x) g1
  -- (5)
  · intro g₁ hg₁ g₂ hg₂ Φ x _
    obtain ⟨hσ₁L, hσ₁⟩ := transport_smul hL x hg₁
    set σ₁ := transport L x (x <• g₁)
    obtain ⟨hσ₂L, hσ₂⟩ := transport_smul hL (x <• g₁) hg₂
    set σ₂ := transport L (x <• g₁) ((x <• g₁) <• g₂)
    obtain ⟨hk, hkg⟩ := germ_out (Φ ((x <• g₁) <• g₂))
    set k := ((Φ ((x <• g₁) <• g₂)).out : H)
    -- the inner action at `x·g₁`
    have hin : (x <• g₁) <• (σ₂ * k * σ₂⁻¹) = x <• g₁ := conj_fix hσ₂ hk
    have hin' : germ (x <• g₁) (σ₂ * k * σ₂⁻¹) = germAction L g₂ Φ (x <• g₁) := rfl
    rw [germAction_eq hL hg₁ (germAction L g₂ Φ) x hσ₁L hσ₁ hin hin']
    -- the outer action
    have e : (x <• g₁) <• g₂ = x <• (g₁ * g₂) := (rsmul_mul x g₁ g₂).symm
    have hk' : (x <• (g₁ * g₂)) <• k = x <• (g₁ * g₂) := by rw [← e]; exact hk
    have hkg' : germ (x <• (g₁ * g₂)) k = Φ (x <• (g₁ * g₂)) := germ_eq_of_eq Φ e hkg
    have hσ12 : x <• (σ₁ * σ₂) = x <• (g₁ * g₂) := by rw [rsmul_mul, hσ₁, hσ₂, e]
    rw [germAction_eq hL (G.mul_mem hg₁ hg₂) Φ x (L.mul_mem hσ₁L hσ₂L) hσ12 hk' hkg']
    congr 1
    group
end
