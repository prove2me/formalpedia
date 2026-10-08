-- Prove2me | solution 1 for ErschlerZheng.isSubgroup_localGermSet_and_germSubgroupoid_closed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-05T23:25:12.442194+00:00
-- url     : https://prove2.me/submissions/9c85ab03-ffee-4eb7-ac76-89282399a855

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

theorem exists_L_of_orbit {G L : Subgroup H} (hL : IsAuxiliary (X := X) G L) {o x : X}
    (hx : x ∈ rightOrbit G o) : ∃ σ ∈ L, o <• σ = x := by
  have : x ∈ rightOrbit L o := by rw [hL.1 o]; exact hx
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

theorem conjGerm_inv {o x : X} {ρ : H} (hρ : o <• ρ = x) {a : H} (ha : x <• a = x) :
    germ o (ρ * a⁻¹ * ρ⁻¹) = (germ o (ρ * a * ρ⁻¹))⁻¹ := by
  rw [show ρ * a⁻¹ * ρ⁻¹ = (ρ * a * ρ⁻¹)⁻¹ by group, germ_inv (conj_fix hρ ha)]

theorem conjGerm_trivial {o x : X} {ρ : H} (hρ : o <• ρ = x) {τ : H} (hτ : x <• τ = x)
    (h1 : germ x τ = 1) : germ o (ρ * τ * ρ⁻¹) = 1 := by
  rw [germ_conj_eq hρ hτ (rsmul_one x) (by rw [h1, germ_one]), mul_one, mul_inv_cancel, germ_one]

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

theorem transport_orbit {G L : Subgroup H} (hL : IsAuxiliary (X := X) G L) {o x : X}
    (hx : x ∈ rightOrbit G o) : transport L o x ∈ L ∧ o <• transport L o x = x :=
  transport_spec (exists_L_of_orbit hL hx)

theorem transport_smul {G L : Subgroup H} (hL : IsAuxiliary (X := X) G L) (x : X) {g : H}
    (hg : g ∈ G) : transport L x (x <• g) ∈ L ∧ x <• transport L x (x <• g) = x <• g :=
  transport_spec (exists_L_of_mem hL x hg)

/-- Membership in `H_x` through any `σ ∈ L` with `o·σ = x`. -/
theorem mem_local_iff {G L : Subgroup H} (hL : IsAuxiliary (X := X) G L) {o : X}
    (Ho : Subgroup (GermGroup (H := H) o)) {x : X} (hx : x ∈ rightOrbit G o) {σ : H} (hσL : σ ∈ L)
    (hσ : o <• σ = x) {h : H} (hhGL : h ∈ G ⊔ L) (hh : x <• h = x) :
    germ x h ∈ localGermSet G L o Ho x ↔ germ o (σ * h * σ⁻¹) ∈ Ho := by
  obtain ⟨hρL, hρ⟩ := transport_orbit hL hx
  constructor
  · rintro ⟨h', -, hh', e, hmem⟩
    rw [germ_conj_eq hσ hh hh' e.symm, conjGerm_indep hL hσL hρL hσ hρ hh']
    exact hmem
  · intro hmem
    refine ⟨h, hhGL, hh, rfl, ?_⟩
    rw [conjGerm_indep hL hρL hσL hρ hσ hh]
    exact hmem

theorem le_sup_L {G L : Subgroup H} {σ : H} (h : σ ∈ L) : σ ∈ G ⊔ L :=
  (le_sup_right : L ≤ G ⊔ L) h

theorem le_sup_G {G L : Subgroup H} {g : H} (h : g ∈ G) : g ∈ G ⊔ L :=
  (le_sup_left : G ≤ G ⊔ L) h

end GermConj

end ErschlerZheng
end

section
/-!
# B2: the claims inside Notation 3.1 (pp. 17–18)

For `σ ∈ L` with `o·σ = x`, the map `h ↦ (σhσ⁻¹, o)` on elements fixing `x` is multiplicative,
depends only on the germ of `h` at `x`, and does not depend on `σ` (the isotropy of `L` is trivial).
`H_x` is the preimage of `H_o` under it; everything in Notation 3.1 follows.
-/

open scoped RightActions

namespace ErschlerZheng


end ErschlerZheng
end

section
open scoped RightActions
open ErschlerZheng
open GermBase GermConj in
theorem solution {H : Type*} [Group H] {X : Type*}
    [TopologicalSpace X] [MulAction Hᵐᵒᵖ X] [ContinuousConstSMul Hᵐᵒᵖ X] (G L : Subgroup H)
    (hL : IsAuxiliary (X := X) G L) :
    (∀ x : X, ∀ g ∈ G, x <• g = x → ∀ σ₁ ∈ L, ∀ σ₂ ∈ L, x <• σ₁ = x <• σ₂ →
        GermEq (x <• σ₁) (σ₁⁻¹ * g * σ₁) (σ₂⁻¹ * g * σ₂)) ∧
    ∀ o : X, isotropy (G ⊔ L) o ≠ ⊥ → ∀ Ho : Subgroup (GermGroup (H := H) o),
      Ho < isotropy (G ⊔ L) o →
      (∀ x ∈ rightOrbit G o, ∀ σ ∈ L, o <• σ = x → ∃ K : Subgroup (GermGroup (H := H) x),
        (K : Set (GermGroup (H := H) x)) =
          {θ | ∃ h ∈ G ⊔ L, x <• h = x ∧ germ x h = θ ∧ germ o (σ * h * σ⁻¹) ∈ Ho} ∧
        K < isotropy (G ⊔ L) x) ∧
      localGermSet G L o Ho o = (Ho : Set (GermGroup (H := H) o)) ∧
      (∀ x ∈ rightOrbit G o, ∀ σ ∈ L, o <• σ = x → ∀ h ∈ G ⊔ L, x <• h = x →
        (germ x h ∈ localGermSet G L o Ho x ↔ germ o (σ * h * σ⁻¹) ∈ Ho)) ∧
      (∀ g ∈ G, ∀ x ∈ rightOrbit G o, ∀ σ ∈ L, x <• σ = x <• g →
        ((g, x) ∈ germSubgroupoid G L o Ho ↔ germ x (g * σ⁻¹) ∈ localGermSet G L o Ho x)) ∧
      (∀ g g' : H, ∀ x : X, (g, x) ∈ germSubgroupoid G L o Ho → g' ∈ G → GermEq x g g' →
        (g', x) ∈ germSubgroupoid G L o Ho) ∧
      (∀ x ∈ rightOrbit G o, ((1 : H), x) ∈ germSubgroupoid G L o Ho) ∧
      (∀ g : H, ∀ x : X, (g, x) ∈ germSubgroupoid G L o Ho →
        (g⁻¹, x <• g) ∈ germSubgroupoid G L o Ho) ∧
      ∀ g h : H, ∀ x : X, (g, x) ∈ germSubgroupoid G L o Ho →
        (h, x <• g) ∈ germSubgroupoid G L o Ho → (g * h, x) ∈ germSubgroupoid G L o Ho := by
  -- germ of `g σ⁻¹` at `x` does not depend on `σ ∈ L` with `x·σ = x·g`
  have hgσ : ∀ g ∈ G, ∀ x : X, ∀ σ ∈ L, ∀ σ' ∈ L, x <• σ = x <• g → x <• σ' = x <• g →
      germ x (g * σ⁻¹) = germ x (g * σ'⁻¹) := by
    intro g hg x σ hσL σ' hσ'L hσ hσ'
    have f1 : x <• (g * σ'⁻¹) = x := by rw [rsmul_mul, ← hσ', rsmul_inv_smul]
    have τfix : x <• (σ' * σ⁻¹) = x := by rw [rsmul_mul, hσ', ← hσ, rsmul_inv_smul]
    have hτ : germ x (σ' * σ⁻¹) = 1 :=
      germ_eq_one_of_isotropy (hL.2 x) (L.mul_mem hσ'L (L.inv_mem hσL)) τfix
    rw [show g * σ⁻¹ = (g * σ'⁻¹) * (σ' * σ⁻¹) by group, germ_mul f1 τfix, hτ, mul_one]
  have hfixgσ : ∀ g : H, ∀ x : X, ∀ σ : H, x <• σ = x <• g → x <• (g * σ⁻¹) = x := by
    intro g x σ hσ; rw [rsmul_mul, ← hσ, rsmul_inv_smul]
  refine ⟨?_, fun o _hGo Ho hHo => ?_⟩
  -- (1) U6
  · intro x g hg hgx σ₁ hσ₁ σ₂ hσ₂ e
    have hρL : σ₁⁻¹ * σ₂ ∈ L := L.mul_mem (L.inv_mem hσ₁) hσ₂
    have hρz : (x <• σ₁) <• (σ₁⁻¹ * σ₂) = x <• σ₁ := by
      rw [rsmul_mul, rsmul_inv_smul, e]
    have hρ1 : germ (x <• σ₁) (σ₁⁻¹ * σ₂) = 1 := germ_eq_one_of_isotropy (hL.2 _) hρL hρz
    have hρ1' : germ (x <• σ₁) (σ₁⁻¹ * σ₂)⁻¹ = 1 := by rw [germ_inv hρz, hρ1, inv_one]
    have hzx : (x <• σ₁) <• σ₁⁻¹ = x := rsmul_inv_smul x σ₁
    have hk : (x <• σ₁) <• (σ₁⁻¹ * g * σ₁) = x <• σ₁ := by
      have := conj_fix hzx hgx; rwa [inv_inv] at this
    have e' : σ₂⁻¹ * g * σ₂ = (σ₁⁻¹ * σ₂)⁻¹ * (σ₁⁻¹ * g * σ₁) * (σ₁⁻¹ * σ₂)⁻¹⁻¹ := by group
    have hk' : (x <• σ₁) <• (σ₂⁻¹ * g * σ₂) = x <• σ₁ := by
      rw [e']; exact conj_fix (rsmul_inv_eq hρz) hk
    rw [← germ_eq_iff hk hk', e', germ_conj_of_trivial (rsmul_inv_eq hρz) hk hρ1']
  -- (2)–(8): the claims of Notation 3.1
  have hlocal_one : ∀ x ∈ rightOrbit G o, (1 : GermGroup (H := H) x) ∈ localGermSet G L o Ho x := by
    intro x hx
    obtain ⟨hρL, hρ⟩ := transport_orbit hL hx
    refine ⟨1, Subgroup.one_mem _, rsmul_one x, germ_one x, ?_⟩
    rw [mul_one, mul_inv_cancel, germ_one]
    exact Ho.one_mem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (2) H_x, built from any `σ ∈ L` with `o·σ = x`, is a proper subgroup of Ĝ_x
  · intro x hx σ hσL hσ
    have hset : localGermSet G L o Ho x =
        {θ | ∃ h ∈ G ⊔ L, x <• h = x ∧ germ x h = θ ∧ germ o (σ * h * σ⁻¹) ∈ Ho} := by
      ext θ
      constructor
      · intro hθ
        obtain ⟨h, hGL, hhx, rfl, -⟩ := id hθ
        exact ⟨h, hGL, hhx, rfl, (mem_local_iff hL Ho hx hσL hσ hGL hhx).mp hθ⟩
      · rintro ⟨h, hGL, hhx, rfl, hmem⟩
        exact (mem_local_iff hL Ho hx hσL hσ hGL hhx).mpr hmem
    rw [← hset]
    obtain ⟨hρL, hρ⟩ := transport_orbit hL hx
    set ρ := transport L o x
    let K : Subgroup (GermGroup (H := H) x) :=
      { carrier := localGermSet G L o Ho x
        mul_mem' := by
          rintro _ _ ⟨h₁, h₁GL, h₁x, rfl, h₁o⟩ ⟨h₂, h₂GL, h₂x, rfl, h₂o⟩
          refine ⟨h₁ * h₂, Subgroup.mul_mem _ h₁GL h₂GL, by rw [rsmul_mul, h₁x, h₂x],
            germ_mul h₁x h₂x, ?_⟩
          rw [conjGerm_mul hρ h₁x h₂x]
          exact Ho.mul_mem h₁o h₂o
        one_mem' := hlocal_one x hx
        inv_mem' := by
          rintro _ ⟨h₁, h₁GL, h₁x, rfl, h₁o⟩
          refine ⟨h₁⁻¹, Subgroup.inv_mem _ h₁GL, rsmul_inv_eq h₁x, germ_inv h₁x, ?_⟩
          rw [conjGerm_inv hρ h₁x]
          exact Ho.inv_mem h₁o }
    refine ⟨K, rfl, ?_⟩
    have hle : K ≤ isotropy (G ⊔ L) x := by
      rintro _ ⟨h₁, h₁GL, h₁x, rfl, -⟩
      exact germ_mem_isotropy h₁GL h₁x
    obtain ⟨γ₀, hγ₀, hγ₀Ho⟩ := SetLike.exists_of_lt hHo
    obtain ⟨k, hkGL, hko, rfl⟩ := exists_of_mem_isotropy hγ₀
    refine lt_of_le_of_ne hle fun e => ?_
    have hxρ : x <• ρ⁻¹ = o := by rw [← hρ, rsmul_inv_smul]
    have hh : x <• (ρ⁻¹ * k * ρ⁻¹⁻¹) = x := conj_fix hxρ hko
    have hGL : ρ⁻¹ * k * ρ⁻¹⁻¹ ∈ G ⊔ L :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (le_sup_L (L.inv_mem hρL)) hkGL)
        (le_sup_L (L.inv_mem (L.inv_mem hρL)))
    have hmem : germ x (ρ⁻¹ * k * ρ⁻¹⁻¹) ∈ K := by
      rw [e]; exact germ_mem_isotropy hGL hh
    obtain ⟨h', h'GL, h'x, he, h'o⟩ := hmem
    apply hγ₀Ho
    rw [germ_conj_eq hρ h'x hh he] at h'o
    rwa [show ρ * (ρ⁻¹ * k * ρ⁻¹⁻¹) * ρ⁻¹ = k by group] at h'o
  -- Λ(o) = H_o
  · have hoo : o ∈ rightOrbit G o := ⟨1, G.one_mem, by rw [MulOpposite.op_one, one_smul]⟩
    ext θ
    constructor
    · intro hθ
      obtain ⟨h, hGL, hho, rfl, -⟩ := id hθ
      have := (mem_local_iff hL Ho hoo L.one_mem (rsmul_one o) hGL hho).mp hθ
      rwa [one_mul, inv_one, mul_one] at this
    · intro hθ
      obtain ⟨h, hGL, hho, rfl⟩ := exists_of_mem_isotropy (hHo.le hθ)
      refine (mem_local_iff hL Ho hoo L.one_mem (rsmul_one o) hGL hho).mpr ?_
      rwa [one_mul, inv_one, mul_one]
  -- (3) H_x does not depend on σ_x
  · intro x hx σ hσL hσ h hhGL hh
    exact mem_local_iff hL Ho hx hσL hσ hhGL hh
  -- (4) ℋ does not depend on σ
  · intro g hg x hx σ hσL hσ
    obtain ⟨hτL, hτ⟩ := transport_smul hL x hg
    have e := hgσ g hg x σ hσL _ hτL hσ hτ
    constructor
    · rintro ⟨-, -, hmem⟩; rw [e]; exact hmem
    · intro hmem; exact ⟨hg, hx, by rw [← e]; exact hmem⟩
  -- (5) ℋ is a union of germ classes
  · rintro g g' x ⟨hg, hx, hmem⟩ hg' e
    dsimp only at hg hx hmem
    have hxg : x <• g = x <• g' := e.self_of_nhds
    refine ⟨hg', hx, ?_⟩
    obtain ⟨hτL, hτ⟩ := transport_smul hL x hg
    rw [← hxg]
    have f1 := hfixgσ g x _ hτ
    have f2 : x <• (g' * (transport L x (x <• g))⁻¹) = x := hfixgσ g' x _ (hτ.trans hxg)
    rw [← (germ_eq_iff f1 f2).mpr (germEq_comp e (germEq_refl _ _))]
    exact hmem
  -- (6) identities
  · intro x hx
    refine ⟨G.one_mem, hx, ?_⟩
    obtain ⟨hτL, hτ⟩ := transport_smul hL x G.one_mem
    rw [one_mul, germ_eq_one_of_isotropy (hL.2 x) (L.inv_mem hτL)
      (rsmul_inv_eq (hτ.trans (rsmul_one x)))]
    exact hlocal_one x hx
  -- (7) inverses
  · rintro g x ⟨hg, hx, hmem⟩
    dsimp only at hg hx hmem
    set y := x <• g
    have hy : y ∈ rightOrbit G o := orbit_smul hx hg
    refine ⟨G.inv_mem hg, hy, ?_⟩
    obtain ⟨hσL, hσ⟩ := transport_smul hL x hg
    set σ := transport L x y
    obtain ⟨hσ'L, hσ'⟩ := transport_smul hL y (G.inv_mem hg)
    set σ' := transport L y (y <• g⁻¹)
    have hyx : y <• g⁻¹ = x := rsmul_inv_smul x g
    obtain ⟨hρL, hρ⟩ := transport_orbit hL hx
    set ρ := transport L o x
    have hρy : o <• (ρ * σ) = y := by rw [rsmul_mul, hρ, hσ]
    have hk : y <• (g⁻¹ * σ'⁻¹) = y := hfixgσ g⁻¹ y σ' hσ'
    rw [mem_local_iff hL Ho hy (L.mul_mem hρL hσL) hρy
      (Subgroup.mul_mem _ (le_sup_G (G.inv_mem hg)) (le_sup_L (L.inv_mem hσ'L))) hk]
    rw [mem_local_iff hL Ho hx hρL hρ (Subgroup.mul_mem _ (le_sup_G hg) (le_sup_L (L.inv_mem hσL)))
      (hfixgσ g x σ hσ)] at hmem
    have hτ : x <• (σ * σ') = x := by rw [rsmul_mul, hσ, hσ', hyx]
    have hτ1 : germ x (σ * σ') = 1 :=
      germ_eq_one_of_isotropy (hL.2 x) (L.mul_mem hσL hσ'L) hτ
    have hfix1 : x <• (g * σ⁻¹) = x := hfixgσ g x σ hσ
    have e : ρ * σ * (g⁻¹ * σ'⁻¹) * (ρ * σ)⁻¹ =
        ρ * ((g * σ⁻¹)⁻¹ * (σ * σ')⁻¹) * ρ⁻¹ := by group
    rw [e, conjGerm_mul hρ (rsmul_inv_eq hfix1) (rsmul_inv_eq hτ), conjGerm_inv hρ hfix1,
      conjGerm_trivial hρ (rsmul_inv_eq hτ) (by rw [germ_inv hτ, hτ1, inv_one]), mul_one]
    exact Ho.inv_mem hmem
  -- (8) composition
  · rintro g h x ⟨hg, hx, hmem⟩ ⟨hh, hy, hmem'⟩
    dsimp only at hg hx hmem hh hy hmem'
    set y := x <• g
    refine ⟨G.mul_mem hg hh, hx, ?_⟩
    obtain ⟨hσL, hσ⟩ := transport_smul hL x hg
    set σ := transport L x y
    obtain ⟨hσ₂L, hσ₂⟩ := transport_smul hL y hh
    set σ₂ := transport L y (y <• h)
    obtain ⟨hσ₃L, hσ₃⟩ := transport_smul hL x (G.mul_mem hg hh)
    set σ₃ := transport L x (x <• (g * h))
    obtain ⟨hρL, hρ⟩ := transport_orbit hL hx
    set ρ := transport L o x
    have hρy : o <• (ρ * σ) = y := by rw [rsmul_mul, hρ, hσ]
    have f1 : x <• (g * σ⁻¹) = x := hfixgσ g x σ hσ
    have f2 : y <• (h * σ₂⁻¹) = y := hfixgσ h y σ₂ hσ₂
    have hyσ : y <• σ⁻¹ = x := by
      show (x <• g) <• σ⁻¹ = x
      rw [← hσ, rsmul_inv_smul]
    have f2' : x <• (σ * (h * σ₂⁻¹) * σ⁻¹) = x := by
      rw [rsmul_mul, rsmul_mul, hσ]
      show (y <• (h * σ₂⁻¹)) <• σ⁻¹ = x
      rw [f2, hyσ]
    have hτ : x <• (σ * σ₂ * σ₃⁻¹) = x := by
      rw [rsmul_mul, rsmul_mul, hσ, hσ₂, ← rsmul_mul x g h, ← hσ₃, rsmul_inv_smul]
    have hτ1 : germ x (σ * σ₂ * σ₃⁻¹) = 1 :=
      germ_eq_one_of_isotropy (hL.2 x) (L.mul_mem (L.mul_mem hσL hσ₂L) (L.inv_mem hσ₃L)) hτ
    rw [mem_local_iff hL Ho hx hρL hρ (Subgroup.mul_mem _ (le_sup_G hg) (le_sup_L (L.inv_mem hσL)))
      f1] at hmem
    rw [mem_local_iff hL Ho hy (L.mul_mem hρL hσL) hρy
      (Subgroup.mul_mem _ (le_sup_G hh) (le_sup_L (L.inv_mem hσ₂L))) f2] at hmem'
    have hfix : x <• (g * h * σ₃⁻¹) = x := hfixgσ (g * h) x σ₃ hσ₃
    rw [mem_local_iff hL Ho hx hρL hρ
      (Subgroup.mul_mem _ (le_sup_G (G.mul_mem hg hh)) (le_sup_L (L.inv_mem hσ₃L))) hfix]
    have e1 : g * h * σ₃⁻¹ = (g * σ⁻¹) * ((σ * (h * σ₂⁻¹) * σ⁻¹) * (σ * σ₂ * σ₃⁻¹)) := by group
    have e2 : ρ * σ * (h * σ₂⁻¹) * (ρ * σ)⁻¹ = ρ * (σ * (h * σ₂⁻¹) * σ⁻¹) * ρ⁻¹ := by group
    rw [e2] at hmem'
    have f3 : x <• ((σ * (h * σ₂⁻¹) * σ⁻¹) * (σ * σ₂ * σ₃⁻¹)) = x := by
      rw [rsmul_mul, f2', hτ]
    rw [e1, conjGerm_mul hρ f1 f3, conjGerm_mul hρ f2' hτ, conjGerm_trivial hρ hτ hτ1, mul_one]
    exact Ho.mul_mem hmem hmem'
end
