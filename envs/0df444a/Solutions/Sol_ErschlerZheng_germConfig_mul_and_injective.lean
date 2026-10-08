-- Prove2me | solution 1 for ErschlerZheng.germConfig_mul_and_injective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T00:07:05.57409+00:00
-- url     : https://prove2.me/submissions/87fdcd2b-9efd-4985-bccf-ab55a0881762

import Mathlib
import Definitions.Def_ErschlerZheng_Germs
import Theorems.Thm_ErschlerZheng_germEq_mul_and_germ_mul
import Theorems.Thm_ErschlerZheng_germAction_wellDefined_and_mul

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

theorem rsmul_inv_smul (y : X) (h : H) : (y <• h) <• h⁻¹ = y := by
  rw [← rsmul_mul, mul_inv_cancel, rsmul_one]

theorem germ_mul {x : X} {g h : H} (hg : x <• g = x) (hh : x <• h = x) :
    germ x (g * h) = germ x g * germ x h :=
  (germEq_mul_and_germ_mul x).2 g h hg hh

theorem germ_def {x : X} {h : H} (hh : x <• h = x) :
    germ x h = QuotientGroup.mk ⟨h, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top h, hh⟩⟩ := by
  unfold germ; rw [dif_pos hh]

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

theorem germ_mem_isotropy {K : Subgroup H} {x : X} {h : H} (hK : h ∈ K) (hh : x <• h = x) :
    germ x h ∈ isotropy K x := by
  rw [germ_def hh]
  refine ⟨⟨h, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top h, hh⟩⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_inf.mpr ⟨hK, hh⟩

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

theorem transport_smul {G L : Subgroup H} (hL : IsAuxiliary (X := X) G L) (x : X) {g : H}
    (hg : g ∈ G) : transport L x (x <• g) ∈ L ∧ x <• transport L x (x <• g) = x <• g :=
  transport_spec (exists_L_of_mem hL x hg)

theorem le_sup_L {G L : Subgroup H} {σ : H} (h : σ ∈ L) : σ ∈ G ⊔ L :=
  (le_sup_right : L ≤ G ⊔ L) h

theorem le_sup_G {G L : Subgroup H} {g : H} (h : g ∈ G) : g ∈ G ⊔ L :=
  (le_sup_left : G ≤ G ⊔ L) h

end GermConj

end ErschlerZheng
end

section
/-!
# B6: Fact 3.5 (p. 19), `ϑ(g) = (Φ_g, g)` is a monomorphism

The cocycle identity `Φ_{g₁g₂}(x) = Φ_{g₁}(x) (τ_{g₁}Φ_{g₂})(x)` from the description of `τ` (B5,
imported) and multiplicativity of germs (B1): both sides are the germ at `x` of `g₁g₂σ⁻¹` for
some `σ ∈ L` with `x·σ = x·g₁g₂`.
-/

open scoped RightActions

namespace ErschlerZheng

end ErschlerZheng
end

section
open scoped RightActions
open ErschlerZheng
open GermBase GermConj in
theorem solution {H : Type*} [Group H] {X : Type*} [TopologicalSpace X]
    [MulAction Hᵐᵒᵖ X] [ContinuousConstSMul Hᵐᵒᵖ X] (G L : Subgroup H)
    (hL : IsAuxiliary (X := X) G L) (o : X) :
    (∀ g ∈ G, ∀ x ∈ rightOrbit G o, germConfig L g x ∈ isotropy (G ⊔ L) x) ∧
      (∀ g₁ ∈ G, ∀ g₂ ∈ G, ∀ x ∈ rightOrbit G o,
        germConfig L (g₁ * g₂) x =
          germConfig L g₁ x * germAction L g₁ (germConfig L g₂) x) ∧
      Function.Injective fun g : G =>
        ((fun x : rightOrbit G o => germConfig L (g : H) (x : X)), (g : H)) := by
  have hfix : ∀ (g : H) (x : X) (σ : H), x <• σ = x <• g → x <• (g * σ⁻¹) = x := by
    intro g x σ hσ; rw [rsmul_mul, ← hσ, rsmul_inv_smul]
  refine ⟨?_, ?_, ?_⟩
  -- (1)
  · intro g hg x _
    obtain ⟨hσL, hσ⟩ := transport_smul hL x hg
    exact germ_mem_isotropy (Subgroup.mul_mem _ (le_sup_G hg) (le_sup_L (L.inv_mem hσL)))
      (hfix g x _ hσ)
  -- (2)
  · intro g₁ hg₁ g₂ hg₂ x hx
    obtain ⟨hσ₁L, hσ₁⟩ := transport_smul hL x hg₁
    set σ₁ := transport L x (x <• g₁)
    obtain ⟨hσ₂L, hσ₂⟩ := transport_smul hL (x <• g₁) hg₂
    set σ₂ := transport L (x <• g₁) ((x <• g₁) <• g₂)
    obtain ⟨hσ₃L, hσ₃⟩ := transport_smul hL x (G.mul_mem hg₁ hg₂)
    set σ₃ := transport L x (x <• (g₁ * g₂))
    have hin : (x <• g₁) <• (g₂ * σ₂⁻¹) = x <• g₁ := hfix g₂ (x <• g₁) σ₂ hσ₂
    have hB5 := (germAction_wellDefined_and_mul G L hL o).1 g₁ hg₁ (germConfig L g₂) x hx σ₁
      hσ₁L hσ₁ (g₂ * σ₂⁻¹) hin rfl
    rw [hB5]
    unfold germConfig
    have f1 : x <• (g₁ * σ₁⁻¹) = x := hfix g₁ x σ₁ hσ₁
    have f2 : x <• (σ₁ * (g₂ * σ₂⁻¹) * σ₁⁻¹) = x := conj_fix hσ₁ hin
    rw [← germ_mul f1 f2]
    have hτ : x <• (σ₁ * σ₂ * σ₃⁻¹) = x := by
      rw [rsmul_mul, rsmul_mul, hσ₁, hσ₂, ← rsmul_mul x g₁ g₂, ← hσ₃, rsmul_inv_smul]
    have hτ1 : germ x (σ₁ * σ₂ * σ₃⁻¹) = 1 :=
      germ_eq_one_of_isotropy (hL.2 x) (L.mul_mem (L.mul_mem hσ₁L hσ₂L) (L.inv_mem hσ₃L)) hτ
    have f12 : x <• (g₁ * σ₁⁻¹ * (σ₁ * (g₂ * σ₂⁻¹) * σ₁⁻¹)) = x := by rw [rsmul_mul, f1, f2]
    rw [show g₁ * g₂ * σ₃⁻¹ = (g₁ * σ₁⁻¹ * (σ₁ * (g₂ * σ₂⁻¹) * σ₁⁻¹)) * (σ₁ * σ₂ * σ₃⁻¹) by group,
      germ_mul f12 hτ, hτ1, mul_one]
  -- (3)
  · intro a b h
    exact Subtype.ext (congrArg Prod.snd h)
end
