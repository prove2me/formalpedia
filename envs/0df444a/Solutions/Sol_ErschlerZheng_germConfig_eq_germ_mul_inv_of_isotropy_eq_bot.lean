-- Prove2me | solution 1 for ErschlerZheng.germConfig_eq_germ_mul_inv_of_isotropy_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:44:25.70237+00:00
-- url     : https://prove2.me/submissions/16b9ecab-cef0-4dab-95d7-95de13198680

import Mathlib
import Definitions.Def_ErschlerZheng_Germs
import Theorems.Thm_ErschlerZheng_germEq_mul_and_germ_mul
import Definitions.Def_ErschlerZheng_Grigorchuk

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

theorem transport_spec {L : Subgroup H} {x y : X} (h : ∃ σ ∈ L, x <• σ = y) :
    transport L x y ∈ L ∧ x <• transport L x y = y := by
  unfold transport
  exact Classical.epsilon_spec (p := fun σ => σ ∈ L ∧ x <• σ = y) (by
    obtain ⟨σ, h1, h2⟩ := h; exact ⟨σ, h1, h2⟩)

end GermBase

end ErschlerZheng
end

section
/-!
# Basic facts about sections, `a`, and the generators `b_ω, c_ω, d_ω`

Development helpers for the Grigorchuk part of the Erschler–Zheng mission (not published).
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace GrigBasic

/-! ### Sections -/

/-! ### The root swap -/

/-! ### `a` and the generators -/

/-! ### Words -/

end GrigBasic

end ErschlerZheng
end

section
/-!
# Rays: prefixes, shifts, and the action of sections
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace RayBasic

open GrigBasic

end RayBasic

end ErschlerZheng
end

section
/-!
# New germ items: the condition `x = x₁ … xₙ 1^∞` in `HasGermAt`, and the choice of `σ` in (3.3)

1. For `ω₀ = 0`, the generator `d_ω` is its own section at the empty prefix, fixes every vertex
   below `0`, has trivial germ at `01^∞`, and has a `d`-germ at `01^∞` in the sense of
   `HasGermAt` exactly when all but finitely many letters of `ω` are `0`.
2. When the isotropy group of `L` at `x` is trivial, `germConfig L g x` is the germ of `gσ⁻¹` at
   `x` for every `σ ∈ L` with `x·σ = x·g`, not only for the chosen `transport L x (x·g)`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace NewGerms

open GrigBasic RayBasic GermBase

/-! ### Cylinders and sections (as in `GrigGermsDev`, whose module imports an unrelated stub) -/

/-! ### Item 1 -/

end NewGerms

/-! ### Item 2 -/

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
open GermBase in
theorem solution {H : Type*} [Group H] {X : Type*}
    [TopologicalSpace X] [MulAction Hᵐᵒᵖ X] [ContinuousConstSMul Hᵐᵒᵖ X] (L : Subgroup H)
    (g : H) (x : X) (hL : isotropy L x = ⊥) (σ : H) (hσ : σ ∈ L) (hσx : x <• σ = x <• g) :
    germConfig L g x = germ x (g * σ⁻¹) := by
  obtain ⟨hτL, hτx⟩ := transport_spec (L := L) (x := x) (y := x <• g) ⟨σ, hσ, hσx⟩
  set τ := transport L x (x <• g)
  have hgσ : x <• (g * σ⁻¹) = x := by rw [rsmul_mul, ← hσx, rsmul_inv_smul]
  have hστ : x <• (σ * τ⁻¹) = x := by rw [rsmul_mul, hσx, ← hτx, rsmul_inv_smul]
  have h1 : germ x (σ * τ⁻¹) = 1 :=
    germ_eq_one_of_isotropy hL (L.mul_mem hσ (L.inv_mem hτL)) hστ
  have h2 : g * τ⁻¹ = (g * σ⁻¹) * (σ * τ⁻¹) := by group
  unfold germConfig
  rw [h2, germ_mul hgσ hστ, h1, mul_one]
end
