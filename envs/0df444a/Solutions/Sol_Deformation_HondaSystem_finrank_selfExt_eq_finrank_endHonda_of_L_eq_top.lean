-- Prove2me | solution 1 for Deformation.HondaSystem.finrank_selfExt_eq_finrank_endHonda_of_L_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/810c576b-05bf-5c1f-a485-010cf50ece6f

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_HondaSelfExt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_finrank_selfExt_eq_finrank_endHonda_of_L_eq_top

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v

open LinearMap Submodule Function

namespace WEEC
open Deformation Deformation.HondaSystem

variable {k : Type u} [Field k] {D : Type v} [AddCommGroup D] [Module k D] [FiniteDimensional k D]

theorem finrank_selfExt_eq_of_filteredEnd_eq_top (H : HondaSystem (0 : k) D)
    (hfe : H.filteredEnd = ⊤) (e : H.extPairs ≃ₗ[k] Module.End k D) :
    Module.finrank k H.selfExt = Module.finrank k H.endHonda := by

  have hdef : Module.finrank k H.selfExt =
      Module.finrank k (↥H.extPairs ⧸ (H.innerPairs.comap H.extPairs.subtype)) := rfl
  have hq := Submodule.finrank_quotient_add_finrank (H.innerPairs.comap H.extPairs.subtype)
  have hc : Module.finrank k (H.innerPairs.comap H.extPairs.subtype) = Module.finrank k H.innerPairs :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (innerPairs_le_extPairs H))
  have hinner : H.innerPairs = LinearMap.range H.innerDerivation := by
    rw [innerPairs, hfe, Submodule.map_top]
  have hend : H.endHonda = LinearMap.ker H.innerDerivation := by
    rw [endHonda, hfe, top_inf_eq]
  have hrn : Module.finrank k H.innerPairs + Module.finrank k (LinearMap.ker H.innerDerivation) =
      Module.finrank k (Module.End k D) := by
    rw [hinner]; exact LinearMap.finrank_range_add_finrank_ker _
  have he := LinearEquiv.finrank_eq e
  rw [hend, hdef]
  have key : Module.finrank k (↥H.extPairs ⧸ (H.innerPairs.comap H.extPairs.subtype)) +
      Module.finrank k (H.innerPairs.comap H.extPairs.subtype) =
      Module.finrank k (LinearMap.ker H.innerDerivation) +
      Module.finrank k (H.innerPairs.comap H.extPairs.subtype) := by
    rw [hq, he, ← hrn, hc, add_comm]
  exact Nat.add_right_cancel key

end WEEC

open Deformation Deformation.HondaSystem in

theorem solution
    {k : Type u} [Field k] {D : Type v} [AddCommGroup D] [Module k D]
    [FiniteDimensional k D] {ℓ : k} (hℓ : ℓ = 0) (H : Deformation.HondaSystem ℓ D)
    (hL : H.L = ⊤) :
    Module.finrank k H.selfExt = Module.finrank k H.endHonda := by
  subst hℓ

  have hF : H.F = 0 := by
    apply LinearMap.range_eq_bot.mp
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, -, hy⟩ := H.sh1_le x (by rw [hL]; trivial) hx
    rw [Submodule.mem_bot, hy, zero_smul]
  have hVinj : Function.Injective H.V := by
    intro x y hxy
    have := H.sh3 (x - y) (by rw [hL]; trivial) (by rw [map_sub, hxy, sub_self])
    exact sub_eq_zero.mp this
  have hVsurj : Function.Surjective H.V := LinearMap.injective_iff_surjective.mp hVinj
  have hfe : H.filteredEnd = ⊤ := by
    ext a
    simp only [mem_filteredEnd_iff, hL, Submodule.mem_top, imp_self, implies_true]

  have hmem : ∀ XY : Module.End k D × Module.End k D, XY ∈ H.extPairs ↔ XY.1 = 0 := by
    intro XY
    rw [mem_extPairs_iff, hF, LinearMap.comp_zero, LinearMap.zero_comp, add_zero, zero_add]
    constructor
    · rintro ⟨h1, -⟩
      ext x
      obtain ⟨y, rfl⟩ := hVsurj x
      rw [← LinearMap.comp_apply, h1, LinearMap.zero_apply, LinearMap.zero_apply]
    · intro h
      rw [h, LinearMap.comp_zero, LinearMap.zero_comp]
      exact ⟨rfl, rfl⟩
  let e : H.extPairs ≃ₗ[k] Module.End k D :=
    { toFun := fun XY => XY.1.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun Y => ⟨(0, Y), (hmem _).mpr rfl⟩
      left_inv := fun XY => by
        apply Subtype.ext
        ext1
        · exact ((hmem XY.1).mp XY.2).symm
        · rfl
      right_inv := fun Y => rfl }
  exact WEEC.finrank_selfExt_eq_of_filteredEnd_eq_top H hfe e

end S_Deformation_HondaSystem_finrank_selfExt_eq_finrank_endHonda_of_L_eq_top
end P2MW
export P2MW.S_Deformation_HondaSystem_finrank_selfExt_eq_finrank_endHonda_of_L_eq_top (solution)
