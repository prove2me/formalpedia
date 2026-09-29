-- Prove2me | solution 1 for Deformation.HondaSystem.finrank_selfExt_eq_finrank_endHonda_of_L_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/5c5fafbe-7a01-551f-b35e-66d0685b082d

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_HondaSelfExt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_finrank_selfExt_eq_finrank_endHonda_of_L_eq_bot

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
    (hL : H.L = ⊥) :
    Module.finrank k H.selfExt = Module.finrank k H.endHonda := by
  subst hℓ

  have hFsurj : Function.Surjective H.F := by
    have h := H.sh2'
    rw [hL, sup_bot_eq, LinearMap.range_eq_top] at h
    exact h
  have hFinj : Function.Injective H.F := LinearMap.injective_iff_surjective.mpr hFsurj
  have hV : H.V = 0 := by
    ext x
    apply hFinj
    rw [H.toDieudonneDatum.F_V_apply, zero_smul, LinearMap.zero_apply, map_zero]
  have hfe : H.filteredEnd = ⊤ := by
    ext a
    simp only [mem_filteredEnd_iff, hL, Submodule.mem_bot, Submodule.mem_top, iff_true]
    intro x hx; rw [hx, map_zero]

  have hmem : ∀ XY : Module.End k D × Module.End k D, XY ∈ H.extPairs ↔ XY.2 = 0 := by
    intro XY
    rw [mem_extPairs_iff, hV, LinearMap.comp_zero, LinearMap.zero_comp, add_zero, zero_add]
    constructor
    · rintro ⟨h1, -⟩
      ext x
      apply hFinj
      rw [LinearMap.zero_apply, map_zero, ← LinearMap.comp_apply, h1, LinearMap.zero_apply]
    · intro h
      rw [h, LinearMap.comp_zero, LinearMap.zero_comp]
      exact ⟨rfl, rfl⟩
  let e : H.extPairs ≃ₗ[k] Module.End k D :=
    { toFun := fun XY => XY.1.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun X => ⟨(X, 0), (hmem _).mpr rfl⟩
      left_inv := fun XY => by
        apply Subtype.ext
        ext1
        · rfl
        · exact ((hmem XY.1).mp XY.2).symm
      right_inv := fun X => rfl }
  exact WEEC.finrank_selfExt_eq_of_filteredEnd_eq_top H hfe e

end S_Deformation_HondaSystem_finrank_selfExt_eq_finrank_endHonda_of_L_eq_bot
end P2MW
export P2MW.S_Deformation_HondaSystem_finrank_selfExt_eq_finrank_endHonda_of_L_eq_bot (solution)
