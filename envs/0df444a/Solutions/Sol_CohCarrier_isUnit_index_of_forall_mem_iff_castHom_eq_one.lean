-- Prove2me | solution 1 for CohCarrier.isUnit_index_of_forall_mem_iff_castHom_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/0b5e0449-f0b0-59f8-82de-c282f36ce8e5

import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_isUnit_index_of_forall_mem_iff_castHom_eq_one

set_option autoImplicit false

open IsLocalRing

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (N r : ℕ) [NeZero N] (hr : r.Prime) (hr1 : ¬ p ∣ r - 1) [NeZero (N * r)]
    (H₀ : Subgroup (ZMod (N * r))ˣ)
    (hH₀ : ∀ v : (ZMod (N * r))ˣ, v ∈ H₀ ↔ ZMod.castHom (dvd_mul_left r N) (ZMod r) (v : ZMod (N * r)) = 1) :
    IsUnit ((H₀.index : ℕ) : 𝒪) := by
  haveI : Fact r.Prime := ⟨hr⟩

  set f : (ZMod (N * r))ˣ →* (ZMod r)ˣ := ZMod.unitsMap (dvd_mul_left r N) with hf
  have hker : H₀ = f.ker := by
    ext v
    rw [hH₀, MonoidHom.mem_ker, ← Units.val_eq_one, hf, ZMod.unitsMap_def, Units.coe_map]
    rfl
  have hidx : H₀.index = r - 1 := by
    rw [hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective (dvd_mul_left r N)),
      Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units]
  rw [hidx]

  by_contra hnu
  have hmem : ((r - 1 : ℕ) : 𝒪) ∈ maximalIdeal 𝒪 := (mem_maximalIdeal _).mpr hnu
  have hcop : Nat.Coprime p (r - 1) := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hr1
  have hcop' : IsCoprime (p : 𝒪) ((r - 1 : ℕ) : 𝒪) := by
    have := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom 𝒪)
    simpa using this
  obtain ⟨a, b, hab⟩ := hcop'
  apply (maximalIdeal.isMaximal 𝒪).ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp𝒪) (Ideal.mul_mem_left _ _ hmem)

end S_CohCarrier_isUnit_index_of_forall_mem_iff_castHom_eq_one
end P2MW
export P2MW.S_CohCarrier_isUnit_index_of_forall_mem_iff_castHom_eq_one (solution)
