-- Prove2me | solution 1 for CohCarrier.injective_iDeg_one_of_isUnit_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4207bf35-c134-5b4c-9611-537c1da6ebbe

import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_injective_iDeg_one_of_isUnit_relIndex

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CongruenceSubgroup

namespace Ws23D3b

open CongruenceSubgroup CohCarrier
open scoped MatrixGroups

variable (M : ℕ) [NeZero M] (H H' : Subgroup (ZMod M)ˣ)

theorem coe_iotaDeg_one (h : LevelLE M M H' H 1) (γ : ↥(GammaH M H)) :
    ((iotaDeg M M H' H 1 h γ : ↥(GammaH M H')) : SL(2, ℤ)) = (γ : SL(2, ℤ)) := by
  show conjLowerMat 1 (γ : SL(2, ℤ)) (h.dvd_entry γ) = _
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [conjLowerMat]

theorem pow_relIndex_mem (δ : ↥(GammaH M H')) :
    ((δ ^ H.relIndex H' : ↥(GammaH M H')) : SL(2, ℤ)) ∈ GammaH M H := by
  obtain ⟨hδ0, hδH'⟩ := mem_GammaH_iff.mp δ.2
  rw [Subgroup.coe_pow, mem_GammaH_iff]
  refine ⟨Subgroup.pow_mem _ hδ0 _, ?_⟩

  set u : (ZMod M)ˣ := gamma0Units M ⟨(δ : SL(2, ℤ)), hδ0⟩ with hu
  have hu' : u ∈ H' := hδH'
  have hpow : (⟨u, hu'⟩ : ↥H') ^ (H.subgroupOf H').index ∈ H.subgroupOf H' :=
    Subgroup.pow_index_mem (H.subgroupOf H') ⟨u, hu'⟩
  rw [Subgroup.mem_subgroupOf, SubgroupClass.coe_pow] at hpow
  have e : gamma0Units M ⟨((⟨(δ : SL(2, ℤ)), hδ0⟩ : Gamma0 M) ^ H.relIndex H' : Gamma0 M), Subgroup.pow_mem _ hδ0 _⟩
      = u ^ H.relIndex H' := by
    rw [← map_pow]
  convert hpow using 1
  exact e

variable (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A]

theorem main (h : LevelLE M M H' H 1) (hunit : IsUnit ((H.relIndex H' : ℕ) : R)) :
    Function.Injective (iDeg' M M H' H 1 A h) := by
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨δ, rfl⟩ := Additive.ofMul.surjective x

  have hvan : ∀ (γ : ↥(GammaH M H')) (hγ : (γ : SL(2, ℤ)) ∈ GammaH M H), φ (Additive.ofMul γ) = 0 := by
    intro γ hγ
    have h1 := DFunLike.congr_fun hφ (Additive.ofMul (⟨(γ : SL(2, ℤ)), hγ⟩ : ↥(GammaH M H)))
    rw [AddMonoidHom.zero_apply] at h1
    have h2 : (iotaDeg M M H' H 1 h ⟨(γ : SL(2, ℤ)), hγ⟩ : ↥(GammaH M H')) = γ :=
      Subtype.ext (coe_iotaDeg_one M H H' h ⟨(γ : SL(2, ℤ)), hγ⟩)
    rw [← h2]
    exact h1

  set m : ℕ := H.relIndex H' with hm
  have hmul : m • φ (Additive.ofMul δ) = 0 := by
    rw [← map_nsmul, ← ofMul_pow]
    exact hvan (δ ^ m) (pow_relIndex_mem M H H' δ)
  obtain ⟨w, hw⟩ := hunit
  rw [AddMonoidHom.zero_apply]
  calc φ (Additive.ofMul δ) = ((w⁻¹ : Rˣ) : R) • ((w : R) • φ (Additive.ofMul δ)) := by
        rw [smul_smul, Units.inv_mul, one_smul]
    _ = 0 := by rw [hw, Nat.cast_smul_eq_nsmul, hmul, smul_zero]

end Ws23D3b

open CongruenceSubgroup in
theorem solution
    (M : ℕ) [NeZero M] (H H' : Subgroup (ZMod M)ˣ)
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A]
    (h : CohCarrier.LevelLE M M H' H 1)
    (hunit : IsUnit ((H.relIndex H' : ℕ) : R)) :
    Function.Injective (CohCarrier.iDeg' M M H' H 1 A h) :=
  Ws23D3b.main M H H' R A h hunit

end S_CohCarrier_injective_iDeg_one_of_isUnit_relIndex
end P2MW
export P2MW.S_CohCarrier_injective_iDeg_one_of_isUnit_relIndex (solution)
