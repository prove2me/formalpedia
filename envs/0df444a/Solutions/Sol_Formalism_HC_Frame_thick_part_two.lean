-- Prove2me | solution 1 for Formalism.HC.Frame.thick_part_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:04:59.657903+00:00
-- url     : https://prove2.me/submissions/7defdbde-dc63-4453-a659-9390c317e172

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_eq_zero_of_mem_cyclic_of_projection
import Theorems.Thm_Formalism_HC_Frame_zsmul_generator_eq_zero_iff
import Theorems.Thm_Formalism_HC_Frame_dig_eq_zsmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
private theorem sub_smul_eq_sub_smul_a0_of_dig_eq (t u₀ x : φ.A) (p q : ℤ) (sp sq : ℕ)
    (hp : t + p • x = φ.dig sp + u₀) (hq : t + q • x = φ.dig sq + u₀) :
    (q - p) • x = ((sq : ℤ) - sp) • φ.a0 := by
  rw [sub_zsmul, sub_zsmul, ← φ.dig_eq_zsmul, ← φ.dig_eq_zsmul, eq_sub_of_add_eq hq.symm,
    eq_sub_of_add_eq hp.symm]
  abel
end Formalism.HC.Frame
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution {L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < φ.n0)
    (u₀ t x : φ.A) (hord : addOrderOf (φ.h x) ≤ 4 * L) :
    {y : φ.A | (∃ i : ℤ, y = t + i • x) ∧ φ.InTranslate T u₀ y}.ncard ≤ 1 := by
  rw [Set.ncard_le_one (Set.toFinite _)]
  rintro y1 ⟨⟨i, rfl⟩, s1, hs1, h1⟩ y2 ⟨⟨j, rfl⟩, s2, hs2, h2⟩
  have e : (j - i) • x = ((s2 : ℤ) - s1) • φ.a0 := sub_smul_eq_sub_smul_a0_of_dig_eq φ t u₀ x i j s1 s2 h1 h2
  have hm0 : 0 < addOrderOf (φ.h x) := addOrderOf_pos _
  have hz : ((addOrderOf (φ.h x) : ℤ) • (((s2 : ℤ) - s1) • φ.a0)) = 0 := by
    apply φ.eq_zero_of_mem_cyclic_of_projection
    · exact φ.A0.zsmul_mem (φ.A0.zsmul_mem (AddSubgroup.mem_zmultiples φ.a0) _) _
    · rw [← e, map_zsmul, map_zsmul, smul_comm, natCast_zsmul, addOrderOf_nsmul_eq_zero, smul_zero]
  rw [smul_smul, φ.zsmul_generator_eq_zero_iff] at hz
  have t1 : 4 * (L : ℤ) * s1 < φ.n0 := by exact_mod_cast hT s1 hs1
  have t2 : 4 * (L : ℤ) * s2 < φ.n0 := by exact_mod_cast hT s2 hs2
  have hmL : (addOrderOf (φ.h x) : ℤ) ≤ 4 * L := by exact_mod_cast hord
  have hm0' : (0 : ℤ) < addOrderOf (φ.h x) := by exact_mod_cast hm0
  have p1 : (addOrderOf (φ.h x) : ℤ) * s2 ≤ 4 * L * s2 :=
    mul_le_mul_of_nonneg_right hmL (by positivity)
  have p2 : (addOrderOf (φ.h x) : ℤ) * s1 ≤ 4 * L * s1 :=
    mul_le_mul_of_nonneg_right hmL (by positivity)
  have p3 : 0 ≤ (addOrderOf (φ.h x) : ℤ) * s1 := by positivity
  have p4 : 0 ≤ (addOrderOf (φ.h x) : ℤ) * s2 := by positivity
  have hz' := Int.eq_zero_of_abs_lt_dvd hz (abs_lt.2 ⟨by linarith, by linarith⟩)
  have hs : s1 = s2 := by
    rcases mul_eq_zero.1 hz' with h | h
    · omega
    · omega
  rw [h1, h2, hs]
end Formalism.HC.Frame
