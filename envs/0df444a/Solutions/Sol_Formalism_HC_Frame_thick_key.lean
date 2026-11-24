-- Prove2me | solution 1 for Formalism.HC.Frame.thick_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:59:22.568948+00:00
-- url     : https://prove2.me/submissions/382356e9-49f8-4c70-bf79-dc4f280b2bdd

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
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
theorem _root_.solution {L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < φ.n0) (hR : NoRel T L)
    (u₀ t x : φ.A) (hord : 4 * L < addOrderOf x) (i₀ a b c : ℤ)
    (ha : a ∈ Finset.Ico i₀ (i₀ + L)) (hc : c ∈ Finset.Ico i₀ (i₀ + L)) (hab : a < b)
    (hbc : b < c) (hxa : φ.InTranslate T u₀ (t + a • x)) (hxb : φ.InTranslate T u₀ (t + b • x))
    (hxc : φ.InTranslate T u₀ (t + c • x)) : False := by
  obtain ⟨s1, hs1, h1⟩ := hxa
  obtain ⟨s2, hs2, h2⟩ := hxb
  obtain ⟨s3, hs3, h3⟩ := hxc
  rw [Finset.mem_Ico] at ha hc
  have small : ∀ k : ℤ, 0 < k → k < L → k • x ≠ 0 := by
    intro k hk hkL hk0
    have := Int.le_of_dvd hk (addOrderOf_dvd_iff_zsmul_eq_zero.2 hk0)
    omega
  have e12 := sub_smul_eq_sub_smul_a0_of_dig_eq φ t u₀ x a b s1 s2 h1 h2
  have e13 := sub_smul_eq_sub_smul_a0_of_dig_eq φ t u₀ x a c s1 s3 h1 h3
  have e23 := sub_smul_eq_sub_smul_a0_of_dig_eq φ t u₀ x b c s2 s3 h2 h3
  by_cases h12 : s1 = s2
  · subst h12
    exact small (b - a) (by omega) (by omega) (by rw [e12, sub_self, zero_zsmul])
  by_cases h13 : s1 = s3
  · subst h13
    exact small (c - a) (by omega) (by omega) (by rw [e13, sub_self, zero_zsmul])
  by_cases h23 : s2 = s3
  · subst h23
    exact small (c - b) (by omega) (by omega) (by rw [e23, sub_self, zero_zsmul])
  apply hR s1 hs1 s2 hs2 s3 hs3 h12 h13 h23 (b - a) (c - a) (abs_pos.2 (by omega))
    (abs_le.2 ⟨by omega, by omega⟩) (abs_pos.2 (by omega)) (abs_le.2 ⟨by omega, by omega⟩) (by omega)
  have hD : ((c - a) * ((s2 : ℤ) - s1) - (b - a) * ((s3 : ℤ) - s1)) • φ.a0 = 0 := by
    rw [sub_zsmul, ← smul_smul, ← smul_smul, ← e12, ← e13, smul_smul, smul_smul,
      mul_comm (c - a)]
    abel
  rw [φ.zsmul_generator_eq_zero_iff] at hD
  have t1 : 4 * (L : ℤ) * s1 < φ.n0 := by exact_mod_cast hT s1 hs1
  have t2 : 4 * (L : ℤ) * s2 < φ.n0 := by exact_mod_cast hT s2 hs2
  have t3 : 4 * (L : ℤ) * s3 < φ.n0 := by exact_mod_cast hT s3 hs3
  have hcaL : c - a ≤ L := by omega
  have hbaL : b - a ≤ L := by omega
  have hs1' : (0 : ℤ) ≤ s1 := by positivity
  have hs2' : (0 : ℤ) ≤ s2 := by positivity
  have hs3' : (0 : ℤ) ≤ s3 := by positivity
  have pA2 : (c - a) * (s2 : ℤ) ≤ L * s2 := mul_le_mul_of_nonneg_right hcaL hs2'
  have pA1 : (c - a) * (s1 : ℤ) ≤ L * s1 := mul_le_mul_of_nonneg_right hcaL hs1'
  have pB3 : (b - a) * (s3 : ℤ) ≤ L * s3 := mul_le_mul_of_nonneg_right hbaL hs3'
  have pB1 : (b - a) * (s1 : ℤ) ≤ L * s1 := mul_le_mul_of_nonneg_right hbaL hs1'
  have qA2 : 0 ≤ (c - a) * (s2 : ℤ) := mul_nonneg (by omega) hs2'
  have qA1 : 0 ≤ (c - a) * (s1 : ℤ) := mul_nonneg (by omega) hs1'
  have qB3 : 0 ≤ (b - a) * (s3 : ℤ) := mul_nonneg (by omega) hs3'
  have qB1 : 0 ≤ (b - a) * (s1 : ℤ) := mul_nonneg (by omega) hs1'
  have hz := Int.eq_zero_of_abs_lt_dvd hD (abs_lt.2 ⟨by linarith, by linarith⟩)
  linear_combination hz
end Formalism.HC.Frame
