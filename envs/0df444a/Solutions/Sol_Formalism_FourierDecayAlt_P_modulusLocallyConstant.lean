-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.modulusLocallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:25.000352+00:00
-- url     : https://prove2.me/submissions/122f7f91-0b25-40e7-beef-371736268074

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_mem_mulR_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_pow_mul_pow_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_isLat_mulR
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_small
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_one_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_inv_bounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_mulR_mul_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open A6x4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.ModLocConst := by
  intro K _ _ _ R ψ hD hQ Om hOm hu E hE
  obtain ⟨ϖ, hp, hex⟩ := hD.unif
  have hpq : (ϖ : K) * ((ϖ⁻¹ : Kˣ) : K) = 1 := ϖ.mul_inv
  generalize (ϖ : K) = p at hp hex hpq
  generalize ((ϖ⁻¹ : Kˣ) : K) = q at hpq
  obtain ⟨k, hk⟩ := inv_bounded hD hQ hpq hp hex hOm hu
  obtain ⟨j, hj⟩ := small hD hQ hpq hp hex hE
  have hab := pow_mul_pow_one hpq (j + 1 + k)
  refine ⟨mulR R (p ^ (j + 1 + k)), isLat_mulR hD hab, ?_⟩
  intro z hz l hl
  have hzw : z * Ring.inverse z = 1 := Ring.mul_inverse_cancel z (hu z hz)
  have hkz := hk z hz
  generalize Ring.inverse z = w at hzw hkz ⊢
  have hr := (mem_mulR_iff hab l).1 hl
  have hr' : q ^ (j + 1 + k) * l * (p ^ k * w) ∈ R := R.mul_mem hr hkz
  generalize hx : q ^ (j + 1 + k) * l * (p ^ k * w) = x at hr'
  have hlw : l * w = p ^ (j + 1) * x := by
    rw [← hx]
    have e : p ^ (j + 1) * (q ^ (j + 1 + k) * l * (p ^ k * w)) =
        (p ^ (j + 1 + k) * q ^ (j + 1 + k)) * (l * w) := by
      rw [pow_add p (j + 1) k]
      ring
    rw [e, hab, one_mul]
  obtain ⟨w', hw', hvR, hw'R⟩ := one_add hD hQ hpq hp hex (R.mul_mem (R.pow_mem hp j) hr')
  have hzl : z + l = z * (1 + p * (p ^ j * x)) := by
    have e : p * (p ^ j * x) = l * w := by rw [hlw]; ring
    rw [e]
    linear_combination (-l) * hzw
  refine ⟨?_, ?_, ?_⟩
  · apply IsUnit.of_mul_eq_one (w * w')
    rw [hzl]
    calc z * (1 + p * (p ^ j * x)) * (w * w') = (z * w) * ((1 + p * (p ^ j * x)) * w') := by ring
      _ = 1 := by rw [hzw, hw', one_mul]
  · unfold modK
    rw [hzl, mulR_mul_unit hw' hvR hw'R]
  · apply hj
    rw [hlw]
    have e : q ^ j * (p ^ (j + 1) * x) = (p ^ j * q ^ j) * (p * x) := by ring
    rw [e, pow_mul_pow_one hpq, one_mul]
    exact R.mul_mem hp hr'
end Formalism.FourierDecayAlt.P
