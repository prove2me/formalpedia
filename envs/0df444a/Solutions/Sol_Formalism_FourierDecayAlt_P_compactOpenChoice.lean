-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.compactOpenChoice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:40.886967+00:00
-- url     : https://prove2.me/submissions/2d2a960d-a019-4f4b-af15-ac7d8fd9d1a9

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_mem_mulR_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_pow_mul_pow_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_psi_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_isLat_mulR
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_small
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_bounded

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
theorem _root_.solution : Formalism.FourierDecayAlt.A6.LatChoice := by
  intro K _ _ _ R ψ hD hQ
  obtain ⟨ϖ, hp, hex⟩ := hD.unif
  have hpq : (ϖ : K) * ((ϖ⁻¹ : Kˣ) : K) = 1 := ϖ.mul_inv
  constructor
  · intro C hC
    obtain ⟨m, hm⟩ := bounded hD hp hex hC
    have hab := pow_mul_pow_one hpq m
    refine ⟨mulR R ((ϖ : K) ^ m), isLat_mulR hD hab, ?_, ?_⟩
    · intro x hx
      have h := (mem_mulR_iff hab x).1 hx
      have e : x = (ϖ : K) ^ m * (((ϖ⁻¹ : Kˣ) : K) ^ m * x) := by linear_combination (-x) * hab
      rw [e]
      exact R.mul_mem (R.pow_mem hp m) h
    · intro z hz l hl
      apply psi_one hD
      have h := (mem_mulR_iff hab l).1 hl
      have e : z * l = ((ϖ : K) ^ m * z) * (((ϖ⁻¹ : Kˣ) : K) ^ m * l) := by
        linear_combination (-(z * l)) * hab
      rw [e]
      exact R.mul_mem (hm z hz) h
  · intro V hV
    obtain ⟨m, hm⟩ := small hD hQ hpq hp hex hV
    have hab := pow_mul_pow_one hpq m
    have hba : ((ϖ⁻¹ : Kˣ) : K) ^ m * (ϖ : K) ^ m = 1 := by rw [mul_comm]; exact hab
    refine ⟨mulR R (((ϖ⁻¹ : Kˣ) : K) ^ m), isLat_mulR hD hba, ?_, ?_⟩
    · intro x hx
      exact (mem_mulR_iff hba x).2 (R.mul_mem (R.pow_mem hp m) hx)
    · intro z hz
      apply hm
      apply (hD.selfDual _).1
      intro r hr
      have hl : ((ϖ⁻¹ : Kˣ) : K) ^ m * r ∈ mulR R (((ϖ⁻¹ : Kˣ) : K) ^ m) := by
        apply (mem_mulR_iff hba _).2
        rw [← mul_assoc, hab, one_mul]
        exact hr
      have h := hz _ hl
      have e : ((ϖ⁻¹ : Kˣ) : K) ^ m * z * r = z * (((ϖ⁻¹ : Kˣ) : K) ^ m * r) := by ring
      rw [e]
      exact h
end Formalism.FourierDecayAlt.P
