-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.annihilatorCharacters
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:40.795638+00:00
-- url     : https://prove2.me/submissions/13051c00-ccdb-40bd-be99-70e46cca0e7b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_addChar_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_mem_mulR_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_pow_mul_pow_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_small
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_dual_exists

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
theorem _root_.solution : Formalism.FourierDecayAlt.A6.PerpDual := by
  intro K _ _ _ R ψ hD hQ L₁ hL₁ hle χ hχ
  obtain ⟨ϖ, hp, hex⟩ := hD.unif
  have hpq : (ϖ : K) * ((ϖ⁻¹ : Kˣ) : K) = 1 := ϖ.mul_inv
  constructor
  · obtain ⟨m, hm⟩ := small hD hQ hpq hp hex (hL₁.1.mem_nhds L₁.zero_mem)
    have hab := pow_mul_pow_one hpq m
    obtain ⟨z, hz⟩ := dual_exists hD hab (R.pow_mem hp m) χ
      (fun r hr => hχ r (hm _ ((mem_mulR_iff hab _).1 hr)))
    refine ⟨z, ?_, hz⟩
    intro l hl
    have h := hz ⟨l, hle hl⟩
    rw [hχ ⟨l, hle hl⟩ hl] at h
    exact h.symm
  · intro z z' hz hz'
    apply (hD.selfDual _).1
    intro r hr
    have h1 := hz ⟨r, hr⟩
    have h2 := hz' ⟨r, hr⟩
    have h3 : ψ ((z - z') * r) * ψ (z' * r) = ψ (z * r) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    have h4 : ψ (z' * r) = ψ (z * r) := by rw [← h1, ← h2]
    rw [h4] at h3
    exact mul_right_cancel₀ (addChar_ne_zero ψ _) (by rw [h3, one_mul])
end Formalism.FourierDecayAlt.P
