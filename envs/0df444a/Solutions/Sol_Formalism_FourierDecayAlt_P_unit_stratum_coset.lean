-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.unit_stratum_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:58:32.526455+00:00
-- url     : https://prove2.me/submissions/51c2d434-12c5-460b-b367-46699a27d408

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Minors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block32EqZeroOfUnipotent
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x9_block31_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x9_block31_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x9_block32_eq_zero_of_unipotent
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x9_block32_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open Formalism.FourierDecayAlt.P.S3x9 Formalism.FourierDecayAlt.S3 Matrix
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.UnitStratumCoset := by
  intro o _ _ _ ϖ hϖ r k j₀ M X₀ hj h31
  have hres : IsLocalRing.residue o ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hϖ.not_isUnit
  have h32 : (b32 j₀).map (IsLocalRing.residue o) = 0 := by
    rw [← block32_map]; exact block32_eq_zero_of_unipotent hj.2
  refine ⟨X₀ + b31 (j₀ * M), ?_, ?_⟩
  · rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, block31_add, block31_smul, h31, smul_add]
  · rw [block31_mul, h31]
    have e : ∀ a b : Matrix (Fin r) (Fin r) o,
        (a + b).map (IsLocalRing.residue o) = a.map (IsLocalRing.residue o) + b.map (IsLocalRing.residue o) :=
      fun a b => Matrix.map_add (IsLocalRing.residue o) (map_add _) a b
    have z1 : ((ϖ • X₀) * b11 M).map (IsLocalRing.residue o) = 0 := by
      rw [Matrix.smul_mul]
      ext a b
      simp [hres]
    have z2 : (b32 j₀ * b21 M).map (IsLocalRing.residue o) = 0 := by
      rw [Matrix.map_mul, h32, Matrix.zero_mul]
    rw [e, e, e, e, z1, z2]
    simp
end Formalism.FourierDecayAlt.P
