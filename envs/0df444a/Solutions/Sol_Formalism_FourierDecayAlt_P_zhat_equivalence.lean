-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.zhat_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:23:20.837172+00:00
-- url     : https://prove2.me/submissions/c4deaba0-d2cb-4b84-b3ae-c8616b051d66

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_uMap_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_colEq
import Theorems.Thm_Formalism_QuantumDeterminants_S_F
import Theorems.Thm_Formalism_QuantumDeterminants_Sset_UH
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_Zhat_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.ZhatEquiv := by
  intro k r z z' hz hz' s hs s' hs' g
  obtain ⟨U, _, _, hsF⟩ := S_F hz.1 hs
  obtain ⟨U', _, _, hs'F⟩ := S_F hz'.1 hs'
  rw [uMap_eq hz s U (colEq hsF), uMap_eq hz' s' U' (colEq hs'F), Zhat_eq, Zhat_eq]
  have hsU : sᴴ * Hpk k r * s = Hpk k r := Sset_UH hs
  have hu : IsUnit s.det := WeylGroupFacts.isUnit_of_uh hsU
  have hHs : Hpk k r * s⁻¹ = sᴴ * Hpk k r := by
    calc Hpk k r * s⁻¹ = sᴴ * Hpk k r * s * s⁻¹ := by rw [hsU]
      _ = sᴴ * Hpk k r := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  calc (Fm k r z)ᴴ * Hpk k r * (s⁻¹ * g * s') * Fm k r z'
      = (Fm k r z)ᴴ * (Hpk k r * s⁻¹) * g * (s' * Fm k r z') := by simp only [Matrix.mul_assoc]
    _ = (Fm k r z)ᴴ * (sᴴ * Hpk k r) * g * (Fm k r z' * U') := by rw [hHs, hs'F]
    _ = (s * Fm k r z)ᴴ * Hpk k r * g * Fm k r z' * U' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (Fm k r z * U)ᴴ * Hpk k r * g * Fm k r z' * U' := by rw [hsF]
    _ = Uᴴ * ((Fm k r z)ᴴ * Hpk k r * g * Fm k r z') * U' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P
