-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.gV_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:20:55.55531+00:00
-- url     : https://prove2.me/submissions/517b2a5e-8f40-442d-abf3-f9994a579f51

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_Rn_mem
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts
import Theorems.Thm_Formalism_QuantumDeterminants_uHGroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution {k j ρ : ℕ} (x x' : RC k j ρ) (M : B.Mat k (j + ρ)) (hM : M ∈ B.GV k (j + ρ)) :
    (Rn k j ρ x)⁻¹ * M * Rn k j ρ x' ∈ B.GV k (j + ρ) := by
  have hH : IsUnit (Hpk k (j + ρ)).det := by
    have h := (hpkFacts k (j + ρ)).2.1
    have h2 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one] at h2
    exact isUnit_iff_exists_inv.mpr ⟨_, h2⟩
  obtain ⟨-, hmul, hinv⟩ := uHGroup _ (Hpk k (j + ρ)) hH
  exact hmul _ (hmul _ (hinv _ (Rn_mem x)).2 _ hM) _ (Rn_mem x')
end Formalism.FourierDecayAlt.P.Ux6
