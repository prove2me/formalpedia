-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.norm_long_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:22.40366+00:00
-- url     : https://prove2.me/submissions/68b07bb6-d851-4813-ba23-3614127c9f59

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_norm_entry_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_wMat_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution {d : ℕ} (z : ℂ) (v : UT d → ℂ) (Z : Mat d) (hZ : Z = ptLong d z * G.upper v) :
    ‖z • v‖ ≤ ‖Z‖ := by
  have hent : ∀ i j, ‖(ptLong d z * G.upper v) i j‖ ≤ ‖Z‖ := fun i j => by
    have he : Z i j = (ptLong d z * G.upper v) i j := by rw [hZ]
    rw [← he]; exact norm_entry_le Z i j
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun ⟨⟨i, j⟩, hij⟩ => ?_
  have h := hent i.rev j
  have hij' : i < j := hij
  rw [ptLong, Matrix.smul_mul, Matrix.smul_apply, wMat_mul_apply, Fin.rev_rev] at h
  simpa [G.upper, strictUpper, hij', Matrix.one_apply, hij'.ne] using h
end Formalism.FourierDecayAlt.P.G7
