-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.herm_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:45:23.777514+00:00
-- url     : https://prove2.me/submissions/8b53c0c9-c52a-458e-abe0-04780bce7f90

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_sum_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_hermitian_matrix_mul_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_Hmul_iL
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_Hmul_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (k r' : ℕ) (u v : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) u v =
      conj (v (i0 k r')) * u (iL k r') + herm (Hpk k r') (res k r' u) (res k r' v) + conj (v (iL k r')) * u (i0 k r') := by
  have hres : ∀ j, (Hpk k (1 + r') *ᵥ u) (levPos k 1 r' j) = (Hpk k r' *ᵥ res k r' u) j :=
    fun j => congrFun (Hmul_res k r' u) j
  simp only [herm, dotProduct]
  rw [sum_split k r']
  simp only [Pi.star_apply, hermitian_matrix_mul_first, Hmul_iL, hres, starRingEnd_apply, res]
  try ring
end Formalism.FourierDecayAlt.P.B2x5
