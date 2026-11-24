-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.Hmul_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:22:54.371205+00:00
-- url     : https://prove2.me/submissions/eb56a4cf-17d2-4c79-b813-c8da1958c8b8

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_sum_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_hermitian_levi_entry_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_H_lev_iL
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_H_lev_lev

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
theorem _root_.solution (k r' : ℕ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    res k r' (Hpk k (1 + r') *ᵥ u) = Hpk k r' *ᵥ res k r' u := by
  funext j
  simp only [res, mulVec, dotProduct]
  rw [sum_split k r']
  simp [hermitian_levi_entry_zero, H_lev_iL, H_lev_lev]
end Formalism.FourierDecayAlt.P.B2x5
