-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.heisClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:23:06.860812+00:00
-- url     : https://prove2.me/submissions/3c57432e-010b-42a3-b1bd-8d7c7a1e31af

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_heisMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_heisenberg_at_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_heisenberg_mul_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_heisInv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_coord_heis
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_isClosed_Hset

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
theorem _root_.solution : HeisClosed := by
  intro k r'
  refine ⟨fun x y h => ?_, ⟨?_, ?_, ?_, ?_, isClosed_Hset k r'⟩⟩
  · have := congrArg (coord k r') h
    rwa [coord_heis, coord_heis] at this
  · exact Set.mem_range.mpr ⟨(0, 0), heisenberg_at_zero k r'⟩
  · intro a ha b hb
    obtain ⟨x, rfl⟩ := Set.mem_range.mp ha
    obtain ⟨y, rfl⟩ := Set.mem_range.mp hb
    exact Set.mem_range.mpr ⟨_, (heisMul k r' x y).symm⟩
  · intro a ha
    obtain ⟨x, rfl⟩ := Set.mem_range.mp ha
    exact Set.mem_range.mpr ⟨_, (heisInv k r' x).symm⟩
  · intro a ha
    obtain ⟨x, rfl⟩ := Set.mem_range.mp ha
    exact Matrix.isUnit_det_of_right_inverse (heisenberg_mul_neg k r' x)
end Formalism.FourierDecayAlt.P.B2x5
