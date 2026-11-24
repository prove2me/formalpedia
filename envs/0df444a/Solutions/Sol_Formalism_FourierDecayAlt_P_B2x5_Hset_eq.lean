-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.Hset_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:41:37.629505+00:00
-- url     : https://prove2.me/submissions/9058a70b-f3db-4d7e-95bc-0e2e1682296c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_coord_heis

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
theorem _root_.solution (k r' : ℕ) : Hset k r' = {g | heis0 k r' (coord k r' g) = g} := by
  ext g
  constructor
  · intro hg
    obtain ⟨x, rfl⟩ := (show g ∈ Set.range (heis0 k r') from hg)
    show heis0 k r' (coord k r' (heis0 k r' x)) = heis0 k r' x
    rw [coord_heis]
  · intro h
    show g ∈ Set.range (heis0 k r')
    exact ⟨coord k r' g, h⟩
end Formalism.FourierDecayAlt.P.B2x5
