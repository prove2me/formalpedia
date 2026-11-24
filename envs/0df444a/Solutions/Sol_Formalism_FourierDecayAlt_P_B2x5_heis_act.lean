-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.heis_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:03:08.470042+00:00
-- url     : https://prove2.me/submissions/209c35ec-9e53-4dbb-babc-c245476107a4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_sum

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
theorem _root_.solution (k r' : ℕ) (v u : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) :
    heisG k r' v b *ᵥ u = u - herm (Hpk k (1 + r')) u v • e0 k r' + herm (Hpk k (1 + r')) u (e0 k r') • (v + b • e0 k r') := by
  have key : ∀ (w c : Fin (2 * (1 + r') + k + 1) → ℂ), vecMulVec w c *ᵥ u = (∑ j, c j * u j) • w := by
    intro w c
    funext i
    simp only [mulVec, dotProduct, vecMulVec, of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [heisG, sub_mulVec, add_mulVec, one_mulVec, key, herm_sum]
end Formalism.FourierDecayAlt.P.B2x5
