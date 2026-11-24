-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.row_of_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:21:23.620514+00:00
-- url     : https://prove2.me/submissions/65dd26b3-002c-49a8-ad9d-945ec89a4bd2

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement

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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution {m : ℕ} (g H : Matrix (Fin m) (Fin m) ℂ) (i₀ j : Fin m)
    (hc : ∀ p, g p i₀ = if p = i₀ then 1 else 0) : (gᴴ * H * g) i₀ j = (H * g) i₀ j := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single i₀]
  · rw [Matrix.conjTranspose_apply, hc i₀, if_pos rfl, star_one, one_mul]
  · intro m _ hm
    rw [Matrix.conjTranspose_apply, hc m, if_neg hm, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.LongWeylElement
