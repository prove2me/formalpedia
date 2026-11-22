-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MeanNormSquaredBound.inner_sum_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:50.982237+00:00
-- url     : https://prove2.me/submissions/7c147c49-7cbc-46a6-9f65-e376385633ce

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanNormSquaredBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.MeanNormSquaredBound
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.MeanNormSquaredBound
theorem _root_.solution {ι κ : Type} (S : Finset ι) (S' : Finset κ) (c : ι → ℂ) (d : κ → ℂ)
    (v : ι → E) (v' : κ → E) :
    inner ℂ (∑ j ∈ S', d j • v' j) (∑ i ∈ S, c i • v i) =
      ∑ i ∈ S, ∑ j ∈ S', c i * conj (d j) * inner ℂ (v' j) (v i) := by
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring
end Formalism.FourierDecayAlt.P.MeanNormSquaredBound
