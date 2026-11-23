-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MeanNormSquaredBound.sum_sub_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:41.995813+00:00
-- url     : https://prove2.me/submissions/921eac0d-e90c-4a6c-9d86-fcdfd8810baa

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
theorem _root_.solution {α β M : Type} [AddCommMonoid M] (A : Finset α) (B : Finset β)
    (f : α × β → M) : ∑ p : ↥A × ↥B, f (p.1.1, p.2.1) = ∑ p ∈ A ×ˢ B, f p := by
  rw [Fintype.sum_prod_type, Finset.sum_product, ← Finset.sum_coe_sort A]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [← Finset.sum_coe_sort B]
end Formalism.FourierDecayAlt.P.MeanNormSquaredBound
