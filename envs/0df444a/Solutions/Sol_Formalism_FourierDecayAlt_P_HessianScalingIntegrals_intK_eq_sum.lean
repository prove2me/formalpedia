-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HessianScalingIntegrals.intK_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:17.911868+00:00
-- url     : https://prove2.me/submissions/c9c8119f-686d-4f00-bbb3-c698a10c6e4d

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HessianScalingIntegrals

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HessianScalingIntegrals
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.HessianScalingIntegrals
theorem _root_.solution (R : Subring K) (Λ L : AddSubgroup K) (d : ℕ)
    (hfin : {y : Fin d → K ⧸ Λ | ∀ i, (Quotient.out (y i) : K) ∈ L}.Finite)
    (g : (Fin d → K) → ℂ) (hg : ∀ x, g x ≠ 0 → ∀ i, x i ∈ L) :
    intK R Λ d g = (volL R Λ : ℂ) ^ d * ∑ y ∈ hfin.toFinset, g (fun i => Quotient.out (y i)) := by
  unfold intK
  congr 1
  apply finsum_eq_sum_of_support_subset
  intro y hy
  simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
  exact hg _ hy
end Formalism.FourierDecayAlt.P.HessianScalingIntegrals
