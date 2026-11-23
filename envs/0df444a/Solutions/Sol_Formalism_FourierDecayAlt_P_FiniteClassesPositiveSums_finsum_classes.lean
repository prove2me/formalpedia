-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.finsum_classes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:32:11.225846+00:00
-- url     : https://prove2.me/submissions/9a74de3a-fbee-449d-8caf-91645a5b6dd8

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteClassesPositiveSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
variable {K : Type} [CommRing K] (R : Subring K)
variable {R} {F : Finset (Point K)} {Lc : Set K} {S : Finset (K ⧸ R.toAddSubgroup)}
namespace Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
theorem _root_.solution (hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ Lc → y ∈ S)
    {Θ : K → Point K → Point K → ℂ}
    (h3 : ∀ x, x ∉ Lc → ∀ h ∈ F, ∀ h' ∈ F, Θ x h h' = 0) {h h' : Point K} (hh : h ∈ F)
    (hh' : h' ∈ F) :
    ∑ᶠ y : K ⧸ R.toAddSubgroup, Θ (Quotient.out y) h h' = ∑ y ∈ S, Θ (Quotient.out y) h h' := by
  apply finsum_eq_sum_of_support_subset
  intro y hy
  by_contra hyS
  exact hy (h3 _ (fun hc => hyS (hS y hc)) h hh h' hh')
end Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
