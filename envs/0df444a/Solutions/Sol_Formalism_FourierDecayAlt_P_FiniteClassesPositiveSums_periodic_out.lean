-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.periodic_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:44.44822+00:00
-- url     : https://prove2.me/submissions/dcb2690e-e9d2-4636-b751-1b621af91984

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteClassesPositiveSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_out_mk

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
namespace Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
theorem _root_.solution {β : Type} (f : K → β) (h1 : ∀ x, ∀ r ∈ R, f (x + r) = f x) (x : K) :
    f (Quotient.out ((x : K) : K ⧸ R.toAddSubgroup)) = f x := by
  obtain ⟨r, hr, e⟩ := out_mk R x
  rw [e, h1 x r hr]
end Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
