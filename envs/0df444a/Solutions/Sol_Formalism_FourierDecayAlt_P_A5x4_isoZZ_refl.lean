-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x4.isoZZ_refl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:19.198613+00:00
-- url     : https://prove2.me/submissions/93d6eab0-925c-4c2d-9950-c192520b9057

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_lamLin_mk_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x4
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x4
theorem _root_.solution {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) :
    LinearEquiv.refl R (coker R Z) ∈ isoZZ R Z Z :=
  ⟨rfl, fun _ _ h => (lamLin_mk_eq R Z h).symm⟩
end Formalism.FourierDecayAlt.P.A5x4
