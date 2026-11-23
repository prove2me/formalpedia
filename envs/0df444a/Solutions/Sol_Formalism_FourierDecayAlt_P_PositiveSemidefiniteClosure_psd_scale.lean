-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.psd_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:38.313217+00:00
-- url     : https://prove2.me/submissions/63c8fa97-8bca-4066-9546-17acfea7bfc9

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedVectorChoices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
namespace Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
theorem _root_.solution {X : Type} {F : Finset X} {k : X → X → ℂ} (c : X → ℝ) (hk : IsPSD F k) :
    IsPSD F (fun x y => ((c x * c y : ℝ) : ℂ) * k x y) := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (((c x * c y : ℝ) : ℂ) * k x y) =
      ∑ x ∈ F, ∑ y ∈ F, (a x * (c x : ℂ)) * conj (a y * (c y : ℂ)) * k x y :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [map_mul, Complex.conj_ofReal]; push_cast; ring
  rw [this]; exact hk _
end Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
