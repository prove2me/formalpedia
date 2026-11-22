-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.psd_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:59.510499+00:00
-- url     : https://prove2.me/submissions/c45a1f92-69f0-4d76-92aa-9f4b1b1b3360

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
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
theorem _root_.solution {F : Finset α} {k k' : α → α → ℂ} (h : IsPSD F k)
    (e : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y) : IsPSD F k' := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y = ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y :=
    sum_congr rfl fun x hx => sum_congr rfl fun y hy => by rw [e x hx y hy]
  rw [this]; exact h a
end Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
