-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite.psd_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:05.677724+00:00
-- url     : https://prove2.me/submissions/19443b35-2114-4d67-9d13-cefc5626eeb2

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanPositiveSemidefinite

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
variable {X : Type}
namespace Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
theorem _root_.solution {F : Finset X} {k : X → X → ℂ} (c : ℝ) (hc : 0 ≤ c) (hk : IsPSD F k) :
    IsPSD F (fun x y => (c : ℂ) * k x y) := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((c : ℂ) * k x y) =
      (c : ℂ) * ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [this, Complex.re_ofReal_mul, Complex.im_ofReal_mul, (hk a).1]
  exact ⟨by simp, mul_nonneg hc (hk a).2⟩
end Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
