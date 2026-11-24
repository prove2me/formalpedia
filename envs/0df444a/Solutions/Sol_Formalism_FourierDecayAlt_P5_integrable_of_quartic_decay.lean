-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.integrable_of_quartic_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:45:23.120165+00:00
-- url     : https://prove2.me/submissions/a4d0bfb2-1979-4639-b871-949922fa1247

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSplitAssocMeasurePreserving

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : Measure (Mt P.k P.r)} [SFinite μ]
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (φ : ℂ → ℂ) (hφc : Continuous φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C * (1 + ‖t‖) ^ (-4 : ℤ)) :
    Integrable φ := by
  have hI : Integrable (fun t : ℂ => (1 + ‖t‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  refine (hI.const_mul C).mono' hφc.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  have h4 : (1 + ‖t‖) ^ (-(4 : ℝ)) = (1 + ‖t‖) ^ (-4 : ℤ) := by
    rw [show (-(4 : ℝ)) = ((-4 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  rw [h4]
  exact hC t
end Formalism.FourierDecayAlt.P5
