-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.complex_norm_eq_re_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:46:35.586718+00:00
-- url     : https://prove2.me/submissions/d98e43b1-2aae-463a-b35a-2f955a066a1b

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
theorem _root_.solution {z : ℂ} (hz : 0 ≤ z) : ‖z‖ = z.re := by
  obtain ⟨h1, h2⟩ := Complex.nonneg_iff.mp hz
  have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [← h2])
  conv_lhs => rw [hz']
  rw [Complex.norm_real, Real.norm_of_nonneg h1]
end Formalism.FourierDecayAlt.P5
