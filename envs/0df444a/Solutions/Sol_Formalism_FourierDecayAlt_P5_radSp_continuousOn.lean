-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.radSp_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:39:41.624684+00:00
-- url     : https://prove2.me/submissions/d8c5efc9-59e5-4796-8638-efd7ead9bf67

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasurableOfContinuousOnZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (Φ : RadSp k r z z' π π') :
    ContinuousOn (fun x : (Fin r → ℂ) × Mx k r => (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2) (DomR k r z z') := by
  obtain ⟨-, hs, -⟩ := Φ.2
  intro x₀ hx₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs x₀ hx₀
  have hFc : ContinuousAt F x₀ := hF.continuousOn.continuousAt (hU.mem_nhds hxU)
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hΦ x₀ hxU hx₀.2.1)
  filter_upwards [inter_mem_nhdsWithin (DomR k r z z') (hU.mem_nhds hxU)] with x hx
  exact hΦ x hx.2 hx.1.2.1
end Formalism.FourierDecayAlt.P5
