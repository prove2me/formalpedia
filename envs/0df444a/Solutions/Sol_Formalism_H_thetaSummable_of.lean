-- Prove2me | solution 1 for Formalism.H.thetaSummable_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:54.2488+00:00
-- url     : https://prove2.me/submissions/2e5df74d-7df2-44ec-a573-01f2f2a8a89a

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Assembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace Formalism.H
theorem _root_.solution (h2 : Periodization V) (h5 : GaussFourier V) : ThetaSummable V := by
  intro Λ _ _ t ht x
  obtain ⟨hc, hO, -⟩ := h5 t ht
  have hd : (Module.finrank ℝ V : ℝ) < Module.finrank ℝ V + 1 := by linarith
  obtain ⟨-, hs, -⟩ := h2 Λ _ hc _ hd (hO _)
  exact Complex.summable_ofReal.1 (hs x)
end Formalism.H
