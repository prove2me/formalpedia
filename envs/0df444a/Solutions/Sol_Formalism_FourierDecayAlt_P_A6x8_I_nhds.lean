-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x8.I_nhds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:46:03.740013+00:00
-- url     : https://prove2.me/submissions/a0a14450-1449-498e-8c3c-5318c8d0c499

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x8
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.A6x8
theorem _root_.solution {R : Subring K} (ho : IsOpen (R : Set K)) (a : Kˣ) : I R (a : K) ∈ 𝓝 (0 : K) := by
  have : I R (a : K) = (fun x => ((a⁻¹ : Kˣ) : K) * x) ⁻¹' (R : Set K) := by
    ext x; constructor
    · rintro ⟨r, hr, rfl⟩
      show ((a⁻¹ : Kˣ) : K) * ((a : K) * r) ∈ R
      simpa using hr
    · intro hx
      exact ⟨_, hx, by simp⟩
  rw [this]
  refine (ho.preimage (continuous_const.mul continuous_id)).mem_nhds ?_
  show ((a⁻¹ : Kˣ) : K) * 0 ∈ R
  simp
end Formalism.FourierDecayAlt.P.A6x8
