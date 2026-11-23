-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x8.small_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:13.516234+00:00
-- url     : https://prove2.me/submissions/6093d1a8-84dc-4854-872a-ba5980cc8d53

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_small_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_small_add

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
theorem _root_.solution {Om : Set K} (hC : IsCompact Om) (hO : IsOpen Om) :
    ∃ E ∈ 𝓝 (0 : K), ∀ z ∈ Om, ∀ κ : K, κ - 1 ∈ E → κ * z ∈ Om := by
  obtain ⟨W, hW, h1⟩ := small_add hC hO
  obtain ⟨E, hE, h2⟩ := small_mul hC hW
  refine ⟨E, hE, fun z hz κ hκ => ?_⟩
  have := h1 z hz _ (h2 _ hκ z hz)
  have e : z + (κ - 1) * z = κ * z := by ring
  rwa [e] at this
end Formalism.FourierDecayAlt.P.A6x8
