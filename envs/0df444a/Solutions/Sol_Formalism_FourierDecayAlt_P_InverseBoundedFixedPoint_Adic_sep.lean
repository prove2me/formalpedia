-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.sep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:56.885482+00:00
-- url     : https://prove2.me/submissions/9ff05701-9138-4cfb-9147-a1c7052ddfa3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
namespace Adic
theorem _root_.solution (h : Adic R ϖ) (x : K) (hx : ∀ n, x ∈ I R ((ϖ : K) ^ n)) : x = 0 := by
  have := h.t2
  by_contra hx0
  have hW : ({x}ᶜ : Set K) ∈ 𝓝 (0 : K) := isOpen_compl_singleton.mem_nhds (by
    simpa using Ne.symm hx0)
  obtain ⟨n, hn⟩ := h.basis _ hW
  obtain ⟨r, hr, e⟩ := hx n
  exact hn r hr e.symm
end Adic
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
