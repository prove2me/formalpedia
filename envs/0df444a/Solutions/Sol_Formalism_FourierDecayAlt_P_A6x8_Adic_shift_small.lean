-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x8.Adic.shift_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:50:09.474125+00:00
-- url     : https://prove2.me/submissions/9d419cad-dfe4-45d3-91c2-d4b15a117148

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_I_nhds
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Near_mul

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
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.A6x8
namespace Adic
theorem _root_.solution (h : Adic R ϖ) (Sg : Finset K) (a : Kˣ) :
    ∃ V ∈ 𝓝 (0 : K), ∀ t ∈ V, ∀ σ ∈ Sg, σ * t ∈ I R (a : K) := by
  refine ⟨⋂ σ ∈ Sg, (fun t => σ * t) ⁻¹' I R (a : K),
    (Filter.biInter_finset_mem Sg).2 fun σ _ => ?_, fun t ht σ hσ => ?_⟩
  · have : ContinuousAt (fun t : K => σ * t) 0 := (continuous_const.mul continuous_id).continuousAt
    exact this.preimage_mem_nhds (by simpa using I_nhds h.isOpen a)
  · exact Set.mem_iInter₂.1 ht σ hσ
end Adic
end Formalism.FourierDecayAlt.P.A6x8
