-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.small_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:14.364121+00:00
-- url     : https://prove2.me/submissions/3e3292f5-a795-4b7a-9120-f8c1511e95f2

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
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
theorem _root_.solution {C : Set K} (hC : IsCompact C) {W : Set K} (hW : W ∈ 𝓝 (0 : K)) :
    ∃ U ∈ 𝓝 (0 : K), ∀ u ∈ U, ∀ c ∈ C, u * c ∈ W := by
  obtain ⟨W', hW'W, hW'o, h0⟩ := mem_nhds_iff.1 hW
  have hn : IsOpen ((fun p : K × K => p.1 * p.2) ⁻¹' W') := hW'o.preimage continuous_mul
  obtain ⟨u, v, hu, -, hsu, htv, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : K))) hC hn (by
      rintro ⟨a, b⟩ ⟨ha, -⟩
      have ha' : a = 0 := ha
      simp [ha', h0])
  exact ⟨u, hu.mem_nhds (hsu rfl), fun a ha c hc => hW'W (huv (Set.mk_mem_prod ha (htv hc)))⟩
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
