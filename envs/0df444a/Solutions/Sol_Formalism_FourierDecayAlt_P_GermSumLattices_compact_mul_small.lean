-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.compact_mul_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:29.338076+00:00
-- url     : https://prove2.me/submissions/613b952d-7cd7-460a-afa2-b1ed7c24a70f

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution {C : Set K} (hC : IsCompact C) {W : Set K} (hW : W ∈ 𝓝 (0 : K)) :
    ∃ E ∈ 𝓝 (0 : K), ∀ z ∈ C, ∀ e ∈ E, z * e ∈ W := by
  obtain ⟨W', hW'W, hW'o, h0⟩ := mem_nhds_iff.1 hW
  have hn : IsOpen {p : K × K | p.1 * p.2 ∈ W'} := hW'o.preimage continuous_mul
  obtain ⟨u, v, hu, hv, hCu, h0v, huv⟩ :=
    generalized_tube_lemma hC (isCompact_singleton (x := (0 : K))) hn (by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      have hb' : b = 0 := hb
      subst hb'
      simpa using h0)
  exact ⟨v, hv.mem_nhds (h0v rfl), fun z hz e he =>
    hW'W (huv (show ((z, e) : K × K) ∈ u ×ˢ v from ⟨hCu hz, he⟩))⟩
end Formalism.FourierDecayAlt.P.GermSumLattices
