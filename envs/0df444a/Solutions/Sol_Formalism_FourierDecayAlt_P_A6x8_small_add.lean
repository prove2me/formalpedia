-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x8.small_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:17.325326+00:00
-- url     : https://prove2.me/submissions/53288da8-e00b-4424-a446-6361688efc9c

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
theorem _root_.solution {Om : Set K} (hC : IsCompact Om) (hO : IsOpen Om) :
    ∃ W ∈ 𝓝 (0 : K), ∀ z ∈ Om, ∀ w ∈ W, z + w ∈ Om := by
  have hn : IsOpen ((fun p : K × K => p.1 + p.2) ⁻¹' Om) := hO.preimage continuous_add
  obtain ⟨u, v, -, hv, hsu, htv, huv⟩ :=
    generalized_tube_lemma hC (isCompact_singleton (x := (0 : K))) hn (by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      have hb' : b = 0 := hb
      simpa [hb'] using ha)
  exact ⟨v, hv.mem_nhds (htv rfl), fun z hz w hw => huv (Set.mk_mem_prod (hsu hz) hw)⟩
end Formalism.FourierDecayAlt.P.A6x8
