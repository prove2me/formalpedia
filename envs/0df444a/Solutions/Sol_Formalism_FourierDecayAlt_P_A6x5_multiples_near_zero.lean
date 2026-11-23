-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x5.multiples_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:21.745872+00:00
-- url     : https://prove2.me/submissions/da486efa-26b7-4eaa-879e-0f2bc4cc1523

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x5
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.A6x5
theorem _root_.solution (C : Set K) (hC : IsCompact C) (i : K) (hi : ∀ a : K, a * i ∈ C)
    (W : Set K) (hW : W ∈ 𝓝 (0 : K)) : ∃ k : ℕ, ((k + 1 : ℕ) : K) * i ∈ W := by
  obtain ⟨a, _, ha⟩ := hC.exists_mapClusterPt_of_frequently (l := atTop)
    (f := fun n : ℕ => (n : K) * i) (Eventually.of_forall fun n => hi _).frequently
  have hc : Tendsto (fun p : K × K => p.2 - p.1) (𝓝 (a, a)) (𝓝 0) := by
    have : Continuous (fun p : K × K => p.2 - p.1) := continuous_snd.sub continuous_fst
    simpa using this.tendsto (a, a)
  have h1 := hc hW
  rw [nhds_prod_eq, Filter.mem_map, Filter.mem_prod_self_iff] at h1
  obtain ⟨W', hW', hsub⟩ := h1
  have hf := Filter.frequently_atTop.1 (ha.frequently hW')
  obtain ⟨n, _, hn⟩ := hf 0
  obtain ⟨m, hm, hm'⟩ := hf (n + 1)
  obtain ⟨k, rfl⟩ : ∃ k, m = n + 1 + k := ⟨m - (n + 1), by omega⟩
  refine ⟨k, ?_⟩
  have h2 : (((n : K) * i, ((n + 1 + k : ℕ) : K) * i) : K × K) ∈ W' ×ˢ W' := ⟨hn, hm'⟩
  have h3 := hsub h2
  simp only [Set.mem_preimage] at h3
  have h4 : ((n + 1 + k : ℕ) : K) * i - (n : K) * i = ((k + 1 : ℕ) : K) * i := by
    push_cast; ring
  rwa [h4] at h3
end Formalism.FourierDecayAlt.P.A6x5
