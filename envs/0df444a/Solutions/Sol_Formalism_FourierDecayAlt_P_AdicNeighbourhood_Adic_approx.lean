-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.Adic.approx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:36.725822+00:00
-- url     : https://prove2.me/submissions/7d959178-917f-4646-96eb-4273f2fcb3d9

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdicNeighbourhood
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood
namespace Adic
theorem _root_.solution (h : Adic R ϖ) (f : K → K) (hf : Continuous f) (b : K)
    (ha : ∀ n : ℕ, ∃ r ∈ R, ∃ e ∈ R, f r = b + (ϖ : K) ^ n * e) : ∃ r ∈ R, f r = b := by
  have := h.t2
  have hcl : IsClosed (f '' (R : Set K)) := (h.isCompact.image hf).isClosed
  have hb : b ∈ closure (f '' (R : Set K)) := by
    rw [mem_closure_iff_nhds]
    intro N hN
    have hW : {y | b + y ∈ N} ∈ 𝓝 (0 : K) := by
      have : ContinuousAt (fun y : K => b + y) 0 := (continuous_const.add continuous_id).continuousAt
      exact this.preimage_mem_nhds (by simpa using hN)
    obtain ⟨n, hn⟩ := h.basis _ hW
    obtain ⟨r, hr, e, he, hre⟩ := ha n
    exact ⟨f r, by rw [hre]; exact hn e he, r, hr, rfl⟩
  rw [hcl.closure_eq] at hb
  obtain ⟨r, hr, e⟩ := hb
  exact ⟨r, hr, e⟩
end Adic
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
