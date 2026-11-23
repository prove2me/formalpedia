-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.tube
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:59.933741+00:00
-- url     : https://prove2.me/submissions/cd6edc48-20e7-45d9-a17d-925d97a89241

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution (h : Ctx K R ϖ) {W : Set K} (hW : W ∈ 𝓝 (0 : K)) :
    ∃ V ∈ 𝓝 (0 : K), ∀ v ∈ V, ∀ r ∈ R, v * r ∈ W := by
  obtain ⟨W', hsub, hopen, h0⟩ := mem_nhds_iff.1 hW
  obtain ⟨u, v, hu, _, h0u, hRv, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : K))) h.isCompact
      (n := (fun p : K × K => p.1 * p.2) ⁻¹' W') (hopen.preimage continuous_mul)
      (by
        rintro ⟨a, b⟩ ⟨ha, _⟩
        simp only [Set.mem_singleton_iff] at ha
        simp only [Set.mem_preimage, ha, zero_mul]; exact h0)
  refine ⟨u, hu.mem_nhds (h0u rfl), fun x hx r hr => hsub ?_⟩
  exact huv (Set.mk_mem_prod hx (hRv hr))
end Formalism.FourierDecayAlt.P.HenselRootsBounded
