-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.approx_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:07.254393+00:00
-- url     : https://prove2.me/submissions/a2986fc3-6269-4761-a39f-e2d9bddd3c7f

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_isClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_inter_zero

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
theorem _root_.solution (h : Ctx K R ϖ) {C : Set K} (hC : IsCompact C) {f : K → K} (hf : Continuous f)
    (hap : ∀ k : ℕ, ∃ w ∈ C, f w ∈ Pk R ϖ k) : ∃ w ∈ C, f w = 0 := by
  have := h.t2
  have := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun k : ℕ => C ∩ f ⁻¹' (Pk R ϖ k : Set K))
    (by
      intro i x hx
      exact ⟨hx.1, Pk_mono h.mem (by push_cast; omega) hx.2⟩)
    (by intro i; obtain ⟨w, hw, hw'⟩ := hap i; exact ⟨w, hw, hw'⟩)
    (hC.inter_right ((Pk_isClosed h _).preimage hf))
    (fun i => hC.isClosed.inter ((Pk_isClosed h _).preimage hf))
  obtain ⟨w, hw⟩ := this
  rw [Set.mem_iInter] at hw
  exact ⟨w, (hw 0).1, inter_zero h fun k => (hw k).2⟩
end Formalism.FourierDecayAlt.P.HenselRootsBounded
