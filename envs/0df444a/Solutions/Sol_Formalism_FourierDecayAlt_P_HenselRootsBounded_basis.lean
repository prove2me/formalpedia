-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:07.410768+00:00
-- url     : https://prove2.me/submissions/3dc9d998-b0d2-485a-9027-a3bbbe15e044

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_isCompact
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
theorem _root_.solution (h : Ctx K R ϖ) {W : Set K} (hW : W ∈ 𝓝 (0 : K)) :
    ∃ k : ℕ, ∀ x ∈ Pk R ϖ k, x ∈ W := by
  have := h.t2
  by_contra hcon
  push Not at hcon
  obtain ⟨W', hsub, hopen, h0⟩ := mem_nhds_iff.1 hW
  have := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun k : ℕ => (Pk R ϖ k : Set K) ∩ W'ᶜ)
    (by
      intro i x hx
      exact ⟨Pk_mono h.mem (by push_cast; omega) hx.1, hx.2⟩)
    (by intro i; obtain ⟨w, hw, hw'⟩ := hcon i; exact ⟨w, hw, fun hh => hw' (hsub hh)⟩)
    ((Pk_isCompact h _).inter_right hopen.isClosed_compl)
    (fun i => (Pk_isClosed h _).inter hopen.isClosed_compl)
  obtain ⟨w, hw⟩ := this
  rw [Set.mem_iInter] at hw
  have hw0 : w = 0 := inter_zero h fun k => (hw k).1
  exact (hw 0).2 (hw0 ▸ h0)
end Formalism.FourierDecayAlt.P.HenselRootsBounded
