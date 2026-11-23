-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.bounded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:54.050842+00:00
-- url     : https://prove2.me/submissions/17967d65-75a5-4aa9-879f-e90601907fd1

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_isOpen
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_ex

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
theorem _root_.solution (h : Ctx K R ϖ) {C : Set K} (hC : IsCompact C) :
    ∃ b : ℕ, ∀ c ∈ C, c ∈ Pk R ϖ (-(b : ℤ)) := by
  obtain ⟨b, hb⟩ := hC.elim_directed_cover (fun b : ℕ => (Pk R ϖ (-(b : ℤ)) : Set K))
    (fun b => Pk_isOpen h _)
    (by
      intro x _
      obtain ⟨b, hb⟩ := Pk_ex h x
      exact Set.mem_iUnion.2 ⟨b, hb⟩)
    (by
      intro i j
      exact ⟨max i j, fun x hx => Pk_mono h.mem (by push_cast; omega) hx,
        fun x hx => Pk_mono h.mem (by push_cast; omega) hx⟩)
  exact ⟨b, fun c hc => hb hc⟩
end Formalism.FourierDecayAlt.P.HenselRootsBounded
