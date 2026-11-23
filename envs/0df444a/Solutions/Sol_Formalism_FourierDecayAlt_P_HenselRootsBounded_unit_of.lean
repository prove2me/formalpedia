-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.unit_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:19.584271+00:00
-- url     : https://prove2.me/submissions/3c9ada52-2bd3-4f08-be3b-757d32f0e83f

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_HenselRootsBounded_inv_one_add__182a426a02a7

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
theorem _root_.solution (h : Ctx K R ϖ) {k : ℤ} (hk : 1 ≤ k) {w : K} (hw : w ∈ Pk R ϖ k) :
    ∃ (ω : Kˣ) (w' : K), (ω : K) = 1 + w ∧ ((ω⁻¹ : Kˣ) : K) = 1 + w' ∧ w' ∈ Pk R ϖ k := by
  obtain ⟨w', hw', h1⟩ := inv_one_add' h hk hw
  exact ⟨⟨1 + w, 1 + w', h1, by rw [mul_comm]; exact h1⟩, w', rfl, rfl, hw'⟩
end Formalism.FourierDecayAlt.P.HenselRootsBounded
