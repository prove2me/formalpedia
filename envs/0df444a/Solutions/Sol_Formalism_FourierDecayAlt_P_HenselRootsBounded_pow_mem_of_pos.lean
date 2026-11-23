-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.pow_mem_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:54.788882+00:00
-- url     : https://prove2.me/submissions/932e1bf0-82e0-4d6e-a501-0814f845540b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_smul__abf4aaf00d8f
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_R

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
theorem _root_.solution (h : Ctx K R ϖ) {k : ℤ} (hk : 0 ≤ k) {x : K} (hx : x ∈ Pk R ϖ k) {m : ℕ}
    (hm : 1 ≤ m) : x ^ m ∈ Pk R ϖ k := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ]
  exact Pk_smul' (R.pow_mem (Pk_R h.mem hk hx) j) hx
end Formalism.FourierDecayAlt.P.HenselRootsBounded
