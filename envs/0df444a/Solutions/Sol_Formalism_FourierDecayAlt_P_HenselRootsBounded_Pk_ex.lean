-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.Pk_ex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:53:31.843846+00:00
-- url     : https://prove2.me/submissions/5e369c7b-f9cd-4cd6-bf66-fdafef5b8d02

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_mem_Pk

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
theorem _root_.solution (h : Ctx K R ϖ) (x : K) : ∃ b : ℕ, x ∈ Pk R ϖ (-(b : ℤ)) := by
  obtain ⟨m, hm⟩ := h.ex x
  refine ⟨m, ?_⟩
  rw [mem_Pk, neg_neg, zpow_natCast, Units.val_pow_eq_pow_val]; exact hm
end Formalism.FourierDecayAlt.P.HenselRootsBounded
