-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.mat_extC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:33.982831+00:00
-- url     : https://prove2.me/submissions/999e670c-4987-47a2-92f9-844b624db33d

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.RF
variable {K : Type} [Field K] [StarRing K] {n : ℕ} {J : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)}
omit [StarRing K]
namespace CompanionTheory.D.gk.RF
theorem _root_.solution {A B : Matrix (Fin n) (Fin n) K} (h : ∀ z, A *ᵥ z = B *ᵥ z) : A = B :=
  Matrix.ext fun i j => by simpa using congrFun (h (Pi.single j 1)) i
end CompanionTheory.D.gk.RF
