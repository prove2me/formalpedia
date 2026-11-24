-- Prove2me | solution 1 for Formalism.RankSupermodularCovolume.cast_rank_eq_moduleRank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:54.47468+00:00
-- url     : https://prove2.me/submissions/fcfbc430-0a71-440e-9a73-3a81854fa0bd

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.RankSupermodularCovolume
open Formalism.F
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.RankSupermodularCovolume
theorem _root_.solution (N : Submodule ℤ E) [DiscreteTopology N] :
    ((rk N : ℕ) : Cardinal) = Module.rank ℤ N := by
  unfold rk
  exact Module.finrank_eq_rank ℤ N
end Formalism.RankSupermodularCovolume
