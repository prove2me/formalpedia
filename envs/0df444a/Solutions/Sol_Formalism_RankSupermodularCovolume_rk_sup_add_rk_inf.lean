-- Prove2me | solution 1 for Formalism.RankSupermodularCovolume.rk_sup_add_rk_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:45:04.566722+00:00
-- url     : https://prove2.me/submissions/4e2d712c-2d93-4026-af11-2b7fedfe0d7f

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Theorems.Thm_Formalism_RankSupermodularCovolume_cast_rank_eq_moduleRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Submodule
noncomputable section
namespace Formalism.RankSupermodularCovolume
open Formalism.F
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
private theorem discreteTopology_of_le_discrete (L A : Submodule ℤ E) [DiscreteTopology L] (h : A ≤ L) :
    DiscreteTopology A :=
  DiscreteTopology.of_subset (s := (L : Set E)) ‹_› h
end
end Formalism.RankSupermodularCovolume
namespace Formalism.HN
open Formalism.F Formalism.RankSupermodularCovolume
end Formalism.HN
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.RankSupermodularCovolume
open Formalism.F
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.RankSupermodularCovolume
theorem _root_.solution (L A B : Submodule ℤ E) [DiscreteTopology L] (hA : A ≤ L)
    (hB : B ≤ L) : rk (A ⊔ B) + rk (A ⊓ B) = rk A + rk B := by
  haveI : DiscreteTopology A := discreteTopology_of_le_discrete L A hA
  haveI : DiscreteTopology B := discreteTopology_of_le_discrete L B hB
  haveI : DiscreteTopology ↥(A ⊔ B) := discreteTopology_of_le_discrete L _ (sup_le hA hB)
  haveI : DiscreteTopology ↥(A ⊓ B) := discreteTopology_of_le_discrete L _ (inf_le_left.trans hA)
  have h := Submodule.rank_sup_add_rank_inf_eq A B
  apply Nat.cast_injective (R := Cardinal)
  push_cast
  rw [cast_rank_eq_moduleRank, cast_rank_eq_moduleRank,
    cast_rank_eq_moduleRank, cast_rank_eq_moduleRank]
  exact h
end Formalism.RankSupermodularCovolume
