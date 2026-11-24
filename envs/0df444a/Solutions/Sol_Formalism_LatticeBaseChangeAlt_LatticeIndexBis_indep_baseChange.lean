-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.LatticeIndexBis.indep_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:35:28.729451+00:00
-- url     : https://prove2.me/submissions/cb28b3cc-e41b-42be-b311-f80274e055e9

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeIndexBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.LatticeIndexBis
namespace Formalism.LatticeBaseChangeAlt.LatticeIndexBis
theorem _root_.solution {K K' V V₁ ι : Type} [Field K] [Field K'] [Algebra K K'] [AddCommGroup V]
    [Module K V] [AddCommGroup V₁] [Module K' V₁] [Module K V₁] [IsScalarTower K K' V₁]
    (j : V →ₗ[K] V₁) (hj : IsBaseChange K' j) (a : ι → V) (ha : LinearIndependent K a) :
    LinearIndependent K' (fun i => j (a i)) := by
  classical
  have hs : LinearIndepOn K id (Set.range a) := by
    first
    | exact (linearIndepOn_id_range_iff ha.injective).2 ha
    | exact ha.to_subtype_range
    | exact (linearIndependent_subtype_range ha.injective).2 ha
  let B := Module.Basis.extend hs
  let B' := hj.basis B
  have hB' : LinearIndependent K' (fun i : hs.extend (Set.subset_univ _) => j (i : V)) := by
    have h1 := B'.linearIndependent
    convert h1 using 1
    funext i
    rw [IsBaseChange.basis_apply, Module.Basis.coe_extend]
    rfl
  have hsub : ∀ i, a i ∈ hs.extend (Set.subset_univ _) :=
    fun i => hs.subset_extend _ ⟨i, rfl⟩
  exact hB'.comp (fun i => ⟨a i, hsub i⟩) (fun i i' h => ha.injective (congrArg Subtype.val h))
end Formalism.LatticeBaseChangeAlt.LatticeIndexBis
