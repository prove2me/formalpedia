-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.linearIndependent_of_isBaseChange_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:35:26.34966+00:00
-- url     : https://prove2.me/submissions/f4ceb15f-a7ae-41bd-b533-5da9965162a7

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LinearIndependentOfIsBaseChange

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
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution {K K' V V₁ ι : Type} [Field K] [Field K'] [Algebra K K']
    [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K' V₁] [Module K V₁]
    [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁) (hj : IsBaseChange K' j) (v : ι → V)
    (hv : LinearIndependent K v) : LinearIndependent K' (fun i => j (v i)) := by
  classical
  have hs : LinearIndepOn K id (Set.range v) := by
    first
    | exact hv.linearIndepOn_id_range
    | exact (linearIndepOn_id_range_iff hv.injective).mpr hv
  let B := Basis.extend hs
  have hsub : Set.range v ⊆ hs.extend (Set.subset_univ _) := hs.subset_extend (Set.subset_univ _)
  let g : ι → hs.extend (Set.subset_univ _) := fun i => ⟨v i, hsub (Set.mem_range_self i)⟩
  have hg : Function.Injective g := fun a c h => hv.injective (congrArg Subtype.val h)
  have hB' : (fun i => j (v i)) = (hj.basis B) ∘ g := by
    funext i
    first
    | simp [B, g, IsBaseChange.basis_apply, Basis.coe_extend]
    | simp [B, g, Basis.coe_extend]
  rw [hB']
  exact (hj.basis B).linearIndependent.comp g hg
end Formalism.LatticeBaseChangeAlt
