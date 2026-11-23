-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:00.177643+00:00
-- url     : https://prove2.me/submissions/a7f1c8de-0e17-45c3-b1af-f1ac08d8212d

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (rel : M → N → Prop) (Z : N →ₗ[R] P) (hex : ∀ f, ∃ G, rel f G)
    (hadd : ∀ f f' G G', rel f G → rel f' G' → rel (f + f') (G + G'))
    (hsmul : ∀ (c : R) f G, rel f G → rel (c • f) (c • G))
    (hkey : ∀ f G G', rel f G → rel f G' → Z G = Z G') :
    ∃ io : M →ₗ[R] P, ∀ f G, rel f G → io f = Z G := by
  choose g hg using hex
  refine ⟨{ toFun := fun f => Z (g f), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro f f'
    show Z (g (f + f')) = Z (g f) + Z (g f')
    rw [hkey (f + f') (g (f + f')) (g f + g f') (hg _) (hadd _ _ _ _ (hg f) (hg f')), map_add]
  · intro c f
    show Z (g (c • f)) = (RingHom.id R) c • Z (g f)
    rw [hkey (c • f) (g (c • f)) (c • g f) (hg _) (hsmul c f _ (hg f)), map_smul, RingHom.id_apply]
  · intro f G hG
    exact hkey f (g f) G (hg f) hG
end Formalism.BranchingDeterminantCap
