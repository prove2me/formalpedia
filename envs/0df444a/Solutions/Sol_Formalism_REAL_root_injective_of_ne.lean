-- Prove2me | solution 1 for Formalism.REAL.root_injective_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:18.962054+00:00
-- url     : https://prove2.me/submissions/ce025da7-dc7c-4a26-81aa-89eba334a0f7

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {a b a' b' : Fin n} (hab : a ≠ b) (h : root a b = root a' b') :
    a = a' ∧ b = b' := by
  have hba : b ≠ a := Ne.symm hab
  have h1 := congrFun h a
  have h2 := congrFun h b
  simp only [root, Pi.sub_apply, Pi.single_apply, if_pos rfl, if_neg hab, if_neg hba] at h1 h2
  have e1 : a = a' := by
    by_contra e1
    rw [if_neg e1] at h1
    split_ifs at h1 <;> norm_num at h1
  subst e1
  refine ⟨rfl, ?_⟩
  by_contra e4
  rw [if_neg hba, if_neg e4] at h2
  norm_num at h2
end Formalism.REAL
