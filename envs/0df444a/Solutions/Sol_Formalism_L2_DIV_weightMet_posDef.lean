-- Prove2me | solution 1 for Formalism.L2.DIV.weightMet_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:56.086377+00:00
-- url     : https://prove2.me/submissions/7f4e53be-e650-4a6c-be89-0e4dcba4cc11

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_Formalism_L2_DIV_metOfSpec
import Theorems.Thm_Formalism_L2_DIV_weightMet_form
import Theorems.Thm_Formalism_L2_DIV_sum_map_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] {n : ℕ} {Ix : Type} [Fintype Ix]
namespace Formalism.L2.DIV
theorem _root_.solution (pr : Ix → Matrix (Fin n) (Fin n) K) (t : Ix → InfinitePlace K → ℝ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ v, IsUnit (X v).det)
    (ht : ∀ p v, 0 < t p v) (hsum : ∑ p, pr p = 1) (v : InfinitePlace K) :
    (weightMet pr t X v).PosDef := by
  have hM := (metOfSpec n _ (hX v)).1
  have hpsd : (weightMet pr t X v).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro p _
    apply Matrix.PosSemidef.smul (hM.posSemidef.conjTranspose_mul_mul_same _)
    exact_mod_cast (ht p v).le
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hpsd.1 fun x hx => ?_
  rw [weightMet_form]
  have ht' : ∀ p, (0 : ℂ) < ((t p v : ℝ) : ℂ) := fun p => by exact_mod_cast ht p v
  apply Finset.sum_pos'
  · intro p _
    exact mul_nonneg (ht' p).le (hM.posSemidef.dotProduct_mulVec_nonneg _)
  · by_contra hcon
    apply hx
    have h0 : ∀ p, ((pr p).map v.embedding).mulVec x = 0 := by
      intro p
      by_contra hp
      exact hcon ⟨p, Finset.mem_univ p, mul_pos (ht' p) (hM.dotProduct_mulVec_pos hp)⟩
    have h1 : x = (∑ p, (pr p).map v.embedding).mulVec x := by
      rw [sum_map_eq_one pr hsum, Matrix.one_mulVec]
    rw [h1, Matrix.sum_mulVec]
    exact Finset.sum_eq_zero fun p _ => h0 p
end Formalism.L2.DIV
