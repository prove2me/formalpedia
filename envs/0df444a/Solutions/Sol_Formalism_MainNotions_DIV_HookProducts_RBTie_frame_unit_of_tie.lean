-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.frame_unit_of_tie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:32:42.540217+00:00
-- url     : https://prove2.me/submissions/c7be6f31-2ed1-4c1f-aeaa-a762b6c524ee

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_cQ_mul_cP
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_gram_tie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField Module
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.HookProducts Formalism.MainNotions.DIV.HookProducts.RBTie
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
variable (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
  (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K)
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
theorem _root_.solution (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (hXA : IsUnit (XA v).det) : IsUnit (X v).det := by
  by_contra hX
  have hinv : (X v)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hX
  have hg := gram_tie b XA X e h v
  rw [hinv, Matrix.conjTranspose_zero, Matrix.zero_mul] at hg
  have hM : (XA v)⁻¹ * cP b e v = 0 := by
    open scoped ComplexOrder in exact Matrix.conjTranspose_mul_self_eq_zero.mp hg
  have hP : cP b e v = 0 := by
    have h2 := congrArg (fun M => XA v * M) hM
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXA, Matrix.one_mul, Matrix.mul_zero] at h2
    exact h2
  have h1 := cQ_mul_cP b e v
  rw [hP, Matrix.mul_zero] at h1
  obtain rfl | hd := Nat.eq_zero_or_pos d
  · exact hX (by simp)
  · have h3 := congrFun (congrFun h1 ⟨0, hd⟩) ⟨0, hd⟩
    simp at h3
end Formalism.MainNotions.DIV.HookProducts.RBTie
