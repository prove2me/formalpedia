-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDual_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:19.725801+00:00
-- url     : https://prove2.me/submissions/cb1cadc8-8000-49fb-be95-75831823a995

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_herm
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_mat
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_sgn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ)
    (hst : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    (hX : ∀ v, IsFrame h b v (X v)) (v : InfinitePlace K) (x y : V) :
    (v.embedding (h x y)).re = ∑ i, sgnAt h b X v i * ((fcoord b X v x i).re * (fcoord b X v y i).re
      + (fcoord b X v x i).im * (fcoord b X v y i).im) := by
  obtain ⟨hu, -⟩ := hX v
  rw [majDual_herm h b v hst x y, ← majDual_mat (gramAt h b v) (X v) hu,
    (majDual_sgn h b X hX v).1]
  simp only [fcoord, dotProduct, Matrix.mulVec_diagonal, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring1
end Formalism.HermitianLatticesTheory
