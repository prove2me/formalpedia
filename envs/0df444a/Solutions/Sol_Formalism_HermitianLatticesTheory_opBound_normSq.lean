-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.opBound_normSq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:00.293391+00:00
-- url     : https://prove2.me/submissions/1cb90554-bc99-4f79-8cb8-1df87af032f7

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_OpBound
import Theorems.Thm_Formalism_HermitianLatticesTheory_opBound_cnorm_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (z : V) :
    ‖realize b X z‖ ^ 2 = ∑ v, cnorm (fcoord b X v z) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type, opBound_cnorm_sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  show ‖realizeRaw b X z (v, i, 0)‖ ^ 2 + ‖realizeRaw b X z (v, i, 1)‖ ^ 2 = _
  simp only [realizeRaw, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_neg (by decide : (1 : Fin 2) ≠ 0),
    if_true, Real.norm_eq_abs, sq_abs, Complex.sq_norm,
    Complex.normSq_apply]
  ring
end Formalism.HermitianLatticesTheory
