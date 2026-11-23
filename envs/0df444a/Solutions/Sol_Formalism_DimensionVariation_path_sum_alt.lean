-- Prove2me | solution 1 for Formalism.DimensionVariation.path_sum_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:59.661537+00:00
-- url     : https://prove2.me/submissions/6612bfd6-394d-48bc-a3a6-5ba33e2ad8fe

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound
import Theorems.Thm_Formalism_DimensionVariation_CB_chainFun_succ
import Theorems.Thm_Formalism_DimensionVariation_CB_chainFun_sum
import Theorems.Thm_Formalism_DimensionVariation_CB_single_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)
open CB
namespace Formalism.DimensionVariation
theorem _root_.solution : PathSum := by
  intro m
  induction m with
  | zero =>
    intro AA _ _ H _ E G
    have key : ∀ F : (∀ i : Fin 1, AA i) → (∀ a, H 0 a),
        (∀ al, F al = Pi.single (al 0) (G (al 0))) → ∑ al, F al = G := by
      intro F hF
      rw [Fintype.sum_equiv (Equiv.piUnique (α := Fin 1) AA) F (fun a => Pi.single a (G a)) hF]
      exact Finset.univ_sum_single G
    exact Eq.symm (key _ (fun al => rfl))
  | succ m ih =>
    intro AA _ _ H _ E G
    have h1 := chainFun_succ (C := fun i => ∀ a, H i a) (fun j => blockMap (E j)) G (Fin.last m)
    have h2 := ih (fun i => AA i.succ) (fun i => H i.succ) (fun j => E j.succ) (blockMap (E 0) G)
    refine h1.trans (h2.trans ?_)
    have hL : ∀ al' : (∀ i : Fin (m + 1), AA i.succ),
        Pi.single (M := fun b => H (Fin.last m).succ b) (al' (Fin.last m))
          (chainFun (C := fun i => H i.succ (al' i))
          (fun j => E j.succ (al' j.castSucc) (al' j.succ)) (Fin.last m) (blockMap (E 0) G (al' 0))) =
        ∑ a : AA 0, Pi.single (M := fun b => H (Fin.last m).succ b) (al' (Fin.last m))
          (chainFun (C := fun i => H i.succ (al' i))
          (fun j => E j.succ (al' j.castSucc) (al' j.succ)) (Fin.last m) (E 0 a (al' 0) (G a))) := by
      intro al'
      rw [← single_sum (H := fun b => H (Fin.last m).succ b)]
      exact congrArg (Pi.single (M := fun b => H (Fin.last m).succ b) (al' (Fin.last m)))
        (chainFun_sum (C := fun i => H i.succ (al' i))
          (fun j => E j.succ (al' j.castSucc) (al' j.succ)) Finset.univ
          (fun a => E 0 a (al' 0) (G a)) (Fin.last m))
    have hR : ∀ (a : AA 0) (al' : ∀ i : Fin (m + 1), AA i.succ),
        Pi.single (M := fun b => H (Fin.last m).succ b) (al' (Fin.last m))
          (chainFun (C := fun i => H i.succ (al' i))
          (fun j => E j.succ (al' j.castSucc) (al' j.succ)) (Fin.last m) (E 0 a (al' 0) (G a))) =
        (fun al : (∀ i, AA i) => Pi.single (al (Fin.last (m + 1))) (chainFun (C := fun i => H i (al i))
          (fun j => E j (al j.castSucc) (al j.succ)) (Fin.last (m + 1)) (G (al 0)))) (Fin.cons a al') := by
      intro a al'
      exact congrArg (Pi.single (M := fun b => H (Fin.last m).succ b) (al' (Fin.last m)))
        (chainFun_succ (C := fun i => H i ((Fin.cons a al' : ∀ i, AA i) i))
          (fun j => E j ((Fin.cons a al' : ∀ i, AA i) j.castSucc) ((Fin.cons a al' : ∀ i, AA i) j.succ))
          (G a) (Fin.last m)).symm
    rw [Finset.sum_congr rfl (fun al' _ => hL al'), Finset.sum_comm]
    rw [← Fintype.sum_equiv (Fin.consEquiv AA) (fun p => (fun al : (∀ i, AA i) => Pi.single (al (Fin.last (m + 1))) (chainFun (C := fun i => H i (al i))
          (fun j => E j (al j.castSucc) (al j.succ)) (Fin.last (m + 1)) (G (al 0)))) (Fin.cons p.1 p.2)) (fun al : (∀ i, AA i) => Pi.single (al (Fin.last (m + 1))) (chainFun (C := fun i => H i (al i))
          (fun j => E j (al j.castSucc) (al j.succ)) (Fin.last (m + 1)) (G (al 0))))
      (fun p => rfl), ← Finset.univ_product_univ, Finset.sum_product]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun al' _ => hR a al'))
end Formalism.DimensionVariation
