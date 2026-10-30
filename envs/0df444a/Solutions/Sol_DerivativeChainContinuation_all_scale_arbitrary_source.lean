-- Prove2me | solution 1 for DerivativeChainContinuation.all_scale_arbitrary_source
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:32:09.568153+00:00
-- url     : https://prove2.me/submissions/c6e8703c-b6ea-4df5-8596-e7c90ad689de

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AllScaleCompression
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainContinuation_ScaleMoments
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_all_scale_compression_bound
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Polynomial
open scoped BigOperators


open DerivativeChainContinuation in
theorem solution (n : ℕ) (hn : 0 < n) (a : Fin (n+1) → ℂ)
    (z : ℂ) (t : ℝ) (ht : 0 < t) :
    let b := fun i => a i-z;
    let δ := schoenbergDeficit (∏ i,(X-C (a i-complexCentroid a)));
    0 ≤ scaleCompressionGap b t ∧
      scaleCompressionGap b t ≤ t*scaleMeanZero b t*min 1 (δ/t) ∧
      t*scaleMeanZero b t*min 1 (δ/t) ≤ min 1 (δ/t) ∧
      scaleCompressionGap b t ≤ t*scaleMeanZero b t*(1-Real.exp (-δ/t)) ∧
      (t*scaleMeanZero b t)^2*Real.exp (-δ/t) ≤ t*scaleDerivativeProduct b t/scaleSourceProduct b t := by
  let u := complexCentroid a
  have hzero : (∑ i,(a i-u))=0 := by
    have hnC : (n+1:ℂ) ≠ 0 := by exact_mod_cast (show n+1 ≠ 0 by omega)
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_add,Nat.cast_one,u,complexCentroid]
    field_simp
    <;> ring
  have h := all_scale_compression_bound n hn (fun i => a i-u) hzero (z-u) t ht
  have hf : (fun i => a i-u-(z-u))=(fun i => a i-z) := by funext i; ring
  dsimp only at h ⊢
  rw [hf] at h
  exact h
