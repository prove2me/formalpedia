-- Prove2me | solution 1 for DerivativeChainPhaseLock.actual_paired_radial_kappa
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:48:31.451783+00:00
-- url     : https://prove2.me/submissions/5d2d3216-f9fe-410c-816c-cc3eaf9fcd9c

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
import Definitions.Def_DerivativeChainAnalytic_KappaDefinitions
import Definitions.Def_DerivativeChainAnalytic_ProjectiveHistories
import Definitions.Def_DerivativeChainContinuation_AppellCoefficients
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPhaseLock_actual_paired_projective_law
import Theorems.Thm_DerivativeChainPrefixLaws_history_law_endpoint_weights
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainFiniteHistory
end DerivativeChainFiniteHistory
namespace DerivativeChainPhaseLock
end DerivativeChainPhaseLock
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation DerivativeChainPrivate
namespace DerivativeChainPrefixLaws
noncomputable section















theorem rootLawSquareCost_nonneg {n : ℕ} (a : Fin (n+1) → ℂ) (w : Fin (n+1) → ℝ)
    (hw : ∀ i,0 ≤ w i) : 0 ≤ rootLawSquareCost a w :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))

theorem ratioValues_nonneg {n : ℕ} (a : Fin (n+1) → ℂ) {q : ℝ}
    (hq : q ∈ ratioValues a) : 0 ≤ q := by
  obtain ⟨w,hw,hv,rfl⟩ := hq
  exact div_nonneg (rootLawSquareCost_nonneg a w hw.1) hv.le



theorem kappa_le_of_weights {n : ℕ} (a : Fin (n+1) → ℂ) (w : Fin (n+1) → ℝ)
    (hw : BalancedWeights a (complexCentroid a) w) (hv : 0 < rootLawVariance a w)
    (K : ℝ) (hcost : rootLawSquareCost a w ≤ K*rootLawVariance a w) : kappa a ≤ K := by
  have hb : BddBelow (ratioValues a) := ⟨0,fun q hq => ratioValues_nonneg a hq⟩
  have hm : rootLawSquareCost a w/rootLawVariance a w ∈ ratioValues a := ⟨w,hw,hv,rfl⟩
  exact (csInf_le hb hm).trans ((div_le_iff₀ hv).2 hcost)













end
end DerivativeChainPrefixLaws


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate DerivativeChainFiniteHistory
universe v
namespace DerivativeChainPrefixLaws
noncomputable section





theorem kappa_le_of_history_law {n : ℕ} {a : Fin (n+1) → ℂ} {u : ℂ}
    {κ : Type v} [Fintype κ] (L : FiniteBalancedHistoryLaw a u κ)
    (hV : 0 < L.endpointVariance) (K : ℝ)
    (hcost : L.meanSquareCost ≤ K*L.endpointVariance) : kappa a ≤ K := by
  obtain ⟨W,hw,hvar,hC⟩ := history_law_endpoint_weights L
  apply kappa_le_of_weights a W hw (by rwa [hvar]) K
  rw [hvar]
  exact hC.trans hcost



end
end DerivativeChainPrefixLaws


end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory DerivativeChainContinuation
namespace DerivativeChainPhaseLock
noncomputable section

theorem complex_difference_square (x y : ℂ) :
    ‖y-x‖^2=‖y‖^2+‖x‖^2-2*(y*star x).re := by
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,
    Complex.sub_im,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem complex_sum_square (x y : ℂ) :
    ‖y+x‖^2=‖y‖^2+‖x‖^2+2*(y*star x).re := by
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.add_re,
    Complex.add_im,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem projective_radial_step (x y : ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hr : ‖x‖ ≤ ‖y‖)
    (hang : 2*(‖y‖*‖x‖-|(y*star x).re|) ≤ (K-1)*(‖y‖-‖x‖)^2) :
    projectiveStep x y ≤ Real.sqrt K*(‖y‖-‖x‖) := by
  have hsq := Real.sq_sqrt hK
  have hR : 0 ≤ Real.sqrt K*(‖y‖-‖x‖) := mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hr)
  by_cases hd : 0 ≤ (y*star x).re
  · rw [abs_of_nonneg hd] at hang
    have he := complex_difference_square x y
    have hb : ‖y-x‖ ≤ Real.sqrt K*(‖y‖-‖x‖) := by
      have hn := norm_nonneg (y-x)
      nlinarith [sq_nonneg (‖y‖-‖x‖)]
    exact le_trans (min_le_left _ _) hb
  · rw [abs_of_neg (lt_of_not_ge hd)] at hang
    have he := complex_sum_square x y
    have hb : ‖y+x‖ ≤ Real.sqrt K*(‖y‖-‖x‖) := by
      have hn := norm_nonneg (y+x)
      nlinarith [sq_nonneg (‖y‖-‖x‖)]
    exact le_trans (min_le_right _ _) hb

theorem projective_radial_length (x : ℕ → ℂ) (n : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hr : ∀ k<n, ‖x k‖ ≤ ‖x (k+1)‖)
    (hang : ∀ k<n, 2*(‖x (k+1)‖*‖x k‖-|(x (k+1)*star (x k)).re|) ≤
      (K-1)*(‖x (k+1)‖-‖x k‖)^2) :
    projectivePathLength x n ≤ Real.sqrt K*(‖x n‖-‖x 0‖) := by
  calc
    projectivePathLength x n ≤ ∑ k∈Finset.range n,Real.sqrt K*(‖x (k+1)‖-‖x k‖) := by
      apply Finset.sum_le_sum
      intro k hk
      exact projective_radial_step (x k) (x (k+1)) K hK
        (hr k (Finset.mem_range.mp hk)) (hang k (Finset.mem_range.mp hk))
    _ = Real.sqrt K*(‖x n‖-‖x 0‖) := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_range_sub (fun k => ‖x k‖) n

theorem actual_paired_radial_lift {n : ℕ} (a : Fin (n+1) → ℂ)
    (hc : ∀ j, Odd j → appellCoefficients (fromRoots a) j=0)
    (x : ℕ → ℂ) (hx : IsChain a (fun i => x i.val)) (hx0 : x 0=0)
    (K : ℝ) (hK : 0 ≤ K)
    (hr : ∀ k<n, ‖x k‖ ≤ ‖x (k+1)‖)
    (hang : ∀ k<n, 2*(‖x (k+1)‖*‖x k‖-|(x (k+1)*star (x k)).re|) ≤
      (K-1)*(‖x (k+1)‖-‖x k‖)^2) :
    ∃ L : FiniteBalancedHistoryLaw a 0 (Fin 2),
      (∀ i,L.weights i=1/2) ∧ L.paths 0=projectiveHistory x n ∧
      L.paths 1=(fun i => -projectiveHistory x n i) ∧
      (∀ i,chainCost (L.paths i) ≤ Real.sqrt K*‖x n‖) ∧
      L.endpointVariance=‖x n‖^2 ∧ L.meanSquareCost ≤ K*L.endpointVariance := by
  obtain ⟨L,hw,hp,hm,hcost,hvar,hmean⟩ := actual_paired_projective_law a hc x hx hx0
  have hb := projective_radial_length x n K hK hr hang
  rw [hx0,norm_zero,sub_zero] at hb
  have hp0 : 0 ≤ projectivePathLength x n := by
    apply Finset.sum_nonneg
    intro k hk
    exact le_min (norm_nonneg _) (norm_nonneg _)
  refine ⟨L,hw,hp,hm,?_,hvar,?_⟩
  · intro i
    rw [hcost]
    exact hb
  · rw [hmean,hvar]
    have hs := Real.sq_sqrt hK
    have hn := norm_nonneg (x n)
    nlinarith [sq_nonneg (Real.sqrt K*‖x n‖-projectivePathLength x n)]



end
end DerivativeChainPhaseLock



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory DerivativeChainContinuation
open DerivativeChainPhaseLock












theorem solution {n : ℕ} (a : Fin (n+1) → ℂ)
    (hc : ∀ j, Odd j → _root_.DerivativeChainContinuation.appellCoefficients (_root_.DerivativeChainPrivate.fromRoots a) j=0)
    (x : ℕ → ℂ) (hx : _root_.DerivativeChainPrivate.IsChain a (fun i => x i.val)) (hx0 : x 0=0)
    (hxend : x n ≠ 0) (K : ℝ) (hK : 0 ≤ K)
    (hr : ∀ k<n, ‖x k‖ ≤ ‖x (k+1)‖)
    (hang : ∀ k<n, 2*(‖x (k+1)‖*‖x k‖-|(x (k+1)*star (x k)).re|) ≤
      (K-1)*(‖x (k+1)‖-‖x k‖)^2) :
    _root_.DerivativeChainPrefixLaws.kappa a ≤ K := by
  obtain ⟨L,hw,hp,hm,hcost,hvar,hmean⟩ := _root_.DerivativeChainPhaseLock.actual_paired_radial_lift a hc x hx hx0 K hK hr hang
  apply _root_.DerivativeChainPrefixLaws.kappa_le_of_history_law L _ K hmean
  rw [hvar]
  exact sq_pos_of_pos (norm_pos_iff.mpr hxend)
