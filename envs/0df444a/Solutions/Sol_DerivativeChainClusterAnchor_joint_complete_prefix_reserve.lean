-- Prove2me | solution 1 for DerivativeChainClusterAnchor.joint_complete_prefix_reserve
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:29:05.216731+00:00
-- url     : https://prove2.me/submissions/607d7398-9f31-4653-bd43-7a202067f2e3

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterPrefix
import Definitions.Def_DerivativeChainContinuation_ComplexHistories
import Definitions.Def_DerivativeChainContinuation_FiniteRootHistories
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainClusterAnchor_uniform_complete_history_law
import Theorems.Thm_DerivativeChainContinuation_finite_weighted_variance
import Theorems.Thm_DerivativeChainPrivate_exists_nonpos_of_probability_mean_zero
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators



theorem finite_weighted_square_bound {ι : Type} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) :
    (∑ i, w i*f i)^2 ≤ ∑ i, w i*(f i)^2 := by
  have h1 (i : ι) : Real.sqrt (w i)*(Real.sqrt (w i)*f i)=w i*f i := by
    rw [← mul_assoc,← pow_two,Real.sq_sqrt (hw i)]
  have h2 (i : ι) : (Real.sqrt (w i)*f i)^2=w i*(f i)^2 := by
    rw [mul_pow,Real.sq_sqrt (hw i)]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i)*f i)
  simpa only [h1,h2,Real.sq_sqrt (hw _),hs,one_mul] using hh

theorem finite_weighted_exists_le_mean {ι : Type} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) :
    ∃ i, f i ≤ ∑ j, w j*f j := by
  have he : (∑ i, w i*(f i-∑ j, w j*f j))=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hs,one_mul,sub_self]
  obtain ⟨i,hi⟩ := DerivativeChainPrivate.exists_nonpos_of_probability_mean_zero w _ hw hs he
  exact ⟨i,by linarith⟩

end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation DerivativeChainPrivate
namespace DerivativeChainClusterAnchor
noncomputable section



theorem finite_history_cost_energy (h : ℕ) (z : ℕ → ℂ) :
    (chainCost (fun i : Fin (h+1) => z i.val))^2 ≤ (h:ℝ)*historyEnergy h z := by
  change (∑ i : Fin h, ‖z (i.val+1)-z i.val‖)^2 ≤ (h:ℝ)*historyEnergy h z
  by_cases hh : h=0
  · subst h; simp [chainCost,historyEnergy]
  have hhR : (h:ℝ) ≠ 0 := by exact_mod_cast hh
  have hs : (∑ _j : Fin h, (h:ℝ)⁻¹)=1 := by simp [hhR]
  have hc := finite_weighted_square_bound (fun _ : Fin h => (h:ℝ)⁻¹)
    (fun j => ‖z (j.val+1)-z j.val‖) (fun _ => by positivity) hs
  have he : (∑ j : Fin h, ‖z (j.val+1)-z j.val‖^2)=historyEnergy h z :=
    Fin.sum_univ_eq_sum_range (fun k => ‖z (k+1)-z k‖^2) h
  simp only [← Finset.mul_sum] at hc
  rw [he] at hc
  field_simp at hc
  exact hc



end
end DerivativeChainClusterAnchor


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainClusterAnchor






theorem solution (r : _root_.DerivativeChainContinuation.ComplexRootRows) (h : ℕ)
    (hstep : ∀ k<h, _root_.DerivativeChainContinuation.UniformPolynomialStep r k) (c : ℂ) :
    ∃ z : Fin (h+1) → ℂ, _root_.DerivativeChainContinuation.IsComplexRowHistory r z ∧
      _root_.DerivativeChainPrivate.chainCost z+‖z (Fin.last h)-c‖ ≤
        Real.sqrt ((h:ℝ)*_root_.DerivativeChainClusterAnchor.rowCenteredVariance r h (r 0 0))+
          Real.sqrt (_root_.DerivativeChainClusterAnchor.rowCenteredVariance r h (r 0 0)+‖r 0 0-c‖^2) := by
  obtain ⟨κ,inst,hdata⟩ := _root_.DerivativeChainClusterAnchor.uniform_complete_history_law r h hstep
  letI : Fintype κ := inst
  obtain ⟨w,z,last,hw0,hws,hend,hroots,hmarg,hmean,henergy⟩ := hdata
  let V := _root_.DerivativeChainClusterAnchor.rowCenteredVariance r h (r 0 0)
  let L : κ → ℝ := fun i => _root_.DerivativeChainPrivate.chainCost (fun j : Fin (h+1) => z i j.val)
  let d : κ → ℝ := fun i => ‖z i h-c‖
  have hV : 0 ≤ V := by dsimp [V,_root_.DerivativeChainClusterAnchor.rowCenteredVariance]; positivity
  have hL0 (i : κ) : 0 ≤ L i := by dsimp [L,_root_.DerivativeChainPrivate.chainCost]; positivity
  have hd0 (i : κ) : 0 ≤ d i := norm_nonneg _
  have hmoment : (∑ i, w i*‖z i h-r 0 0‖^2)=V := by
    simp_rw [hend]
    exact hmarg (fun j => ‖r h j-r 0 0‖^2)
  have hE : (∑ i, w i*_root_.DerivativeChainContinuation.historyEnergy h (z i))=V := henergy.trans hmoment
  have hLE : (∑ i, w i*(L i)^2) ≤ (h:ℝ)*V := by
    calc
      _ ≤ ∑ i, w i*((h:ℝ)*_root_.DerivativeChainContinuation.historyEnergy h (z i)) := Finset.sum_le_sum
        (fun i _ => mul_le_mul_of_nonneg_left (_root_.DerivativeChainClusterAnchor.finite_history_cost_energy h (z i)) (hw0 i))
      _ = (h:ℝ)*(∑ i, w i*_root_.DerivativeChainContinuation.historyEnergy h (z i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hE]
  have hLsq := (_root_.DerivativeChainContinuation.finite_weighted_square_bound w L hw0 hws).trans hLE
  have hDE : (∑ i, w i*(d i)^2)=V+‖r 0 0-c‖^2 := by
    have hh := _root_.DerivativeChainContinuation.finite_weighted_variance w (fun i => z i h) (r 0 0) c hws hmean
    rw [hmoment] at hh
    simpa only [d,add_comm] using hh
  have hDsq := _root_.DerivativeChainContinuation.finite_weighted_square_bound w d hw0 hws
  rw [hDE] at hDsq
  have hLm0 : 0 ≤ ∑ i, w i*L i := Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 i) (hL0 i))
  have hDm0 : 0 ≤ ∑ i, w i*d i := Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 i) (hd0 i))
  have hLm : (∑ i, w i*L i) ≤ Real.sqrt ((h:ℝ)*V) := by
    nlinarith [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg h) hV),Real.sqrt_nonneg ((h:ℝ)*V)]
  have hDm : (∑ i, w i*d i) ≤ Real.sqrt (V+‖r 0 0-c‖^2) := by
    nlinarith [Real.sq_sqrt (add_nonneg hV (sq_nonneg ‖r 0 0-c‖)),
      Real.sqrt_nonneg (V+‖r 0 0-c‖^2)]
  obtain ⟨i,hi⟩ := _root_.DerivativeChainContinuation.finite_weighted_exists_le_mean w (fun i => L i+d i) hw0 hws
  have htotal : L i+d i ≤ Real.sqrt ((h:ℝ)*V)+Real.sqrt (V+‖r 0 0-c‖^2) := by
    simp only [mul_add,Finset.sum_add_distrib] at hi
    linarith
  refine ⟨(fun j => z i j.val),?_,?_⟩
  · intro j
    exact hroots i j.val (by omega)
  · simpa only [Fin.val_last,L,d,V] using htotal
