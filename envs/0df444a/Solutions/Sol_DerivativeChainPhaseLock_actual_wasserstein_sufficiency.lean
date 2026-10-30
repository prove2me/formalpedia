-- Prove2me | solution 1 for DerivativeChainPhaseLock.actual_wasserstein_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:50:42.44086+00:00
-- url     : https://prove2.me/submissions/430687f5-8e4c-4023-924f-010a4043ac44

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
import Definitions.Def_DerivativeChainAnalytic_KappaDefinitions
import Definitions.Def_DerivativeChainAnalytic_UniformTransportHistories
import Definitions.Def_DerivativeChainAnalytic_UniformWasserstein
import Definitions.Def_DerivativeChainAnalytic_WassersteinSufficiency
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPhaseLock_actual_endpoint_cost_lipschitz
import Theorems.Thm_DerivativeChainPhaseLock_uniform_kernel_minimum
import Theorems.Thm_DerivativeChainPhaseLock_uniform_transport_actual_history_law
import Theorems.Thm_DerivativeChainPhaseLock_weighted_lipschitz_square_bound
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













theorem uniform_balanced_weights {n : ℕ} (a : Fin (n+1) → ℂ) :
    BalancedWeights a (complexCentroid a) (fun _ => (n+1:ℝ)⁻¹) := by
  refine ⟨(fun _ => by positivity),?_,?_⟩
  · simp [show (n:ℝ)+1 ≠ 0 by positivity]
  · rw [← Finset.mul_sum]
    push_cast
    rw [complexCentroid]
    ring

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

theorem kappa_of_collapsed {n : ℕ} (a : Fin (n+1) → ℂ)
    (ha : ∀ i,a i=complexCentroid a) : kappa a=0 := by
  have he : ratioValues a=∅ := by
    ext q
    constructor
    · rintro ⟨w,hw,hv,hq⟩
      simp [rootLawVariance,ha] at hv
    · intro hq
      cases hq
  rw [kappa,he,Real.sInf_empty]







theorem endpoint_cost_nonneg {n : ℕ} (a : Fin (n+1) → ℂ) (v : ℂ) :
    0 ≤ complexEndpointCost a v := by
  apply Real.sInf_nonneg
  rintro t ⟨z,hz,he,rfl⟩
  unfold chainCost
  positivity

theorem endpoint_cost_le_chain {n : ℕ} (a : Fin (n+1) → ℂ) (z : Fin (n+1) → ℂ)
    (hz : IsChain a z) : complexEndpointCost a (z (Fin.last n)) ≤ chainCost z := by
  unfold complexEndpointCost
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro t ⟨zz,hzz,he,rfl⟩
    unfold chainCost
    positivity
  · exact ⟨z,hz,rfl,rfl⟩

end
end DerivativeChainPrefixLaws



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open DerivativeChainPrefixLaws
namespace DerivativeChainPhaseLock
noncomputable section











theorem uniformW1_attained {m n : ℕ} (x : Fin (m+1) → ℂ) (y : Fin (n+1) → ℂ) :
    ∃ K,UniformKernel m n K ∧ uniformKernelCost x y K=uniformW1 x y := by
  obtain ⟨K,hK,hmin⟩ := uniform_kernel_minimum x y
  refine ⟨K,hK,?_⟩
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨K,hK,rfl⟩,?_⟩
  rintro q ⟨Q,hQ,rfl⟩
  exact hmin Q hQ

theorem uniformW1_nonneg {m n : ℕ} (x : Fin (m+1) → ℂ) (y : Fin (n+1) → ℂ) :
    0 ≤ uniformW1 x y := by
  obtain ⟨K,hK,hcost⟩ := uniformW1_attained x y
  rw [← hcost]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hK.1 i j) (norm_nonneg _))

end
end DerivativeChainPhaseLock



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainContinuation DerivativeChainFiniteHistory
open DerivativeChainPrefixLaws
namespace DerivativeChainPhaseLock
noncomputable section





theorem optimal_uniform_actual_history_law (n : ℕ) (a : Fin (n+1) → ℂ)
    (r : ComplexRootRows) (htop : r n=a) (hstep : ∀ k<n,UniformPolynomialStep r k) :
    ∃ (κ : Type) (inst : Fintype κ),letI := inst;
      ∃ L : FiniteBalancedHistoryLaw a (r 0 0) κ,
        (∀ f : ℂ → ℝ,(∑ i,L.weights i*f (L.paths i (Fin.last n)))=
          ∑ j,(n+1:ℝ)⁻¹*f (a j)) ∧
        (∑ i,L.weights i*chainCost (L.paths i))=towerTransportLength r n := by
  classical
  choose K hK hcost using (fun k : ℕ => uniformW1_attained (r k) (r (k+1)))
  obtain ⟨κ,inst,hdata⟩ := uniform_transport_actual_history_law n a r htop hstep K (fun k hk => hK k)
  letI : Fintype κ := inst
  obtain ⟨L,hmarg,hmean⟩ := hdata
  refine ⟨κ,inst,L,hmarg,?_⟩
  simpa only [towerTransportLength,hcost] using hmean

end
end DerivativeChainPhaseLock



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainContinuation DerivativeChainFiniteHistory
open DerivativeChainPrefixLaws
namespace DerivativeChainPhaseLock
noncomputable section





theorem uniformSourceVariance_nonneg {n : ℕ} (a : Fin (n+1) → ℂ) :
    0 ≤ uniformSourceVariance a := by unfold uniformSourceVariance rootLawVariance; positivity

theorem uniform_ratio_eq {n : ℕ} (a : Fin (n+1) → ℂ) :
    uniformComplexTransportRatio a=uniformSourceSquareCost a/uniformSourceVariance a := by
  unfold uniformComplexTransportRatio uniformSourceSquareCost uniformSourceVariance
    rootLawSquareCost rootLawVariance
  rw [← Finset.mul_sum,← Finset.mul_sum]
  symm
  exact mul_div_mul_left _ _ (inv_ne_zero (by positivity : (n+1:ℝ) ≠ 0))

theorem uniform_zero_variance_collapsed {n : ℕ} (a : Fin (n+1) → ℂ)
    (hV : uniformSourceVariance a=0) : ∀ i,a i=complexCentroid a := by
  intro i
  have hsum : (∑ j : Fin (n+1),(n+1:ℝ)⁻¹*‖a j-complexCentroid a‖^2)=0 := hV
  have hterm : (n+1:ℝ)⁻¹*‖a i-complexCentroid a‖^2=0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n+1)))) =>
        mul_nonneg (by positivity : 0 ≤ (n+1:ℝ)⁻¹) (sq_nonneg ‖a j-complexCentroid a‖))).mp hsum i (Finset.mem_univ i)
  have hn : (n+1:ℝ)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  have hs : ‖a i-complexCentroid a‖^2=0 := (mul_eq_zero.mp hterm).resolve_left hn
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))

theorem kappa_le_uniform_ratio {n : ℕ} (a : Fin (n+1) → ℂ) :
    kappa a ≤ uniformComplexTransportRatio a := by
  by_cases hV : uniformSourceVariance a=0
  · rw [kappa_of_collapsed a (uniform_zero_variance_collapsed a hV),uniform_ratio_eq,hV,div_zero]
  · have hv : 0 < uniformSourceVariance a := lt_of_le_of_ne (uniformSourceVariance_nonneg a) (Ne.symm hV)
    apply kappa_le_of_weights a (fun _ => (n+1:ℝ)⁻¹) (uniform_balanced_weights a) hv
    rw [uniform_ratio_eq]
    exact (div_mul_cancel₀ (uniformSourceSquareCost a) hV).symm.le

theorem actual_uniform_transport_square_bound (n : ℕ) (a : Fin (n+1) → ℂ)
    (r : ComplexRootRows) (htop : r n=a) (hstep : ∀ k<n,UniformPolynomialStep r k) :
    uniformSourceSquareCost a ≤ (towerTransportLength r n)^2+uniformSourceVariance a := by
  obtain ⟨κ,inst,hdata⟩ := optimal_uniform_actual_history_law n a r htop hstep
  letI : Fintype κ := inst
  obtain ⟨L,hmarg,hmean⟩ := hdata
  have hEC : (∑ i,L.weights i*complexEndpointCost a (L.paths i (Fin.last n))) ≤
      towerTransportLength r n := by
    rw [← hmean]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (endpoint_cost_le_chain a (L.paths i) (L.actual i)) (L.nonneg i)
  rw [hmarg (complexEndpointCost a)] at hEC
  have hw := uniform_balanced_weights a
  have hT : 0 ≤ towerTransportLength r n := by
    apply Finset.sum_nonneg
    intro k _
    exact uniformW1_nonneg _ _
  exact weighted_lipschitz_square_bound (fun _ : Fin (n+1) => (n+1:ℝ)⁻¹) a
    (complexCentroid a) (fun i => complexEndpointCost a (a i)) hw.1 hw.2.1 hw.2.2
    (fun i => endpoint_cost_nonneg a (a i)) (actual_endpoint_cost_lipschitz a)
    (towerTransportLength r n) hT hEC



end
end DerivativeChainPhaseLock



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainContinuation DerivativeChainFiniteHistory
open DerivativeChainPrefixLaws
open DerivativeChainPhaseLock
















theorem solution (n : ℕ) (a : Fin (n+1) → ℂ)
    (r : _root_.DerivativeChainContinuation.ComplexRootRows) (htop : r n=a) (hstep : ∀ k<n,_root_.DerivativeChainContinuation.UniformPolynomialStep r k)
    (hT : _root_.DerivativeChainPhaseLock.towerTransportLength r n ≤ Real.sqrt 15*Real.sqrt (_root_.DerivativeChainPhaseLock.uniformSourceVariance a)) :
    _root_.DerivativeChainPrefixLaws.kappa a ≤ _root_.DerivativeChainContinuation.uniformComplexTransportRatio a ∧ _root_.DerivativeChainContinuation.uniformComplexTransportRatio a ≤ 16 := by
  refine ⟨_root_.DerivativeChainPhaseLock.kappa_le_uniform_ratio a,?_⟩
  have hV := _root_.DerivativeChainPhaseLock.uniformSourceVariance_nonneg a
  have hlen : 0 ≤ _root_.DerivativeChainPhaseLock.towerTransportLength r n := by
    apply Finset.sum_nonneg
    intro k _
    exact _root_.DerivativeChainPhaseLock.uniformW1_nonneg _ _
  have hsquare : (_root_.DerivativeChainPhaseLock.towerTransportLength r n)^2 ≤ 15*_root_.DerivativeChainPhaseLock.uniformSourceVariance a := by
    have h := (sq_le_sq₀ hlen (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 hT
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15),Real.sq_sqrt hV] at h
    exact h
  have hcost : _root_.DerivativeChainPhaseLock.uniformSourceSquareCost a ≤ 16*_root_.DerivativeChainPhaseLock.uniformSourceVariance a := by
    have h := _root_.DerivativeChainPhaseLock.actual_uniform_transport_square_bound n a r htop hstep
    linarith
  rw [_root_.DerivativeChainPhaseLock.uniform_ratio_eq]
  by_cases hz : _root_.DerivativeChainPhaseLock.uniformSourceVariance a=0
  · rw [hz,div_zero]; norm_num
  · exact (div_le_iff₀ (lt_of_le_of_ne hV (Ne.symm hz))).2 hcost
