-- Prove2me | solution 1 for DerivativeChainContinuation.collinear_greedy_min_cost
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:15:38.852019+00:00
-- url     : https://prove2.me/submissions/d18fc9f7-65d7-4cee-bc37-d3d6e93eb267

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_GreedyStatement
import Definitions.Def_DerivativeChainContinuation_RealTransportGeneral
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_affine_greedy_iff
import Theorems.Thm_DerivativeChainContinuation_real_greedy_min_cost
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators







theorem affine_inverse_value (o c w : ℂ) (hc : c≠0) : o+c*((w-o)/c)=w := by
  field_simp
  ring



theorem affine_greedy_inverse {n : ℕ} (a z : Fin (n+1) → ℂ)
    (o c : ℂ) (hc : c≠0) (hz : IsGreedyChain (fun i => o+c*a i) z) :
    IsGreedyChain a (fun i => (z i-o)/c) := by
  apply (affine_greedy_iff a _ o c hc).mp
  have he : (fun i => o+c*((z i-o)/c))=z := funext (fun i => affine_inverse_value o c (z i) hc)
  rwa [he]














end DerivativeChainContinuation


open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







theorem chainCost_scale {n : ℕ} (z : Fin n → ℂ) (c : ℂ) :
    chainCost (fun i => c * z i) = ‖c‖ * chainCost z := by
  simp only [chainCost, ← mul_sub, norm_mul, Finset.mul_sum]

end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate











theorem chainCost_translate {n : ℕ} (z : Fin n → ℂ) (u : ℂ) :
    chainCost (fun i => z i + u) = chainCost z := by
  simp only [chainCost, add_sub_add_right_eq_sub]

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial





theorem chainCost_affine {n : ℕ} (z : Fin n → ℂ) (a c : ℂ) :
    chainCost (fun i => a+c*z i) = ‖c‖*chainCost z := by
  have hfun : (fun i => a+c*z i) = (fun i => c*z i+a) := by funext i; ring
  rw [hfun,chainCost_translate,chainCost_scale]



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



theorem solution (n : ℕ) (hn : 1 ≤ n) (a : Fin (n+1) → ℝ)
    (o c : ℂ) (hc : c≠0) :
    ∃ z : Fin (n+1) → ℂ,IsGreedyChain (fun i => o+c*(a i : ℂ)) z ∧
      chainCost z=‖c‖*min (realCentroid a-orderedSource a 0)
        (orderedSource a (Fin.last n)-realCentroid a) ∧
      (∀ w : Fin (n+1) → ℂ,IsGreedyChain (fun i => o+c*(a i : ℂ)) w → chainCost z ≤ chainCost w) ∧
      chainCost z ≤ ‖c‖*(orderedSource a (Fin.last n)-orderedSource a 0)/2 := by
  obtain ⟨z,hz,hcost,hmin,hspan⟩ := real_greedy_min_cost n hn a
  refine ⟨fun i => o+c*z i,(affine_greedy_iff _ z o c hc).mpr hz,?_,?_,?_⟩
  · rw [chainCost_affine,hcost]
  · intro w hw
    let v : Fin (n+1) → ℂ := fun i => (w i-o)/c
    have hv : IsGreedyChain (fun i => (a i : ℂ)) v := affine_greedy_inverse _ w o c hc hw
    have hfun : w=(fun i => o+c*v i) := by
      funext i
      exact (affine_inverse_value o c (w i) hc).symm
    rw [hfun,chainCost_affine,chainCost_affine]
    exact mul_le_mul_of_nonneg_left (hmin v hv) (norm_nonneg c)
  · rw [chainCost_affine]
    have h := mul_le_mul_of_nonneg_left hspan (norm_nonneg c)
    nlinarith
