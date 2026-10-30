-- Prove2me | solution 1 for DerivativeChainContinuation.collinear_greedy_all_histories
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:10:17.215824+00:00
-- url     : https://prove2.me/submissions/f7f2c414-fe24-46f4-a40a-f11c9e67de2d

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_GreedyReal
import Definitions.Def_DerivativeChainContinuation_GreedyStatement
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainContinuation_RealTransportGeneral
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_affine_complex_row_root_iff
import Theorems.Thm_DerivativeChainContinuation_affine_greedy_iff
import Theorems.Thm_DerivativeChainContinuation_real_greedy_all_histories
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
    ∃ r : RealRows,r n=orderedSource a ∧ (∀ k ≤ n,Monotone (r k)) ∧
      (∀ k ≤ n,∀ w : ℂ,(row (fun i => o+c*(a i : ℂ)) (k+1)).eval w=0 ↔
        ∃ j : Fin (k+1),w=o+c*(r k j : ℂ)) ∧
      (∀ z : Fin (n+1) → ℂ,IsGreedyChain (fun i => o+c*(a i : ℂ)) z ↔
        (∀ i,z i=o+c*(leftRow r i.val : ℂ)) ∨
        (∀ i,z i=o+c*(rightRow r i.val : ℂ))) ∧
      (∀ z : Fin (n+1) → ℂ,IsGreedyChain (fun i => o+c*(a i : ℂ)) z →
        chainCost z=‖c‖*(realCentroid a-orderedSource a 0) ∨
        chainCost z=‖c‖*(orderedSource a (Fin.last n)-realCentroid a)) := by
  obtain ⟨r,hr,hm,hs,hrows,hclass,hcost,hex⟩ := real_greedy_all_histories n hn a
  refine ⟨r,hr,hm,?_,?_,?_⟩
  · intro k hk w
    constructor
    · intro hw
      let v := (w-o)/c
      have hwfun : o+c*v=w := affine_inverse_value o c w hc
      have hv := (affine_complex_row_root_iff (fun i => (a i : ℂ)) o c hc (k+1) v).mp
        (by rwa [hwfun])
      obtain ⟨j,hj⟩ := (hrows k hk v).mp hv
      exact ⟨j,by rw [←hwfun,hj]⟩
    · rintro ⟨j,rfl⟩
      exact (affine_complex_row_root_iff (fun i => (a i : ℂ)) o c hc (k+1) _).mpr
        ((hrows k hk _).mpr ⟨j,rfl⟩)
  · intro z
    constructor
    · intro hz
      let v : Fin (n+1) → ℂ := fun i => (z i-o)/c
      have hv := affine_greedy_inverse (fun i => (a i : ℂ)) z o c hc hz
      rcases (hclass v).mp hv with hl | hrr
      · left
        intro i
        have he := affine_inverse_value o c (z i) hc
        change o+c*v i=z i at he
        rw [hl i] at he
        exact he.symm
      · right
        intro i
        have he := affine_inverse_value o c (z i) hc
        change o+c*v i=z i at he
        rw [hrr i] at he
        exact he.symm
    · rintro (hl | hrr)
      · have he : z=(fun i => o+c*(leftRow r i.val : ℂ)) := funext hl
        rw [he]
        exact (affine_greedy_iff _ _ o c hc).mpr ((hclass _).mpr (Or.inl (fun i => rfl)))
      · have he : z=(fun i => o+c*(rightRow r i.val : ℂ)) := funext hrr
        rw [he]
        exact (affine_greedy_iff _ _ o c hc).mpr ((hclass _).mpr (Or.inr (fun i => rfl)))
  · intro z hz
    let v : Fin (n+1) → ℂ := fun i => (z i-o)/c
    have hv := affine_greedy_inverse (fun i => (a i : ℂ)) z o c hc hz
    have he : z=(fun i => o+c*v i) := by
      funext i
      exact (affine_inverse_value o c (z i) hc).symm
    rw [he,chainCost_affine]
    rcases hcost v hv with hl | hrr
    · exact Or.inl (by rw [hl])
    · exact Or.inr (by rw [hrr])
