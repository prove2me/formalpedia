-- Prove2me | solution 1 for DerivativeChainContinuation.positive_aligned_affine_all_greedy
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:09:36.386344+00:00
-- url     : https://prove2.me/submissions/833f0f96-6fc8-4970-a225-1aa4e3a3830e

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_PositiveGreedyChain
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_actual_greedy_chain_exists
import Theorems.Thm_DerivativeChainContinuation_affine_complex_row_root_iff
import Theorems.Thm_DerivativeChainContinuation_affine_greedy_iff
import Theorems.Thm_DerivativeChainContinuation_positive_aligned_all_greedy
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





theorem affine_complex_distance (o c z w : ℂ) :
    ‖(o+c*z)-(o+c*w)‖=‖c‖*‖z-w‖ := by
  rw [show (o+c*z)-(o+c*w)=c*(z-w) by ring,norm_mul]

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


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem actual_complex_source_natDegree {n : ℕ} (a : Fin (n+1) → ℂ) :
    (fromRoots a).natDegree=n+1 := by
  simp only [fromRoots]
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))]
  simp
























end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators



theorem complexHistoryOf_affine {n : ℕ} (z : Fin (n+1) → ℂ) (o c : ℂ)
    (j : ℕ) (hj : j ≤ n) :
    complexHistoryOf (fun i => o+c*z i) j=o+c*complexHistoryOf z j := by
  simp only [complexHistoryOf,dif_pos (show j<n+1 by omega)]












end DerivativeChainContinuation



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial







theorem spoke_natDegree (k r : ℕ) (q : Polynomial ℝ) (hq : q ≠ 0) (hk : 0 < k) :
    (spokePoly k r q).natDegree = r + k * q.natDegree := by
  have hmap : q.map Complex.ofRealHom ≠ 0 := Polynomial.map_ne_zero hq
  have hcomp : (q.map Complex.ofRealHom).comp (X ^ k) ≠ 0 := by
    rw [ne_eq, Polynomial.comp_eq_zero_iff]
    simp only [hmap, false_or]
    intro h
    have hdegree := congrArg Polynomial.natDegree h.2
    simp only [natDegree_X_pow, natDegree_C] at hdegree
    omega
  rw [spokePoly, natDegree_mul (pow_ne_zero _ X_ne_zero) hcomp,
    natDegree_X_pow, natDegree_comp, natDegree_map, natDegree_X_pow]
  ring









end DerivativeChainPrivate


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



theorem solution (n : ℕ) (a : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) (hp : fromRoots a=spokePoly k r Q)
    (o c : ℂ) (hc : c≠0) :
    (∃ z : Fin (n+1) → ℂ,IsGreedyChain (fun i => o+c*a i) z) ∧
      ∃ b : ℝ,0<b ∧ Q.eval b=0 ∧ (∀ y : ℝ,Q.eval y=0 → y ≤ b) ∧
        ∀ z : Fin (n+1) → ℂ,IsGreedyChain (fun i => o+c*a i) z →
          chainCost z=‖c‖*b^((k : ℝ)⁻¹) ∧
            ∀ i : Fin (n+1),k ≤ i.val+1 →
              z i≠o ∧
                (∀ w : ℂ,(row (fun j => o+c*a j) (i.val+1)).eval w=0 → ‖w-o‖ ≤ ‖z i-o‖) ∧
                ∃ d : ℝ,1 ≤ d ∧ z i-o=(d : ℂ)*(complexHistoryOf z (k-1)-o) := by
  obtain ⟨hex,b,hb,hbroot,hbmax,hall⟩ := positive_aligned_all_greedy n a k r Q hk hQ hQdegree hp
  refine ⟨actual_greedy_chain_exists n (fun i => o+c*a i),b,hb,hbroot,hbmax,?_⟩
  intro z hz
  let v : Fin (n+1) → ℂ := fun i => (z i-o)/c
  have hv : IsGreedyChain a v := affine_greedy_inverse a z o c hc hz
  obtain ⟨hcost,hphase⟩ := hall v hv
  have hfun : z=(fun i => o+c*v i) := by
    funext i
    exact (affine_inverse_value o c (z i) hc).symm
  have hd : (spokePoly k r Q).natDegree=n+1 := by rw [←hp,actual_complex_source_natDegree]
  have hkl : k ≤ n+1 := by
    have hg := spoke_natDegree k r Q hQ.1 (by omega)
    have hm : k ≤ k*Q.natDegree := Nat.le_mul_of_pos_right k hQdegree
    omega
  refine ⟨?_,?_⟩
  · rw [hfun,chainCost_affine,hcost]
  · intro i hi
    obtain ⟨hvi,hmax,d,hd,hform⟩ := hphase i hi
    have hzi : z i≠o := by
      intro he
      apply hvi
      dsimp only [v]
      rw [he,sub_self,zero_div]
    refine ⟨hzi,?_,d,hd,?_⟩
    · intro w hw
      let u := (w-o)/c
      have hwfun : o+c*u=w := affine_inverse_value o c w hc
      have huroot := (affine_complex_row_root_iff a o c hc (i.val+1) u).mp (by rwa [hwfun])
      have hbound := mul_le_mul_of_nonneg_left (hmax u huroot) (norm_nonneg c)
      have hwnorm : ‖w-o‖=‖c‖*‖u‖ := by
        simpa only [mul_zero,add_zero,sub_zero,hwfun] using affine_complex_distance o c u 0
      have hpointnorm : ‖z i-o‖=‖c‖*‖v i‖ := by
        have hh := affine_complex_distance o c (v i) 0
        rw [←congrFun hfun i] at hh
        simpa only [mul_zero,add_zero,sub_zero] using hh
      rw [hwnorm,hpointnorm]
      exact hbound
    · have hact : complexHistoryOf z (k-1)=o+c*complexHistoryOf v (k-1) := by
        conv_lhs => rw [hfun]
        exact complexHistoryOf_affine v o c (k-1) (by omega)
      have hpoint : z i=o+c*v i := congrFun hfun i
      rw [hpoint,hact,hform]
      ring
