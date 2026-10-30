-- Prove2me | solution 1 for DerivativeChainContinuation.positive_affine_activation_radius
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:27:42.372989+00:00
-- url     : https://prove2.me/submissions/79b0e30b-2107-4324-a7ab-8fc8b12dba29

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_PositiveGreedyChain
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_affine_greedy_iff
import Theorems.Thm_DerivativeChainContinuation_positive_activation_radius
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

theorem solution (n : ℕ) (a z : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) (hp : fromRoots a=spokePoly k r Q)
    (o c : ℂ) (hc : c≠0) (hz : IsGreedyChain (fun i => o+c*a i) z) :
    ‖complexHistoryOf z (k-1)-o‖=‖c‖*(Q.roots.sum/(Nat.choose (n+1) k : ℝ))^((k : ℝ)⁻¹) := by
  let v : Fin (n+1) → ℂ := fun i => (z i-o)/c
  have hv := affine_greedy_inverse a z o c hc hz
  have hbase := positive_activation_radius n a v k r Q hk hQ hQdegree hp hv.1
  have hdegree : (spokePoly k r Q).natDegree=n+1 := by rw [←hp,actual_complex_source_natDegree]
  have hkl : k ≤ n+1 := by
    have hg := spoke_natDegree k r Q hQ.1 (by omega)
    have hm : k ≤ k*Q.natDegree := Nat.le_mul_of_pos_right k hQdegree
    omega
  have hfun : z=(fun i => o+c*v i) := by
    funext i
    exact (affine_inverse_value o c (z i) hc).symm
  have hact : complexHistoryOf z (k-1)=o+c*complexHistoryOf v (k-1) := by
    conv_lhs => rw [hfun]
    exact complexHistoryOf_affine v o c (k-1) (by omega)
  rw [hact,show (o+c*complexHistoryOf v (k-1))-o=c*complexHistoryOf v (k-1) by ring,
    norm_mul,hbase]
