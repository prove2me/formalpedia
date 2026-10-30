-- Prove2me | solution 1 for DerivativeChainContinuation.positive_activation_radius
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:21:59.308095+00:00
-- url     : https://prove2.me/submissions/9f695772-fad4-4906-b541-cc4c8186ce7d

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveGreedyChain
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_activation_parameter_formula
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


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





theorem complexHistoryOf_root {n : ℕ} (a z : Fin (n+1) → ℂ)
    (hz : DerivativeChainPrivate.IsChain a z) (j : ℕ) (hj : j ≤ n) :
    (row a (j+1)).eval (complexHistoryOf z j)=0 := by
  simpa only [complexHistoryOf,dif_pos (show j<n+1 by omega)] using hz ⟨j,by omega⟩











end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators







theorem positive_power_norm (k : ℕ) (w : ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hpow : w^k=(t : ℂ)) : ‖w‖^k=t := by
  have h := congrArg norm hpow
  simpa only [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht] using h










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
    (hz : DerivativeChainPrivate.IsChain a z) :
    ‖complexHistoryOf z (k-1)‖=(Q.roots.sum/(Nat.choose (n+1) k : ℝ))^((k : ℝ)⁻¹) := by
  obtain ⟨hpositive,hformula⟩ := positive_activation_parameter_formula n a k r Q hk hQ hQdegree hp
  have hdegree : (spokePoly k r Q).natDegree=n+1 := by rw [←hp,actual_complex_source_natDegree]
  have hkl : k ≤ n+1 := by
    have hg := spoke_natDegree k r Q hQ.1 (by omega)
    have hm : k ≤ k*Q.natDegree := Nat.le_mul_of_pos_right k hQdegree
    omega
  have hroot : (row a k).eval (complexHistoryOf z (k-1))=0 := by
    have h := complexHistoryOf_root a z hz (k-1) (by omega)
    simpa only [show k-1+1=k by omega] using h
  have hpow := positive_power_norm k (complexHistoryOf z (k-1)) _ hpositive.le ((hformula _).mp hroot)
  have hrpow : ((Q.roots.sum/(Nat.choose (n+1) k : ℝ))^((k : ℝ)⁻¹))^k=
      Q.roots.sum/(Nat.choose (n+1) k : ℝ) :=
    Real.rpow_inv_natCast_pow hpositive.le (by omega)
  exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hpositive.le _) (show k≠0 by omega)).mp
    (hpow.trans hrpow.symm)
