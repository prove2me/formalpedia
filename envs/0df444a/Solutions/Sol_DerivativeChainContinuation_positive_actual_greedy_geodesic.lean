-- Prove2me | solution 1 for DerivativeChainContinuation.positive_actual_greedy_geodesic
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:03:11.629541+00:00
-- url     : https://prove2.me/submissions/3c81389c-af3c-428b-ba37-646d8ffd0463

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_PositiveGreedyChain
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_actual_greedy_after_activation
import Theorems.Thm_DerivativeChainContinuation_positive_actual_greedy_step
import Theorems.Thm_DerivativeChainContinuation_positive_actual_low_row_root_zero
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



theorem complexHistoryOf_val {n : ℕ} (z : Fin (n+1) → ℂ) (i : Fin (n+1)) :
    complexHistoryOf z i.val=z i := by simp [complexHistoryOf,i.isLt]

theorem complexHistoryOf_root {n : ℕ} (a z : Fin (n+1) → ℂ)
    (hz : DerivativeChainPrivate.IsChain a z) (j : ℕ) (hj : j ≤ n) :
    (row a (j+1)).eval (complexHistoryOf z j)=0 := by
  simpa only [complexHistoryOf,dif_pos (show j<n+1 by omega)] using hz ⟨j,by omega⟩











end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation

theorem ray_geodesic_norm (w : ℂ) (t : ℝ) (ht : 1≤t) :
    ‖(t : ℂ)*w-w‖=‖(t : ℂ)*w‖-‖w‖ := by
  have hform : (t : ℂ)*w-w=((t-1 : ℝ) : ℂ)*w := by push_cast; ring
  rw [hform,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤t-1),
    abs_of_nonneg (by linarith : 0≤t)]
  ring







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









end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate







theorem chainCost_eq_sum_range {n : ℕ} (f : ℕ → ℂ) :
    chainCost (fun i : Fin n => f i.val) =
      ∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖ := by
  unfold chainCost
  exact Fin.sum_univ_eq_sum_range (fun i => ‖f (i + 1) - f i‖) (n - 1)





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



theorem solution {n : ℕ} (a z : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) (hp : fromRoots a=spokePoly k r Q)
    (hz : IsGreedyChain a z) :
    (∀ j<n,‖complexHistoryOf z (j+1)-complexHistoryOf z j‖=
      ‖complexHistoryOf z (j+1)‖-‖complexHistoryOf z j‖) ∧
      chainCost z=‖z (Fin.last n)‖ ∧
      (∀ w : ℂ,(fromRoots a).eval w=0 → ‖w‖ ≤ ‖z (Fin.last n)‖) ∧
      ∀ i : Fin (n+1),k ≤ i.val+1 →
        ∃ c : ℝ,1 ≤ c ∧ z i=(c : ℂ)*complexHistoryOf z (k-1) := by
  have hhigh := positive_actual_greedy_after_activation a z k r Q hk hQ hQdegree hp hz
  have hstep (j : ℕ) (hj : j<n) :
      ‖complexHistoryOf z (j+1)-complexHistoryOf z j‖=
        ‖complexHistoryOf z (j+1)‖-‖complexHistoryOf z j‖ := by
    by_cases hlow : j+1<k
    · have hz0 : complexHistoryOf z j=0 := positive_actual_low_row_root_zero a k r Q hk hQ hp
        (j+1) (by omega) (by omega) hlow _ (complexHistoryOf_root a z hz.1 j (by omega))
      simp [hz0]
    · obtain ⟨hw,hmax,hform⟩ := hhigh (j+1) (by omega) (by omega)
      obtain ⟨hnew,hnewmax,c,hc,hnewform⟩ := positive_actual_greedy_step a z k r Q hk hQ hQdegree hp hz
        (j+1) (by omega) (by omega) (by simpa using hw) (by simpa using hmax)
      have he : complexHistoryOf z (j+1)=(c : ℂ)*complexHistoryOf z j := by simpa using hnewform
      rw [he]
      exact ray_geodesic_norm _ c hc
  have hzero : complexHistoryOf z 0=0 := positive_actual_low_row_root_zero a k r Q hk hQ hp
    1 (by omega) (by omega) (by omega) _ (complexHistoryOf_root a z hz.1 0 (by omega))
  have hd : (spokePoly k r Q).natDegree=n+1 := by rw [←hp,actual_complex_source_natDegree]
  have hkl : k ≤ n+1 := by
    have hg := spoke_natDegree k r Q hQ.1 (by omega)
    have hm : k ≤ k*Q.natDegree := Nat.le_mul_of_pos_right k hQdegree
    omega
  refine ⟨hstep,?_,?_,?_⟩
  · have he : z=(fun i => complexHistoryOf z i.val) := funext (fun i => (complexHistoryOf_val z i).symm)
    rw [he,chainCost_eq_sum_range]
    change (∑ j∈Finset.range n,‖complexHistoryOf z (j+1)-complexHistoryOf z j‖)=_
    have hsum : (∑ j∈Finset.range n,‖complexHistoryOf z (j+1)-complexHistoryOf z j‖)=
        ∑ j∈Finset.range n,(‖complexHistoryOf z (j+1)‖-‖complexHistoryOf z j‖) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hstep j (Finset.mem_range.mp hj)
    rw [hsum,Finset.sum_range_sub (fun i => ‖complexHistoryOf z i‖) n,hzero,norm_zero,sub_zero]
    rfl
  · have h := (hhigh (n+1) hkl le_rfl).2.1
    intro w hw
    have hw' : (row a (n+1)).eval w=0 := by simpa only [row,Nat.sub_self,Function.iterate_zero_apply] using hw
    have hh := h w hw'
    simpa only [Nat.add_sub_cancel,show n=(Fin.last n).val from rfl,complexHistoryOf_val] using hh
  · intro i hi
    obtain ⟨hw,hmax,c,hc,hform⟩ := hhigh (i.val+1) hi (by omega)
    refine ⟨c,hc,?_⟩
    simpa only [Nat.add_sub_cancel,complexHistoryOf_val] using hform
