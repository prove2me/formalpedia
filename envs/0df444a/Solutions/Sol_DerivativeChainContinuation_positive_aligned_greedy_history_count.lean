-- Prove2me | solution 1 for DerivativeChainContinuation.positive_aligned_greedy_history_count
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:30:21.876423+00:00
-- url     : https://prove2.me/submissions/a380f629-4aa4-48c4-960b-5407ae87a494

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_PositiveGreedyChain
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_actual_greedy_chain_exists
import Theorems.Thm_DerivativeChainContinuation_finite_derivative_chains
import Theorems.Thm_DerivativeChainContinuation_positive_actual_activation_roots
import Theorems.Thm_DerivativeChainContinuation_positive_actual_greedy_after_activation
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











theorem positive_actual_chain_before_activation {n : ℕ} (a z : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hp : fromRoots a=spokePoly k r Q) (hz : DerivativeChainPrivate.IsChain a z) :
    ∀ i : Fin (n+1),i.val+1<k → z i=0 := by
  intro i hi
  exact positive_actual_low_row_root_zero a k r Q hk hQ hp (i.val+1) (by omega)
    (by omega) hi (z i) (hz i)












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









end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate













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

theorem iterate_derivative_comp_affine (p : Polynomial ℂ) (a c : ℂ) (k : ℕ) :
    derivative^[k] (p.comp (C a+C c*X)) =
      C (c^k)*(derivative^[k] p).comp (C a+C c*X) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,derivative_C_mul,derivative_comp]
    simp only [derivative_add,derivative_C,derivative_mul,zero_mul,derivative_X,
      mul_one,zero_add,Function.iterate_succ_apply']
    rw [pow_succ,C_mul]
    ring







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




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem positive_spoke_rotation_comp (k r : ℕ) (Q : Polynomial ℝ)
    (ζ : ℂ) (hζ : ζ^k=1) :
    (spokePoly k r Q).comp (C 0+C ζ*X)=C (ζ^r)*spokePoly k r Q := by
  simp only [spokePoly,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.X_comp,
    C_0,zero_add,Polynomial.comp_assoc,mul_pow,←map_pow,hζ,map_one,one_mul]
  ring

theorem positive_spoke_rotation_row_root_iff {n : ℕ} (a : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hp : fromRoots a=spokePoly k r Q)
    (ζ : ℂ) (hζ : ζ^k=1) (hζne : ζ≠0) (m : ℕ) (z : ℂ) :
    (row a m).eval (ζ*z)=0 ↔ (row a m).eval z=0 := by
  have he := congrArg (fun p : Polynomial ℂ => (derivative^[n+1-m] p).eval z)
    (positive_spoke_rotation_comp k r Q ζ hζ)
  rw [iterate_derivative_comp_affine,iterate_derivative_C_mul] at he
  simp only [eval_mul,eval_C,eval_comp,eval_add,eval_X,zero_add] at he
  rw [←hp] at he
  change ζ^(n+1-m)*(row a m).eval (ζ*z)=ζ^r*(row a m).eval z at he
  constructor
  · intro hz
    rw [hz,mul_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ hζne)
  · intro hz
    rw [hz,mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hζne)

theorem positive_greedy_rotation {n : ℕ} (a z : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k)
    (hp : fromRoots a=spokePoly k r Q) (hz : IsGreedyChain a z)
    (ζ : ℂ) (hζ : ζ^k=1) : IsGreedyChain a (fun i => ζ*z i) := by
  have hζne : ζ≠0 := by intro h; rw [h,zero_pow (show k≠0 by omega)] at hζ; exact zero_ne_one hζ
  have hnorm : ‖ζ‖=1 := by
    have hpow : ‖ζ‖^k=(1 : ℝ)^k := by rw [←norm_pow,hζ,norm_one,one_pow]
    exact (pow_left_inj₀ (norm_nonneg ζ) (by positivity) (show k≠0 by omega)).mp hpow
  refine ⟨?_,?_⟩
  · intro i
    exact (positive_spoke_rotation_row_root_iff a k r Q hp ζ hζ hζne (i.val+1) (z i)).mpr (hz.1 i)
  · intro i w hw
    let v := w/ζ
    have hwfun : ζ*v=w := by dsimp only [v]; field_simp
    have hv := (positive_spoke_rotation_row_root_iff a k r Q hp ζ hζ hζne (i.val+2) v).mp
      (by rwa [hwfun])
    have h := hz.2 i v hv
    have hd (x y : ℂ) : ‖ζ*x-ζ*y‖=‖x-y‖ := by rw [←mul_sub,norm_mul,hnorm,one_mul]
    rw [←hwfun,hd,hd]
    exact h

theorem positive_greedy_determined_by_activation {n : ℕ} (a z w : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) (hp : fromRoots a=spokePoly k r Q)
    (hz : IsGreedyChain a z) (hw : IsGreedyChain a w)
    (heq : complexHistoryOf z (k-1)=complexHistoryOf w (k-1)) : z=w := by
  have hzHigh := positive_actual_greedy_after_activation a z k r Q hk hQ hQdegree hp hz
  have hwHigh := positive_actual_greedy_after_activation a w k r Q hk hQ hQdegree hp hw
  funext i
  by_cases hi : i.val+1<k
  · have hzi := positive_actual_chain_before_activation a z k r Q hk hQ hp hz.1 i hi
    have hwi := positive_actual_chain_before_activation a w k r Q hk hQ hp hw.1 i hi
    rw [hzi,hwi]
  · obtain ⟨hzi,hzmax,c,hc,hzc⟩ := hzHigh (i.val+1) (by omega) (by omega)
    obtain ⟨hwi,hwmax,d,hd,hwd⟩ := hwHigh (i.val+1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel,complexHistoryOf_val] at hzi hzmax hzc hwi hwmax hwd
    have hnorm : ‖z i‖=‖w i‖ := le_antisymm (hwmax _ (hz.1 i)) (hzmax _ (hw.1 i))
    rw [←heq] at hwd
    have hact : complexHistoryOf z (k-1)≠0 := by
      intro h0
      rw [h0,mul_zero] at hzc
      exact hzi hzc
    have hcoeff : c=d := by
      rw [hzc,hwd,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
        Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ c),abs_of_nonneg (by linarith : 0 ≤ d)] at hnorm
      exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hact) hnorm
    rw [hzc,hwd,hcoeff]

theorem positive_greedy_every_activation {n : ℕ} (a : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) (hp : fromRoots a=spokePoly k r Q)
    (v : ℂ) (hv : (row a k).eval v=0) :
    ∃ z : Fin (n+1) → ℂ,IsGreedyChain a z ∧ complexHistoryOf z (k-1)=v := by
  have hd : (spokePoly k r Q).natDegree=n+1 := by rw [←hp,actual_complex_source_natDegree]
  have hkl : k ≤ n+1 := by
    have hg := spoke_natDegree k r Q hQ.1 (by omega)
    have hm : k ≤ k*Q.natDegree := Nat.le_mul_of_pos_right k hQdegree
    omega
  obtain ⟨b,hb,hactivation⟩ := positive_actual_activation_roots a k r Q hk hQ hQdegree hp
  obtain ⟨z,hz⟩ := actual_greedy_chain_exists n a
  let u := complexHistoryOf z (k-1)
  have huroot : (row a k).eval u=0 := by
    have h := complexHistoryOf_root a z hz.1 (k-1) (by omega)
    simpa only [Set.mem_ofPred_eq,show k-1+1=k by omega] using h
  have hupow := (hactivation u).mp huroot
  have hvpow := (hactivation v).mp hv
  have hune : u≠0 := by
    intro h
    rw [h,zero_pow (show k≠0 by omega)] at hupow
    have h0 : b=0 := Complex.ofReal_injective hupow.symm
    linarith
  let ζ := v/u
  have hζ : ζ^k=1 := by
    dsimp only [ζ]
    rw [div_pow,hvpow,hupow,div_self (by exact_mod_cast (ne_of_gt hb))]
  refine ⟨fun i => ζ*z i,positive_greedy_rotation a z k r Q hk hp hz ζ hζ,?_⟩
  have h := complexHistoryOf_affine z 0 ζ (k-1) (by omega)
  simp only [zero_add] at h
  rw [h]
  exact div_mul_cancel₀ v hune

theorem complex_power_root_count (k : ℕ) (hk : 1 ≤ k) (b : ℂ) (hb : b≠0) :
    Set.ncard {z : ℂ | z^k=b}=k := by
  classical
  let p : Polynomial ℂ := X^k-C b
  have hpne : p≠0 := X_pow_sub_C_ne_zero (by omega) b
  have hsep : p.Separable := separable_X_pow_sub_C b (by exact_mod_cast (show k≠0 by omega)) hb
  have hcard : Fintype.card (p.rootSet ℂ)=p.natDegree :=
    card_rootSet_eq_natDegree hsep (IsAlgClosed.splits_domain p)
  have hset : {z : ℂ | z^k=b}=p.rootSet ℂ := by
    ext z
    simp [Polynomial.mem_rootSet_of_ne hpne,p,aeval_def,sub_eq_zero]
  rw [hset,←Nat.card_coe_set_eq,Nat.card_eq_fintype_card,hcard]
  exact natDegree_X_pow_sub_C






























end DerivativeChainContinuation

theorem solution (n : ℕ) (a : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) (hp : fromRoots a=spokePoly k r Q) :
    {z : Fin (n+1) → ℂ | IsGreedyChain a z}.Finite ∧
      Set.ncard {z : Fin (n+1) → ℂ | IsGreedyChain a z}=k := by
  have hfinite : {z : Fin (n+1) → ℂ | IsGreedyChain a z}.Finite :=
    (finite_derivative_chains a).subset (fun z hz => hz.1)
  refine ⟨hfinite,?_⟩
  have hd : (spokePoly k r Q).natDegree=n+1 := by rw [←hp,actual_complex_source_natDegree]
  have hkl : k ≤ n+1 := by
    have hg := spoke_natDegree k r Q hQ.1 (by omega)
    have hm : k ≤ k*Q.natDegree := Nat.le_mul_of_pos_right k hQdegree
    omega
  have hcard : Set.ncard {z : Fin (n+1) → ℂ | IsGreedyChain a z}=
      Set.ncard {v : ℂ | (row a k).eval v=0} := by
    apply Set.ncard_congr (fun z _ => complexHistoryOf z (k-1))
    · intro z hz
      have h := complexHistoryOf_root a z hz.1 (k-1) (by omega)
      simpa only [Set.mem_ofPred_eq,show k-1+1=k by omega] using h
    · intro z w hz hw he
      exact positive_greedy_determined_by_activation a z w k r Q hk hQ hQdegree hp hz hw he
    · intro v hv
      obtain ⟨z,hz,he⟩ := positive_greedy_every_activation a k r Q hk hQ hQdegree hp v hv
      exact ⟨z,hz,he⟩
  obtain ⟨b,hb,hactivation⟩ := positive_actual_activation_roots a k r Q hk hQ hQdegree hp
  have hset : {v : ℂ | (row a k).eval v=0}={v : ℂ | v^k=(b : ℂ)} := by
    ext v
    exact hactivation v
  rw [hcard,hset]
  exact complex_power_root_count k (by omega) (b : ℂ) (by exact_mod_cast (ne_of_gt hb))
