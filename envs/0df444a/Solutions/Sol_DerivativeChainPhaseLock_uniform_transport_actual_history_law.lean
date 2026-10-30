-- Prove2me | solution 1 for DerivativeChainPhaseLock.uniform_transport_actual_history_law
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:47:51.605898+00:00
-- url     : https://prove2.me/submissions/c4a02bb7-2e36-4c78-9b23-cf25f9a1446c

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
import Definitions.Def_DerivativeChainAnalytic_UniformWasserstein
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_complex_tower_factor
import Theorems.Thm_DerivativeChainPrefixLaws_uniform_labelled_histories
import Theorems.Thm_DerivativeChainPrefixLaws_uniform_step_centroid
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
open Polynomial DerivativeChainContinuation
namespace DerivativeChainPrefixLaws
noncomputable section



theorem uniform_row_centroid (r : ComplexRootRows) (n : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (h : ℕ) (hh : h ≤ n) :
    complexCentroid (r h)=r 0 0 := by
  induction h with
  | zero => simp [complexCentroid]
  | succ h ih =>
    rw [uniform_step_centroid r h (hstep h (by omega)),ih (by omega)]













end
end DerivativeChainPrefixLaws



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
namespace DerivativeChainPrefixLaws
noncomputable section



theorem uniform_slot_history_isChain (n : ℕ) (a : Fin (n+1) → ℂ)
    (r : ComplexRootRows) (htop : r n=a) (hstep : ∀ k<n,UniformPolynomialStep r k)
    (slots : (k : ℕ) → Fin (k+1)) :
    IsChain a (fun i : Fin (n+1) => r i.val (slots i.val)) := by
  have hp : complexRowProduct r n=fromRoots a := by simp only [complexRowProduct,htop,fromRoots]
  intro i
  obtain ⟨c,hc,he⟩ := complex_tower_factor r n hstep i.val (by omega)
  rw [hp] at he
  have hr : (complexRowProduct r i.val).eval (r i.val (slots i.val))=0 := by
    simp only [complexRowProduct,eval_prod,eval_sub,eval_X,eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ (slots i.val)) (sub_self _)
  change ((derivative^[n+1-(i.val+1)]) (fromRoots a)).eval (r i.val (slots i.val))=0
  rw [show n+1-(i.val+1)=n-i.val by omega,he,eval_mul,hr,mul_zero]

end
end DerivativeChainPrefixLaws



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainContinuation DerivativeChainFiniteHistory
open DerivativeChainPrefixLaws
open DerivativeChainPhaseLock




theorem solution (n : ℕ) (a : Fin (n+1) → ℂ)
    (r : _root_.DerivativeChainContinuation.ComplexRootRows) (htop : r n=a) (hstep : ∀ k<n,_root_.DerivativeChainContinuation.UniformPolynomialStep r k)
    (K : (k : ℕ) → Fin (k+1) → Fin (k+2) → ℝ)
    (hK : ∀ k<n,_root_.DerivativeChainPhaseLock.UniformKernel k (k+1) (K k)) :
    ∃ (κ : Type) (inst : Fintype κ),letI := inst;
      ∃ L : _root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw a (r 0 0) κ,
        (∀ f : ℂ → ℝ,(∑ i,L.weights i*f (L.paths i (Fin.last n)))=
          ∑ j,(n+1:ℝ)⁻¹*f (a j)) ∧
        (∑ i,L.weights i*_root_.DerivativeChainPrivate.chainCost (L.paths i))=
          ∑ k : Fin n,_root_.DerivativeChainPhaseLock.uniformKernelCost (r k.val) (r (k.val+1)) (K k.val) := by
  classical
  obtain ⟨κ,inst,hdata⟩ := _root_.DerivativeChainPrefixLaws.uniform_labelled_histories n K
    (fun k hk => (hK k hk).1) (fun k hk => (hK k hk).2.1) (fun k hk => by convert (hK k hk).2.2 using 1 <;> norm_num [Nat.cast_add,Nat.cast_one,add_assoc])
  letI : Fintype κ := inst
  obtain ⟨w,slots,hw,hs,hmarg,hjoint⟩ := hdata
  let z : κ → Fin (n+1) → ℂ := fun i j => r j.val (slots i j.val)
  have hmean : (∑ j,(↑((n+1:ℝ)⁻¹):ℂ)*r n j)=r 0 0 := by
    have hc := _root_.DerivativeChainPrefixLaws.uniform_row_centroid r n hstep n le_rfl
    rw [← Finset.mul_sum]
    push_cast
    rw [← hc,_root_.DerivativeChainContinuation.complexCentroid]
    ring
  have hb : (∑ i,(w i:ℂ)*z i (Fin.last n))=r 0 0 := by
    apply Complex.ext
    · have hm := hmarg n le_rfl (fun j => (r n j).re)
      have hc : (∑ j,(n+1:ℝ)⁻¹*(r n j).re)=(r 0 0).re := by
        simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using congrArg Complex.re hmean
      simpa only [z,Fin.val_last,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero] using hm.trans hc
    · have hm := hmarg n le_rfl (fun j => (r n j).im)
      have hc : (∑ j,(n+1:ℝ)⁻¹*(r n j).im)=(r 0 0).im := by
        simpa only [Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using congrArg Complex.im hmean
      simpa only [z,Fin.val_last,Complex.im_sum,Complex.mul_im,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,add_zero] using hm.trans hc
  let L : _root_.DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw a (r 0 0) κ := {
    weights := w
    nonneg := hw
    total := hs
    paths := z
    actual := fun i => _root_.DerivativeChainPrefixLaws.uniform_slot_history_isChain n a r htop hstep (slots i)
    start := by intro i; change r 0 (slots i 0)=r 0 0; rw [Fin.eq_zero (slots i 0)]
    balanced := hb }
  refine ⟨κ,inst,L,?_,?_⟩
  · intro f
    simpa only [L,z,Fin.val_last,htop] using hmarg n le_rfl (fun j => f (r n j))
  · change (∑ i,w i*(∑ k : Fin n,‖r (k.val+1) (slots i (k.val+1))-r k.val (slots i k.val)‖))=_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    exact hjoint k.val k.isLt (fun j l => ‖r (k.val+1) l-r k.val j‖)
