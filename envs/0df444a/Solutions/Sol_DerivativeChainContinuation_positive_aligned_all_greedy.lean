-- Prove2me | solution 1 for DerivativeChainContinuation.positive_aligned_all_greedy
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:06:50.244918+00:00
-- url     : https://prove2.me/submissions/47058c70-2e6f-4e6a-b85d-fda183a3c7e4

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_PositiveGreedyChain
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_actual_greedy_chain_exists
import Theorems.Thm_DerivativeChainContinuation_positive_actual_greedy_after_activation
import Theorems.Thm_DerivativeChainContinuation_positive_actual_greedy_geodesic
import Theorems.Thm_DerivativeChainContinuation_positive_quotient_outer_root
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



theorem spoke_eval_real_power (k r : ℕ) (q : Polynomial ℝ) (w : ℂ) (y : ℝ)
    (hw : w ^ k = (y : ℂ)) :
    (spokePoly k r q).eval w = w ^ r * ((q.eval y : ℝ) : ℂ) := by
  simp only [spokePoly, eval_mul, eval_pow, eval_X, eval_comp, hw]
  exact congrArg (fun z : ℂ => w ^ r * z)
    (Polynomial.eval_map_apply (f := Complex.ofRealHom) (p := q) y)



theorem spoke_root_power_real (k r : ℕ) (q : Polynomial ℝ) (hq : q.Splits)
    (hqne : q ≠ 0) (w : ℂ) (hw : w ≠ 0) (hz : (spokePoly k r q).eval w = 0) :
    ∃ y : ℝ, w ^ k = (y : ℂ) := by
  have heval : (q.map Complex.ofRealHom).eval (w ^ k) = 0 := by
    simp only [spokePoly, eval_mul, eval_pow, eval_X, eval_comp] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hw)
  obtain ⟨y, hy⟩ := hq.mem_range_of_isRoot hqne heval
  exact ⟨y, hy.symm⟩

end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

















theorem positive_spoke_nonzero_root_power (k r : ℕ) (Q : Polynomial ℝ)
    (hQ : PositiveQuotient Q) (z : ℂ) (hz : z≠0)
    (hroot : (spokePoly k r Q).eval z=0) :
    ∃ t : ℝ,0<t ∧ z^k=(t : ℂ) ∧ Q.eval t=0 := by
  obtain ⟨t,ht⟩ := spoke_root_power_real k r Q hQ.2.1 hQ.1 z hz hroot
  have hv : Q.eval t=0 := by
    rw [spoke_eval_real_power k r Q z t ht] at hroot
    have h := (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ hz)
    exact Complex.ofReal_eq_zero.mp h
  exact ⟨t,hQ.2.2 t ((mem_roots hQ.1).mpr hv),ht,hv⟩






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

theorem solution (n : ℕ) (a : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) (hp : fromRoots a=spokePoly k r Q) :
    (∃ z : Fin (n+1) → ℂ,IsGreedyChain a z) ∧
      ∃ b : ℝ,0<b ∧ Q.eval b=0 ∧ (∀ y : ℝ,Q.eval y=0 → y ≤ b) ∧
        ∀ z : Fin (n+1) → ℂ,IsGreedyChain a z →
          chainCost z=b^((k : ℝ)⁻¹) ∧
            ∀ i : Fin (n+1),k ≤ i.val+1 →
              z i≠0 ∧ (∀ w : ℂ,(row a (i.val+1)).eval w=0 → ‖w‖ ≤ ‖z i‖) ∧
                ∃ c : ℝ,1 ≤ c ∧ z i=(c : ℂ)*complexHistoryOf z (k-1) := by
  refine ⟨actual_greedy_chain_exists n a,?_⟩
  obtain ⟨b,hb,hbroot,hbmax⟩ := positive_quotient_outer_root Q hQ hQdegree
  refine ⟨b,hb,hbroot,hbmax,?_⟩
  intro z hz
  obtain ⟨hsteps,hcost,hmax,hphase⟩ := positive_actual_greedy_geodesic a z k r Q hk hQ hQdegree hp hz
  have hhigh := positive_actual_greedy_after_activation a z k r Q hk hQ hQdegree hp hz
  have hd : (spokePoly k r Q).natDegree=n+1 := by rw [←hp,actual_complex_source_natDegree]
  have hkl : k ≤ n+1 := by
    have hg := spoke_natDegree k r Q hQ.1 (by omega)
    have hm : k ≤ k*Q.natDegree := Nat.le_mul_of_pos_right k hQdegree
    omega
  have hendnonzero : z (Fin.last n)≠0 := by
    have h := (hhigh (n+1) hkl le_rfl).1
    simpa only [Nat.add_sub_cancel,show n=(Fin.last n).val from rfl,complexHistoryOf_val] using h
  have hendroot : (spokePoly k r Q).eval (z (Fin.last n))=0 := by
    have h := hz.1 (Fin.last n)
    simpa only [row,Fin.val_last,Nat.sub_self,Function.iterate_zero_apply,hp] using h
  obtain ⟨t,ht,hpow,htroot⟩ := positive_spoke_nonzero_root_power k r Q hQ _ hendnonzero hendroot
  have hnormpow := positive_power_norm k _ t ht.le hpow
  let R : ℝ := b^((k : ℝ)⁻¹)
  have hR : 0<R := Real.rpow_pos_of_pos hb _
  have hRpow : R^k=b := Real.rpow_inv_natCast_pow hb.le (by omega)
  have hRcomplex : (R : ℂ)^k=(b : ℂ) := by rw [←Complex.ofReal_pow,hRpow]
  have hRroot : (fromRoots a).eval (R : ℂ)=0 := by
    rw [hp,spoke_eval_real_power k r Q _ b hRcomplex,hbroot]
    simp
  have hlow : R ≤ ‖z (Fin.last n)‖ := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR] using hmax _ hRroot
  have huppow : ‖z (Fin.last n)‖^k ≤ R^k := by rw [hnormpow,hRpow]; exact hbmax t htroot
  have hup : ‖z (Fin.last n)‖ ≤ R := le_of_pow_le_pow_left₀ (by omega) hR.le huppow
  refine ⟨hcost.trans (le_antisymm hup hlow),?_⟩
  intro i hi
  have h := hhigh (i.val+1) hi (by omega)
  simpa only [Nat.add_sub_cancel,complexHistoryOf_val] using h
