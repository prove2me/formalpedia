-- Prove2me | solution 1 for DerivativeChainContinuation.positive_spoke_low_degree_root_zero
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:58:03.034452+00:00
-- url     : https://prove2.me/submissions/6350570a-0289-4a5a-91a3-7ebeb7f3e7da

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators



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

theorem solution (k r : ℕ) (Q : Polynomial ℝ)
    (hk : 2≤k) (hQ : PositiveQuotient Q)
    (hdegree : (spokePoly k r Q).natDegree<k) (z : ℂ)
    (hroot : (spokePoly k r Q).eval z=0) : z=0 := by
  by_contra hz
  obtain ⟨t,ht,hpow,heval⟩ := positive_spoke_nonzero_root_power k r Q hQ z hz hroot
  have hdeg := spoke_natDegree k r Q hQ.1 (by omega)
  have hQdeg : Q.natDegree=0 := by
    by_contra hn
    have hle : k≤k*Q.natDegree := Nat.le_mul_of_pos_right k (by omega)
    omega
  have hQC := eq_C_of_natDegree_eq_zero hQdeg
  have hQne : Q.coeff 0≠0 := by
    intro he
    rw [hQC,he,C_0] at hQ
    exact hQ.1 rfl
  rw [hQC,eval_C] at heval
  exact hQne heval
