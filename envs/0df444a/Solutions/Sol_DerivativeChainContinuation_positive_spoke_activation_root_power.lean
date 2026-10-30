-- Prove2me | solution 1 for DerivativeChainContinuation.positive_spoke_activation_root_power
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:22:33.027777+00:00
-- url     : https://prove2.me/submissions/7c665d1f-aed9-426b-bd45-1a65928c4563

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_spoke_activation_row
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









theorem positive_linear_quotient_single_root (V : Polynomial ℝ)
    (hV : PositiveQuotient V) (hdegree : V.natDegree=1) :
    ∃ b : ℝ,0<b ∧ V.eval b=0 ∧ ∀ t : ℝ,V.eval t=0 → t=b := by
  have hc : V.roots.card=1 := by rw [←hV.2.1.natDegree_eq_card_roots,hdegree]
  obtain ⟨b,hb⟩ := Multiset.card_eq_one.mp hc
  have hmem : b∈V.roots := by rw [hb]; simp
  refine ⟨b,hV.2.2 b hmem,(mem_roots hV.1).mp hmem,?_⟩
  intro t ht
  have htm := (mem_roots hV.1).mpr ht
  rw [hb] at htm
  simpa using htm







end DerivativeChainContinuation



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial











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



theorem positiveQuotient_eval_ne_of_nonpos (Q : Polynomial ℝ) (hQ : PositiveQuotient Q)
    (x : ℝ) (hx : x≤0) : Q.eval x≠0 := by
  intro h
  have hp := hQ.2.2 x ((mem_roots hQ.1).mpr h)
  linarith













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

theorem solution (n k r : ℕ) (Q : Polynomial ℝ)
    (hk : 2≤k) (hQ : PositiveQuotient Q) (hQdegree : 0<Q.natDegree)
    (hdegree : (spokePoly k r Q).natDegree=n+1) :
    ∃ b : ℝ,0<b ∧ ∀ z : ℂ,
      (derivative^[n+1-k] (spokePoly k r Q)).eval z=0 ↔ z^k=(b : ℂ) := by
  obtain ⟨V,hV,hVdegree,heq⟩ := positive_spoke_activation_row n k r Q hk hQ hQdegree hdegree
  obtain ⟨b,hb,hbroot,hbunique⟩ := positive_linear_quotient_single_root V hV hVdegree
  refine ⟨b,hb,?_⟩
  intro z
  rw [heq]
  constructor
  · intro hz
    have hz0 : z≠0 := by
      intro he
      subst z
      have hV0 := positiveQuotient_eval_ne_of_nonpos V hV 0 le_rfl
      rw [spoke_eval_real_power k 0 V 0 0 (by simp [show k≠0 by omega]),pow_zero,one_mul] at hz
      exact hV0 (Complex.ofReal_eq_zero.mp hz)
    obtain ⟨t,ht,hpow,hroot⟩ := positive_spoke_nonzero_root_power k 0 V hV z hz0 hz
    rw [hbunique t hroot] at hpow
    exact hpow
  · intro hz
    rw [spoke_eval_real_power k 0 V z b hz,hbroot]
    simp
