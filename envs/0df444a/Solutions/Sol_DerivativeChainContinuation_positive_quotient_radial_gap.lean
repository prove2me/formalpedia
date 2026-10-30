-- Prove2me | solution 1 for DerivativeChainContinuation.positive_quotient_radial_gap
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:40:57.905631+00:00
-- url     : https://prove2.me/submissions/89ab8a50-c873-4a17-bbb3-aeffe6ba0ea0

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainContinuation_PositiveWeightedMidpoint
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_product_radial_gap
import Theorems.Thm_DerivativeChainContinuation_positive_quotient_sorted_factor
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



theorem positiveWeighted_C_mul (s k : ℕ) (Q : Polynomial ℝ) (c : ℝ) :
    positiveWeighted s k (C c*Q)=C c*positiveWeighted s k Q := by
  simp only [positiveWeighted,derivative_C_mul]
  ring


end DerivativeChainContinuation

theorem solution (s k : ℕ) (Q : Polynomial ℝ)
    (hQ : PositiveQuotient Q) (hQdegree : 0<Q.natDegree) (hk : 2 ≤ k)
    (b t : ℝ) (hB : Q.eval b=0) (hBmax : ∀ v : ℝ,Q.eval v=0 → v ≤ b)
    (ht : 0<t) (hroot : (positiveWeighted s k Q).eval t=0)
    (hmax : ∀ v : ℝ,0<v → (positiveWeighted s k Q).eval v=0 → v ≤ t)
    (R x y : ℝ) (hR : 0 ≤ R) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hRpow : R^k=b) (hxpow : x^k=t)
    (hparent : y=0 ∨ Q.eval (y^k)=0) (hyR : y<R) : R+y<2*x := by
  obtain ⟨n,a,ha,hpositive,hn,hfac⟩ := positive_quotient_sorted_factor Q hQ
  cases n with
  | zero => omega
  | succ n =>
    have hc : Q.leadingCoeff≠0 := leadingCoeff_ne_zero.mpr hQ.1
    have hfacroot (v : ℝ) : Q.eval v=0 ↔ ∃ i : Fin (n+1),v=a i := by
      rw [hfac,eval_mul,eval_C,mul_eq_zero,or_iff_right hc]
      simp only [realRootProduct,eval_prod,eval_sub,eval_X,eval_C,
        Finset.prod_eq_zero_iff,Finset.mem_univ,true_and,sub_eq_zero]
    have hlast : a (Fin.last n)=b := by
      apply le_antisymm
      · exact hBmax _ ((hfacroot _).mpr ⟨Fin.last n,rfl⟩)
      · obtain ⟨i,hi⟩ := (hfacroot b).mp hB
        rw [hi]
        exact ha (Fin.le_last _)
    have hW : positiveWeighted s k Q=C Q.leadingCoeff*positiveWeighted s k (realRootProduct a) := by
      calc
        positiveWeighted s k Q=positiveWeighted s k (C Q.leadingCoeff*realRootProduct a) :=
          congrArg (positiveWeighted s k) hfac
        _=C Q.leadingCoeff*positiveWeighted s k (realRootProduct a) :=
          positiveWeighted_C_mul s k (realRootProduct a) Q.leadingCoeff
    have hroot' : (positiveWeighted s k (realRootProduct a)).eval t=0 := by
      rw [hW,eval_mul,eval_C] at hroot
      exact (mul_eq_zero.mp hroot).resolve_left hc
    have hmax' (v : ℝ) (hv : 0<v) (hvroot : (positiveWeighted s k (realRootProduct a)).eval v=0) : v ≤ t := by
      apply hmax v hv
      rw [hW,eval_mul,eval_C,hvroot,mul_zero]
    apply positive_product_radial_gap n s k a ha hpositive hk t ht hroot' hmax' R x y hR hx hy
      (by rw [hRpow,hlast]) hxpow _ hyR
    rcases hparent with hz | hr
    · exact Or.inl hz
    · exact Or.inr ((hfacroot _).mp hr)
