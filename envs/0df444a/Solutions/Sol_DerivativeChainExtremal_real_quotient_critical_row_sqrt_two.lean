-- Prove2me | solution 1 for DerivativeChainExtremal.real_quotient_critical_row_sqrt_two
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:16:35.486656+00:00
-- url     : https://prove2.me/submissions/f1611c7f-cfe7-4ee2-a4d4-dc8b9ae172b6

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainExtremal_polynomial_radial_prefix
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation





theorem solution (p : Polynomial ℂ)
    (n k r : ℕ) (hn : 1 ≤ n) (hdegree : p.natDegree=n+1) (q : Polynomial ℝ)
    (σ C₀ o : ℂ) (R : ℝ) (hk : 2 ≤ k) (hr : r < k)
    (hq : q.Splits) (hC : C₀ ≠ 0) (hσ : ‖σ‖=1)
    (hcore : p.derivative.comp (C (_root_.DerivativeChainContinuation.rootCentroid p)+C σ*X)=C C₀*_root_.DerivativeChainPrivate.spokePoly k r q)
    (hR : 0 ≤ R) (ha : ∀ w : ℂ, p.eval w=0 → ‖w-o‖ ≤ R) :
    ∃ z : Fin (n+1) → ℂ,
      (∀ i, (derivative^[n+1-(i.val+1)] p).eval (z i)=0) ∧ z 0=_root_.DerivativeChainContinuation.rootCentroid p ∧
      _root_.DerivativeChainPrivate.chainCost z ≤ Real.sqrt 2*Real.sqrt (R^2-‖_root_.DerivativeChainContinuation.rootCentroid p-o‖^2) := by
  have hc : (derivative^[n+1-n] p).comp (C (_root_.DerivativeChainContinuation.rootCentroid p)+C σ*X)=C C₀*_root_.DerivativeChainPrivate.spokePoly k r q := by
    simpa using hcore
  obtain ⟨z,hzr,hz0,hcost⟩ := _root_.DerivativeChainExtremal.polynomial_radial_prefix p n n k r hdegree q σ C₀ o R
    hn (by omega) hk hr hq hC hσ hc hR ha
  exact ⟨z,hzr,hz0,by simpa using hcost⟩
