-- Prove2me | solution 1 for DerivativeChainContinuation.normalized_sixth_prefix_eight
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:21:19.692986+00:00
-- url     : https://prove2.me/submissions/3f2a6bef-224a-4a5d-81d6-24d480a35ace

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticErrorDerivative
import Definitions.Def_DerivativeChainPrivate_SixthSepticInverse
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_normalized_sixth_extend_prefix_seven
import Theorems.Thm_DerivativeChainContinuation_normalized_sixth_prefix_seven
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


theorem solution (β : ℂ) (hR : 0≤β.re) (hI : 0<β.im) :
    ∃ z : Fin 8 → ℂ,
      (∀ i,(derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (z i)=0) ∧
      z 0=0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      0<(z 7).im ∧ 26/5<(z 7).re^2 ∧
      β/z 7=(((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*(z 7)^2-
        ((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder (z 7)/z 7 ∧
      (sixthOcticRemainder (z 7)).re/(z 7).re≤9/1000 ∧
      (sixthOcticRemainder (z 7)).im/(z 7).im≤0 ∧
      (3*((sixthOcticRemainder (z 7)).re/(z 7).re)-(sixthOcticRemainder (z 7)).im/(z 7).im)/2≤73/4000 ∧
      26/5≤(z 7).re^2-3*(z 7).im^2 := by
  obtain ⟨f,hroot,hzero,hr,hi,him,hX,hinv,hA,hB,hC,hW⟩:=normalized_sixth_prefix_seven β hR hI
  obtain ⟨z,hext,hroots,hz0,hmr,hmi,hzi,hzX,hgraph,hA',hB',hC',hW'⟩:=
    normalized_sixth_extend_prefix_seven β hR hI f hroot hzero hr hi him hX hinv
  exact ⟨z,hroots,hz0,hmr,hmi,hzi,hzX,hgraph,hA',hB',hC',hW'⟩
