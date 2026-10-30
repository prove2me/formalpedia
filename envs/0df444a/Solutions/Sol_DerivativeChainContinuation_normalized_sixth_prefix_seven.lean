-- Prove2me | solution 1 for DerivativeChainContinuation.normalized_sixth_prefix_seven
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:17:09.767422+00:00
-- url     : https://prove2.me/submissions/3bfc2e70-53ee-4e83-9a19-0a312a138186

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticInverse
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Theorems.Thm_DerivativeChainContinuation_normalized_sixth_extend_prefix_five
import Theorems.Thm_DerivativeChainContinuation_normalized_sixth_extend_prefix_six
import Theorems.Thm_DerivativeChainContinuation_normalized_sixth_prefix_five
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
    ∃ z : Fin 7 → ℂ,
      (∀ i,(derivative^[18-(i.val+1)] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval (z i)=0) ∧
      z 0=0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      0<(z 6).im ∧ 4<(z 6).re^2 ∧
      β/z 6=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*(z 6)^2-
        ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder (z 6)/z 6 ∧
      (sixthSepticRemainder (z 6)).re/(z 6).re≤39/2000 ∧
      (sixthSepticRemainder (z 6)).im/(z 6).im≤0 ∧
      (3*((sixthSepticRemainder (z 6)).re/(z 6).re)-(sixthSepticRemainder (z 6)).im/(z 6).im)/2≤39/1000 ∧
      4≤(z 6).re^2-3*(z 6).im^2 := by
  obtain ⟨f,hroot,hzero,hr,hi,hpos,hX,hinv⟩:=normalized_sixth_prefix_five β hR hI.le
  obtain ⟨μ,hfinite,hsupp,hμ,f₆,hext,hroots,hz0,hmr,hmi,hzi,hzX,hgraph⟩:=
    normalized_sixth_extend_prefix_five β hR hI f hroot hzero hr hi hpos hX hinv
  letI : IsFiniteMeasure μ:=hfinite
  obtain ⟨z,hext',hroots',hz0',hmr',hmi',hzi',hzX',hgraph',hA,hB,hC,hW⟩:=
    normalized_sixth_extend_prefix_six μ hsupp hμ β hR hI f₆ hroots hz0 hmr hmi hzi hzX hgraph
  exact ⟨z,hroots',hz0',hmr',hmi',hzi',hzX',hgraph',hA,hB,hC,hW⟩
