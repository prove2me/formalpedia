-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_sixth_octic_step_with_bounds
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:17:01.300859+00:00
-- url     : https://prove2.me/submissions/538b32f2-1280-4471-86db-47da44f2b34c

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticErrorDerivative
import Definitions.Def_DerivativeChainPrivate_SixthSepticInverse
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_normalized_sixth_octic_step
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_selected_bounds
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


theorem solution (β w : ℂ) (hR : 0≤β.re) (hI : 0<β.im)
    (hwpos : 0<w.re) (hwim : 0<w.im) (hwX : 4≤w.re^2)
    (hwroot : (1360/13)*β^2*w-35*β*w^4+85*β*w^2-(1445/78)*β+
      w^7-7*w^5+(595/48)*w^3-(1445/312)*w=0)
    (hwinv : β/w=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*w^2-
      ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder w/w) :
    ∃ z : ℂ,
      (5440/13)*β^2*z^2-(92480/429)*β^2-56*β*z^5+(680/3)*β*z^3-(5780/39)*β*z+
        z^8-(28/3)*z^6+(595/24)*z^4-(1445/78)*z^2+24565/13728=0 ∧
      w.re≤z.re ∧ w.im≤z.im ∧ 0<z.im ∧ 26/5<z.re^2 ∧
      β/z=(((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*z^2-
        ((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder z/z ∧
      (sixthOcticRemainder z).re/z.re≤9/1000 ∧ (sixthOcticRemainder z).im/z.im≤0 ∧
      (3*((sixthOcticRemainder z).re/z.re)-(sixthOcticRemainder z).im/z.im)/2≤73/4000 ∧
      26/5≤z.re^2-3*z.im^2 := by
  obtain ⟨z,hz,hr,hi,hgraph⟩:=normalized_sixth_octic_step β w hR hI hwpos hwim hwX hwroot hwinv
  have hx : 0<z.re := lt_of_lt_of_le hwpos hr
  have hy : 0<z.im := lt_of_lt_of_le hwim hi
  have hX : 4≤z.re^2 := by nlinarith only [hwX,hwpos,hr]
  obtain ⟨hloc,hA,hB,hC,hW⟩:=sixth_octic_selected_bounds β z hR hx hy hX hgraph
  exact ⟨z,hz,hr,hi,hy,hloc,hgraph,hA,hB,hC,hW⟩
