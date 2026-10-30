-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_sixth_selected_septic_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:11:51.876566+00:00
-- url     : https://prove2.me/submissions/b2c75691-1353-456f-b20b-2bc751fbc25f

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticInverse
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Theorems.Thm_DerivativeChainPrivate_normalized_sixth_septic_step
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_selected_bounds
import Theorems.Thm_DerivativeChainPrivate_sixth_sextic_correction_bounds
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ,t∈Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ u : ℂ, 0<u.im → sexticShift (-85/43) (1445/1806) (24565/211302) u=
      TeschlQM.Herglotz.borelTransform μ u)
    (β w : ℂ) (hR : 0≤β.re) (hI : 0<β.im)
    (hwpos : 0<w.re) (hwim : 0<w.im) (hwX : 7/2≤w.re^2)
    (hwroot : (1360/91)*β^2-20*β*w^3+(170/7)*β*w+w^6-5*w^4+(85/16)*w^2-1445/2184=0)
    (hwinv : β/w=(((455-3*Real.sqrt 19565)/680:ℝ):ℂ)*w^2-
      (((559-3*Real.sqrt 19565)/688:ℝ):ℂ)+
      ((3*Real.sqrt 19565/680:ℝ):ℂ)*(∫ t : ℝ,(w^2-(t:ℂ))⁻¹ ∂μ)) :
    ∃ z : ℂ,
      (1360/13)*β^2*z-35*β*z^4+85*β*z^2-(1445/78)*β+
        z^7-7*z^5+(595/48)*z^3-(1445/312)*z=0 ∧
      w.re≤z.re ∧ w.im≤z.im ∧ 0<z.im ∧ 4<z.re^2 ∧
      β/z=(((455-3*Real.sqrt 15145)/2720:ℝ):ℂ)*z^2-
        ((13/32-77*Real.sqrt 15145/37280:ℝ):ℂ)+sixthSepticRemainder z/z ∧
      (sixthSepticRemainder z).re/z.re≤39/2000 ∧ (sixthSepticRemainder z).im/z.im≤0 ∧
      (3*((sixthSepticRemainder z).re/z.re)-(sixthSepticRemainder z).im/z.im)/2≤39/1000 ∧
      4≤z.re^2-3*z.im^2 := by
  let E₀:=((3*Real.sqrt 19565/680:ℝ):ℂ)*(w*(∫ t : ℝ,(w^2-(t:ℂ))⁻¹ ∂μ))
  have hw : w≠0 := by intro he; simp [he] at hwpos
  have hg : β/w=(((455-3*Real.sqrt 19565)/680:ℝ):ℂ)*w^2-
      (((559-3*Real.sqrt 19565)/688:ℝ):ℂ)+E₀/w := by
    convert hwinv using 1
    dsimp [E₀]
    field_simp
  obtain ⟨_,hA,hB,_,hC⟩:=sixth_sextic_correction_bounds μ hsupp hμ w hwpos hwim hwX
  change E₀.re/w.re≤29/1600 at hA
  change E₀.im/w.im≤0 at hB
  change (3*(E₀.re/w.re)-E₀.im/w.im)/2≤319/6400 at hC
  obtain ⟨z,hz,hr,hi,hgraph⟩:=normalized_sixth_septic_step β w E₀ hR hI hwpos hwim hwX hwroot hg hA hB (by linarith)
  have hx : 0<z.re := lt_of_lt_of_le hwpos hr
  have hy : 0<z.im := lt_of_lt_of_le hwim hi
  have hX : 7/2≤z.re^2 := by nlinarith only [hwX,hwpos,hr]
  obtain ⟨hloc,hAz,hBz,hCz,hW⟩:=sixth_septic_selected_bounds β z hR hx hy hX hgraph
  exact ⟨z,hz,hr,hi,hy,hloc,hgraph,hAz,hBz,hCz,hW⟩
