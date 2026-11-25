-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_dil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:13:22.635869+00:00
-- url     : https://prove2.me/submissions/ead2a3de-e121-41b5-8507-7a03599f6854

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_integral_norm_dil_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_memLp_dil
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_integrable_sq_of_memLp
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_dil_cpt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (f : ℂ → E) (hf : MemLp f 2 volume) (ζ : ℂ) (hζ : ζ ≠ 0) :
    Tendsto (fun ρ : ℂ => ∫ z, ‖‖ρ‖ • f (ρ * z) - ‖ζ‖ • f (ζ * z)‖ ^ 2) (𝓝 ζ) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hf' : MemLp f (ENNReal.ofReal 2) volume := by simpa using hf
  obtain ⟨g, hgs, hfg, hgc, hgm⟩ :=
    hf'.exists_hasCompactSupport_integral_rpow_sub_le two_pos (ε := ε / 12) (by positivity)
  have hfg' : ∫ z, ‖f z - g z‖ ^ 2 ≤ ε / 12 := by
    have e : (fun z => ‖f z - g z‖ ^ (2 : ℝ)) = fun z => ‖f z - g z‖ ^ 2 := by
      funext z
      exact Real.rpow_two _
    rw [e] at hfg
    exact hfg
  have hgm2 : MemLp g 2 volume := by simpa using hgm
  have hT := tendsto_dil_cpt g hgc hgs ζ hζ
  rw [Metric.tendsto_nhds] at hT
  filter_upwards [hT (ε / 6) (by positivity), eventually_ne_nhds hζ] with ρ hρT hρ0
  have hnn : ∀ (h : ℂ → ℝ), 0 ≤ ∫ z, ‖h z‖ ^ 2 := fun h => integral_nonneg fun _ => by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => by positivity)] at hρT ⊢
  have h3 : ∀ a b c : E, ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
    intro a b c
    have h1 := norm_add₃_le (a := a) (b := b) (c := c)
    have h2 : ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖a‖ - ‖c‖)]
  have hdfg : MemLp (fun z => f z - g z) 2 volume := hf.sub hgm2
  have hdgf : MemLp (fun z => g z - f z) 2 volume := hgm2.sub hf
  have iA := integrable_sq_of_memLp (memLp_dil hdfg ρ hρ0)
  have iB := integrable_sq_of_memLp ((memLp_dil hgm2 ρ hρ0).sub (memLp_dil hgm2 ζ hζ))
  have iC := integrable_sq_of_memLp (memLp_dil hdgf ζ hζ)
  have iL := integrable_sq_of_memLp ((memLp_dil hf ρ hρ0).sub (memLp_dil hf ζ hζ))
  have hA := integral_norm_dil_sq (fun w => f w - g w) ρ hρ0
  have hC := integral_norm_dil_sq (fun w => g w - f w) ζ hζ
  have hgf : ∫ z, ‖g z - f z‖ ^ 2 = ∫ z, ‖f z - g z‖ ^ 2 := by
    congr 1
    funext z
    rw [norm_sub_rev]
  have hmono : ∫ z, ‖‖ρ‖ • f (ρ * z) - ‖ζ‖ • f (ζ * z)‖ ^ 2 ≤
      ∫ z, 3 * (‖‖ρ‖ • (f (ρ * z) - g (ρ * z))‖ ^ 2 +
        ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2 + ‖‖ζ‖ • (g (ζ * z) - f (ζ * z))‖ ^ 2) := by
    refine integral_mono iL (((iA.add iB).add iC).const_mul 3) fun z => ?_
    have e : ‖ρ‖ • f (ρ * z) - ‖ζ‖ • f (ζ * z) = ‖ρ‖ • (f (ρ * z) - g (ρ * z)) +
        (‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)) + ‖ζ‖ • (g (ζ * z) - f (ζ * z)) := by
      rw [smul_sub, smul_sub]
      abel
    simp only
    rw [e]
    exact h3 _ _ _
  have hs1 : ∫ z, (‖‖ρ‖ • (f (ρ * z) - g (ρ * z))‖ ^ 2 +
        ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2 + ‖‖ζ‖ • (g (ζ * z) - f (ζ * z))‖ ^ 2) =
      (∫ z, (‖‖ρ‖ • (f (ρ * z) - g (ρ * z))‖ ^ 2 + ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2)) +
        ∫ z, ‖‖ζ‖ • (g (ζ * z) - f (ζ * z))‖ ^ 2 :=
    integral_add (iA.add iB) iC
  have hs2 : ∫ z, (‖‖ρ‖ • (f (ρ * z) - g (ρ * z))‖ ^ 2 + ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2) =
      (∫ z, ‖‖ρ‖ • (f (ρ * z) - g (ρ * z))‖ ^ 2) + ∫ z, ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2 :=
    integral_add iA iB
  rw [integral_const_mul, hs1, hs2] at hmono
  rw [hA, hC, hgf] at hmono
  linarith
end Formalism.FourierDecayAlt.P.PBK
