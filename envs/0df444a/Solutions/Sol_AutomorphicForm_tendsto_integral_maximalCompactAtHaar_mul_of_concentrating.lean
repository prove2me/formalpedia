-- Prove2me | solution 1 for AutomorphicForm.tendsto_integral_maximalCompactAtHaar_mul_of_concentrating
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/fee84040-af2f-598e-a7bb-44c8600b2c2f

import Mathlib
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_tendsto_integral_maximalCompactAtHaar_mul_of_concentrating

set_option autoImplicit false

set_option maxHeartbeats 1600000

noncomputable section

namespace Ws23
namespace Pointwise

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

variable {K : Type} [Field K] [NumberField K]

abbrev Kc (K : Type) [Field K] [NumberField K] : Type := ↥(maximalCompactAt K ∅)
abbrev μK (K : Type) [Field K] [NumberField K] : Measure (Kc K) := maximalCompactAtHaar K ∅

theorem integral_ofReal_eq {κ : Kc K → ℝ} (hκc : Continuous κ) : ∫ k, (κ k : ℂ) ∂(μK K) = ((∫ k, κ k ∂(μK K) : ℝ) : ℂ) := by
  have hint : Integrable κ (μK K) := hκc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have := Complex.ofRealCLM.integral_comp_comm hint
  simpa only [Complex.ofRealCLM_apply] using this

theorem main
    (κ : ℕ → Kc K → ℝ)
    (hκc : ∀ n, Continuous (κ n)) (hκ0 : ∀ n k, 0 ≤ κ n k) (hκ1 : ∀ n, ∫ k, κ n k ∂(μK K) = 1)
    (hκU : ∀ U ∈ nhds (1 : Kc K),
      Filter.Tendsto (fun n => ∫ k in Uᶜ, κ n k ∂(μK K)) Filter.atTop (nhds 0))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (x : AdelicGL2 (𝓞 K) K) :
    Filter.Tendsto (fun n => ∫ k, (κ n k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(μK K)) Filter.atTop
      (nhds (f x)) := by

  set g : Kc K → ℂ := fun k => f (x * (k : AdelicGL2 (𝓞 K) K)) with hg
  have hgc : Continuous g := hf.comp ((continuous_const_mul x).comp continuous_subtype_val)
  have hg1 : g 1 = f x := by simp [hg]
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ k, ‖g k‖ ≤ M := by
    refine ⟨sSup (Set.range fun k => ‖g k‖) + 1, ?_, fun k => ?_⟩
    · have : 0 ≤ sSup (Set.range fun k => ‖g k‖) :=
        Real.sSup_nonneg (by rintro _ ⟨k, rfl⟩; exact norm_nonneg _)
      linarith
    · exact (le_csSup ((isCompact_range hgc.norm).bddAbove) (Set.mem_range_self k)).trans (le_add_of_nonneg_right zero_le_one)
  rw [Metric.tendsto_atTop]
  intro ε hε

  set U : Set (Kc K) := {k | dist (g k) (g 1) < ε / 2} with hU
  have hUo : IsOpen U := isOpen_lt (hgc.dist continuous_const) continuous_const
  have hU1 : U ∈ nhds (1 : Kc K) := hUo.mem_nhds (by show dist (g 1) (g 1) < ε / 2; rw [dist_self]; exact half_pos hε)
  have hUm : MeasurableSet U := hUo.measurableSet

  have htail := hκU U hU1
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨N, hN⟩ := htail (ε / (4 * M)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hκint : Integrable (κ n) (μK K) := (hκc n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hκgint : Integrable (fun k => (κ n k : ℂ) * (g k - g 1)) (μK K) :=
    ((Complex.continuous_ofReal.comp (hκc n)).mul (hgc.sub continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

  have hA : Integrable (fun k => (κ n k : ℂ) * g k) (μK K) :=
    ((Complex.continuous_ofReal.comp (hκc n)).mul hgc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hB : Integrable (fun k => (κ n k : ℂ) * g 1) (μK K) :=
    ((Complex.continuous_ofReal.comp (hκc n)).mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hdiff : ∫ k, (κ n k : ℂ) * g k ∂(μK K) - f x = ∫ k, (κ n k : ℂ) * (g k - g 1) ∂(μK K) := by
    have h1 : ∫ k, (κ n k : ℂ) * g 1 ∂(μK K) = g 1 := by
      rw [integral_mul_const, integral_ofReal_eq (hκc n), hκ1 n, Complex.ofReal_one, one_mul]
    have e : (fun k => (κ n k : ℂ) * (g k - g 1)) = fun k => (κ n k : ℂ) * g k - (κ n k : ℂ) * g 1 := by
      funext k; ring
    rw [e, integral_sub hA hB, h1, hg1]
  rw [dist_eq_norm]
  show ‖∫ k, (κ n k : ℂ) * g k ∂(μK K) - f x‖ < ε
  rw [hdiff, ← integral_add_compl hUm hκgint]

  have hin : ‖∫ k in U, (κ n k : ℂ) * (g k - g 1) ∂(μK K)‖ ≤ ε / 2 := by
    have hb : ∀ᵐ k ∂((μK K).restrict U), ‖(κ n k : ℂ) * (g k - g 1)‖ ≤ κ n k * (ε / 2) := by
      rw [ae_restrict_iff' hUm]
      refine Filter.Eventually.of_forall fun k hk => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hκ0 n k), ← dist_eq_norm]
      exact mul_le_mul_of_nonneg_left (le_of_lt hk) (hκ0 n k)
    refine (norm_integral_le_of_norm_le (hκint.integrableOn.mul_const _) hb).trans ?_
    rw [integral_mul_const]
    have : ∫ k in U, κ n k ∂(μK K) ≤ 1 := by
      rw [← hκ1 n]
      exact setIntegral_le_integral hκint (Filter.Eventually.of_forall (hκ0 n))
    nlinarith

  have hout : ‖∫ k in Uᶜ, (κ n k : ℂ) * (g k - g 1) ∂(μK K)‖ < ε / 2 := by
    have hb : ∀ᵐ k ∂((μK K).restrict Uᶜ), ‖(κ n k : ℂ) * (g k - g 1)‖ ≤ κ n k * (2 * M) := by
      refine Filter.Eventually.of_forall fun k => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hκ0 n k)]
      refine mul_le_mul_of_nonneg_left ?_ (hκ0 n k)
      exact (norm_sub_le _ _).trans (by linarith [hM k, hM 1])
    refine (norm_integral_le_of_norm_le (hκint.integrableOn.mul_const _) hb).trans_lt ?_
    rw [integral_mul_const]
    have htl := hN n hn
    rw [Real.dist_eq, sub_zero] at htl
    have h0 : 0 ≤ ∫ k in Uᶜ, κ n k ∂(μK K) := setIntegral_nonneg hUm.compl fun k _ => hκ0 n k
    rw [abs_of_nonneg h0] at htl
    calc (∫ k in Uᶜ, κ n k ∂(μK K)) * (2 * M) < ε / (4 * M) * (2 * M) := mul_lt_mul_of_pos_right htl (by positivity)
      _ = ε / 2 := by field_simp; ring
  calc ‖∫ k in U, (κ n k : ℂ) * (g k - g 1) ∂(μK K) + ∫ k in Uᶜ, (κ n k : ℂ) * (g k - g 1) ∂(μK K)‖
      ≤ ‖∫ k in U, (κ n k : ℂ) * (g k - g 1) ∂(μK K)‖ + ‖∫ k in Uᶜ, (κ n k : ℂ) * (g k - g 1) ∂(μK K)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hin hout
    _ = ε := by ring

end Ws23.Pointwise

end

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    (κ : ℕ → ↥(maximalCompactAt K ∅) → ℝ)
    (hκc : ∀ n, Continuous (κ n)) (hκ0 : ∀ n k, 0 ≤ κ n k) (hκ1 : ∀ n, ∫ k, κ n k ∂(maximalCompactAtHaar K ∅) = 1)
    (hκU : ∀ U ∈ nhds (1 : ↥(maximalCompactAt K ∅)),
      Filter.Tendsto (fun n => ∫ k in Uᶜ, κ n k ∂(maximalCompactAtHaar K ∅)) Filter.atTop (nhds 0))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (x : AdelicGL2 (𝓞 K) K) :
    Filter.Tendsto (fun n => ∫ k, (κ n k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactAtHaar K ∅)) Filter.atTop
      (nhds (f x)) :=
  Ws23.Pointwise.main κ hκc hκ0 hκ1 hκU f hf x

end S_AutomorphicForm_tendsto_integral_maximalCompactAtHaar_mul_of_concentrating
end P2MW
export P2MW.S_AutomorphicForm_tendsto_integral_maximalCompactAtHaar_mul_of_concentrating (solution)
