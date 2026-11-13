-- Prove2me | solution 1 for CountingLLL.RandomRAM.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:58:49.68372+00:00
-- url     : https://prove2.me/submissions/535abc7e-a7d4-4fad-ac5f-6b8c3d15ec83

import Theorems.Thm_CountingLLL_RandomRAM_reciprocal_stopping
import Theorems.Thm_CountingLLL_RandomRAM_reciprocal_expected_cost
import Theorems.Thm_CountingLLL_RandomRAM_reciprocal_output_mean
import Theorems.Thm_CountingLLL_RandomRAM_reciprocal_second_moment

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- All conclusions of #442 Lemma 5.4, with each draw's cost allowed to depend on its value. -/
theorem solution {β : Type} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    (Y : β → ℝ) (K : β → ℝ≥0∞) (hY : Measurable Y) (hK : Measurable K)
    (hY2 : MemLp Y 2 ν)
    (hr0 : 0 ≤ ∫ x, Y x ∂ν) (hr1 : (∫ x, Y x ∂ν) < 1)
    (hM : (∫ x, (Y x)^2 ∂ν) < 1) (hτ : ν {x | Y x ≠ 0} < 1) :
    let μ : Measure (ℕ → β) := Measure.infinitePi fun _ : ℕ => ν
    let r : ℝ := ∫ x, Y x ∂ν
    let M : ℝ := ∫ x, (Y x)^2 ∂ν
    let τ : ℝ≥0∞ := ν {x | Y x ≠ 0}
    let W : (ℕ → β) → ℝ := fun ω => ∑' n : ℕ, ∏ k ∈ Finset.range n, Y (ω k)
    let S : ℕ → Set (ℕ → β) := fun n => {ω | ∀ i < n, Y (ω i) ≠ 0}
    (∀ᵐ ω ∂μ, ∃ k, Y (ω k) = 0) ∧
    (∀ (ω : ℕ → β) (k : ℕ), Y (ω k) = 0 →
      W ω = ∑ n ∈ Finset.range (k+1), ∏ j ∈ Finset.range n, Y (ω j)) ∧
    Integrable W μ ∧ (∫ ω, W ω ∂μ) = (1-r)⁻¹ ∧
    Integrable (fun ω => (W ω)^2) μ ∧
    (∫ ω, (W ω)^2 ∂μ) = (1+r)/((1-r)*(1-M)) ∧
    (∫⁻ ω, ∑' n : ℕ, (S n).indicator (1 : (ℕ → β) → ℝ≥0∞) ω ∂μ) = (1-τ)⁻¹ ∧
    (∫⁻ ω, ∑' n : ℕ, (S n).indicator (fun ω => K (ω n)) ω ∂μ) =
      (∫⁻ x, K x ∂ν) / (1-τ) := by
  dsimp only
  let ρ : Measure ℝ := ν.map Y
  letI : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hY.aemeasurable
  let μ : Measure (ℕ → β) := Measure.infinitePi fun _ : ℕ => ν
  let rhoInf : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => ρ
  let T : (ℕ → β) → (ℕ → ℝ) := fun ω k => Y (ω k)
  let W : (ℕ → ℝ) → ℝ := fun ω => ∑' n : ℕ, ∏ k ∈ Finset.range n, ω k
  let S : Set β := {x | Y x ≠ 0}
  have hS : MeasurableSet S := (measurableSet_singleton 0).compl.preimage hY
  have hT : Measurable T := measurable_pi_lambda _ (fun k => hY.comp (measurable_pi_apply k))
  have hmap : μ.map T = rhoInf :=
    Measure.infinitePi_map_pi (fun _ : ℕ => ν) (f := fun _ => Y) (fun _ => hY)
  have hρ2 : MemLp (fun x : ℝ => x) 2 ρ := by
    apply (memLp_map_measure_iff aestronglyMeasurable_id hY.aemeasurable).2
    exact hY2
  have hρmean : (∫ x, x ∂ρ) = ∫ x, Y x ∂ν := by
    change (∫ x, (id : ℝ → ℝ) x ∂(ν.map Y)) = _
    rw [integral_map hY.aemeasurable aestronglyMeasurable_id]
    rfl
  have hρsquare : (∫ x, x^2 ∂ρ) = ∫ x, (Y x)^2 ∂ν := by
    rw [show ρ = ν.map Y from rfl, integral_map hY.aemeasurable (by fun_prop)]
  have hρτ : ρ {x | x ≠ 0} = ν S := by
    change (ν.map Y) ({0} : Set ℝ)ᶜ = ν S
    rw [Measure.map_apply hY (measurableSet_singleton 0).compl]
    rfl
  have hρr0 : 0 ≤ ∫ x, x ∂ρ := by rw [hρmean]; exact hr0
  have hρr1 : (∫ x, x ∂ρ) < 1 := by rw [hρmean]; exact hr1
  have hρM : (∫ x, x^2 ∂ρ) < 1 := by rw [hρsquare]; exact hM
  have hρτ1 : ρ {x | x ≠ 0} < 1 := by rw [hρτ]; exact hτ
  have hstop := CountingLLL.RandomRAM.reciprocal_stopping ρ
  have hfirst := CountingLLL.RandomRAM.reciprocal_output_mean ρ hρ2 hρr0 hρr1 hρM
  simp only [Fin.prod_univ_eq_prod_range] at hfirst
  have hsecond := CountingLLL.RandomRAM.reciprocal_second_moment ρ hρ2 hρr0 hρr1 hρM hρτ1
  have hWmeas : Measurable W := by
    apply Measurable.tsum
    intro n
    fun_prop
  have hhit_meas : MeasurableSet {ω : ℕ → ℝ | ∃ k, ω k = 0} := by
    have heq : {ω : ℕ → ℝ | ∃ k, ω k = 0} = ⋃ k : ℕ, {ω | ω k = 0} := by ext ω; simp
    rw [heq]
    exact MeasurableSet.iUnion fun k => (measurableSet_singleton 0).preimage (measurable_pi_apply k)
  have hhit : ∀ᵐ ω ∂μ, ∃ k, Y (ω k) = 0 := by
    have hh := hstop.2.1 hρτ1
    change (∀ᵐ ω ∂rhoInf, ∃ n, ω n = 0) at hh
    rw [← hmap] at hh
    exact (ae_map_iff hT.aemeasurable hhit_meas).1 hh
  have hWint : Integrable (W ∘ T) μ := by
    have hh := hfirst.1
    change Integrable W rhoInf at hh
    rw [← hmap] at hh
    exact hh.comp_measurable hT
  have hW2int : Integrable (fun ω => (W (T ω))^2) μ := by
    have hh := hsecond.1
    change Integrable (fun ω => (W ω)^2) rhoInf at hh
    rw [← hmap] at hh
    exact hh.comp_measurable hT
  have hWmean : (∫ ω, W (T ω) ∂μ) = (1 - ∫ x, Y x ∂ν)⁻¹ := by
    have hmapInt := integral_map (μ := μ) (φ := T) (f := W) hT.aemeasurable hWmeas.aestronglyMeasurable
    rw [hmap] at hmapInt
    rw [← hmapInt]
    change (∫ ω, W ω ∂rhoInf) = _
    exact hfirst.2.1.trans (by rw [hρmean])
  have hW2mean : (∫ ω, (W (T ω))^2 ∂μ) =
      (1 + ∫ x, Y x ∂ν) / ((1 - ∫ x, Y x ∂ν) * (1 - ∫ x, (Y x)^2 ∂ν)) := by
    have hmapInt := integral_map (μ := μ) (φ := T) (f := fun ω => (W ω)^2)
      hT.aemeasurable (hWmeas.pow_const 2).aestronglyMeasurable
    rw [hmap] at hmapInt
    rw [← hmapInt, hsecond.2, hρmean, hρsquare]
  have hcount := CountingLLL.RandomRAM.reciprocal_expected_cost ν S hS (fun _ => 1) measurable_const
  have hcost := CountingLLL.RandomRAM.reciprocal_expected_cost ν S hS K hK
  have hcount' : (∫⁻ ω, ∑' n : ℕ,
      ({ω' : ℕ → β | ∀ i < n, Y (ω' i) ≠ 0}).indicator (1 : (ℕ → β) → ℝ≥0∞) ω ∂μ) =
      (1 - ν S)⁻¹ := by
    simpa [S, μ, lintegral_const, Pi.one_def] using hcount
  have hcost' : (∫⁻ ω, ∑' n : ℕ,
      ({ω' : ℕ → β | ∀ i < n, Y (ω' i) ≠ 0}).indicator (fun ω => K (ω n)) ω ∂μ) =
      (∫⁻ x, K x ∂ν) / (1 - ν S) := by
    simpa [S, μ] using hcost
  refine ⟨hhit, ?_, ?_, hWmean, hW2int, hW2mean, hcount', hcost'⟩
  · intro ω k hk
    exact hfirst.2.2 (T ω) k hk
  · exact hWint
