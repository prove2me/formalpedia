-- Prove2me | solution 1 for CountingLLL.RandomRAM.reciprocal_output_mean
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:40:02.922899+00:00
-- url     : https://prove2.me/submissions/cc9f4f76-8e78-44fa-bd91-00061c433258

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ResearchReciprocalMean

noncomputable def prefixProduct (n : ℕ) (ω : ℕ → ℝ) : ℝ := ∏ j : Fin n, ω j.val

noncomputable def output (ω : ℕ → ℝ) : ℝ := ∑' n, prefixProduct n ω

private theorem finite_product_facts (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun x : ℝ => x) ν) (n : ℕ) :
    Integrable (prefixProduct n) (Measure.infinitePi fun _ : ℕ => ν) ∧
    (∫ ω, prefixProduct n ω ∂(Measure.infinitePi fun _ : ℕ => ν)) = (∫ x, x ∂ν) ^ n ∧
    (∫ ω, ‖prefixProduct n ω‖ ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      (∫ x, ‖x‖ ∂ν) ^ n := by
  let μ : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => ν
  have hm : ∀ j : Fin n, Measurable (fun ω : ℕ → ℝ => ω j.val) :=
    fun j => measurable_pi_apply j.val
  have hind : iIndepFun (fun (j : Fin n) (ω : ℕ → ℝ) => ω j.val) μ := by
    have hall : iIndepFun (fun (j : ℕ) (ω : ℕ → ℝ) => ω j) μ :=
      iIndepFun_infinitePi (fun _ => measurable_id)
    exact hall.precomp Fin.val_injective
  have heval : ∀ j : Fin n, μ.map (fun ω => ω j.val) = ν := by
    intro j
    exact Measure.infinitePi_map_eval (fun _ : ℕ => ν) j.val
  have hvec : AEMeasurable (fun (ω : ℕ → ℝ) (j : Fin n) => ω j.val) μ :=
    aemeasurable_pi_iff.mpr (fun j => (hm j).aemeasurable)
  have hmap : μ.map (fun (ω : ℕ → ℝ) (j : Fin n) => ω j.val) =
      Measure.pi (fun _ : Fin n => ν) := by
    rw [hind.map_fun_eq_pi_map (fun j => (hm j).aemeasurable)]
    simp_rw [heval]
  have hprod : Integrable (fun x : Fin n → ℝ => ∏ j, x j)
      (Measure.pi (fun _ : Fin n => ν)) := Integrable.fintype_prod (fun _ => hν)
  rw [← hmap] at hprod
  have h_integrable : Integrable (prefixProduct n) μ := by
    change Integrable (fun ω : ℕ → ℝ => ∏ j : Fin n, ω j.val) μ
    exact hprod.comp_aemeasurable hvec
  have hmean : (∫ ω, prefixProduct n ω ∂μ) = (∫ x, x ∂ν) ^ n := by
    have h := hind.integral_fun_prod_eq_prod_integral (fun j => (hm j).aestronglyMeasurable)
    have hcoord : ∀ j : Fin n, (∫ ω, ω j.val ∂μ) = ∫ x, x ∂ν := by
      intro j
      change (∫ ω, (id : ℝ → ℝ) (ω j.val) ∂μ) = ∫ x, x ∂ν
      rw [← integral_map (hm j).aemeasurable aestronglyMeasurable_id, heval]
      rfl
    simp only [prefixProduct, hcoord, Finset.prod_const, Finset.card_fin] at h ⊢
    exact h
  have habs : (∫ ω, ‖prefixProduct n ω‖ ∂μ) = (∫ x, ‖x‖ ∂ν) ^ n := by
    have h := hind.integral_fun_prod_comp (f := fun (_ : Fin n) x => ‖x‖)
      (fun j => (hm j).aemeasurable) (fun _ => by fun_prop)
    have hcoord : ∀ j : Fin n, (∫ ω, ‖ω j.val‖ ∂μ) = ∫ x, ‖x‖ ∂ν := by
      intro j
      rw [← integral_map (hm j).aemeasurable (by fun_prop), heval]
    simp only [← norm_prod, prefixProduct, hcoord, Finset.prod_const, Finset.card_fin] at h ⊢
    exact h
  exact ⟨h_integrable, hmean, habs⟩

/-- The reciprocal output has the correct mean under the paper's moment assumptions. -/
theorem output_mean (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : MemLp (fun x : ℝ => x) 2 ν)
    (hr0 : 0 ≤ ∫ x, x ∂ν) (hr1 : (∫ x, x ∂ν) < 1)
    (hM : (∫ x, x ^ 2 ∂ν) < 1) :
    Integrable output (Measure.infinitePi fun _ : ℕ => ν) ∧
    (∫ ω, output ω ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      (1 - ∫ x, x ∂ν)⁻¹ := by
  let μ : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => ν
  let q : ℝ := ∫ x, ‖x‖ ∂ν
  have hq0 : 0 ≤ q := integral_nonneg fun x => norm_nonneg _
  have hqvar := variance_nonneg (fun x : ℝ => ‖x‖) ν
  rw [variance_eq_sub hν.norm] at hqvar
  simp only [Pi.pow_apply, Real.norm_eq_abs, sq_abs] at hqvar
  have hq1 : q < 1 := by
    dsimp [q]
    dsimp [q] at hq0
    nlinarith
  have hνint : Integrable (fun x : ℝ => x) ν := hν.integrable (by norm_num)
  have hsum : Summable (fun n => ∫ ω, ‖prefixProduct n ω‖ ∂μ) := by
    have heq : (fun n => ∫ ω, ‖prefixProduct n ω‖ ∂μ) = (fun n => q ^ n) := by
      funext n
      exact (finite_product_facts ν hνint n).2.2
    rw [heq]
    exact summable_geometric_of_lt_one hq0 hq1
  have hexp : (∫ ω, output ω ∂μ) = (1 - ∫ x, x ∂ν)⁻¹ := by
    unfold output
    rw [← integral_tsum_of_summable_integral_norm (fun n => (finite_product_facts ν hνint n).1) hsum]
    have heq : (fun n => ∫ ω, prefixProduct n ω ∂μ) =
        (fun n => (∫ x, x ∂ν) ^ n) := by
      funext n
      exact (finite_product_facts ν hνint n).2.1
    rw [heq]
    exact tsum_geometric_of_lt_one hr0 hr1
  have hint : Integrable output μ := by
    by_contra hnot
    have hzero := integral_undef hnot
    have hpos : 0 < (1 - ∫ x, x ∂ν)⁻¹ := inv_pos.mpr (by linarith)
    linarith
  exact ⟨hint, hexp⟩

/-- Once a zero is observed, every later prefix product vanishes. -/
theorem output_eq_finite (ω : ℕ → ℝ) (k : ℕ) (hzero : ω k = 0) :
    output ω = ∑ n ∈ Finset.range (k + 1), prefixProduct n ω := by
  classical
  unfold output
  apply tsum_eq_sum
  intro n hn
  have hk : k < n := by simpa using hn
  unfold prefixProduct
  apply Finset.prod_eq_zero (i := ⟨k, hk⟩) (Finset.mem_univ _)
  exact hzero

end ResearchReciprocalMean

open ResearchReciprocalMean

theorem solution (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : MemLp (fun x : ℝ => x) 2 ν)
    (hr0 : 0 ≤ ∫ x, x ∂ν) (hr1 : (∫ x, x ∂ν) < 1)
    (hM : (∫ x, x ^ 2 ∂ν) < 1) :
    let W : (ℕ → ℝ) → ℝ := fun ω => ∑' n : ℕ, ∏ j : Fin n, ω j.val
    Integrable W (Measure.infinitePi fun _ : ℕ => ν) ∧
    (∫ ω, W ω ∂(Measure.infinitePi fun _ : ℕ => ν)) = (1 - ∫ x, x ∂ν)⁻¹ ∧
    (∀ (ω : ℕ → ℝ) (k : ℕ), ω k = 0 →
      W ω = ∑ n ∈ Finset.range (k + 1), ∏ j : Fin n, ω j.val) := by
  exact ⟨(output_mean ν hν hr0 hr1 hM).1,
    (output_mean ν hν hr0 hr1 hM).2, output_eq_finite⟩
