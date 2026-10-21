-- Prove2me | solution 1 for CorreaThreshold.Nonadaptive.expected_max_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:01:36.613435+00:00
-- url     : https://prove2.me/submissions/b26344e2-bedd-44c9-aff5-b3841e7b2694

import Mathlib
import Definitions.Def_CorreaThreshold_Nonadaptive_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

lemma tie_null {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P)
    (hcont : ∀ i, ∀ x : ℝ, P {ω | X i ω = x} = 0)
    (i j : Fin n) (hij : i ≠ j) : P {ω | X i ω = X j ω} = 0 := by
  have hI : IndepFun (X i) (X j) P := hind.indepFun hij
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map (hXm i).aemeasurable (hXm j).aemeasurable).1 hI
  have hdiag : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} := measurableSet_eq_fun measurable_fst measurable_snd
  have hpm : Measurable (fun ω => (X i ω, X j ω)) := (hXm i).prodMk (hXm j)
  have h1 : P {ω | X i ω = X j ω} = (P.map (fun ω => (X i ω, X j ω))) {p : ℝ × ℝ | p.1 = p.2} := by
    rw [Measure.map_apply hpm hdiag]
    rfl
  rw [h1, hmap, Measure.prod_apply hdiag]
  have : ∀ x : ℝ, (P.map (X j)) (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0 := by
    intro x
    have hs : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} := by
      ext y; simp [eq_comm]
    rw [hs, Measure.map_apply (hXm j) (measurableSet_singleton x)]
    have := hcont j x
    simpa [Set.preimage] using this
  have hz : (fun x : ℝ => (P.map (X j)) (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2})) = fun _ => 0 := funext this
  rw [hz]
  exact lintegral_zero

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} [NeZero n]
    (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω)
    (hind : iIndepFun X P)
    (hcont : ∀ i, ∀ x : ℝ, P {ω | X i ω = x} = 0) :
    (∫⁻ ω, ENNReal.ofReal (SamuelCahnProphet.Median.maxX X ω) ∂P) =
      ∑ i : Fin n, ∫⁻ ω,
        (if ∀ j, X j ω ≤ X i ω then ENNReal.ofReal (X i ω) else 0) ∂P := by
  classical
  have hae : ∀ᵐ ω ∂P, ∀ i j : Fin n, i ≠ j → X i ω ≠ X j ω := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun ω h => absurd hij h)
    · have h0 := tie_null P X hXm hind hcont i j hij
      rw [ae_iff]
      have : {ω | ¬ (i ≠ j → X i ω ≠ X j ω)} = {ω | X i ω = X j ω} := by
        ext ω; simp [hij]
      rw [this]; exact h0
  have hmeas : ∀ i : Fin n, Measurable (fun ω => if ∀ j, X j ω ≤ X i ω then ENNReal.ofReal (X i ω) else 0) := by
    intro i
    have hA : MeasurableSet {ω | ∀ j, X j ω ≤ X i ω} := by
      have : {ω | ∀ j, X j ω ≤ X i ω} = ⋂ j, {ω | X j ω ≤ X i ω} := by
        ext ω; simp
      rw [this]
      exact MeasurableSet.iInter fun j => measurableSet_le (hXm j) (hXm i)
    exact Measurable.ite hA (hXm i).ennreal_ofReal measurable_const
  rw [← lintegral_finset_sum _ (fun i _ => hmeas i)]
  apply lintegral_congr_ae
  filter_upwards [hae] with ω hω
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty) (fun i => X i ω)
  have hmax : SamuelCahnProphet.Median.maxX X ω = X i0 ω := hi0
  have hle : ∀ j, X j ω ≤ X i0 ω := by
    intro j
    rw [← hmax]
    exact Finset.le_sup' (fun i => X i ω) (Finset.mem_univ j)
  rw [hmax, Finset.sum_eq_single i0]
  · rw [if_pos hle]
  · intro i _ hne
    rw [if_neg]
    intro hall
    have h1 := hall i0
    have h2 := hle i
    exact hω i i0 hne (le_antisymm h2 h1)
  · intro h; exact absurd (Finset.mem_univ i0) h
