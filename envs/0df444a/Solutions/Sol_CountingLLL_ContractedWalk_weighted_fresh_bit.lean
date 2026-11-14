-- Prove2me | solution 1 for CountingLLL.ContractedWalk.weighted_fresh_bit
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:54:51.209246+00:00
-- url     : https://prove2.me/submissions/c6276c01-4347-4b25-b72c-f86cf917fe74

import Definitions.Def_CountingLLL_ContractedWalk
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal BigOperators

private theorem bitLaw_probability (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

/-- A nonnegative prefix-dependent weight factors from the next bit. -/
theorem solution (p : ℝ≥0∞) (hp : p ≤ 1) (t : ℕ)
    (F : ((Finset.range t) → Bool) → ℝ≥0∞) :
    (∫⁻ ω : Tape, F (fun j => ω j) * (if ω t then 1 else 0) ∂tapeLaw p) =
      (∫⁻ ω : Tape, F (fun j => ω j) ∂tapeLaw p) * p := by
  classical
  letI : IsProbabilityMeasure (bitLaw p) := bitLaw_probability p hp
  let μ := tapeLaw p
  let P := Finset.range t
  let Q : Finset ℕ := {t}
  let f : Tape → (P → Bool) := fun ω j => ω j
  let g : Tape → (Q → Bool) := fun ω j => ω j
  have hf : Measurable f := measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  have hg : Measurable g := measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  have hind : iIndepFun (fun k (ω : Tape) => ω k) μ := iIndepFun_infinitePi (fun _ => measurable_id)
  have disj : Disjoint P Q := by simp [P,Q, Finset.disjoint_left]; omega
  have hi := iIndepFun.indepFun_finset P Q disj hind (fun k => measurable_pi_apply k)
  let H : (Q → Bool) → ℝ≥0∞ := fun x => if x ⟨t, by simp [Q]⟩ then 1 else 0
  have hF : Measurable F := Measurable.of_discrete
  have hH : Measurable H := Measurable.of_discrete
  have hi' := hi.comp hF hH
  have hmul := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hF.comp hf) (hH.comp hg) hi'
  have hmass : μ {ω : Tape | ω t = true} = p := by
    have hmap : μ.map (fun ω => ω t) = bitLaw p := Measure.infinitePi_map_eval _ _
    change μ ((fun ω : Tape => ω t) ⁻¹' ({true} : Set Bool)) = p
    rw [← Measure.map_apply (measurable_pi_apply t) (MeasurableSet.singleton true), hmap]
    simp [bitLaw]
  have hHmass : (∫⁻ ω, H (g ω) ∂μ) = p := by
    have heq : (fun ω : Tape => H (g ω)) = ({ω : Tape | ω t = true}).indicator 1 := by
      funext ω; cases h : ω t <;> simp [H, g, Set.indicator, h]
    rw [heq]
    have hs : MeasurableSet {ω : Tape | ω t = true} := (MeasurableSet.singleton true).preimage (measurable_pi_apply t)
    rw [lintegral_indicator_one hs, hmass]
  change (∫⁻ ω, F (f ω) * H (g ω) ∂μ) = (∫⁻ ω, F (f ω) ∂μ) * (∫⁻ ω, H (g ω) ∂μ) at hmul
  rw [hHmass] at hmul
  simpa [f,g,H, Function.comp_def] using hmul

