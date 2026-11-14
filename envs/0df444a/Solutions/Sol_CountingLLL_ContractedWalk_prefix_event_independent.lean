-- Prove2me | solution 1 for CountingLLL.ContractedWalk.prefix_event_independent
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:51:28.840518+00:00
-- url     : https://prove2.me/submissions/8c91b46d-0019-47ee-902a-928566e414e1

import Definitions.Def_CountingLLL_ContractedWalk
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal BigOperators

private theorem bitLaw_probability (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

theorem solution (p : ℝ≥0∞) (hp : p ≤ 1) (t : ℕ) (E : Set Tape)
    (hE : ∀ ω ω', (∀ k < t, ω k = ω' k) → (ω ∈ E ↔ ω' ∈ E)) :
    tapeLaw p {ω | ω ∈ E ∧ ω t = true} = tapeLaw p E * p := by
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
  have disj : Disjoint P Q := by
    simp [P,Q, Finset.disjoint_left]
    omega
  have hi := iIndepFun.indepFun_finset P Q disj hind (fun k => measurable_pi_apply k)
  let F : Set (P → Bool) := {x | ∃ ω : Tape, f ω = x ∧ ω ∈ E}
  let G : Set (Q → Bool) := {x | x ⟨t, by simp [Q]⟩ = true}
  have hF : MeasurableSet F := MeasurableSet.of_discrete
  have hG : MeasurableSet G := MeasurableSet.of_discrete
  have hpre : f ⁻¹' F = {ω : Tape | ω ∈ E} := by
    ext ω
    constructor
    · rintro ⟨ω', heq, hn⟩
      have he : ∀ k < t, ω k = ω' k := by
        intro k hk
        exact (congrFun heq ⟨k, by simpa [P] using hk⟩).symm
      exact (hE ω ω' he).2 hn
    · intro hn; exact ⟨ω, rfl, hn⟩
  have hgpre : g ⁻¹' G = {ω : Tape | ω t = true} := by ext ω; rfl
  have hmass : μ {ω : Tape | ω t = true} = p := by
    have hmap : μ.map (fun ω => ω t) = bitLaw p := Measure.infinitePi_map_eval _ _
    change μ ((fun ω : Tape => ω t) ⁻¹' ({true} : Set Bool)) = p
    rw [← Measure.map_apply (measurable_pi_apply t) (MeasurableSet.singleton true), hmap]
    simp [bitLaw]
  have hcalc := hi.measure_inter_preimage_eq_mul F G hF hG
  rw [hpre, hgpre, hmass] at hcalc
  exact hcalc

