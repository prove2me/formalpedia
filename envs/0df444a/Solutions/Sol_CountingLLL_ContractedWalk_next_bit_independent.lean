-- Prove2me | solution 1 for CountingLLL.ContractedWalk.next_bit_independent
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:27:05.942865+00:00
-- url     : https://prove2.me/submissions/fb8538da-4c01-41a1-80fc-ff887a9e5c00

import Definitions.Def_CountingLLL_ContractedWalk

set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal

private theorem level_ext (ω ω' : Tape) (i t : ℕ) (h : ∀ k < t, ω k = ω' k) : level ω i t = level ω' i t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev : ∀ k < t, ω k = ω' k := by intro k hk; exact h k (by omega)
    have hnow := h t (by omega)
    simp only [level, ih hprev, hnow]

private theorem bitLaw_probability (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

theorem solution (p : ℝ≥0∞) (hp : p ≤ 1) (i t : ℕ) :
    tapeLaw p {ω | level ω i t ≠ 0 ∧ ω t = true} = tapeLaw p {ω | level ω i t ≠ 0} * p := by
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
  let F : Set (P → Bool) := {x | ∃ ω : Tape, f ω = x ∧ level ω i t ≠ 0}
  let G : Set (Q → Bool) := {x | x ⟨t, by simp [Q]⟩ = true}
  have hF : MeasurableSet F := MeasurableSet.of_discrete
  have hG : MeasurableSet G := MeasurableSet.of_discrete
  have hpre : f ⁻¹' F = {ω : Tape | level ω i t ≠ 0} := by
    ext ω
    constructor
    · rintro ⟨ω', heq, hn⟩
      have he : ∀ k < t, ω k = ω' k := by
        intro k hk
        exact (congrFun heq ⟨k, by simpa [P] using hk⟩).symm
      simpa [level_ext ω ω' i t he] using hn
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
