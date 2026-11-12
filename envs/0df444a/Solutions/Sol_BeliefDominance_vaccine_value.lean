-- Prove2me | solution 1 for BeliefDominance.vaccine_value
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T19:38:13.929246+00:00
-- url     : https://prove2.me/submissions/87636960-f151-4102-9e88-a0b804f1a142

import Definitions.Def_BeliefDominance_vaccineProblem

namespace Aux_BeliefDominance_vaccine_value
open BeliefDominance

private lemma effectiveProb_mem' (i : Virologist) (e : Strain × Effort) :
    0 ≤ effectiveProb i e.1 e.2 ∧ effectiveProb i e.1 e.2 ≤ 1 := by
  obtain ⟨s, t⟩ := e
  rcases i with _ | _ <;> rcases s with _ | _ <;> rcases t with (_ | _ | _) | (_ | _ | _) <;>
    norm_num [effectiveProb]

private lemma strainProb_nonneg' (i : Virologist) (s : Strain) : 0 ≤ strainProb i s := by
  rcases i with _ | _ <;> rcases s with _ | _ <;> norm_num [strainProb]

private lemma vaccineWeight_nonneg' (i : Virologist) (ω : Strain × VaccineOutcome) :
    0 ≤ vaccineWeight i ω := by
  refine mul_nonneg (mul_nonneg (strainProb_nonneg' i _) (by split_ifs <;> norm_num)) ?_
  refine Finset.prod_nonneg fun e _ => ?_
  have h := effectiveProb_mem' i e
  split_ifs
  · exact h.1
  · linarith [h.2]

private lemma mass_belief (i : Virologist) (y : Strain) (z : VaccineOutcome) :
    mass (belief i) y z = vaccineWeight i (y, z) := by
  simp only [mass, belief, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (vaccineWeight_nonneg' i (y, z))

private lemma sum_ind_prod (i : Virologist) (e₀ : Strain × Effort) :
    (∑ b : Strain × Effort → Bool,
      (if b e₀ then (1 : ℝ) else 0) *
        ∏ e : Strain × Effort,
          if b e then effectiveProb i e.1 e.2 else 1 - effectiveProb i e.1 e.2) =
      effectiveProb i e₀.1 e₀.2 := by
  have hfactor : ∀ b : Strain × Effort → Bool,
      (if b e₀ then (1 : ℝ) else 0) *
        (∏ e : Strain × Effort,
          if b e then effectiveProb i e.1 e.2 else 1 - effectiveProb i e.1 e.2) =
      ∏ e : Strain × Effort,
        (if e = e₀ then (if b e then (1 : ℝ) else 0) else 1) *
          (if b e then effectiveProb i e.1 e.2 else 1 - effectiveProb i e.1 e.2) := by
    intro b
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_eq_single e₀]
    · simp
    · intro e _ hne
      simp [hne]
    · intro hmem
      exact absurd (Finset.mem_univ e₀) hmem
  simp_rw [hfactor]
  have h := Finset.prod_univ_sum (fun _ : Strain × Effort => (Finset.univ : Finset Bool))
    (fun e c => (if e = e₀ then (if c then (1 : ℝ) else 0) else 1) *
      (if c then effectiveProb i e.1 e.2 else 1 - effectiveProb i e.1 e.2))
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  rw [Finset.prod_eq_single e₀]
  · simp
  · intro e _ hne
    simp [hne]
  · intro hmem
    exact absurd (Finset.mem_univ e₀) hmem

private lemma sum_utility_prod (i : Virologist) (s : Strain) (x₁ x₂ : Vaccine) :
    (∑ b : Strain × Effort → Bool,
      vaccineUtility x₁ x₂ (s, b) *
        ∏ e : Strain × Effort,
          if b e then effectiveProb i e.1 e.2 else 1 - effectiveProb i e.1 e.2) =
      conditionalValue i s x₁ x₂ := by
  unfold vaccineUtility conditionalValue
  by_cases h : x₁ = x₂
  · simp only [h, ↓reduceIte]
    exact sum_ind_prod i (s, .two x₂)
  · simp only [h, ↓reduceIte]
    simp_rw [ right_distrib ]
    rw [Finset.sum_add_distrib, sum_ind_prod i (s, .one x₁), sum_ind_prod i (s, .one x₂)]

lemma V_belief_eq (x : Vaccine × (Strain → Vaccine)) (i : Virologist) :
    vaccineProblem.V x (belief i) =
      strainProb i .A * conditionalValue i .A x.1 (x.2 .A) +
        strainProb i .B * conditionalValue i .B x.1 (x.2 .B) := by
  unfold Problem.V
  rw [tsum_fintype, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have hinner : ∀ y s : Strain,
      (∑ b : Strain × Effort → Bool,
        vaccineProblem.U x.1 (x.2 y) (s, b) * mass (belief i) y (s, b)) =
      if s = y then strainProb i y * conditionalValue i y x.1 (x.2 y) else 0 := by
    intro y s
    simp_rw [mass_belief, vaccineWeight, vaccineProblem]
    by_cases hsy : s = y
    · subst hsy
      simp only [↓reduceIte, mul_one]
      have hpull : ∀ b : Strain × Effort → Bool,
          vaccineUtility x.1 (x.2 s) (s, b) *
            (strainProb i s * ∏ e : Strain × Effort,
              if b e then effectiveProb i e.1 e.2 else 1 - effectiveProb i e.1 e.2) =
          strainProb i s * (vaccineUtility x.1 (x.2 s) (s, b) *
            ∏ e : Strain × Effort,
              if b e then effectiveProb i e.1 e.2 else 1 - effectiveProb i e.1 e.2) := by
        intro b; ring
      simp_rw [hpull, ← Finset.mul_sum, sum_utility_prod]
    · simp [hsy]
  simp_rw [hinner]
  have hU : ∀ g : Strain → ℝ, ∑ s : Strain, g s = g .A + g .B := fun g => by
    rw [show (Finset.univ : Finset Strain) = {Strain.A, Strain.B} from rfl,
      Finset.sum_pair (by decide)]
  have hBA : Strain.B ≠ Strain.A := by decide
  simp_rw [hU]
  simp [hBA, hBA.symm]

end Aux_BeliefDominance_vaccine_value

open BeliefDominance Aux_BeliefDominance_vaccine_value

theorem solution :
    vaccineProblem.WellPosed ∧
    (∀ (x : Vaccine × (Strain → Vaccine)) (i : Virologist),
      vaccineProblem.V x (belief i) =
        strainProb i .A * conditionalValue i .A x.1 (x.2 .A) +
          strainProb i .B * conditionalValue i .B x.1 (x.2 .B)) ∧
    vaccineProblem.V (strat .β .α .β) (belief .v1) = 4 / 5 := by
  refine ⟨fun f _ x _ => (hasSum_fintype _).summable, V_belief_eq, ?_⟩
  rw [V_belief_eq]
  simp [strat, strainProb, conditionalValue, effectiveProb]
  norm_num
