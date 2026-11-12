-- Prove2me | solution 1 for BeliefDominance.vaccine_fallible
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T19:44:38.855216+00:00
-- url     : https://prove2.me/submissions/393203d3-e4ff-48f5-9eb4-4ee71a8b1153

import Definitions.Def_BeliefDominance_vaccineProblem

namespace Aux_BeliefDominance_vaccine_fallible
open BeliefDominance

private lemma effectiveProb_mem' (i : Virologist) (e : Strain × Effort) :
    0 ≤ effectiveProb i e.1 e.2 ∧ effectiveProb i e.1 e.2 ≤ 1 := by
  obtain ⟨s, t⟩ := e
  rcases i with _ | _ <;> rcases s with _ | _ <;> rcases t with (_ | _ | _) | (_ | _ | _) <;>
    norm_num [effectiveProb]

private lemma strainProb_nonneg' (i : Virologist) (s : Strain) : 0 ≤ strainProb i s := by
  rcases i with _ | _ <;> rcases s with _ | _ <;> norm_num [strainProb]

private lemma strainProb_ne_zero (i : Virologist) (s : Strain) : strainProb i s ≠ 0 := by
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

private lemma sum_prod_eff (i : Virologist) :
    (∑ b : Strain × Effort → Bool, ∏ e : Strain × Effort,
      if b e then effectiveProb i e.1 e.2 else 1 - effectiveProb i e.1 e.2) = 1 := by
  have h := Finset.prod_univ_sum (fun _ : Strain × Effort => (Finset.univ : Finset Bool))
    (fun e c => if c then effectiveProb i e.1 e.2 else 1 - effectiveProb i e.1 e.2)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  simp

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
    · intro e _ hne; simp [hne]
    · intro hmem; exact absurd (Finset.mem_univ e₀) hmem
  simp_rw [hfactor]
  have h := Finset.prod_univ_sum (fun _ : Strain × Effort => (Finset.univ : Finset Bool))
    (fun e c => (if e = e₀ then (if c then (1 : ℝ) else 0) else 1) *
      (if c then effectiveProb i e.1 e.2 else 1 - effectiveProb i e.1 e.2))
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  rw [Finset.prod_eq_single e₀]
  · simp
  · intro e _ hne; simp [hne]
  · intro hmem; exact absurd (Finset.mem_univ e₀) hmem

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
    simp_rw [right_distrib]
    rw [Finset.sum_add_distrib, sum_ind_prod i (s, .one x₁), sum_ind_prod i (s, .one x₂)]

private lemma sum_strain_eq (g : Strain → ℝ) : ∑ s : Strain, g s = g .A + g .B := by
  rw [show (Finset.univ : Finset Strain) = {Strain.A, Strain.B} from rfl,
    Finset.sum_pair (by decide)]

private lemma fY_belief (i : Virologist) (y : Strain) :
    fY (belief i) y = strainProb i y := by
  unfold fY
  rw [tsum_fintype, Fintype.sum_prod_type]
  have hinner : ∀ s : Strain,
      (∑ b : Strain × Effort → Bool, mass (belief i) y (s, b)) =
      if s = y then strainProb i y else 0 := by
    intro s
    simp_rw [mass_belief, vaccineWeight]
    by_cases hsy : s = y
    · subst hsy
      simp only [↓reduceIte, mul_one, ← Finset.mul_sum, sum_prod_eff, mul_one]
    · simp [hsy]
  simp_rw [hinner, sum_strain_eq]
  have hBA : Strain.B ≠ Strain.A := by decide
  cases y <;> simp [hBA, hBA.symm]

private lemma V₂_belief (x₁ a : Vaccine) (y : Strain) (i : Virologist) :
    vaccineProblem.V₂ x₁ a y (belief i) = conditionalValue i y x₁ a := by
  unfold Problem.V₂ fZ
  rw [tsum_fintype]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, fY_belief, Fintype.sum_prod_type]
  have hinner : ∀ s : Strain,
      (∑ b : Strain × Effort → Bool, vaccineProblem.U x₁ a (s, b) * mass (belief i) y (s, b)) =
      if s = y then strainProb i y * conditionalValue i y x₁ a else 0 := by
    intro s
    simp_rw [mass_belief, vaccineWeight, vaccineProblem]
    by_cases hsy : s = y
    · subst hsy
      simp only [↓reduceIte, mul_one]
      have hpull : ∀ b : Strain × Effort → Bool,
          vaccineUtility x₁ a (s, b) *
            (strainProb i s * ∏ e : Strain × Effort,
              if b e then effectiveProb i e.1 e.2 else 1 - effectiveProb i e.1 e.2) =
          strainProb i s * (vaccineUtility x₁ a (s, b) *
            ∏ e : Strain × Effort,
              if b e then effectiveProb i e.1 e.2 else 1 - effectiveProb i e.1 e.2) := by
        intro b; ring
      simp_rw [hpull, ← Finset.mul_sum, sum_utility_prod]
    · simp [hsy]
  simp_rw [hinner, sum_strain_eq]
  have hBA : Strain.B ≠ Strain.A := by decide
  have hne := strainProb_ne_zero i y
  cases y <;> simp [hBA, hBA.symm, mul_div_cancel_left₀ _ hne]

private lemma V_belief_eq (x : Vaccine × (Strain → Vaccine)) (i : Virologist) :
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
  simp_rw [hinner, sum_strain_eq]
  have hBA : Strain.B ≠ Strain.A := by decide
  simp [hBA, hBA.symm]

def strainProbN : Virologist → Strain → ℕ
  | .v1, .A => 9
  | .v1, .B => 1
  | .v2, .A => 1
  | .v2, .B => 9

def effProbN : Virologist → Strain → Effort → ℕ
  | .v1, .A, .one .α => 60
  | .v1, .A, .one .β => 20
  | .v1, .A, .one .γ => 10
  | .v1, .A, .two .α => 85
  | .v1, .A, .two .β => 40
  | .v1, .A, .two .γ => 30
  | .v1, .B, .one .α => 10
  | .v1, .B, .one .β => 30
  | .v1, .B, .one .γ => 40
  | .v1, .B, .two .α => 40
  | .v1, .B, .two .β => 80
  | .v1, .B, .two .γ => 65
  | .v2, .A, .one .α => 40
  | .v2, .A, .one .β => 10
  | .v2, .A, .one .γ => 20
  | .v2, .A, .two .α => 80
  | .v2, .A, .two .β => 55
  | .v2, .A, .two .γ => 80
  | .v2, .B, .one .α => 0
  | .v2, .B, .one .β => 50
  | .v2, .B, .one .γ => 20
  | .v2, .B, .two .α => 10
  | .v2, .B, .two .β => 65
  | .v2, .B, .two .γ => 80

def condValN (i : Virologist) (s : Strain) (x₁ x₂ : Vaccine) : ℕ :=
  if x₁ = x₂ then effProbN i s (.two x₁) else effProbN i s (.one x₁) + effProbN i s (.one x₂)

def valN (i : Virologist) (t : Vaccine × Vaccine × Vaccine) : ℕ :=
  strainProbN i .A * condValN i .A t.1 t.2.1 + strainProbN i .B * condValN i .B t.1 t.2.2

def domB (u t : Vaccine × Vaccine × Vaccine) : Bool :=
  decide (valN .v1 t ≤ valN .v1 u) && decide (valN .v2 t ≤ valN .v2 u) &&
    (decide (valN .v1 t < valN .v1 u) || decide (valN .v2 t < valN .v2 u))

def allVaccines : List Vaccine := [.α, .β, .γ]

lemma mem_allVaccines (v : Vaccine) : v ∈ allVaccines := by
  cases v <;> simp [allVaccines]

def noDomB (t : Vaccine × Vaccine × Vaccine) : Bool :=
  allVaccines.all fun u₁ =>
    allVaccines.all fun uA =>
      allVaccines.all fun uB => !domB (u₁, uA, uB) t

lemma strat_eq (x : Vaccine × (Strain → Vaccine)) :
    x = strat x.1 (x.2 .A) (x.2 .B) := by
  ext s
  · rfl
  · cases s <;> rfl

lemma mem_strategies_univ (x : Vaccine × (Strain → Vaccine)) :
    x ∈ vaccineProblem.space.strategies :=
  ⟨Set.mem_univ _, fun _ => Set.mem_univ _⟩

lemma valN_cast (i : Virologist) (a b c : Vaccine) :
    vaccineProblem.V (strat a b c) (belief i) = (valN i (a, b, c) : ℝ) / 1000 := by
  rw [V_belief_eq]
  rcases i with _ | _ <;> rcases a with _ | _ | _ <;>
    rcases b with _ | _ | _ <;> rcases c with _ | _ | _ <;>
    · simp [valN, condValN, strainProbN, effProbN, strat, strainProb, conditionalValue,
        effectiveProb]
      try norm_num

lemma strictPart_le_iff {x y : Vaccine × (Strain → Vaccine)} :
    strictPart vaccineProblem.le x y ↔ vaccineProblem.Dominates y x := by
  unfold strictPart Problem.le
  constructor
  · rintro ⟨hd | hi, hnot⟩
    · exact hd
    · exfalso
      exact hnot (Or.inr fun f hf => (hi f hf).symm)
  · intro hd
    refine ⟨Or.inl hd, ?_⟩
    rintro (hd' | hi')
    · rcases hd'.2 with ⟨f, hf, hgt⟩
      linarith [hd.1 f hf]
    · rcases hd.2 with ⟨f, hf, hgt⟩
      linarith [hi' f hf]

lemma dominates_iff_domB (u₁ uA uB t₁ tA tB : Vaccine) :
    vaccineProblem.Dominates (strat u₁ uA uB) (strat t₁ tA tB) ↔
      domB (u₁, uA, uB) (t₁, tA, tB) = true := by
  unfold Problem.Dominates domB
  have hΦ : ∀ f, f ∈ vaccineProblem.Φ ↔ f = belief .v1 ∨ f = belief .v2 := fun _ => Iff.rfl
  have h1000 : (0 : ℝ) < 1000 := by norm_num
  simp only [hΦ, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left,
    ge_iff_le, gt_iff_lt, valN_cast, div_le_div_iff_of_pos_right h1000,
    div_lt_div_iff_of_pos_right h1000, Nat.cast_le, Nat.cast_lt,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, and_assoc]

lemma strat_eq_iff (a₁ a₂ a₃ b₁ b₂ b₃ : Vaccine) :
    strat a₁ a₂ a₃ = strat b₁ b₂ b₃ ↔ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrFun (congrArg Prod.snd h) .A,
      congrFun (congrArg Prod.snd h) .B⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

lemma opt_iff_noDomB (a b c : Vaccine) :
    strat a b c ∈ optimalStrategies vaccineProblem.space vaccineProblem.le ↔
      noDomB (a, b, c) = true := by
  unfold optimalStrategies noDomB
  simp only [Set.mem_setOf_eq, mem_strategies_univ, true_and, strictPart_le_iff,
    List.all_eq_true, Bool.not_eq_true', ← Bool.not_eq_true]
  constructor
  · intro h u₁ _ uA _ uB _
    exact (dominates_iff_domB u₁ uA uB a b c).not.mp (h (strat u₁ uA uB) trivial)
  · intro h u _
    rw [strat_eq u]
    exact (dominates_iff_domB u.1 (u.2 .A) (u.2 .B) a b c).not.mpr
      (h u.1 (mem_allVaccines _) (u.2 .A) (mem_allVaccines _) (u.2 .B) (mem_allVaccines _))

lemma part1_aux (a b c : Vaccine) :
    (noDomB (a, b, c) = true) ↔
      strat a b c ∈ ({strat .α .α .β, strat .α .α .γ, strat .β .α .β, strat .β .α .γ,
        strat .γ .α .β, strat .γ .α .γ, strat .γ .γ .γ} : Set (Vaccine × (Strain → Vaccine))) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, strat_eq_iff]
  rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> rcases c with _ | _ | _ <;> decide

lemma part1_optimalStrategies :
    optimalStrategies vaccineProblem.space vaccineProblem.le =
      {strat .α .α .β, strat .α .α .γ, strat .β .α .β, strat .β .α .γ,
        strat .γ .α .β, strat .γ .α .γ, strat .γ .γ .γ} := by
  ext x
  rw [strat_eq x, opt_iff_noDomB]
  exact part1_aux x.1 (x.2 .A) (x.2 .B)

lemma part2_optimalAction :
    Vaccine.β ∈ optimalActions vaccineProblem.space vaccineProblem.le₂ .β .A := by
  refine ⟨Set.mem_univ _, fun b _ hsp => ?_⟩
  unfold strictPart Problem.le₂ at hsp
  have hdom : vaccineProblem.Dominates₂ .β .A b .β := by
    rcases hsp with ⟨hd | hi, hnot⟩
    · exact hd
    · exfalso; exact hnot (Or.inr fun f hf => (hi f hf).symm)
  have hv2 : belief .v2 ∈ vaccineProblem.Φy .A := by
    refine ⟨Or.inr rfl, ?_⟩
    rw [fY_belief]
    norm_num [strainProb]
  have hge := hdom.1 (belief .v2) hv2
  rw [V₂_belief, V₂_belief] at hge
  rcases b with _ | _ | _
  · simp [conditionalValue, effectiveProb] at hge; norm_num at hge
  · rcases hdom.2 with ⟨f, _, hgt⟩
    exact lt_irrefl _ hgt
  · simp [conditionalValue, effectiveProb] at hge; norm_num at hge

lemma part3_dominates_beta_beta (v : Vaccine) :
    ∃ x ∈ vaccineProblem.space.strategies,
      vaccineProblem.Dominates x (strat .β .β v) := by
  rcases v with _ | _ | _
  · refine ⟨strat .α .α .β, mem_strategies_univ _, ?_⟩
    rw [dominates_iff_domB]; decide
  · refine ⟨strat .β .α .γ, mem_strategies_univ _, ?_⟩
    rw [dominates_iff_domB]; decide
  · refine ⟨strat .γ .α .β, mem_strategies_univ _, ?_⟩
    rw [dominates_iff_domB]; decide

end Aux_BeliefDominance_vaccine_fallible

open BeliefDominance Aux_BeliefDominance_vaccine_fallible

theorem solution :
    optimalStrategies vaccineProblem.space vaccineProblem.le =
      {strat .α .α .β, strat .α .α .γ, strat .β .α .β, strat .β .α .γ,
        strat .γ .α .β, strat .γ .α .γ, strat .γ .γ .γ} ∧
    Vaccine.β ∈ optimalActions vaccineProblem.space vaccineProblem.le₂ .β .A ∧
    (∀ v : Vaccine, ∃ x ∈ vaccineProblem.space.strategies,
      vaccineProblem.Dominates x (strat .β .β v)) ∧
    ExhibitsFallible vaccineProblem.space vaccineProblem.le vaccineProblem.le₂ := by
  refine ⟨part1_optimalStrategies, part2_optimalAction, part3_dominates_beta_beta, ?_⟩
  refine ⟨strat .β .α .β, ?_, .A, .β, part2_optimalAction, ?_⟩
  · rw [part1_optimalStrategies]; simp
  · intro s _ hs1 hsA
    have hs : s = strat .β .β (s.2 .B) := by
      nth_rw 1 [strat_eq s]
      rw [hs1, hsA]
      rfl
    rw [hs]
    rcases part3_dominates_beta_beta (s.2 .B) with ⟨x, hx, hdom⟩
    exact ⟨x, hx, strictPart_le_iff.mpr hdom⟩
