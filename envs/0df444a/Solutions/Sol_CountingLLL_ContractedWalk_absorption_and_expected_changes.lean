-- Prove2me | solution 1 for CountingLLL.ContractedWalk.absorption_and_expected_changes
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:28:31.33337+00:00
-- url     : https://prove2.me/submissions/722be614-68e4-4865-9ce1-b74f9eb9a3e2

import Definitions.Def_CountingLLL_ContractedWalk

set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal BigOperators

private theorem walk_balance (ω : Tape) (i t : ℕ) :
    level ω i t + (∑ k ∈ Finset.range t, if level ω i k = 0 then 0 else 1) =
      i + 3*(∑ k ∈ Finset.range t, if level ω i k ≠ 0 ∧ ω k = true then 1 else 0) := by
  induction t with
  | zero => simp [level]
  | succ t ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [level]
    split <;> split <;> simp_all <;> omega

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

private theorem next_bit_independent (p : ℝ≥0∞) (hp : p ≤ 1) (i t : ℕ) :
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

private theorem level_ext' (ω ω' : Tape) (i t : ℕ) (h : ∀ k < t, ω k = ω' k) : level ω i t = level ω' i t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev : ∀ k < t, ω k = ω' k := by intro k hk; exact h k (by omega)
    have hnow := h t (by omega)
    simp only [level, ih hprev, hnow]

private theorem active_meas (i t : ℕ) : MeasurableSet {ω : Tape | level ω i t ≠ 0} := by
  classical
  let f : Tape → (Fin t → Bool) := fun ω j => ω j
  have hf : Measurable f := measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  let F : Set (Fin t → Bool) := {x | ∃ ω : Tape, f ω = x ∧ level ω i t ≠ 0}
  have heq : f ⁻¹' F = {ω : Tape | level ω i t ≠ 0} := by
    ext ω
    constructor
    · rintro ⟨ω', heq, hn⟩
      have he : ∀ k < t, ω k = ω' k := by intro k hk; exact (congrFun heq ⟨k,hk⟩).symm
      simpa [level_ext' ω ω' i t he] using hn
    · intro hn; exact ⟨ω, rfl, hn⟩
  rw [← heq]
  exact MeasurableSet.of_discrete.preimage hf

private theorem up_meas (i t : ℕ) : MeasurableSet {ω : Tape | level ω i t ≠ 0 ∧ ω t = true} :=
  (active_meas i t).inter ((MeasurableSet.singleton true).preimage (measurable_pi_apply t))

private theorem bitLaw_probability' (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

private theorem finite_drift (p : ℝ≥0∞) (hp : p ≤ 1) (i n : ℕ) :
    (∑ k ∈ Finset.range n, tapeLaw p {ω | level ω i k ≠ 0}) ≤
      (i : ℝ≥0∞) + 3*p * (∑ k ∈ Finset.range n, tapeLaw p {ω | level ω i k ≠ 0}) := by
  classical
  letI : IsProbabilityMeasure (bitLaw p) := bitLaw_probability' p hp
  let μ := tapeLaw p
  let A : ℕ → Set Tape := fun k => {ω | level ω i k ≠ 0}
  let U : ℕ → Set Tape := fun k => {ω | level ω i k ≠ 0 ∧ ω k = true}
  let fa : ℕ → Tape → ℝ≥0∞ := fun k => (A k).indicator 1
  let fu : ℕ → Tape → ℝ≥0∞ := fun k => (U k).indicator 1
  have hfa : ∀ k, Measurable (fa k) := fun k => measurable_one.indicator (active_meas i k)
  have hfu : ∀ k, Measurable (fu k) := fun k => measurable_one.indicator (up_meas i k)
  have hpoint (ω : Tape) : (∑ k ∈ Finset.range n, fa k ω) ≤ (i : ℝ≥0∞) + 3*(∑ k ∈ Finset.range n, fu k ω) := by
    have hb := walk_balance ω i n
    have hl : (∑ k ∈ Finset.range n, if level ω i k = 0 then 0 else 1) ≤
        i + 3*(∑ k ∈ Finset.range n, if level ω i k ≠ 0 ∧ ω k = true then 1 else 0) := by omega
    have hc : ((∑ k ∈ Finset.range n, if level ω i k = 0 then 0 else 1 : ℕ) : ℝ≥0∞) ≤
        ((i + 3*(∑ k ∈ Finset.range n, if level ω i k ≠ 0 ∧ ω k = true then 1 else 0) : ℕ) : ℝ≥0∞) := by exact_mod_cast hl
    simpa [fa, fu, A, U, Set.indicator, apply_ite] using hc
  have hInt := lintegral_mono hpoint (μ := μ)
  rw [lintegral_finset_sum _ (fun k _ => hfa k)] at hInt
  rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul _ (by fun_prop), lintegral_finset_sum _ (fun k _ => hfu k)] at hInt
  have hA (k : ℕ) : (∫⁻ ω, (A k).indicator (1 : Tape → ℝ≥0∞) ω ∂μ) = μ (A k) := lintegral_indicator_one (active_meas i k)
  have hU (k : ℕ) : (∫⁻ ω, (U k).indicator (1 : Tape → ℝ≥0∞) ω ∂μ) = μ (U k) := lintegral_indicator_one (up_meas i k)
  simp_rw [fa, fu, hA, hU] at hInt
  have hμ : IsProbabilityMeasure μ := by dsimp [μ, tapeLaw]; infer_instance
  letI := hμ
  simp only [measure_univ, mul_one] at hInt
  simp_rw [show ∀ k, μ (U k) = μ (A k) * p from fun k => next_bit_independent p hp i k] at hInt
  rw [← Finset.sum_mul] at hInt
  dsimp [μ,A,U] at hInt
  simpa [mul_assoc, mul_left_comm, mul_comm] using hInt

private theorem finite_bound (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3) (i n : ℕ) :
    (∑ k ∈ Finset.range n, tapeLaw (ENNReal.ofReal θ) {ω | level ω i k ≠ 0}) ≤
      ENNReal.ofReal ((i : ℝ)/(1-3*θ)) := by
  let p := ENNReal.ofReal θ
  have hp : p ≤ 1 := by
    have : θ ≤ (1:ℝ) := by linarith
    simpa [p] using ENNReal.ofReal_le_ofReal this
  letI : IsProbabilityMeasure (bitLaw p) := bitLaw_probability' p hp
  let μ := tapeLaw p
  letI : IsProbabilityMeasure μ := by dsimp [μ,tapeLaw]; infer_instance
  let A : ℝ≥0∞ := ∑ k ∈ Finset.range n, μ {ω | level ω i k ≠ 0}
  have hAle : A ≤ n := by
    dsimp [A]
    calc
      _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa using (measure_mono (μ := μ) (Set.subset_univ {ω | level ω i k ≠ 0}))
      _ = n := by simp
  have hAfinite : A ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hAle (by simp))
  have hpfinite : p ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hp (by simp))
  have hmulfinite : (3*p*A) ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hpfinite) hAfinite
  have hRfinite : ((i : ℝ≥0∞) + 3*p*A) ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨by simp, hmulfinite⟩
  have hineq : A ≤ (i : ℝ≥0∞) + 3*p*A := by simpa [A,μ] using finite_drift p hp i n
  have hreal : A.toReal ≤ ((i : ℝ≥0∞) + 3*p*A).toReal := (ENNReal.toReal_le_toReal hAfinite hRfinite).2 hineq
  have hpReal : p.toReal = θ := by simp [p, hθ0]
  have hnonneg : 0 ≤ A.toReal := ENNReal.toReal_nonneg
  have hden : 0 < 1-3*θ := by linarith
  have hbound : A.toReal ≤ (i : ℝ)/(1-3*θ) := by
    apply (le_div_iff₀ hden).2
    rw [ENNReal.toReal_add (by simp) hmulfinite] at hreal
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofNat] at hreal
    rw [hpReal] at hreal
    nlinarith
  change A ≤ ENNReal.ofReal ((i : ℝ)/(1-3*θ))
  rw [← ENNReal.ofReal_toReal hAfinite]
  exact ENNReal.ofReal_le_ofReal hbound

private theorem expected_bound (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3) (i : ℕ) :
    expectedChanges (ENNReal.ofReal θ) i ≤ ENNReal.ofReal ((i : ℝ)/(1-3*θ)) := by
  classical
  unfold expectedChanges changes
  have heq (t : ℕ) : (fun ω : Tape => if level ω i t = 0 then (0:ℝ≥0∞) else 1) =
      ({ω : Tape | level ω i t ≠ 0}).indicator 1 := by
    funext ω
    by_cases h : level ω i t = 0 <;> simp [h]
  simp_rw [show ∀ t ω, (if level ω i t = 0 then (0:ℝ≥0∞) else 1) = ({ω : Tape | level ω i t ≠ 0}).indicator (1 : Tape → ℝ≥0∞) ω from fun t ω => congrFun (heq t) ω]
  rw [lintegral_tsum (fun t => (measurable_one.indicator (active_meas i t)).aemeasurable)]
  have hInt (t : ℕ) : (∫⁻ ω, ({ω : Tape | level ω i t ≠ 0}).indicator (1 : Tape → ℝ≥0∞) ω ∂tapeLaw (ENNReal.ofReal θ)) = tapeLaw (ENNReal.ofReal θ) {ω | level ω i t ≠ 0} := lintegral_indicator_one (active_meas i t)
  simp_rw [hInt]
  exact ENNReal.tsum_le_of_sum_range_le (finite_bound θ hθ0 hθ i)

private theorem absorption (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3) (i : ℕ) :
    tapeLaw (ENNReal.ofReal θ) {ω | ∃ t, level ω i t = 0} = 1 := by
  classical
  let p := ENNReal.ofReal θ
  have hp : p ≤ 1 := by
    have : θ ≤ (1:ℝ) := by linarith
    simpa [p] using ENNReal.ofReal_le_ofReal this
  letI : IsProbabilityMeasure (bitLaw p) := bitLaw_probability' p hp
  let μ := tapeLaw p
  letI : IsProbabilityMeasure μ := by dsimp [μ,tapeLaw]; infer_instance
  have hmeas : Measurable (fun ω : Tape => changes ω i) := by
    unfold changes
    apply Measurable.tsum
    intro t
    have heq : (fun ω : Tape => if level ω i t = 0 then (0:ℝ≥0∞) else 1) =
        ({ω : Tape | level ω i t ≠ 0}).indicator 1 := by
      funext ω
      by_cases h : level ω i t = 0 <;> simp [h]
    rw [heq]
    exact measurable_one.indicator (active_meas i t)
  have hfinite : (∫⁻ ω, changes ω i ∂μ) ≠ ⊤ := by
    have hb := expected_bound θ hθ0 hθ i
    change (∫⁻ ω, changes ω i ∂μ) ≤ _ at hb
    exact ne_of_lt (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)
  have hae := ae_lt_top hmeas hfinite
  have hstop : ∀ᵐ ω ∂μ, ∃ t, level ω i t = 0 := by
    filter_upwards [hae] with ω hw
    by_contra h
    have hn : ∀ t, level ω i t ≠ 0 := by simpa using h
    have ht : changes ω i = ⊤ := by simp [changes, hn, ENNReal.tsum_one]
    rw [ht] at hw
    exact (lt_irrefl _) hw
  have hset : MeasurableSet {ω : Tape | ∃ t, level ω i t = 0} := by
    have heq : {ω : Tape | ∃ t, level ω i t = 0} = ⋃ t : ℕ, {ω : Tape | level ω i t = 0} := by ext ω; simp
    rw [heq]
    exact MeasurableSet.iUnion fun t => by simpa only [Set.compl_setOf, not_not] using (active_meas i t).compl
  have hnull : μ {ω : Tape | ¬ ∃ t, level ω i t = 0} = 0 := ae_iff.mp hstop
  have hnull' : μ ({ω : Tape | ∃ t, level ω i t = 0}ᶜ) = 0 := by
    change μ {ω : Tape | ¬ ∃ t, level ω i t = 0} = 0
    exact hnull
  have heq := measure_add_measure_compl (μ := μ) hset
  rw [hnull', add_zero, measure_univ] at heq
  exact heq


theorem solution (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3) (i : ℕ) :
    tapeLaw (ENNReal.ofReal θ) {ω | ∃ t, level ω i t = 0} = 1 ∧
    expectedChanges (ENNReal.ofReal θ) i ≤ ENNReal.ofReal ((i : ℝ) / (1-3*θ)) := by
  exact ⟨absorption θ hθ0 hθ i, expected_bound θ hθ0 hθ i⟩
