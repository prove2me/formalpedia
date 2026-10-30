-- Prove2me | solution 1 for FragileBandit.CauchyTail.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T12:46:41.424997+00:00
-- url     : https://prove2.me/submissions/902f5a62-e494-4267-97e9-d5ca6991cb3b

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting
import Theorems.Thm_FragileBandit_CauchyTail_change_of_measure

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm FragileBandit.CauchyTail
open scoped ENNReal Topology

namespace CTL6Aux

variable {K : ℕ}

open Classical


lemma armPullCount_eq_sum {K n : ℕ} (i : Fin K) (h : BanditHistory K n) :
    armPullCount i h = ∑ t : Fin n, if (h t).1 = i then 1 else 0 := by
  unfold armPullCount
  rw [Set.toFinset_ofPred, Finset.card_filter]

lemma armPullCount_le {K n : ℕ} (i : Fin K) (h : BanditHistory K n) :
    armPullCount i h ≤ n := by
  rw [armPullCount_eq_sum]
  calc (∑ t : Fin n, if (h t).1 = i then 1 else 0) ≤ ∑ _t : Fin n, 1 :=
        Finset.sum_le_sum (fun t _ => by split_ifs <;> simp)
    _ = n := by simp

lemma measurable_armPullCount {K n : ℕ} (i : Fin K) :
    Measurable (fun h : BanditHistory K n => armPullCount i h) := by
  have hF : Measurable (fun h : BanditHistory K n => fun t => (h t).1) := by
    rw [measurable_pi_iff]
    intro t
    exact measurable_fst.comp (measurable_pi_apply t)
  have : (fun h : BanditHistory K n => armPullCount i h) =
      (fun a : Fin n → Fin K => ∑ t : Fin n, if a t = i then 1 else 0) ∘
        (fun h : BanditHistory K n => fun t => (h t).1) := by
    funext h; simp [armPullCount_eq_sum]
  rw [this]
  exact (measurable_of_countable _).comp hF


/-- Integral against the step: unfold the step kernel. -/
lemma lintegral_step (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ)
    (h : BanditHistory K T) {F : Fin K × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂(banditStepKernel ν π T h) = ∫⁻ a, ∫⁻ x, F (a, x) ∂(ν.P a) ∂(π.select T h) := by
  unfold banditStepKernel
  rw [Kernel.lintegral_compProd _ _ _ hF]
  rfl

/-- Unfold the integral over `banditMeasure (T+1)`. -/
lemma lintegral_succ (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ)
    {g : BanditHistory K (T + 1) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ h, g h ∂(banditMeasure ν π (T + 1)) =
      ∫⁻ h, ∫⁻ p, g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) ∂(banditStepKernel ν π T h)
        ∂(banditMeasure ν π T) := by
  rw [banditMeasure.eq_2, lintegral_map hg measurable_banditHistorySnoc,
    Measure.lintegral_compProd (f := fun a => g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) a.1 a.2))
      (hg.comp measurable_banditHistorySnoc)]

/-- Number of plays of arm `j` strictly before round `t`. -/
def cntBefore (j : Fin K) {T : ℕ} (h : BanditHistory K T) (t : Fin T) : ℕ :=
  ∑ s : Fin T, if s < t ∧ (h s).1 = j then 1 else 0

/-- Number of rounds `t` in which arm `j` is played for the `≤ m`-th time with reward in `B`. -/
noncomputable def Wc (j : Fin K) (m : ℕ) (B : Set ℝ) {T : ℕ} (h : BanditHistory K T) : ℝ≥0∞ :=
  ∑ t : Fin T, if (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B then 1 else 0

/-- `min (N_j) m`. -/
noncomputable def Mc (j : Fin K) (m : ℕ) {T : ℕ} (h : BanditHistory K T) : ℝ≥0∞ :=
  ((min (armPullCount j h) m : ℕ) : ℝ≥0∞)

lemma cntBefore_snoc_castSucc (j : Fin K) {T : ℕ} (h : BanditHistory K T) (p : Fin K × ℝ)
    (t : Fin T) :
    cntBefore j (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) (Fin.castSucc t) = cntBefore j h t := by
  unfold cntBefore
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.castSucc_lt_castSucc_iff, Fin.snoc_last]
  have : ¬ (Fin.last T < Fin.castSucc t) := not_lt.2 (Fin.le_last _)
  simp [this]

lemma cntBefore_snoc_last (j : Fin K) {T : ℕ} (h : BanditHistory K T) (p : Fin K × ℝ) :
    cntBefore j (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) (Fin.last T) = armPullCount j h := by
  unfold cntBefore
  rw [Fin.sum_univ_castSucc, armPullCount_eq_sum]
  simp [Fin.snoc_castSucc, Fin.castSucc_lt_last]

lemma Wc_snoc (j : Fin K) (m : ℕ) (B : Set ℝ) {T : ℕ} (h : BanditHistory K T) (p : Fin K × ℝ) :
    Wc j m B (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) =
      Wc j m B h + (if p.1 = j ∧ armPullCount j h < m ∧ p.2 ∈ B then 1 else 0) := by
  classical
  unfold Wc
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, cntBefore_snoc_castSucc, cntBefore_snoc_last]

lemma Mc_snoc (j : Fin K) (m : ℕ) {T : ℕ} (h : BanditHistory K T) (p : Fin K × ℝ) :
    Mc j m (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) =
      Mc j m h + (if p.1 = j ∧ armPullCount j h < m then 1 else 0) := by
  unfold Mc
  have hN : armPullCount j (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) =
      armPullCount j h + (if p.1 = j then 1 else 0) := by
    rw [armPullCount_eq_sum, armPullCount_eq_sum, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [hN]
  by_cases hp : p.1 = j
  · by_cases hm : armPullCount j h < m
    · simp only [hp, hm, and_self, if_true]
      rw [min_eq_left (by omega), min_eq_left (by omega)]
      push_cast; ring
    · simp only [hp, hm, and_false, if_false, if_true, add_zero]
      rw [min_eq_right (by omega), min_eq_right (by omega)]
  · simp [hp]

lemma measurable_arms {T : ℕ} :
    Measurable (fun h : BanditHistory K T => fun t => (h t).1) := by
  rw [measurable_pi_iff]
  intro t
  exact measurable_fst.comp (measurable_pi_apply t)

lemma measurable_Wc (j : Fin K) (m : ℕ) {B : Set ℝ} (hB : MeasurableSet B) (T : ℕ) :
    Measurable (fun h : BanditHistory K T => Wc j m B h) := by
  classical
  unfold Wc
  refine Finset.measurable_sum _ (fun t _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  have h1 : MeasurableSet {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t < m} := by
    have : {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t < m} =
        (fun h : BanditHistory K T => fun t => (h t).1) ⁻¹'
          {a : Fin T → Fin K | a t = j ∧
            (∑ s : Fin T, if s < t ∧ a s = j then 1 else 0) < m} := by
      ext h; simp [cntBefore]
    rw [this]
    exact measurable_arms (Set.to_countable _).measurableSet
  have h2 : MeasurableSet {h : BanditHistory K T | (h t).2 ∈ B} :=
    (measurable_snd.comp (measurable_pi_apply t)) hB
  have : {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B} =
      {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t < m} ∩
        {h : BanditHistory K T | (h t).2 ∈ B} := by
    ext h; simp [and_assoc]
  rw [this]; exact h1.inter h2

lemma measurable_Mc (j : Fin K) (m : ℕ) (T : ℕ) :
    Measurable (fun h : BanditHistory K T => Mc j m h) := by
  unfold Mc
  exact (measurable_from_nat (f := fun n : ℕ => ((min n m : ℕ) : ℝ≥0∞))).comp
    (measurable_armPullCount j)

lemma lintegral_sel_ite (μ : Measure (Fin K)) (j : Fin K) (c : ℝ≥0∞) :
    ∫⁻ a, (if a = j then c else 0) ∂μ = c * μ {j} := by
  rw [lintegral_fintype]
  simp [Finset.sum_ite_eq']

lemma step_inc_W (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ) (j : Fin K)
    (P : Prop) {B : Set ℝ} (hB : MeasurableSet B) (h : BanditHistory K T) :
    ∫⁻ p, (if p.1 = j ∧ P ∧ p.2 ∈ B then (1 : ℝ≥0∞) else 0) ∂(banditStepKernel ν π T h) =
      (if P then ν.P j B else 0) * π.select T h {j} := by
  classical
  have hm : Measurable (fun p : Fin K × ℝ =>
      (if p.1 = j ∧ P ∧ p.2 ∈ B then (1 : ℝ≥0∞) else 0)) := by
    refine Measurable.ite ?_ measurable_const measurable_const
    have : {p : Fin K × ℝ | p.1 = j ∧ P ∧ p.2 ∈ B} = ({j} ×ˢ {x | P ∧ x ∈ B}) := by
      ext p; simp
    rw [this]
    refine (MeasurableSet.singleton j).prod ?_
    by_cases hP : P
    · simpa [hP] using hB
    · simp [hP]
  rw [lintegral_step ν π T h hm]
  have : ∀ a : Fin K, ∫⁻ x, (if (a, x).1 = j ∧ P ∧ (a, x).2 ∈ B then (1 : ℝ≥0∞) else 0) ∂(ν.P a)
      = if a = j then (if P then ν.P j B else 0) else 0 := by
    intro a
    by_cases ha : a = j
    · subst ha
      by_cases hP : P
      · simp only [hP, true_and, if_true]
        rw [show (fun x : ℝ => if x ∈ B then (1 : ℝ≥0∞) else 0) = B.indicator 1 from by
          ext x; simp [Set.indicator_apply]]
        exact lintegral_indicator_one hB
      · simp [hP]
    · simp [ha]
  simp_rw [this]
  rw [lintegral_sel_ite]

lemma step_inc_M (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ) (j : Fin K)
    (P : Prop) (h : BanditHistory K T) :
    ∫⁻ p, (if p.1 = j ∧ P then (1 : ℝ≥0∞) else 0) ∂(banditStepKernel ν π T h) =
      (if P then 1 else 0) * π.select T h {j} := by
  have := step_inc_W ν π T j P MeasurableSet.univ h
  simpa using this

lemma lintegral_Wc (ν : StochasticBandit K) (π : BanditPolicy K) (j : Fin K) (m : ℕ)
    {B : Set ℝ} (hB : MeasurableSet B) (T : ℕ) :
    ∫⁻ h, Wc j m B h ∂(banditMeasure ν π T) = ν.P j B * ∫⁻ h, Mc j m h ∂(banditMeasure ν π T) := by
  classical
  induction T with
  | zero =>
    simp [Wc, Mc, armPullCount, banditMeasure.eq_1]
  | succ T ih =>
    rw [lintegral_succ ν π T (measurable_Wc j m hB (T + 1)),
      lintegral_succ ν π T (measurable_Mc j m (T + 1))]
    simp_rw [Wc_snoc, Mc_snoc]
    have hW : ∀ h : BanditHistory K T,
        ∫⁻ p, (Wc j m B h + if p.1 = j ∧ armPullCount j h < m ∧ p.2 ∈ B then 1 else 0)
          ∂(banditStepKernel ν π T h) =
        Wc j m B h + (if armPullCount j h < m then ν.P j B else 0) * π.select T h {j} := by
      intro h
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      congr 1
      convert step_inc_W ν π T j (armPullCount j h < m) hB h
    have hM : ∀ h : BanditHistory K T,
        ∫⁻ p, (Mc j m h + if p.1 = j ∧ armPullCount j h < m then 1 else 0)
          ∂(banditStepKernel ν π T h) =
        Mc j m h + (if armPullCount j h < m then 1 else 0) * π.select T h {j} := by
      intro h
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      congr 1
      convert step_inc_M ν π T j (armPullCount j h < m) h
    simp_rw [hW, hM]
    have hsel : Measurable (fun h : BanditHistory K T => π.select T h {j}) :=
      (π.select T).measurable_coe (MeasurableSet.singleton j)
    have hind : Measurable (fun h : BanditHistory K T =>
        (if armPullCount j h < m then (1 : ℝ≥0∞) else 0)) := by
      refine Measurable.ite ?_ measurable_const measurable_const
      exact measurable_armPullCount j (t := {n : ℕ | n < m}) MeasurableSet.of_discrete
    have heq : ∀ h : BanditHistory K T,
        (if armPullCount j h < m then ν.P j B else 0) * π.select T h {j} =
          ν.P j B * ((if armPullCount j h < m then 1 else 0) * π.select T h {j}) := by
      intro h; split_ifs <;> simp
    simp_rw [heq]
    rw [lintegral_add_left (measurable_Wc j m hB T), lintegral_add_left (measurable_Mc j m T),
      lintegral_const_mul (ν.P j B)
        (f := fun h => (if armPullCount j h < m then (1 : ℝ≥0∞) else 0) * π.select T h {j})
        (hind.mul hsel), ih, mul_add]

/-- Union bound over the first `m` plays of arm `j`. -/
lemma first_plays_bound (ν : StochasticBandit K) (π : BanditPolicy K) (j : Fin K) (m : ℕ)
    {B : Set ℝ} (hB : MeasurableSet B) (T : ℕ) :
    banditMeasure ν π T {h | ∃ t, (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B} ≤
      m * ν.P j B := by
  classical
  calc banditMeasure ν π T {h | ∃ t, (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B}
      ≤ ∫⁻ h, Wc j m B h ∂(banditMeasure ν π T) := by
        rw [← lintegral_indicator_one₀ ?_]
        · apply lintegral_mono
          intro h
          by_cases hh : h ∈ {h : BanditHistory K T | ∃ t, (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B}
          · rw [Set.indicator_of_mem hh]
            obtain ⟨t, ht⟩ := hh
            unfold Wc
            calc (1 : BanditHistory K T → ℝ≥0∞) h = (if (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B then 1 else 0) := by
                  simp [ht]
              _ ≤ _ := Finset.single_le_sum (f := fun t => (if (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B then (1 : ℝ≥0∞) else 0))
                    (fun _ _ => bot_le) (Finset.mem_univ t)
          · rw [Set.indicator_of_notMem hh]; exact bot_le
        · refine (MeasurableSet.nullMeasurableSet ?_)
          have : {h : BanditHistory K T | ∃ t, (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B} =
              ⋃ t, {h | (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B} := by ext h; simp
          rw [this]
          refine MeasurableSet.iUnion (fun t => ?_)
          have hmeas := measurable_Wc j m hB T
          have h1 : MeasurableSet {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t < m} := by
            have : {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t < m} =
                (fun h : BanditHistory K T => fun t => (h t).1) ⁻¹'
                  {a : Fin T → Fin K | a t = j ∧
                    (∑ s : Fin T, if s < t ∧ a s = j then 1 else 0) < m} := by
              ext h; simp [cntBefore]
            rw [this]
            exact measurable_arms (Set.to_countable _).measurableSet
          have h2 : MeasurableSet {h : BanditHistory K T | (h t).2 ∈ B} :=
            (measurable_snd.comp (measurable_pi_apply t)) hB
          have : {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t < m ∧ (h t).2 ∈ B} =
              {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t < m} ∩
                {h : BanditHistory K T | (h t).2 ∈ B} := by
            ext h; simp [and_assoc]
          rw [this]; exact h1.inter h2
    _ = ν.P j B * ∫⁻ h, Mc j m h ∂(banditMeasure ν π T) := lintegral_Wc ν π j m hB T
    _ ≤ ν.P j B * m := by
        gcongr
        calc ∫⁻ h, Mc j m h ∂(banditMeasure ν π T) ≤ ∫⁻ _h, (m : ℝ≥0∞) ∂(banditMeasure ν π T) := by
              apply lintegral_mono; intro h; unfold Mc; show _ ≤ (m : ℝ≥0∞); exact_mod_cast min_le_right (armPullCount j h) m
          _ = m := by simp
    _ = m * ν.P j B := mul_comm _ _

end CTL6Aux

namespace CTL6Aux

variable {K : ℕ}

open Classical

lemma cntBefore_lt (j : Fin K) {T : ℕ} (h : BanditHistory K T) (t : Fin T) (ht : (h t).1 = j) :
    cntBefore j h t < armPullCount j h := by
  rw [armPullCount_eq_sum]
  unfold cntBefore
  have key : ∀ s : Fin T, (if s < t ∧ (h s).1 = j then 1 else 0) + (if s = t then 1 else 0) ≤
      (if (h s).1 = j then 1 else 0) := by
    intro s
    by_cases hs : s = t
    · subst hs; simp [ht]
    · by_cases h1 : (h s).1 = j
      · simp only [hs, h1, and_true, if_false, add_zero, if_true]
        split_ifs <;> omega
      · simp [hs, h1]
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => key s)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  omega

lemma sum_pulls {T : ℕ} (h : BanditHistory K T) : ∑ a : Fin K, armPullCount a h = T := by
  simp_rw [armPullCount_eq_sum]
  rw [Finset.sum_comm]
  simp

lemma prod_ite_pow {T : ℕ} (p : Fin T → Prop) (a : ℝ≥0∞) :
    ∏ t, (if p t then a else 1) = a ^ (Finset.univ.filter p).card := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

end CTL6Aux

open CTL6Aux in
theorem solution {K : ℕ} (M : Set (Measure ℝ))
    (hM : ∀ Q ∈ M, IsProbabilityMeasure Q ∧ Integrable id Q)
    (f : ℝ → ℝ) (hf_pos : ∀ t : ℝ, 1 < t → 0 < f t) (hf_mono : MonotoneOn f (Set.Ioi 1))
    (hf_log : ∀ a : ℝ, a < 1 → ∀ᶠ t : ℝ in atTop, a * Real.log t ≤ f t)
    (hf_o : Tendsto (fun t : ℝ => f t / t) atTop (𝓝 0))
    (π : BanditPolicy K) (𝓔 : Set (StochasticBandit K))
    (h𝓔M : ∀ ν ∈ 𝓔, ∀ j, ν.P j ∈ M)
    (h31 : ∀ ν ∈ 𝓔, ∀ i, 0 < banditGap ν i → ∀ a : ℝ, a < 1 → ∀ᶠ T : ℕ in atTop,
      banditMeasure ν π T {h | (T : ℝ) / K < (armPullCount i h : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(a * f T))))
    (ν : StochasticBandit K) (hν : ν ∈ 𝓔) (i : Fin K) (hi : 0 < banditGap ν i)
    (hclosed : ∀ (Q : Measure ℝ) (hQ : IsProbabilityMeasure Q), Q ∈ M →
      banditOptimalMean ν < ∫ x, x ∂Q → replaceArm ν i Q hQ ∈ 𝓔)
    (hfin : banditDInf M (ν.P i) (banditOptimalMean ν) < ⊤) :
    ∀ m : ℕ, Tendsto (fun T : ℕ => banditMeasure ν π T {h | armPullCount i h ≤ m})
      atTop (𝓝 0) := by
  intro m
  -- an alternative law `Q` for arm `i` with mean above `µ*` and finite divergence
  obtain ⟨Q, hQ, hQlt⟩ : ∃ Q ∈ {Q ∈ M | banditOptimalMean ν < ∫ x, x ∂Q},
      InformationTheory.klDiv (ν.P i) Q < ⊤ := by
    unfold banditDInf at hfin
    simp only [iInf_lt_iff] at hfin
    obtain ⟨Q, hQ, h⟩ := hfin
    exact ⟨Q, hQ, h⟩
  obtain ⟨hQM, hQmean⟩ := hQ
  haveI hQprob : IsProbabilityMeasure Q := (hM Q hQM).1
  set ν₁ := replaceArm ν i Q hQprob with hν₁def
  have hν₁ : ν₁ ∈ 𝓔 := hclosed Q hQprob hQM hQmean
  have hac : ν.P i ≪ Q := (InformationTheory.klDiv_ne_top_iff.1 hQlt.ne).1
  set ρ : ℝ → ℝ≥0∞ := Q.rnDeriv (ν.P i) with hρ
  have hρm : Measurable ρ := Measure.measurable_rnDeriv _ _
  have hρpos : ∀ᵐ x ∂(ν.P i), 0 < ρ x := Measure.rnDeriv_pos' hac
  have hν₁i : ν₁.P i = Q := by simp [hν₁def, replaceArm]
  have hν₁j : ∀ j, j ≠ i → ν₁.P j = ν.P j := fun j hj => by
    simp [hν₁def, replaceArm, Function.update_of_ne hj]
  have hle : ∀ j, banditArmMean ν j ≤ banditOptimalMean ν :=
    fun j => le_ciSup (Set.finite_range _).bddAbove j
  have hgap₁ : ∀ j, j ≠ i → 0 < banditGap ν₁ j := by
    intro j hj
    unfold banditGap
    have h1 : banditArmMean ν₁ i ≤ banditOptimalMean ν₁ :=
      le_ciSup (Set.finite_range _).bddAbove i
    have h2 : banditArmMean ν₁ j = banditArmMean ν j := by
      unfold banditArmMean; rw [hν₁j j hj]
    have h3 : banditArmMean ν₁ i = ∫ x, x ∂Q := by
      unfold banditArmMean; rw [hν₁i]
    rw [h2]; rw [h3] at h1; linarith [hle j]
  -- `f(T) → ∞`, so the bound (31) tends to zero
  have hf_inf : Tendsto (fun T : ℕ => f T) atTop atTop := by
    have h1 : ∀ᶠ T : ℕ in atTop, (1 / 2) * Real.log T ≤ f T :=
      tendsto_natCast_atTop_atTop.eventually (hf_log (1 / 2) (by norm_num))
    exact tendsto_atTop_mono' _ h1
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num))
  have hexp : Tendsto (fun T : ℕ => ENNReal.ofReal (Real.exp (-((1 / 2) * f T)))) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hf_inf.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal this
  set u : ℕ → ℝ≥0∞ := fun T => ∑ j ∈ Finset.univ.erase i,
    banditMeasure ν₁ π T {h | (T : ℝ) / K < (armPullCount j h : ℝ)} with hu_def
  have hu : Tendsto u atTop (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ∑ j ∈ Finset.univ.erase i, (0 : ℝ≥0∞) by simp]
    apply tendsto_finsetSum
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
      (Eventually.of_forall (fun _ => bot_le)) (h31 ν₁ hν₁ j (hgap₁ j hji) (1 / 2) (by norm_num))
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : ε / 2 ≠ 0 := by simp [hε.ne']
  -- choose the threshold `c`
  obtain ⟨c, hc0, hc1, hcm⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      (m : ℝ≥0∞) * (ν.P i) {x | ρ x < ENNReal.ofReal c} ≤ ε / 2 := by
    by_cases hm0 : m = 0
    · exact ⟨1, one_pos, le_rfl, by simp [hm0]⟩
    set A : ℕ → Set ℝ := fun n => {x | ρ x < ENNReal.ofReal (1 / ((n : ℝ) + 1))} with hA
    have hAm : ∀ n, MeasurableSet (A n) := fun n => measurableSet_lt hρm measurable_const
    have hanti : Antitone A := by
      intro n n' hnn' x hx
      simp only [hA, Set.mem_ofPred_eq] at hx ⊢
      refine lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal ?_)
      have : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
      gcongr
    have hInter : (ν.P i) (⋂ n, A n) = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 hρpos)
      intro x hx
      simp only [Set.mem_iInter, hA, Set.mem_ofPred_eq] at hx
      simp only [Set.mem_ofPred_eq, not_lt, nonpos_iff_eq_zero]
      by_contra hne
      by_cases htop : ρ x = ⊤
      · exact absurd (hx 0) (by rw [htop]; exact not_lt.2 le_top)
      have hpos : 0 < (ρ x).toReal := ENNReal.toReal_pos hne htop
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      have := hx n
      rw [← ENNReal.ofReal_toReal htop] at this
      have := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 this
      linarith
    have hlim := tendsto_measure_iInter_atTop (μ := ν.P i)
      (fun n => (hAm n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    rw [hInter] at hlim
    have hpos : 0 < ε / 2 / m := by
      apply ENNReal.div_pos hε2; simp
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hpos)).exists
    refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_, ?_⟩
    · rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · calc (m : ℝ≥0∞) * (ν.P i) (A n) ≤ m * (ε / 2 / m) := by gcongr; exact hn.le
        _ = ε / 2 := ENNReal.mul_div_cancel (by simp [hm0]) (by simp)
  have hcpos : ENNReal.ofReal c ^ m ≠ 0 := by
    apply pow_ne_zero; simp [hc0]
  have hctop : ENNReal.ofReal c ^ m ≠ ⊤ := by
    apply ENNReal.pow_ne_top; simp
  have hthr : 0 < ε / 2 * ENNReal.ofReal c ^ m := by
    apply ENNReal.mul_pos hε2 hcpos
  have hev := (tendsto_order.1 hu).2 _ hthr
  filter_upwards [hev, eventually_gt_atTop (K * m)] with T hT hTKm
  -- the events
  set Bad : Set ℝ := {x | ρ x < ENNReal.ofReal c} with hBad
  have hBadm : MeasurableSet Bad := measurableSet_lt hρm measurable_const
  set Bs : Set (BanditHistory K T) := {h | ∀ t, (h t).1 = i → ENNReal.ofReal c ≤ ρ (h t).2}
    with hBs
  set Nm : Set (BanditHistory K T) := {h | armPullCount i h ≤ m} with hNm
  set G := Nm ∩ Bs with hG
  set U : Set (BanditHistory K T) :=
    {h | ∃ t, (h t).1 = i ∧ cntBefore i h t < m ∧ (h t).2 ∈ Bad} with hU
  have hNmm : MeasurableSet Nm :=
    measurable_armPullCount i (t := {n : ℕ | n ≤ m}) MeasurableSet.of_discrete
  have hBsm : MeasurableSet Bs := by
    have : Bs = ⋂ t : Fin T, ({h : BanditHistory K T | (h t).1 = i}ᶜ ∪
        {h | ENNReal.ofReal c ≤ ρ (h t).2}) := by
      ext h; simp only [hBs, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
      constructor
      · intro hh t; by_cases ht : (h t).1 = i
        · exact Or.inr (hh t ht)
        · exact Or.inl ht
      · intro hh t ht; rcases hh t with h1 | h1
        · exact absurd ht h1
        · exact h1
    rw [this]
    refine MeasurableSet.iInter (fun t => ?_)
    refine MeasurableSet.union (MeasurableSet.compl ?_) ?_
    · exact (measurable_fst.comp (measurable_pi_apply t)) (MeasurableSet.singleton i)
    · exact measurableSet_le measurable_const (hρm.comp (measurable_snd.comp (measurable_pi_apply t)))
  have hGm : MeasurableSet G := hNmm.inter hBsm
  -- (a) split
  have hsplit : Nm ⊆ G ∪ U := by
    intro h hh
    by_cases hb : h ∈ Bs
    · exact Or.inl ⟨hh, hb⟩
    · right
      simp only [hBs, Set.mem_ofPred_eq, not_forall, not_le] at hb
      obtain ⟨t, ht, hlt⟩ := hb
      refine ⟨t, ht, ?_, hlt⟩
      have := cntBefore_lt i h t ht
      have hh' : armPullCount i h ≤ m := hh
      omega
  have hUb : banditMeasure ν π T U ≤ ε / 2 :=
    le_trans (first_plays_bound ν π i m hBadm T) hcm
  -- (b) change of measure
  have hcom := (FragileBandit.CauchyTail.change_of_measure π ν₁ ν {i}
    (fun j hj => hν₁j j (by simpa using hj)) T G hGm).1
  have hlow : ENNReal.ofReal c ^ m * banditMeasure ν π T G ≤
      ∫⁻ h in G, ∏ t : Fin T,
        (if (h t).1 ∈ ({i} : Finset (Fin K)) then
          (ν₁.P (h t).1).rnDeriv (ν.P (h t).1) (h t).2 else 1) ∂(banditMeasure ν π T) := by
    rw [← setLIntegral_const]
    apply setLIntegral_mono' hGm
    intro h hh
    obtain ⟨hhN, hhB⟩ := hh
    calc ENNReal.ofReal c ^ m ≤ ENNReal.ofReal c ^ armPullCount i h :=
          pow_le_pow_of_le_one (by simp) (by simpa using hc1) hhN
      _ = ∏ t : Fin T, (if (h t).1 = i then ENNReal.ofReal c else 1) := by
          rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
          congr 1
          unfold armPullCount
          simp [Set.toFinset_ofPred]
      _ ≤ _ := by
          apply Finset.prod_le_prod'
          intro t _
          by_cases ht : (h t).1 = i
          · have hmem : (h t).1 ∈ ({i} : Finset (Fin K)) := by simp [ht]
            rw [if_pos ht, if_pos hmem, ht, hν₁i]
            exact hhB t ht
          · have hmem : (h t).1 ∉ ({i} : Finset (Fin K)) := by simp [ht]
            rw [if_neg ht, if_neg hmem]
  have hGC : banditMeasure ν₁ π T G ≤ u T := by
    have hsub : G ⊆ ⋃ j ∈ Finset.univ.erase i, {h : BanditHistory K T | (T : ℝ) / K < (armPullCount j h : ℝ)} := by
      intro h hh
      have hN : armPullCount i h ≤ m := hh.1
      by_contra hcon
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hcon
      have hK : (0 : ℝ) < K := by
        have : 0 < K := Fin.pos i
        exact_mod_cast this
      have hsum := sum_pulls h
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
      have hle2 : (∑ j ∈ Finset.univ.erase i, (armPullCount j h : ℝ)) ≤
          ∑ _j ∈ Finset.univ.erase i, (T : ℝ) / K :=
        Finset.sum_le_sum (fun j hj => hcon j hj)
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] at hle2
      have hsumR : (armPullCount i h : ℝ) + ∑ j ∈ Finset.univ.erase i, (armPullCount j h : ℝ) = T := by
        exact_mod_cast hsum
      have hNR : (armPullCount i h : ℝ) ≤ m := by exact_mod_cast hN
      have hTKm' : (K : ℝ) * m < T := by exact_mod_cast hTKm
      have hK1 : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
        rw [Nat.cast_sub (Fin.pos i)]; simp
      rw [hK1] at hle2
      have : (T : ℝ) ≤ m + ((K : ℝ) - 1) * (T / K) := by linarith
      have h3 : ((K : ℝ) - 1) * (T / K) = T - T / K := by field_simp
      rw [h3] at this
      have h4 : (T : ℝ) / K ≤ m := by linarith
      rw [div_le_iff₀ hK] at h4
      linarith
    calc banditMeasure ν₁ π T G ≤ banditMeasure ν₁ π T (⋃ j ∈ Finset.univ.erase i,
          {h : BanditHistory K T | (T : ℝ) / K < (armPullCount j h : ℝ)}) := measure_mono hsub
      _ ≤ u T := measure_biUnion_finset_le _ _
  have hGb : banditMeasure ν π T G ≤ ε / 2 := by
    have h1 : ENNReal.ofReal c ^ m * banditMeasure ν π T G ≤
        ENNReal.ofReal c ^ m * (ε / 2) := by
      calc _ ≤ _ := hlow
        _ ≤ banditMeasure ν₁ π T G := hcom
        _ ≤ u T := hGC
        _ ≤ ε / 2 * ENNReal.ofReal c ^ m := hT.le
        _ = _ := mul_comm _ _
    exact (ENNReal.mul_le_mul_iff_right hcpos hctop).1 h1
  calc banditMeasure ν π T {h | armPullCount i h ≤ m} ≤ banditMeasure ν π T (G ∪ U) :=
        measure_mono hsplit
    _ ≤ banditMeasure ν π T G + banditMeasure ν π T U := measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hGb hUb
    _ = ε := ENNReal.add_halves ε
