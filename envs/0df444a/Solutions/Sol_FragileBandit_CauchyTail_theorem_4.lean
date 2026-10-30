-- Prove2me | solution 1 for FragileBandit.CauchyTail.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T12:52:45.636867+00:00
-- url     : https://prove2.me/submissions/9f101971-6fac-40f0-b3c0-85e48f665785

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting
import Theorems.Thm_FragileBandit_CauchyTail_change_of_measure
import Theorems.Thm_FragileBandit_CauchyTail_lemma_6
import Theorems.Thm_FragileBandit_CauchyTail_random_index_wlln

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm FragileBandit.CauchyTail
open scoped ENNReal Topology

namespace CTT4Aux

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

end CTT4Aux

namespace CTT4Aux

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

end CTT4Aux


namespace CTT4Aux

variable {K : ℕ}

open Classical

lemma cntBefore_le {T : ℕ} (j : Fin K) (h : BanditHistory K T) (t : Fin T) : cntBefore j h t ≤ T := by
  unfold cntBefore
  calc (∑ s : Fin T, if s < t ∧ (h s).1 = j then 1 else 0) ≤ ∑ _s : Fin T, 1 :=
        Finset.sum_le_sum (fun s _ => by split_ifs <;> simp)
    _ = T := by simp

lemma measurable_rewardSum {T : ℕ} (j : Fin K) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (fun h : BanditHistory K T =>
      ∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = j), φ (h t).2) := by
  have : (fun h : BanditHistory K T =>
      ∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = j), φ (h t).2) =
      fun h => ∑ t : Fin T, if (h t).1 = j then φ (h t).2 else 0 := by
    funext h; rw [Finset.sum_filter]
  rw [this]
  refine Finset.measurable_sum _ (fun t _ => Measurable.ite ?_ ?_ measurable_const)
  · exact (measurable_fst.comp (measurable_pi_apply t)) (MeasurableSet.singleton j)
  · exact hφ.comp (measurable_snd.comp (measurable_pi_apply t))

end CTT4Aux

open CTT4Aux in
lemma part32 {K : ℕ} (M : Set (Measure ℝ))
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
    (c : ℝ) (hc : ENNReal.ofReal c * banditDInf M (ν.P i) (banditOptimalMean ν) < 1) :
    Tendsto (fun T : ℕ => banditMeasure ν π T {h | c * f T ≤ (armPullCount i h : ℝ)})
      atTop (𝓝 1) := by
  classical
  by_cases hc0 : c ≤ 0
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 2] with T hT
    have hT' : (1 : ℝ) < T := by
      have : (2 : ℝ) ≤ T := by exact_mod_cast hT
      linarith
    have hfT : 0 < f T := hf_pos T hT'
    have : {h : BanditHistory K T | c * f T ≤ (armPullCount i h : ℝ)} = Set.univ := by
      ext h
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      have : c * f T ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc0 hfT.le
      linarith [(Nat.cast_nonneg (armPullCount i h) : (0 : ℝ) ≤ _)]
    rw [this, measure_univ]
  push_neg at hc0
  set D := banditDInf M (ν.P i) (banditOptimalMean ν) with hDdef
  have hDtop : D ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (by simp [hc0])] at hc
    exact absurd hc (by simp)
  have hDlt : D < ENNReal.ofReal (1 / c) := by
    have hc' := hc
    rw [← ENNReal.ofReal_toReal hDtop, ← ENNReal.ofReal_mul hc0.le, ← ENNReal.ofReal_one,
      ENNReal.ofReal_lt_ofReal_iff one_pos] at hc'
    rw [← ENNReal.ofReal_toReal hDtop]
    refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
    rw [lt_div_iff₀ hc0]; linarith
  obtain ⟨Q, hQ, hQlt⟩ : ∃ Q ∈ {Q ∈ M | banditOptimalMean ν < ∫ x, x ∂Q},
      InformationTheory.klDiv (ν.P i) Q < ENNReal.ofReal (1 / c) := by
    rw [hDdef] at hDlt
    unfold banditDInf at hDlt
    simp only [iInf_lt_iff] at hDlt
    obtain ⟨Q, hQ, h⟩ := hDlt
    exact ⟨Q, hQ, h⟩
  obtain ⟨hQM, hQmean⟩ := hQ
  haveI hQprob : IsProbabilityMeasure Q := (hM Q hQM).1
  have hKLtop : InformationTheory.klDiv (ν.P i) Q ≠ ⊤ := ne_top_of_lt hQlt
  obtain ⟨hac, hllr⟩ := InformationTheory.klDiv_ne_top_iff.1 hKLtop
  set κ : ℝ := (InformationTheory.klDiv (ν.P i) Q).toReal with hκdef
  have hκ0 : 0 ≤ κ := ENNReal.toReal_nonneg
  have hcκ : c * κ < 1 := by
    have h1 := (ENNReal.toReal_lt_toReal hKLtop ENNReal.ofReal_ne_top).2 hQlt
    rw [ENNReal.toReal_ofReal (by positivity), lt_div_iff₀ hc0] at h1
    rw [← hκdef] at h1; linarith
  set δ : ℝ := (1 - c * κ) / (4 * c) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; apply div_pos <;> linarith
  set a : ℝ := (1 + c * κ) / 2 with hadef
  have ha1 : a < 1 := by rw [hadef]; linarith
  set b : ℝ := c * (κ + δ) with hbdef
  have hcδ : c * δ = (1 - c * κ) / 4 := by rw [hδdef]; field_simp
  have hab : b < a := by rw [hbdef, hadef, mul_add, hcδ]; linarith
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  -- the alternative environment
  set ν₁ := replaceArm ν i Q hQprob with hν₁def
  have hν₁ : ν₁ ∈ 𝓔 := hclosed Q hQprob hQM hQmean
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
  -- the log-likelihood ratio and its WLLN
  set ρ : ℝ → ℝ≥0∞ := Q.rnDeriv (ν.P i) with hρ
  have hρm : Measurable ρ := Measure.measurable_rnDeriv _ _
  set φ : ℝ → ℝ := fun x => Real.log (ρ x).toReal with hφdef
  have hφm : Measurable φ := Real.measurable_log.comp (ENNReal.measurable_toReal.comp hρm)
  have hφeq : φ =ᵐ[ν.P i] fun x => -(MeasureTheory.llr (ν.P i) Q x) := by
    filter_upwards [Measure.inv_rnDeriv hac] with x hx
    simp only [hφdef, hρ, MeasureTheory.llr_def]
    rw [← hx, Pi.inv_apply, ENNReal.toReal_inv, Real.log_inv]
  have hφint : Integrable φ (ν.P i) := hllr.neg.congr hφeq.symm
  have hφmean : ∫ y, φ y ∂(ν.P i) = -κ := by
    rw [integral_congr_ae hφeq, integral_neg, hκdef,
      InformationTheory.toReal_klDiv_of_measure_eq hac (by simp)]
  have hN := FragileBandit.CauchyTail.lemma_6 M hM f hf_pos hf_mono hf_log hf_o π 𝓔 h𝓔M h31
    ν hν i hi hclosed (lt_top_iff_ne_top.2 hDtop)
  have hW := FragileBandit.CauchyTail.random_index_wlln ν π i φ hφm hφint hN δ hδ
  rw [hφmean] at hW
  -- the null set of bad rewards
  set Null : Set ℝ := {x | ρ x = 0} ∪ {x | ρ x = ⊤} with hNull
  have hNullm : MeasurableSet Null :=
    (measurableSet_eq_fun hρm measurable_const).union (measurableSet_eq_fun hρm measurable_const)
  have hNull0 : (ν.P i) Null = 0 := by
    have h1 : ∀ᵐ x ∂(ν.P i), 0 < ρ x := Measure.rnDeriv_pos' hac
    have h2 : ∀ᵐ x ∂(ν.P i), ρ x < ⊤ := Measure.rnDeriv_lt_top Q (ν.P i)
    have : ∀ᵐ x ∂(ν.P i), x ∉ Null := by
      filter_upwards [h1, h2] with x hx1 hx2
      simp only [hNull, Set.mem_union, Set.mem_ofPred_eq, not_or]
      exact ⟨hx1.ne', hx2.ne⟩
    exact measure_mono_null (fun x hx => not_not.2 hx) (ae_iff.1 this)
  -- `c f(T) ≤ T / K` eventually
  have hKpos : (0 : ℝ) < K := by
    have : 0 < K := Fin.pos i
    exact_mod_cast this
  have hfT : ∀ᶠ T : ℕ in atTop, c * f T ≤ (T : ℝ) / K := by
    have h1 := hf_o.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / (c * K) by positivity))
    have h2 := tendsto_natCast_atTop_atTop.eventually (h1.and (eventually_gt_atTop (0 : ℝ)))
    filter_upwards [h2] with T hT
    obtain ⟨hT1, hT0⟩ := hT
    rw [div_le_iff₀ hT0] at hT1
    rw [le_div_iff₀ hKpos]
    have hcK : 0 < c * K := by positivity
    calc c * f T * K = (c * K) * f T := by ring
      _ ≤ (c * K) * (1 / (c * K) * T) := mul_le_mul_of_nonneg_left hT1 hcK.le
      _ = T := by field_simp
  have h31all : ∀ᶠ T : ℕ in atTop, ∀ j ∈ Finset.univ.erase i,
      banditMeasure ν₁ π T {h | (T : ℝ) / K < (armPullCount j h : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(a * f T))) := by
    rw [Filter.eventually_all_finset]
    intro j hj
    exact h31 ν₁ hν₁ j (hgap₁ j (Finset.ne_of_mem_erase hj)) a ha1
  -- the bound on `A_T = {N_i(T) < c f(T)}`
  have hmain : ∀ᶠ T : ℕ in atTop,
      banditMeasure ν π T {h | (armPullCount i h : ℝ) < c * f T} ≤
        ENNReal.ofReal ((K - 1 : ℝ) * Real.exp (-((a - b) * f T))) +
        banditMeasure ν π T {h | δ < |(∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = i),
          φ (h t).2) / (armPullCount i h : ℝ) - -κ|} := by
    filter_upwards [hfT, h31all] with T hT1 hT2
    set A : Set (BanditHistory K T) := {h | (armPullCount i h : ℝ) < c * f T} with hA
    set Bv : Set (BanditHistory K T) := {h | δ < |(∑ t ∈ Finset.univ.filter
      (fun t : Fin T => (h t).1 = i), φ (h t).2) / (armPullCount i h : ℝ) - -κ|} with hBv
    set Gd : Set (BanditHistory K T) := {h | ∀ t, (h t).1 = i → (h t).2 ∉ Null} with hGd
    set H := A ∩ Bvᶜ ∩ Gd with hH
    have hAm : MeasurableSet A :=
      measurable_armPullCount i (t := {n : ℕ | (n : ℝ) < c * f T}) MeasurableSet.of_discrete
    have hBvm : MeasurableSet Bv := by
      have hS := measurable_rewardSum (T := T) i hφm
      have hNm : Measurable (fun h : BanditHistory K T => (armPullCount i h : ℝ)) :=
        (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (measurable_armPullCount i)
      exact measurableSet_lt measurable_const (((hS.div hNm).sub measurable_const).abs)
    have hGdm : MeasurableSet Gd := by
      have : Gd = ⋂ t : Fin T, ({h : BanditHistory K T | (h t).1 = i}ᶜ ∪
          {h | (h t).2 ∉ Null}) := by
        ext h; simp only [hGd, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
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
      · exact ((measurable_snd.comp (measurable_pi_apply t)) hNullm).compl
    have hHm : MeasurableSet H := (hAm.inter hBvm.compl).inter hGdm
    -- Gdᶜ is null
    have hGd0 : banditMeasure ν π T Gdᶜ = 0 := by
      refine le_antisymm ?_ bot_le
      calc banditMeasure ν π T Gdᶜ ≤ banditMeasure ν π T
            {h | ∃ t, (h t).1 = i ∧ cntBefore i h t < T + 1 ∧ (h t).2 ∈ Null} := by
            apply measure_mono
            intro h hh
            simp only [hGd, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not] at hh
            obtain ⟨t, ht, hn⟩ := hh
            exact ⟨t, ht, Nat.lt_succ_of_le (cntBefore_le i h t), hn⟩
        _ ≤ (T + 1 : ℕ) * ν.P i Null := first_plays_bound ν π i (T + 1) hNullm T
        _ = 0 := by rw [hNull0, mul_zero]
    -- lower bound on the likelihood ratio over H
    have hlow : ENNReal.ofReal (Real.exp (-(b * f T))) * banditMeasure ν π T H ≤
        ∫⁻ h in H, ∏ t : Fin T,
          (if (h t).1 ∈ ({i} : Finset (Fin K)) then
            (ν₁.P (h t).1).rnDeriv (ν.P (h t).1) (h t).2 else 1) ∂(banditMeasure ν π T) := by
      rw [← setLIntegral_const]
      apply setLIntegral_mono' hHm
      intro h hh
      obtain ⟨⟨hhA, hhB⟩, hhG⟩ := hh
      have hprod : (∏ t : Fin T,
          (if (h t).1 ∈ ({i} : Finset (Fin K)) then
            (ν₁.P (h t).1).rnDeriv (ν.P (h t).1) (h t).2 else 1)) =
          ENNReal.ofReal (Real.exp (∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = i),
            φ (h t).2)) := by
        rw [Finset.sum_filter, Real.exp_sum,
          ENNReal.ofReal_prod_of_nonneg (fun t _ => (Real.exp_pos _).le)]
        apply Finset.prod_congr rfl
        intro t _
        by_cases ht : (h t).1 = i
        · have hmem : (h t).1 ∈ ({i} : Finset (Fin K)) := by simp [ht]
          rw [if_pos hmem, if_pos ht, ht, hν₁i]
          have hng := hhG t ht
          simp only [hNull, Set.mem_union, Set.mem_ofPred_eq, not_or] at hng
          have hpos : 0 < (ρ (h t).2).toReal := ENNReal.toReal_pos hng.1 hng.2
          simp only [hφdef]
          rw [Real.exp_log hpos, ENNReal.ofReal_toReal hng.2]
        · have hmem : (h t).1 ∉ ({i} : Finset (Fin K)) := by simp [ht]
          rw [if_neg hmem, if_neg ht, Real.exp_zero, ENNReal.ofReal_one]
      rw [hprod]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      have hB' : |(∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = i), φ (h t).2) /
          (armPullCount i h : ℝ) - -κ| ≤ δ := by
        simp only [hBv, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hhB; exact hhB
      have hA' : (armPullCount i h : ℝ) < c * f T := hhA
      set S := ∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = i), φ (h t).2 with hSdef
      set N : ℝ := (armPullCount i h : ℝ) with hNdef
      have hN0 : 0 ≤ N := Nat.cast_nonneg _
      have hS : -(κ + δ) * N ≤ S := by
        by_cases hNz : N = 0
        · have hcard : armPullCount i h = 0 := by
            have h0 : (armPullCount i h : ℝ) = 0 := hNz
            exact_mod_cast h0
          have hempty : Finset.univ.filter (fun t : Fin T => (h t).1 = i) = ∅ := by
            unfold armPullCount at hcard
            rw [Set.toFinset_ofPred] at hcard
            exact Finset.card_eq_zero.1 (by convert hcard)
          rw [hSdef, hempty, Finset.sum_empty, hNz, mul_zero]
        · have hNpos : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hNz)
          have h1 := (abs_le.1 hB').1
          have h2 : -(κ + δ) ≤ S / N := by linarith
          rw [le_div_iff₀ hNpos] at h2
          linarith
      have : -(κ + δ) * (c * f T) ≤ -(κ + δ) * N := by
        apply mul_le_mul_of_nonpos_left hA'.le; linarith
      have hbf : -(b * f T) = -(κ + δ) * (c * f T) := by rw [hbdef]; ring
      rw [hbf]; linarith
    have hcom := (FragileBandit.CauchyTail.change_of_measure π ν₁ ν {i}
      (fun j hj => hν₁j j (by simpa using hj)) T H hHm).1
    -- H ⊆ C_T
    have hsub : H ⊆ ⋃ j ∈ Finset.univ.erase i,
        {h : BanditHistory K T | (T : ℝ) / K < (armPullCount j h : ℝ)} := by
      intro h hh
      have hN : (armPullCount i h : ℝ) < c * f T := hh.1.1
      by_contra hcon
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hcon
      have hsum := sum_pulls h
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
      have hle2 : (∑ j ∈ Finset.univ.erase i, (armPullCount j h : ℝ)) ≤
          ∑ _j ∈ Finset.univ.erase i, (T : ℝ) / K :=
        Finset.sum_le_sum (fun j hj => hcon j hj)
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] at hle2
      have hsumR : (armPullCount i h : ℝ) + ∑ j ∈ Finset.univ.erase i, (armPullCount j h : ℝ) = T := by
        exact_mod_cast hsum
      have hK1 : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
        rw [Nat.cast_sub (Fin.pos i)]; simp
      rw [hK1] at hle2
      have h3 : ((K : ℝ) - 1) * (T / K) = T - T / K := by field_simp
      rw [h3] at hle2
      linarith
    have hC : banditMeasure ν₁ π T H ≤
        ENNReal.ofReal ((K - 1 : ℝ) * Real.exp (-(a * f T))) := by
      calc banditMeasure ν₁ π T H ≤ banditMeasure ν₁ π T (⋃ j ∈ Finset.univ.erase i,
            {h : BanditHistory K T | (T : ℝ) / K < (armPullCount j h : ℝ)}) := measure_mono hsub
        _ ≤ ∑ j ∈ Finset.univ.erase i,
            banditMeasure ν₁ π T {h | (T : ℝ) / K < (armPullCount j h : ℝ)} :=
            measure_biUnion_finset_le _ _
        _ ≤ ∑ _j ∈ Finset.univ.erase i, ENNReal.ofReal (Real.exp (-(a * f T))) :=
            Finset.sum_le_sum hT2
        _ = ENNReal.ofReal ((K - 1 : ℝ) * Real.exp (-(a * f T))) := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul, ENNReal.ofReal_mul (by
                have : (1 : ℝ) ≤ K := by exact_mod_cast Fin.pos i
                linarith)]
            congr 1
            rw [← ENNReal.ofReal_natCast, Nat.cast_sub (Fin.pos i)]
            simp
    have hHb : banditMeasure ν π T H ≤
        ENNReal.ofReal ((K - 1 : ℝ) * Real.exp (-((a - b) * f T))) := by
      have hx0 : ENNReal.ofReal (Real.exp (-(b * f T))) ≠ 0 := by
        simp [Real.exp_pos]
      have h1 : ENNReal.ofReal (Real.exp (-(b * f T))) * banditMeasure ν π T H ≤
          ENNReal.ofReal (Real.exp (-(b * f T))) *
            ENNReal.ofReal ((K - 1 : ℝ) * Real.exp (-((a - b) * f T))) := by
        calc _ ≤ _ := hlow
          _ ≤ banditMeasure ν₁ π T H := hcom
          _ ≤ _ := hC
          _ = _ := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
            congr 1
            have : Real.exp (-(a * f T)) = Real.exp (-(b * f T)) * Real.exp (-((a - b) * f T)) := by
              rw [← Real.exp_add]; congr 1; ring
            rw [this]; ring
      exact (ENNReal.mul_le_mul_iff_right hx0 ENNReal.ofReal_ne_top).1 h1
    have hAsub : A ⊆ H ∪ Bv ∪ Gdᶜ := by
      intro h hh
      by_cases hb : h ∈ Bv
      · exact Or.inl (Or.inr hb)
      by_cases hg : h ∈ Gd
      · exact Or.inl (Or.inl ⟨⟨hh, hb⟩, hg⟩)
      · exact Or.inr hg
    calc banditMeasure ν π T A ≤ banditMeasure ν π T (H ∪ Bv ∪ Gdᶜ) := measure_mono hAsub
      _ ≤ banditMeasure ν π T (H ∪ Bv) + banditMeasure ν π T Gdᶜ := measure_union_le _ _
      _ ≤ banditMeasure ν π T H + banditMeasure ν π T Bv + 0 := by
          rw [hGd0]; gcongr; exact measure_union_le _ _
      _ ≤ _ := by rw [add_zero]; gcongr
  -- limits
  have hf_inf : Tendsto (fun T : ℕ => f T) atTop atTop := by
    have h1 : ∀ᶠ T : ℕ in atTop, (1 / 2) * Real.log T ≤ f T :=
      tendsto_natCast_atTop_atTop.eventually (hf_log (1 / 2) (by norm_num))
    exact tendsto_atTop_mono' _ h1
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num))
  have hexp : Tendsto (fun T : ℕ => ENNReal.ofReal ((K - 1 : ℝ) * Real.exp (-((a - b) * f T))))
      atTop (𝓝 0) := by
    have h1 := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hf_inf.const_mul_atTop (by linarith : (0 : ℝ) < a - b))
    have h2 := h1.const_mul ((K : ℝ) - 1)
    rw [mul_zero] at h2
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal h2
  have hA0 : Tendsto (fun T : ℕ => banditMeasure ν π T {h | (armPullCount i h : ℝ) < c * f T})
      atTop (𝓝 0) := by
    have hsum := hexp.add hW
    rw [add_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall (fun _ => bot_le)) hmain
  have hlim := (ENNReal.Tendsto.sub tendsto_const_nhds hA0 (Or.inl ENNReal.one_ne_top) :
    Tendsto (fun T : ℕ => 1 - banditMeasure ν π T {h | (armPullCount i h : ℝ) < c * f T})
      atTop (𝓝 (1 - 0)))
  rw [tsub_zero] at hlim
  refine hlim.congr' (Eventually.of_forall (fun T => ?_))
  have hAm : MeasurableSet {h : BanditHistory K T | (armPullCount i h : ℝ) < c * f T} :=
    measurable_armPullCount i (t := {n : ℕ | (n : ℝ) < c * f T}) MeasurableSet.of_discrete
  rw [← prob_compl_eq_one_sub hAm]
  congr 1
  ext h; simp

lemma CTT4Aux.integrable_count {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (i : Fin K)
    (T : ℕ) : Integrable (fun h => (armPullCount i h : ℝ)) (banditMeasure ν π T) := by
  have hfm : Measurable (fun h : BanditHistory K T => (armPullCount i h : ℝ)) :=
    (measurable_from_nat (f := fun m : ℕ => (m : ℝ))).comp (CTT4Aux.measurable_armPullCount i)
  refine Integrable.of_bound hfm.aestronglyMeasurable (T : ℝ) (Filter.Eventually.of_forall ?_)
  intro h
  simp only [Real.norm_natCast]
  exact_mod_cast CTT4Aux.armPullCount_le i h

open CTT4Aux in
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
      banditOptimalMean ν < ∫ x, x ∂Q → replaceArm ν i Q hQ ∈ 𝓔) :
    (∀ c : ℝ, ENNReal.ofReal c * banditDInf M (ν.P i) (banditOptimalMean ν) < 1 →
      Tendsto (fun T : ℕ => banditMeasure ν π T {h | c * f T ≤ (armPullCount i h : ℝ)})
        atTop (𝓝 1)) ∧
    (∀ c : ℝ, ENNReal.ofReal c * banditDInf M (ν.P i) (banditOptimalMean ν) < 1 →
      ∀ᶠ T : ℕ in atTop, c * f T ≤ expPulls ν π T i) := by
  refine ⟨fun c hc => part32 M hM f hf_pos hf_mono hf_log hf_o π 𝓔 h𝓔M h31 ν hν i hi hclosed c hc,
    fun c hc => ?_⟩
  have hE0 : ∀ T : ℕ, 0 ≤ expPulls ν π T i := fun T =>
    integral_nonneg (fun h => Nat.cast_nonneg _)
  by_cases hc0 : c ≤ 0
  · filter_upwards [eventually_ge_atTop 2] with T hT
    have hT' : (1 : ℝ) < T := by
      have : (2 : ℝ) ≤ T := by exact_mod_cast hT
      linarith
    have hfT : 0 < f T := hf_pos T hT'
    have : c * f T ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc0 hfT.le
    linarith [hE0 T]
  push_neg at hc0
  set D := banditDInf M (ν.P i) (banditOptimalMean ν) with hDdef
  have hDtop : D ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (by simp [hc0])] at hc
    exact absurd hc (by simp)
  set d : ℝ := D.toReal with hd
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hDeq : D = ENNReal.ofReal d := (ENNReal.ofReal_toReal hDtop).symm
  have hcd : c * d < 1 := by
    have hc' := hc
    rw [hDeq, ← ENNReal.ofReal_mul hc0.le, ← ENNReal.ofReal_one,
      ENNReal.ofReal_lt_ofReal_iff one_pos] at hc'
    exact hc'
  set c' : ℝ := c + (1 - c * d) / (2 * (d + 1)) with hc'def
  have hgap : 0 < (1 - c * d) / (2 * (d + 1)) := by apply div_pos <;> linarith
  have hc'c : c < c' := by rw [hc'def]; linarith
  have hc'pos : 0 < c' := by linarith
  have hc'd : c' * d < 1 := by
    have h1 : (1 - c * d) / (2 * (d + 1)) * d ≤ (1 - c * d) / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc c' * d = c * d + (1 - c * d) / (2 * (d + 1)) * d := by rw [hc'def]; ring
      _ ≤ c * d + (1 - c * d) / 2 := by linarith
      _ < 1 := by linarith
  have hc' : ENNReal.ofReal c' * D < 1 := by
    rw [hDeq, ← ENNReal.ofReal_mul hc'pos.le, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hc'd
  have h32 := part32 M hM f hf_pos hf_mono hf_log hf_o π 𝓔 h𝓔M h31 ν hν i hi hclosed c' hc'
  have hr : c / c' < 1 := by rw [div_lt_one hc'pos]; exact hc'c
  have hev := (tendsto_order.1 h32).1 (ENNReal.ofReal (c / c'))
    (by rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hr)
  filter_upwards [hev, eventually_ge_atTop 2] with T hP hT
  have hT' : (1 : ℝ) < T := by
    have : (2 : ℝ) ≤ T := by exact_mod_cast hT
    linarith
  have hfT : 0 < f T := hf_pos T hT'
  have hreal : c / c' < (banditMeasure ν π T).real {h | c' * f T ≤ (armPullCount i h : ℝ)} := by
    rw [measureReal_def]
    exact (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (measure_ne_top _ _)).1 hP
  have hMk := mul_meas_ge_le_integral_of_nonneg (μ := banditMeasure ν π T)
    (Filter.Eventually.of_forall (fun h => (Nat.cast_nonneg (armPullCount i h) : (0 : ℝ) ≤ _)))
    (integrable_count ν π i T) (c' * f T)
  have hEq : ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π T) = expPulls ν π T i := rfl
  rw [hEq] at hMk
  calc c * f T = c' * f T * (c / c') := by field_simp
    _ ≤ c' * f T * (banditMeasure ν π T).real {h | c' * f T ≤ (armPullCount i h : ℝ)} := by
        apply mul_le_mul_of_nonneg_left hreal.le; positivity
    _ ≤ expPulls ν π T i := hMk
