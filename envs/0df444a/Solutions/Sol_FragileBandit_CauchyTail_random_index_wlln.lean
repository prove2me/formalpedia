-- Prove2me | solution 1 for FragileBandit.CauchyTail.random_index_wlln
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T13:08:31.965769+00:00
-- url     : https://prove2.me/submissions/579421d4-a830-4e6e-8c17-99d174caa188

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm FragileBandit.CauchyTail
open scoped ENNReal Topology

namespace CTWAux

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

end CTWAux

namespace CTWAux

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

end CTWAux


namespace CTWAux

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

end CTWAux


namespace CTWAux

variable {K : ℕ}

open Classical

/-- The reward of the `k`-th play (0-indexed) of arm `j`, or `0` if there is none. -/
noncomputable def padobs (j : Fin K) {T : ℕ} (h : BanditHistory K T) (k : ℕ) : ℝ :=
  ∑ t : Fin T, if (h t).1 = j ∧ cntBefore j h t = k then (h t).2 else 0

lemma N_snoc (j : Fin K) {T : ℕ} (h : BanditHistory K T) (p : Fin K × ℝ) :
    armPullCount j (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) =
      armPullCount j h + (if p.1 = j then 1 else 0) := by
  rw [armPullCount_eq_sum, armPullCount_eq_sum, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

lemma padobs_snoc (j : Fin K) {T : ℕ} (h : BanditHistory K T) (p : Fin K × ℝ) (k : ℕ) :
    padobs j (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) k =
      padobs j h k + (if p.1 = j ∧ armPullCount j h = k then p.2 else 0) := by
  unfold padobs
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, cntBefore_snoc_castSucc, cntBefore_snoc_last]

lemma padobs_eq_zero (j : Fin K) {T : ℕ} (h : BanditHistory K T) (k : ℕ)
    (hk : armPullCount j h ≤ k) : padobs j h k = 0 := by
  unfold padobs
  apply Finset.sum_eq_zero
  intro t _
  split_ifs with ht
  · exfalso; have := cntBefore_lt j h t ht.1; omega
  · rfl

lemma rewardSum_eq (j : Fin K) (φ : ℝ → ℝ) : ∀ (T : ℕ) (h : BanditHistory K T),
    ∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = j), φ (h t).2 =
      ∑ k ∈ Finset.range (armPullCount j h), φ (padobs j h k) := by
  intro T
  induction T with
  | zero => intro h; simp [armPullCount]
  | succ T ih =>
    have key : ∀ (h0 : BanditHistory K T) (p : Fin K × ℝ),
        ∑ t ∈ Finset.univ.filter (fun t : Fin (T + 1) =>
          ((Fin.snoc (α := fun _ ↦ Fin K × ℝ) h0 p) t).1 = j),
            φ ((Fin.snoc (α := fun _ ↦ Fin K × ℝ) h0 p) t).2 =
        ∑ k ∈ Finset.range (armPullCount j (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h0 p)),
          φ (padobs j (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h0 p) k) := by
      intro h0 p
      rw [Finset.sum_filter, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [← Finset.sum_filter, ih h0, N_snoc]
      by_cases hp : p.1 = j
      · simp only [hp, if_true, Finset.sum_range_succ]
        congr 1
        · apply Finset.sum_congr rfl
          intro k hk
          rw [padobs_snoc]
          have : ¬ (armPullCount j h0 = k) := by
            have := Finset.mem_range.1 hk; omega
          simp [this]
        · rw [padobs_snoc, padobs_eq_zero j h0 _ le_rfl]
          simp [hp]
      · simp only [hp, if_false, add_zero]
        apply Finset.sum_congr rfl
        intro k _
        rw [padobs_snoc]
        simp [hp]
    intro h
    have := key (Fin.init h) (h (Fin.last T))
    rwa [Fin.snoc_init_self] at this

/-- Observed rewards of arm `j` in order, padded with the fresh sample `w` beyond `N_j`. -/
noncomputable def pad (j : Fin K) {T : ℕ} (h : BanditHistory K T) (w : ℕ → ℝ) : ℕ → ℝ :=
  fun k => if k < armPullCount j h then padobs j h k else w k

lemma pad_snoc (j : Fin K) {T : ℕ} (h : BanditHistory K T) (a : Fin K) (x : ℝ) (w : ℕ → ℝ) :
    pad j (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h (a, x)) w =
      if a = j then Function.update (pad j h w) (armPullCount j h) x else pad j h w := by
  funext k
  unfold pad
  rw [N_snoc, padobs_snoc]
  by_cases ha : a = j
  · simp only [ha, and_true, if_true]
    rcases lt_trichotomy k (armPullCount j h) with hk | hk | hk
    · rw [Function.update_of_ne (by omega)]
      have h1 : k < armPullCount j h + 1 := by omega
      simp [h1, hk, show armPullCount j h ≠ k by omega]
    · subst hk
      rw [Function.update_self, padobs_eq_zero j h _ le_rfl]
      simp
    · rw [Function.update_of_ne (by omega)]
      have h1 : ¬ k < armPullCount j h + 1 := by omega
      have h2 : ¬ k < armPullCount j h := by omega
      simp [h1, h2]
  · simp [ha]

lemma measurable_padobs (j : Fin K) {T : ℕ} (k : ℕ) :
    Measurable (fun h : BanditHistory K T => padobs j h k) := by
  unfold padobs
  refine Finset.measurable_sum _ (fun t _ => Measurable.ite ?_ ?_ measurable_const)
  · have : {h : BanditHistory K T | (h t).1 = j ∧ cntBefore j h t = k} =
        (fun h : BanditHistory K T => fun t => (h t).1) ⁻¹'
          {a : Fin T → Fin K | a t = j ∧
            (∑ s : Fin T, if s < t ∧ a s = j then 1 else 0) = k} := by
      ext h; simp [cntBefore]
    rw [this]
    exact measurable_arms (Set.to_countable _).measurableSet
  · exact measurable_snd.comp (measurable_pi_apply t)

lemma measurable_pad (j : Fin K) (T : ℕ) :
    Measurable (fun q : BanditHistory K T × (ℕ → ℝ) => pad j q.1 q.2) := by
  rw [measurable_pi_iff]
  intro k
  unfold pad
  refine Measurable.ite ?_ ((measurable_padobs j k).comp measurable_fst)
    ((measurable_pi_apply k).comp measurable_snd)
  exact measurable_fst ((measurable_armPullCount j) (t := {n : ℕ | k < n}) MeasurableSet.of_discrete)

end CTWAux

namespace CTWAux

variable {K : ℕ}

open Classical

lemma lintegral_update_infinitePi (Q : Measure ℝ) [IsProbabilityMeasure Q] (i : ℕ)
    {G : (ℕ → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ w, ∫⁻ x, G (Function.update w i x) ∂Q ∂(Measure.infinitePi (fun _ : ℕ => Q)) =
      ∫⁻ w, G w ∂(Measure.infinitePi (fun _ : ℕ => Q)) := by
  set μ := Measure.infinitePi (fun _ : ℕ => Q) with hμ
  set F : (ℕ → ℝ) × ℝ → (ℕ → ℝ) := fun q => Function.update q.1 i q.2 with hFdef
  have hF : Measurable F := measurable_update'
  have hmap : (μ.prod Q).map F = μ := by
    apply Measure.eq_infinitePi
    intro s t ht
    rw [Measure.map_apply hF (MeasurableSet.pi s.countable_toSet (fun k _ => ht k))]
    by_cases hi : i ∈ s
    · have hpre : F ⁻¹' (Set.pi (↑s) t) = (Set.pi (↑(s.erase i)) t) ×ˢ (t i) := by
        ext ⟨w, x⟩
        simp only [hFdef, Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
          Finset.mem_erase]
        constructor
        · intro hh
          refine ⟨fun k ⟨hki, hks⟩ => ?_, ?_⟩
          · have := hh k hks
            rwa [Function.update_of_ne hki] at this
          · have := hh i hi
            rwa [Function.update_self] at this
        · rintro ⟨hh1, hh2⟩ k hks
          by_cases hki : k = i
          · subst hki; rw [Function.update_self]; exact hh2
          · rw [Function.update_of_ne hki]; exact hh1 k ⟨hki, hks⟩
      rw [hpre, Measure.prod_prod, Measure.infinitePi_pi (fun _ : ℕ => Q) (fun k _ => ht k),
        ← Finset.prod_erase_mul _ _ hi]
    · have hpre : F ⁻¹' (Set.pi (↑s) t) = (Set.pi (↑s) t) ×ˢ (Set.univ : Set ℝ) := by
        ext ⟨w, x⟩
        simp only [hFdef, Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
          Set.mem_univ, and_true]
        constructor
        · intro hh k hks
          have := hh k hks
          rwa [Function.update_of_ne (fun h => hi (by rw [← h]; exact hks))] at this
        · intro hh k hks
          rw [Function.update_of_ne (fun h => hi (by rw [← h]; exact hks))]; exact hh k hks
      rw [hpre, Measure.prod_prod, Measure.infinitePi_pi (fun _ : ℕ => Q) (fun k _ => ht k), measure_univ,
        mul_one]
  calc ∫⁻ w, ∫⁻ x, G (Function.update w i x) ∂Q ∂μ
      = ∫⁻ q, G (F q) ∂(μ.prod Q) := (lintegral_prod _ (hG.comp hF).aemeasurable).symm
    _ = ∫⁻ w, G w ∂((μ.prod Q).map F) := (lintegral_map hG hF).symm
    _ = ∫⁻ w, G w ∂μ := by rw [hmap]

lemma pad_update (j : Fin K) {T : ℕ} (h : BanditHistory K T) (w : ℕ → ℝ) (x : ℝ) :
    pad j h (Function.update w (armPullCount j h) x) =
      Function.update (pad j h w) (armPullCount j h) x := by
  funext k
  unfold pad
  by_cases hk : k = armPullCount j h
  · subst hk; simp
  · simp [Function.update_of_ne hk]

lemma measurable_pad_section (j : Fin K) {T : ℕ} (h : BanditHistory K T) :
    Measurable (fun w : ℕ → ℝ => pad j h w) := by
  rw [measurable_pi_iff]
  intro k
  unfold pad
  split_ifs
  · exact measurable_const
  · exact measurable_pi_apply k

/-- The observed rewards of arm `j`, completed by fresh independent draws, are i.i.d. `Q_j`. -/
lemma iid_prefix (ν : StochasticBandit K) (π : BanditPolicy K) (j : Fin K)
    {G : (ℕ → ℝ) → ℝ≥0∞} (hG : Measurable G) (T : ℕ) :
    ∫⁻ h, ∫⁻ w, G (pad j h w) ∂(Measure.infinitePi (fun _ : ℕ => ν.P j))
        ∂(banditMeasure ν π T) =
      ∫⁻ w, G w ∂(Measure.infinitePi (fun _ : ℕ => ν.P j)) := by
  set μQ := Measure.infinitePi (fun _ : ℕ => ν.P j) with hμQ
  have hΦ : ∀ T : ℕ, Measurable (fun h : BanditHistory K T => ∫⁻ w, G (pad j h w) ∂μQ) :=
    fun T => Measurable.lintegral_prod_right'
      (f := fun q : BanditHistory K T × (ℕ → ℝ) => G (pad j q.1 q.2)) (hG.comp (measurable_pad j T))
  induction T with
  | zero =>
    rw [banditMeasure.eq_1, lintegral_dirac' _ (hΦ 0)]
    congr 1
    all_goals (funext w; congr 1; funext k; simp [pad, armPullCount])
  | succ T ih =>
    rw [lintegral_succ ν π T (hΦ (T + 1))]
    have hinner : ∀ h : BanditHistory K T,
        ∫⁻ p, ∫⁻ w, G (pad j (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) w) ∂μQ
          ∂(banditStepKernel ν π T h) = ∫⁻ w, G (pad j h w) ∂μQ := by
      intro h
      have hsn : Measurable (fun p : Fin K × ℝ => Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) :=
        measurable_banditHistorySnoc.comp measurable_prodMk_left
      have hm : Measurable (fun p : Fin K × ℝ =>
          ∫⁻ w, G (pad j (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) w) ∂μQ) :=
        (hΦ (T + 1)).comp hsn
      rw [lintegral_step ν π T h hm]
      have hGp : Measurable (fun w => G (pad j h w)) := hG.comp (measurable_pad_section j h)
      have ha : ∀ a : Fin K, ∫⁻ x, ∫⁻ w, G (pad j (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h (a, x)) w)
          ∂μQ ∂(ν.P a) = ∫⁻ w, G (pad j h w) ∂μQ := by
        intro a
        by_cases haj : a = j
        · have hx : ∀ x : ℝ, ∫⁻ w, G (pad j (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h (a, x)) w) ∂μQ =
              ∫⁻ w, G (pad j h (Function.update w (armPullCount j h) x)) ∂μQ := by
            intro x
            simp only [pad_snoc j h a x, if_pos haj, pad_update j h]
          rw [lintegral_congr hx, haj]
          rw [lintegral_lintegral_swap]
          · exact lintegral_update_infinitePi (ν.P j) (armPullCount j h) hGp
          · apply Measurable.aemeasurable
            exact (hGp.comp (measurable_update' (a := armPullCount j h))).comp measurable_swap
        · have hx : ∀ x : ℝ, ∫⁻ w, G (pad j (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h (a, x)) w) ∂μQ =
              ∫⁻ w, G (pad j h w) ∂μQ := by
            intro x
            simp only [pad_snoc j h a x, if_neg haj]
          rw [lintegral_congr hx, lintegral_const, measure_univ, mul_one]
      rw [lintegral_congr ha, lintegral_const, measure_univ, mul_one]
    rw [lintegral_congr hinner]
    exact ih


/-- SLLN tail bound on the i.i.d. sequence space. -/
lemma slln_tail (Q : Measure ℝ) [IsProbabilityMeasure Q] (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hφ : Integrable φ Q) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n0 : ℕ => Measure.infinitePi (fun _ : ℕ => Q)
      {ω | ∃ n, n0 ≤ n ∧ δ < |(∑ k ∈ Finset.range n, φ (ω k)) / n - ∫ y, φ y ∂Q|})
      atTop (𝓝 0) := by
  set μ := Measure.infinitePi (fun _ : ℕ => Q) with hμ
  set X : ℕ → (ℕ → ℝ) → ℝ := fun k ω => φ (ω k) with hX
  have hXm : ∀ k, Measurable (X k) := fun k => hφm.comp (measurable_pi_apply k)
  have hmap : ∀ k, μ.map (X k) = Q.map φ := by
    intro k
    have : X k = φ ∘ (fun ω : ℕ → ℝ => ω k) := rfl
    rw [this, ← Measure.map_map hφm (measurable_pi_apply k), Measure.infinitePi_map_eval]
  have hint : Integrable (X 0) μ := by
    have h1 : Integrable φ (μ.map (fun ω : ℕ → ℝ => ω 0)) := by
      rw [Measure.infinitePi_map_eval]; exact hφ
    exact h1.comp_measurable (measurable_pi_apply 0)
  have hind : iIndepFun (fun k ω => φ (ω k)) μ :=
    iIndepFun_infinitePi (P := fun _ : ℕ => Q) (X := fun _ => φ) (fun _ => hφm)
  have hpair : Pairwise (Function.onFun (fun f g => f ⟂ᵢ[μ] g) X) := fun i j hij => hind.indepFun hij
  have hident : ∀ i, IdentDistrib (X i) (X 0) μ μ := fun i =>
    ⟨(hXm i).aemeasurable, (hXm 0).aemeasurable, by rw [hmap i, hmap 0]⟩
  have hslln := ProbabilityTheory.strong_law_ae X hint hpair hident
  have hmean : μ[X 0] = ∫ y, φ y ∂Q := by
    have : ∫ ω, X 0 ω ∂μ = ∫ y, φ y ∂(μ.map (fun ω : ℕ → ℝ => ω 0)) := by
      rw [integral_map (measurable_pi_apply 0).aemeasurable hφm.aestronglyMeasurable]
    rw [this, Measure.infinitePi_map_eval]
  rw [hmean] at hslln
  set A : ℕ → Set (ℕ → ℝ) := fun n0 =>
    {ω | ∃ n, n0 ≤ n ∧ δ < |(∑ k ∈ Finset.range n, φ (ω k)) / n - ∫ y, φ y ∂Q|} with hA
  have hAm : ∀ n0, MeasurableSet (A n0) := by
    intro n0
    have : A n0 = ⋃ n, {ω | n0 ≤ n ∧ δ < |(∑ k ∈ Finset.range n, φ (ω k)) / n - ∫ y, φ y ∂Q|} := by
      ext ω; simp [hA]
    rw [this]
    refine MeasurableSet.iUnion (fun n => ?_)
    by_cases hn : n0 ≤ n
    · simp only [hn, true_and]
      refine measurableSet_lt measurable_const ?_
      exact (((Finset.measurable_sum _ (fun k _ => hXm k)).div_const _).sub measurable_const).abs
    · simp [hn]
  have hanti : Antitone A := by
    intro a b hab ω hω
    obtain ⟨n, hn, h⟩ := hω
    exact ⟨n, le_trans hab hn, h⟩
  have hInter : μ (⋂ n0, A n0) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hslln)
    intro ω hω
    simp only [Set.mem_iInter, hA, Set.mem_ofPred_eq] at hω
    simp only [Set.mem_ofPred_eq]
    intro hconv
    have hev := (Metric.tendsto_atTop.1 hconv) δ hδ
    obtain ⟨N0, hN0⟩ := hev
    obtain ⟨n, hn, hlt⟩ := hω N0
    have := hN0 n hn
    rw [Real.dist_eq, smul_eq_mul, inv_mul_eq_div] at this
    linarith
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hAm n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hInter] at hlim
  exact hlim

end CTWAux

open CTWAux in
theorem solution {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (j : Fin K)
    (φ : ℝ → ℝ) (hφm : Measurable φ) (hφ : Integrable φ (ν.P j))
    (hN : ∀ m : ℕ, Tendsto (fun T : ℕ => banditMeasure ν π T {h | armPullCount j h ≤ m})
      atTop (𝓝 0)) :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℕ => banditMeasure ν π T
      {h | δ < |(∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = j), φ (h t).2) /
          (armPullCount j h : ℝ) - ∫ y, φ y ∂(ν.P j)|}) atTop (𝓝 0) := by
  classical
  intro δ hδ
  set mφ := ∫ y, φ y ∂(ν.P j) with hmφ
  set μQ := Measure.infinitePi (fun _ : ℕ => ν.P j) with hμQ
  set A : ℕ → Set (ℕ → ℝ) := fun n0 =>
    {ω | ∃ n, n0 ≤ n ∧ δ < |(∑ k ∈ Finset.range n, φ (ω k)) / n - mφ|} with hA
  have hAm : ∀ n0, MeasurableSet (A n0) := by
    intro n0
    have : A n0 = ⋃ n, {ω : ℕ → ℝ | n0 ≤ n ∧ δ < |(∑ k ∈ Finset.range n, φ (ω k)) / n - mφ|} := by
      ext ω; simp [hA]
    rw [this]
    refine MeasurableSet.iUnion (fun n => ?_)
    by_cases hn : n0 ≤ n
    · simp only [hn, true_and]
      refine measurableSet_lt measurable_const ?_
      exact (((Finset.measurable_sum _
        (fun k _ => hφm.comp (measurable_pi_apply k))).div_const _).sub measurable_const).abs
    · simp [hn]
  have htail := slln_tail (ν.P j) φ hφm hφ δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨n0, hn0⟩ := (htail.eventually (eventually_le_nhds hε2)).exists
  have hev := (hN n0).eventually (eventually_le_nhds hε2)
  filter_upwards [hev] with T hT
  set E := {h : BanditHistory K T | δ < |(∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = j),
      φ (h t).2) / (armPullCount j h : ℝ) - mφ|} with hE
  set F := {h : BanditHistory K T | n0 ≤ armPullCount j h ∧ δ < |(∑ t ∈ Finset.univ.filter
      (fun t : Fin T => (h t).1 = j), φ (h t).2) / (armPullCount j h : ℝ) - mφ|} with hF
  have hNm : Measurable (fun h : BanditHistory K T => (armPullCount j h : ℝ)) :=
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (measurable_armPullCount j)
  have hFm : MeasurableSet F := by
    have h1 : MeasurableSet {h : BanditHistory K T | n0 ≤ armPullCount j h} :=
      measurable_armPullCount j (t := {n : ℕ | n0 ≤ n}) MeasurableSet.of_discrete
    have h2 : MeasurableSet {h : BanditHistory K T | δ < |(∑ t ∈ Finset.univ.filter
        (fun t : Fin T => (h t).1 = j), φ (h t).2) / (armPullCount j h : ℝ) - mφ|} :=
      measurableSet_lt measurable_const
        ((((measurable_rewardSum (T := T) j hφm).div hNm).sub measurable_const).abs)
    exact h1.inter h2
  have hsub : E ⊆ {h | armPullCount j h ≤ n0} ∪ F := by
    intro h hh
    by_cases hc : armPullCount j h ≤ n0
    · exact Or.inl hc
    · exact Or.inr ⟨by omega, hh⟩
  have hFb : banditMeasure ν π T F ≤ μQ (A n0) := by
    have hG : Measurable ((A n0).indicator (1 : (ℕ → ℝ) → ℝ≥0∞)) :=
      measurable_one.indicator (hAm n0)
    calc banditMeasure ν π T F = ∫⁻ h, F.indicator 1 h ∂(banditMeasure ν π T) :=
          (lintegral_indicator_one hFm).symm
      _ ≤ ∫⁻ h, ∫⁻ w, (A n0).indicator 1 (pad j h w) ∂μQ ∂(banditMeasure ν π T) := by
          apply lintegral_mono
          intro h
          by_cases hh : h ∈ F
          · rw [Set.indicator_of_mem hh]
            have hin : ∀ w, pad j h w ∈ A n0 := by
              intro w
              refine ⟨armPullCount j h, hh.1, ?_⟩
              have hsum : ∑ k ∈ Finset.range (armPullCount j h), φ (pad j h w k) =
                  ∑ t ∈ Finset.univ.filter (fun t : Fin T => (h t).1 = j), φ (h t).2 := by
                rw [rewardSum_eq j φ T h]
                apply Finset.sum_congr rfl
                intro k hk
                simp [pad, Finset.mem_range.1 hk]
              rw [hsum]; exact hh.2
            have : ∫⁻ w, (A n0).indicator 1 (pad j h w) ∂μQ = ∫⁻ _w, (1 : ℝ≥0∞) ∂μQ := by
              apply lintegral_congr; intro w; rw [Set.indicator_of_mem (hin w)]; rfl
            show (1 : ℝ≥0∞) ≤ ∫⁻ w, (A n0).indicator 1 (pad j h w) ∂μQ
            rw [this, lintegral_const, measure_univ, mul_one]
          · rw [Set.indicator_of_notMem hh]; exact bot_le
      _ = ∫⁻ w, (A n0).indicator 1 w ∂μQ := iid_prefix ν π j hG T
      _ = μQ (A n0) := lintegral_indicator_one (hAm n0)
  calc banditMeasure ν π T E ≤ banditMeasure ν π T ({h | armPullCount j h ≤ n0} ∪ F) :=
        measure_mono hsub
    _ ≤ banditMeasure ν π T {h | armPullCount j h ≤ n0} + banditMeasure ν π T F :=
        measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hT (le_trans hFb hn0)
    _ = ε := ENNReal.add_halves ε
