-- Prove2me | solution 1 for EntropyLocalCoord.Leader.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:56:34.640945+00:00
-- url     : https://prove2.me/submissions/8e180b97-f1ae-4373-a142-c26cdb3e57d5

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Information

section
set_option autoImplicit false

section Dev
open MeasureTheory

namespace EntropyLocalCoord.Dev.Coupling

variable {X : Type} [MeasurableSpace X]

open Classical in
noncomputable def firstIdx (A : Set X) (ω : ℕ → X) : ℕ :=
  if h : ∃ t, ω t ∈ A then Nat.find h else 0

lemma firstIdx_eq {A : Set X} {ω : ℕ → X} {t : ℕ} (h1 : ω t ∈ A) (h2 : ∀ s < t, ω s ∉ A) :
    firstIdx A ω = t := by
  classical
  have h : ∃ t, ω t ∈ A := ⟨t, h1⟩
  unfold firstIdx
  rw [dif_pos h, Nat.find_eq_iff]
  exact ⟨h1, fun s hs => h2 s hs⟩

lemma firstIdx_spec {A : Set X} {ω : ℕ → X} (h : ∃ t, ω t ∈ A) :
    ω (firstIdx A ω) ∈ A ∧ ∀ s < firstIdx A ω, ω s ∉ A := by
  classical
  unfold firstIdx
  rw [dif_pos h]
  exact ⟨Nat.find_spec h, fun s hs => Nat.find_min h hs⟩

def G (A B : Set X) (t : ℕ) : Set (ℕ → X) :=
  Set.pi (Finset.range (t + 1)) (fun s => if s < t then Aᶜ else A ∩ B)

lemma mem_G {A B : Set X} {t : ℕ} {ω : ℕ → X} :
    ω ∈ G A B t ↔ (∀ s < t, ω s ∉ A) ∧ ω t ∈ A ∧ ω t ∈ B := by
  unfold G
  simp only [Set.mem_pi, Finset.mem_coe, Finset.mem_range]
  constructor
  · intro h
    refine ⟨fun s hs => ?_, ?_⟩
    · have := h s (by omega); simpa [hs] using this
    · have := h t (by omega); simpa using this
  · rintro ⟨h1, h2, h3⟩ s hs
    by_cases h : s < t
    · simpa [h] using h1 s h
    · have : s = t := by omega
      subst this; simpa [h] using ⟨h2, h3⟩

lemma hitset_eq (A B : Set X) :
    {ω : ℕ → X | (∃ t, ω t ∈ A) ∧ ω (firstIdx A ω) ∈ B} = ⋃ t, G A B t := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, mem_G]
  constructor
  · rintro ⟨h, hB⟩
    obtain ⟨h1, h2⟩ := firstIdx_spec h
    exact ⟨_, h2, h1, hB⟩
  · rintro ⟨t, h1, h2, h3⟩
    have := firstIdx_eq h2 h1
    exact ⟨⟨t, h2⟩, by rw [this]; exact h3⟩

lemma measurableSet_G {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (t : ℕ) :
    MeasurableSet (G A B t) := by
  unfold G
  refine MeasurableSet.pi (Finset.countable_toSet _) (fun s _ => ?_)
  by_cases h : s < t <;> simp [h, hA, hB, hA.compl, hA.inter hB]

lemma disjoint_G (A B : Set X) : Pairwise (Function.onFun Disjoint (G A B)) := by
  intro t t' htt'
  wlog h : t < t' generalizing t t'
  · exact (this htt'.symm (by omega)).symm
  rw [Function.onFun, Set.disjoint_left]
  intro ω h1 h2
  rw [mem_G] at h1 h2
  exact h2.1 t h h1.2.1

lemma measure_G (ν : Measure X) [IsProbabilityMeasure ν] {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (t : ℕ) :
    Measure.infinitePi (fun _ : ℕ => ν) (G A B t) = (ν Aᶜ) ^ t * ν (A ∩ B) := by
  unfold G
  rw [Measure.infinitePi_pi _ (fun s _ => by
    by_cases h : s < t <;> simp [h, hA, hB, hA.compl, hA.inter hB])]
  rw [Finset.prod_range_succ]
  simp only [lt_irrefl, if_false]
  congr 1
  rw [show ν Aᶜ ^ t = ∏ _s ∈ Finset.range t, ν Aᶜ by simp]
  refine Finset.prod_congr rfl (fun s hs => ?_)
  simp [Finset.mem_range.mp hs]

/-- Probability that the first hit of `A` lies in `B`. -/
lemma measure_hitset (ν : Measure X) [IsProbabilityMeasure ν] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measure.infinitePi (fun _ : ℕ => ν) {ω : ℕ → X | (∃ t, ω t ∈ A) ∧ ω (firstIdx A ω) ∈ B}
      = ν (A ∩ B) / ν A := by
  rw [hitset_eq, measure_iUnion (disjoint_G A B) (measurableSet_G hA hB)]
  simp_rw [measure_G ν hA hB]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, prob_compl_eq_one_sub hA,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one, div_eq_mul_inv, mul_comm]

lemma measurableSet_hitset {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet {ω : ℕ → X | (∃ t, ω t ∈ A) ∧ ω (firstIdx A ω) ∈ B} := by
  rw [hitset_eq]; exact MeasurableSet.iUnion (measurableSet_G hA hB)

lemma measurableSet_nohit {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet {ω : ℕ → X | ¬ ∃ t, ω t ∈ A} := by
  have : {ω : ℕ → X | ¬ ∃ t, ω t ∈ A} = (⋃ t, {ω : ℕ → X | ω t ∈ A})ᶜ := by
    ext ω; simp
  rw [this]
  exact (MeasurableSet.iUnion (fun t => measurable_pi_apply t hA)).compl

lemma measure_nohit (ν : Measure X) [IsProbabilityMeasure ν] {A : Set X}
    (hA : MeasurableSet A) (hq : ν A ≠ 0) :
    Measure.infinitePi (fun _ : ℕ => ν) {ω : ℕ → X | ¬ ∃ t, ω t ∈ A} = 0 := by
  have h1 := measure_hitset ν hA MeasurableSet.univ
  rw [Set.inter_univ, ENNReal.div_self hq (measure_ne_top _ _)] at h1
  have : {ω : ℕ → X | ¬ ∃ t, ω t ∈ A} = {ω : ℕ → X | (∃ t, ω t ∈ A) ∧ ω (firstIdx A ω) ∈ Set.univ}ᶜ := by
    ext ω; simp
  rw [this, prob_compl_eq_one_sub (measurableSet_hitset hA MeasurableSet.univ), h1]
  simp

lemma measurableSet_pre {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet {ω : ℕ → X | ω (firstIdx A ω) ∈ B} := by
  have : {ω : ℕ → X | ω (firstIdx A ω) ∈ B} =
      {ω : ℕ → X | (∃ t, ω t ∈ A) ∧ ω (firstIdx A ω) ∈ B} ∪
        ({ω : ℕ → X | ¬ ∃ t, ω t ∈ A} ∩ {ω | ω 0 ∈ B}) := by
    ext ω
    by_cases h : ∃ t, ω t ∈ A
    · simp [h]
    · have : firstIdx A ω = 0 := by unfold firstIdx; simp [h]
      have h' : ∀ x, ω x ∉ A := fun x hx => h ⟨x, hx⟩
      simp [h, h', this]
  rw [this]
  exact (measurableSet_hitset hA hB).union ((measurableSet_nohit hA).inter (measurable_pi_apply 0 hB))

lemma measure_pre (ν : Measure X) [IsProbabilityMeasure ν] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hq : ν A ≠ 0) :
    Measure.infinitePi (fun _ : ℕ => ν) {ω : ℕ → X | ω (firstIdx A ω) ∈ B}
      = ν (A ∩ B) / ν A := by
  rw [← measure_hitset ν hA hB]
  apply le_antisymm
  · calc _ ≤ Measure.infinitePi (fun _ : ℕ => ν) ({ω : ℕ → X | (∃ t, ω t ∈ A) ∧ ω (firstIdx A ω) ∈ B}
          ∪ {ω : ℕ → X | ¬ ∃ t, ω t ∈ A}) := by
          apply measure_mono
          intro ω hω
          by_cases h : ∃ t, ω t ∈ A
          · exact Or.inl ⟨h, hω⟩
          · exact Or.inr h
      _ ≤ _ := (measure_union_le _ _).trans (by rw [measure_nohit ν hA hq]; simp)
  · apply measure_mono
    intro ω hω; exact hω.2

end EntropyLocalCoord.Dev.Coupling

section P2
open ENNReal

namespace EntropyLocalCoord.Dev.Coupling

variable {K : Type} [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]

noncomputable def kappa (K : Type) [Fintype K] [MeasurableSpace K] : Measure K :=
  ((Fintype.card K : ℝ≥0∞))⁻¹ • Measure.count

noncomputable def nu (K : Type) [Fintype K] [MeasurableSpace K] : Measure (K × ℝ) :=
  (kappa K).prod (volume.restrict (Set.Icc (0:ℝ) 1))

def S (C : Finset K) (f : K → ℝ) : Set (K × ℝ) := {x | x.1 ∈ C ∧ x.2 ≤ f x.1}

lemma measurableSet_S (C : Finset K) (f : K → ℝ) : MeasurableSet (S C f) := by
  unfold S
  have h1 : MeasurableSet {x : K × ℝ | x.1 ∈ C} := measurable_fst (C.measurableSet)
  have h2 : MeasurableSet {x : K × ℝ | x.2 ≤ f x.1} :=
    measurableSet_le measurable_snd ((measurable_of_finite f).comp measurable_fst)
  exact h1.inter h2

lemma nu_S [Nonempty K] (C : Finset K) (f : K → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    nu K (S C f) = ((Fintype.card K : ℝ≥0∞))⁻¹ * ENNReal.ofReal (∑ a ∈ C, f a) := by
  classical
  unfold nu
  rw [Measure.prod_apply (measurableSet_S C f)]
  have : ∀ a : K, (volume.restrict (Set.Icc (0:ℝ) 1)) (Prod.mk a ⁻¹' S C f)
      = if a ∈ C then ENNReal.ofReal (f a) else 0 := by
    intro a
    by_cases ha : a ∈ C
    · have : Prod.mk a ⁻¹' S C f = Set.Iic (f a) := by
        ext u; simp [S, ha]
      rw [this, if_pos ha, Measure.restrict_apply measurableSet_Iic]
      have : Set.Iic (f a) ∩ Set.Icc (0:ℝ) 1 = Set.Icc 0 (f a) := by
        ext u; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [(hf a).2]⟩
      rw [this, Real.volume_Icc]; simp
    · have : Prod.mk a ⁻¹' S C f = ∅ := by
        ext u; simp [S, ha]
      rw [this, if_neg ha]; simp
  simp_rw [this]
  unfold kappa
  rw [lintegral_smul_measure, lintegral_count, tsum_fintype, smul_eq_mul,
    ← Finset.sum_filter, ← ENNReal.ofReal_sum_of_nonneg (fun a _ => (hf a).1)]
  congr 3
  ext a; simp


lemma kappa_univ [Nonempty K] : kappa K Set.univ = 1 := by
  unfold kappa
  simp only [Measure.smul_apply, Measure.count_univ, smul_eq_mul]
  have h1 : ((ENat.card K : ℕ∞) : ℝ≥0∞) = (Fintype.card K : ℝ≥0∞) := by
    rw [ENat.card_eq_coe_fintype_card]; simp
  rw [h1]
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

instance nu_prob [Nonempty K] : IsProbabilityMeasure (nu K) := by
  constructor
  unfold nu
  rw [show (Set.univ : Set (K × ℝ)) = Set.univ ×ˢ Set.univ from Set.univ_prod_univ.symm,
    Measure.prod_prod, kappa_univ]
  simp


lemma sum_max_min {ι : Type} (K' : Type) [Fintype K'] (μ : ι → K' → ℝ) (i j : ι)
    (h1 : ∑ a, μ i a = 1) (h2 : ∑ a, μ j a = 1) :
    ∑ a, max (μ i a) (μ j a) = 1 + (1/2) * ∑ a, |μ i a - μ j a| := by
  have : ∀ a, max (μ i a) (μ j a) = (μ i a + μ j a + |μ i a - μ j a|) / 2 := by
    intro a
    rcases le_total (μ i a) (μ j a) with h | h
    · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring
  simp_rw [this]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2]
  ring

lemma sum_max_sub_min {ι : Type} (K' : Type) [Fintype K'] (μ : ι → K' → ℝ) (i j : ι) :
    ∑ a, max (μ i a) (μ j a) - ∑ a, min (μ i a) (μ j a) = ∑ a, |μ i a - μ j a| := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [max_sub_min_eq_abs]; exact abs_sub_comm _ _


noncomputable def PP (K : Type) [Fintype K] [MeasurableSpace K] : Measure (ℕ → K × ℝ) :=
  Measure.infinitePi (fun _ : ℕ => nu K)

noncomputable def Lf {ι : Type} (μ : ι → K → ℝ) (i : ι) (ω : ℕ → K × ℝ) : K :=
  (ω (firstIdx (S Finset.univ (μ i)) ω)).1

theorem core [Nonempty K] {ι : Type} (μ : ι → K → ℝ) (hμ0 : ∀ i a, 0 ≤ μ i a)
    (hμ1 : ∀ i, ∑ a, μ i a = 1) :
    (∀ i, Measurable (Lf μ i)) ∧
    (∀ i a, (PP K).real (Lf μ i ⁻¹' {a}) = μ i a) ∧
    ∀ i j, (PP K).real {ω | Lf μ i ω ≠ Lf μ j ω} ≤
      2 * (1/2 * ∑ a, |μ i a - μ j a|) / (1 + 1/2 * ∑ a, |μ i a - μ j a|) := by
  classical
  have hle : ∀ i a, μ i a ≤ 1 := fun i a => by
    rw [← hμ1 i]; exact Finset.single_le_sum (fun b _ => hμ0 i b) (Finset.mem_univ a)
  have hp0 : ((Fintype.card K : ℝ≥0∞))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (by simp)
  have hptop : ((Fintype.card K : ℝ≥0∞))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (by simp [Fintype.card_ne_zero])
  have hA : ∀ i, nu K (S Finset.univ (μ i)) = ((Fintype.card K : ℝ≥0∞))⁻¹ := fun i => by
    rw [nu_S _ _ (fun a => ⟨hμ0 i a, hle i a⟩), hμ1 i]; simp
  have hmeas : ∀ i, Measurable (Lf μ i) := fun i => by
    refine measurable_to_countable' (fun a => ?_)
    exact measurableSet_pre (measurableSet_S Finset.univ (μ i))
      (measurable_fst (measurableSet_singleton a) : MeasurableSet (Prod.fst ⁻¹' {a} : Set (K × ℝ)))
  refine ⟨hmeas, ?_, ?_⟩
  · intro i a
    have h := measure_pre (nu K) (measurableSet_S Finset.univ (μ i))
      (measurable_fst (measurableSet_singleton a) : MeasurableSet (Prod.fst ⁻¹' {a} : Set (K × ℝ)))
      (by rw [hA i]; exact hp0)
    have hs : S Finset.univ (μ i) ∩ Prod.fst ⁻¹' {a} = S {a} (μ i) := by
      ext x; simp [S]; exact and_comm
    rw [hs, nu_S _ _ (fun a => ⟨hμ0 i a, hle i a⟩), hA i] at h
    rw [measureReal_def]
    change ((PP K) {ω | ω (firstIdx (S Finset.univ (μ i)) ω) ∈ Prod.fst ⁻¹' {a}}).toReal = _
    unfold PP
    rw [h, Finset.sum_singleton, mul_comm, ENNReal.mul_div_cancel_right hp0 hptop,
      ENNReal.toReal_ofReal (hμ0 i a)]
  · intro i j
    set p : ℝ≥0∞ := ((Fintype.card K : ℝ≥0∞))⁻¹ with hp
    set Mx : K → ℝ := fun a => max (μ i a) (μ j a) with hMx
    set Mn : K → ℝ := fun a => min (μ i a) (μ j a) with hMn
    have hMx01 : ∀ a, 0 ≤ Mx a ∧ Mx a ≤ 1 := fun a =>
      ⟨le_trans (hμ0 i a) (le_max_left _ _), max_le (hle i a) (hle j a)⟩
    have hMn01 : ∀ a, 0 ≤ Mn a ∧ Mn a ≤ 1 := fun a =>
      ⟨le_min (hμ0 i a) (hμ0 j a), le_trans (min_le_left _ _) (hle i a)⟩
    set M : ℝ := ∑ a, Mx a with hM
    set m : ℝ := ∑ a, Mn a with hm
    set δ : ℝ := 1/2 * ∑ a, |μ i a - μ j a| with hδ
    have hMδ : M = 1 + δ := sum_max_min K μ i j (hμ1 i) (hμ1 j)
    have hMm : M - m = 2 * δ := by
      have := sum_max_sub_min K μ i j
      rw [hδ]; linarith
    have hδ0 : 0 ≤ δ := by
      rw [hδ]; positivity
    have hUeq : S Finset.univ (μ i) ∪ S Finset.univ (μ j) = S Finset.univ Mx := by
      ext x; simp [S, hMx, le_max_iff]
    have hsub : S Finset.univ Mn ⊆ S Finset.univ Mx := by
      intro x hx; simp only [S, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
      exact hx.trans (min_le_max)
    have hnuU : nu K (S Finset.univ Mx) = p * ENNReal.ofReal M := nu_S _ _ hMx01
    have hnuN : nu K (S Finset.univ Mn) = p * ENNReal.ofReal m := nu_S _ _ hMn01
    have hM1 : 0 < M := by rw [hMδ]; linarith
    have hUne : nu K (S Finset.univ Mx) ≠ 0 := by
      rw [hnuU]; exact mul_ne_zero hp0 (by simpa using hM1)
    have hnj : ∀ k, nu K (S Finset.univ (μ k)) ≠ 0 := fun k => by rw [hA k]; exact hp0
    have hDiff : nu K (S Finset.univ Mx \ S Finset.univ Mn) = p * ENNReal.ofReal M - p * ENNReal.ofReal m := by
      rw [measure_diff hsub (measurableSet_S _ _).nullMeasurableSet (measure_ne_top _ _), hnuU, hnuN]
    have hhit := measure_hitset (nu K) (measurableSet_S Finset.univ Mx)
      ((measurableSet_S Finset.univ Mx).diff (measurableSet_S Finset.univ Mn))
    rw [Set.inter_eq_right.mpr Set.diff_subset, hDiff, hnuU] at hhit
    have hsubset : {ω | Lf μ i ω ≠ Lf μ j ω} ⊆
        {ω : ℕ → K × ℝ | (∃ t, ω t ∈ S Finset.univ Mx) ∧
            ω (firstIdx (S Finset.univ Mx) ω) ∈ S Finset.univ Mx \ S Finset.univ Mn}
        ∪ {ω | ¬ ∃ t, ω t ∈ S Finset.univ (μ i)} ∪ {ω | ¬ ∃ t, ω t ∈ S Finset.univ (μ j)} := by
      intro ω hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
      obtain ⟨⟨hh, hi⟩, hj⟩ := hcon
      apply hω
      obtain ⟨t0, ht0⟩ := hi
      have hU : ∃ t, ω t ∈ S Finset.univ Mx := ⟨t0, by rw [← hUeq]; exact Or.inl ht0⟩
      obtain ⟨hT1, hT2⟩ := firstIdx_spec hU
      have hmn : ω (firstIdx (S Finset.univ Mx) ω) ∈ S Finset.univ Mn := by
        by_contra hnm
        exact hh ⟨hU, hT1, hnm⟩
      have hmn' : (ω (firstIdx (S Finset.univ Mx) ω)).2 ≤ μ i (ω (firstIdx (S Finset.univ Mx) ω)).1 ∧
          (ω (firstIdx (S Finset.univ Mx) ω)).2 ≤ μ j (ω (firstIdx (S Finset.univ Mx) ω)).1 := by
        have := hmn
        simpa [S, hMn, le_min_iff] using this
      have hk : ∀ k, (∀ x, x ∈ S Finset.univ (μ k) → x ∈ S Finset.univ Mx) →
          (ω (firstIdx (S Finset.univ Mx) ω)).2 ≤ μ k (ω (firstIdx (S Finset.univ Mx) ω)).1 →
          firstIdx (S Finset.univ (μ k)) ω = firstIdx (S Finset.univ Mx) ω := by
        intro k hsubk hle'
        apply firstIdx_eq
        · simpa [S] using hle'
        · intro s hs hs'
          exact hT2 s hs (hsubk _ hs')
      have hsi : ∀ x, x ∈ S Finset.univ (μ i) → x ∈ S Finset.univ Mx := fun x hx => by
        rw [← hUeq]; exact Or.inl hx
      have hsj : ∀ x, x ∈ S Finset.univ (μ j) → x ∈ S Finset.univ Mx := fun x hx => by
        rw [← hUeq]; exact Or.inr hx
      unfold Lf
      rw [hk i hsi hmn'.1, hk j hsj hmn'.2]
    have hnull : ∀ k, PP K {ω | ¬ ∃ t, ω t ∈ S Finset.univ (μ k)} = 0 := fun k =>
      measure_nohit (nu K) (measurableSet_S _ _) (hnj k)
    have hPle : PP K {ω | Lf μ i ω ≠ Lf μ j ω} ≤
        (p * ENNReal.ofReal M - p * ENNReal.ofReal m) / (p * ENNReal.ofReal M) := by
      calc PP K {ω | Lf μ i ω ≠ Lf μ j ω}
          ≤ PP K (_ ∪ _ ∪ _) := measure_mono hsubset
        _ ≤ _ + _ + _ := (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
        _ = _ := by rw [hnull i, hnull j, add_zero, add_zero]; exact hhit
    have hm0 : 0 ≤ m := Finset.sum_nonneg (fun a _ => (hMn01 a).1)
    have hmM : m ≤ M := by linarith
    have hcalc : (p * ENNReal.ofReal M - p * ENNReal.ofReal m) / (p * ENNReal.ofReal M)
        = ENNReal.ofReal (M - m) / ENNReal.ofReal M := by
      rw [← ENNReal.mul_sub (fun _ _ => hptop), ← ENNReal.ofReal_sub M hm0] 
      exact ENNReal.mul_div_mul_left _ _ hp0 hptop
    have hfin : ENNReal.ofReal (M - m) / ENNReal.ofReal M ≠ ⊤ :=
      ENNReal.div_ne_top ENNReal.ofReal_ne_top (by simpa using hM1)
    rw [hcalc] at hPle
    rw [measureReal_def]
    calc (PP K {ω | Lf μ i ω ≠ Lf μ j ω}).toReal
        ≤ (ENNReal.ofReal (M - m) / ENNReal.ofReal M).toReal := ENNReal.toReal_mono hfin hPle
      _ = 2 * δ / (1 + δ) := by
        rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hM1.le,
          hMm, hMδ]

end EntropyLocalCoord.Dev.Coupling

end P2
end Dev

open MeasureTheory

theorem EntropyLocalCoord.Leader.chk_theorem_4_2 {ι K : Type} [Countable ι] [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (μ : ι → K → ℝ) (hμ0 : ∀ i a, 0 ≤ μ i a)
    (hμ1 : ∀ i, ∑ a, μ i a = 1) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (L : ι → Ω → K),
      (∀ i, Measurable (L i)) ∧
      (∀ i a, P.real (L i ⁻¹' {a}) = μ i a) ∧
      ∀ i j,
        P.real {ω | L i ω ≠ L j ω} ≤
            2 * EntropyLocalCoord.Leader.tvNorm (fun a => μ i a - μ j a) / (1 + EntropyLocalCoord.Leader.tvNorm (fun a => μ i a - μ j a)) ∧
          2 * EntropyLocalCoord.Leader.tvNorm (fun a => μ i a - μ j a) / (1 + EntropyLocalCoord.Leader.tvNorm (fun a => μ i a - μ j a)) ≤
            2 * EntropyLocalCoord.Leader.tvNorm (fun a => μ i a - μ j a) := by
  by_cases hK : Nonempty K
  · obtain ⟨h1, h2, h3⟩ := EntropyLocalCoord.Dev.Coupling.core μ hμ0 hμ1
    haveI := hK
    haveI : IsProbabilityMeasure (EntropyLocalCoord.Dev.Coupling.PP K) := by
      unfold EntropyLocalCoord.Dev.Coupling.PP; infer_instance
    refine ⟨ℕ → K × ℝ, inferInstance, EntropyLocalCoord.Dev.Coupling.PP K, inferInstance,
      EntropyLocalCoord.Dev.Coupling.Lf μ, h1, h2, fun i j => ⟨h3 i j, ?_⟩⟩
    have hδ : 0 ≤ EntropyLocalCoord.Leader.tvNorm (fun a => μ i a - μ j a) := by
      unfold EntropyLocalCoord.Leader.tvNorm; positivity
    set δ := EntropyLocalCoord.Leader.tvNorm (fun a => μ i a - μ j a)
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · haveI : IsEmpty K := not_nonempty_iff.1 hK
    haveI : IsEmpty ι := ⟨fun i => by have := hμ1 i; simp at this⟩
    exact ⟨Unit, inferInstance, Measure.dirac (), inferInstance, fun i => isEmptyElim i,
      fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
end

theorem solution : type_of% @EntropyLocalCoord.Leader.chk_theorem_4_2 := @EntropyLocalCoord.Leader.chk_theorem_4_2
