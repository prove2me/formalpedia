-- Prove2me | solution 1 for BertsekasShreve.AnalyticSelection.analytic_universallyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:08:06.366526+00:00
-- url     : https://prove2.me/submissions/e7c57693-b3b0-410b-b391-59be2afe795c

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability

open MeasureTheory


namespace BertsekasShreve.AnalyticSelection

open Set Filter Topology ENNReal

lemma au_cyl_of_nhds {σ : ℕ → ℕ} {U : Set (ℕ → ℕ)} (hU : U ∈ 𝓝 σ) :
    ∃ m, ∀ τ : ℕ → ℕ, (∀ i < m, τ i = σ i) → τ ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hsub⟩ := hU
  obtain ⟨m, hm⟩ := hI.bddAbove
  refine ⟨m+1, fun τ hτ => hsub ?_⟩
  intro i hi
  have : τ i = σ i := hτ i (Nat.lt_succ_of_le (hm hi))
  rw [this]; exact mem_of_mem_nhds (ht i)

lemma au_Kinf_compact (b : ℕ → ℕ) : IsCompact {σ : ℕ → ℕ | ∀ i, σ i ≤ b i} := by
  have : {σ : ℕ → ℕ | ∀ i, σ i ≤ b i} = Set.pi univ (fun i => Iic (b i)) := by ext; simp [Pi.le_def]
  rw [this]; exact isCompact_univ_pi (fun i => (Set.finite_Iic _).isCompact)

lemma au_cyl_open (σ : ℕ → ℕ) (n : ℕ) : IsOpen {τ : ℕ → ℕ | ∀ i < n, τ i = σ i} := by
  have : {τ : ℕ → ℕ | ∀ i < n, τ i = σ i} = (Iio n).pi (fun i => {σ i}) := by
    ext τ; simp [Set.mem_pi]
  rw [this]; exact isOpen_set_pi (Set.finite_Iio n) (fun i _ => isOpen_discrete _)

lemma au_eventually_sub (b : ℕ → ℕ) {U : Set (ℕ → ℕ)} (hU : IsOpen U)
    (hK : {σ : ℕ → ℕ | ∀ i, σ i ≤ b i} ⊆ U) :
    ∃ k, {σ : ℕ → ℕ | ∀ i < k, σ i ≤ b i} ⊆ U := by
  have key : ∀ σ ∈ {σ : ℕ → ℕ | ∀ i, σ i ≤ b i},
      ∃ m, ∀ τ : ℕ → ℕ, (∀ i < m, τ i = σ i) → τ ∈ U :=
    fun σ hσ => au_cyl_of_nhds (hU.mem_nhds (hK hσ))
  choose! m hm using key
  obtain ⟨F, hFK, hF, hcover⟩ := (au_Kinf_compact b).elim_finite_subcover_image
    (b := {σ : ℕ → ℕ | ∀ i, σ i ≤ b i})
    (c := fun σ => {τ : ℕ → ℕ | ∀ i < m σ, τ i = σ i})
    (fun σ _ => au_cyl_open σ (m σ))
    (fun σ hσ => mem_biUnion hσ (fun i _ => rfl))
  obtain ⟨k, hk⟩ := (hF.image m).bddAbove
  refine ⟨k, fun ρ hρ => ?_⟩
  let ρ' : ℕ → ℕ := fun i => if i < k then ρ i else 0
  have hρ' : ρ' ∈ {σ : ℕ → ℕ | ∀ i, σ i ≤ b i} := by
    intro i
    by_cases hi : i < k
    · simp only [ρ', if_pos hi]; exact hρ i hi
    · simp only [ρ', if_neg hi]; exact Nat.zero_le _
  have := hcover hρ'
  simp only [mem_iUnion, mem_setOf_eq] at this
  obtain ⟨σ, hσF, hagree⟩ := this
  have hmk : m σ ≤ k := hk (mem_image_of_mem m hσF)
  apply hm σ (hFK hσF) ρ
  intro i hi
  have h1 := hagree i hi
  have hik : i < k := lt_of_lt_of_le hi hmk
  simp only [ρ', if_pos hik] at h1
  exact h1

noncomputable def auSeqB (g : (ℕ → ℕ) → ℕ → ℕ) : ℕ → (ℕ → ℕ)
  | 0 => 0
  | k+1 => Function.update (auSeqB g k) k (g (auSeqB g k) k)

lemma auSeqB_agree (g : (ℕ → ℕ) → ℕ → ℕ) :
    ∀ n i, i < n → auSeqB g n i = auSeqB g (i+1) i := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    by_cases h : i = n
    · subst h; rfl
    · have hin : i < n := by omega
      show Function.update (auSeqB g n) n (g (auSeqB g n) n) i = _
      rw [Function.update_of_ne h]
      exact ih i hin

lemma au_analytic_inner {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (f : (ℕ → ℕ) → X)
    (hf : Continuous f) (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ C : Set X, MeasurableSet C ∧ C ⊆ range f ∧ μ (range f) ≤ μ C + ε := by
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε ℕ
  let Kk : (ℕ → ℕ) → ℕ → Set (ℕ → ℕ) := fun b k => {σ | ∀ i < k, σ i ≤ b i}
  have step : ∀ b k, ∃ m, μ (f '' Kk b k) ≤
      μ (f '' Kk (Function.update b k m) (k+1)) + δ k := by
    intro b k
    have hU : Kk b k = ⋃ m, Kk (Function.update b k m) (k+1) := by
      ext σ
      simp only [Kk, mem_setOf_eq, mem_iUnion]
      constructor
      · intro h
        refine ⟨σ k, fun i hi => ?_⟩
        by_cases hik : i = k
        · subst hik; simp
        · rw [Function.update_of_ne hik]; exact h i (by omega)
      · rintro ⟨m, h⟩ i hi
        have := h i (by omega)
        rwa [Function.update_of_ne (by omega)] at this
    have hmono : Monotone (fun m => f '' Kk (Function.update b k m) (k+1)) := by
      intro m m' hmm' τ hτ
      obtain ⟨σ, hσ, rfl⟩ := hτ
      refine ⟨σ, fun i hi => ?_, rfl⟩
      have := hσ i hi
      by_cases hik : i = k
      · subst hik; simp only [Function.update_self] at this ⊢; omega
      · rwa [Function.update_of_ne hik] at this ⊢
    have hS : μ (f '' Kk b k) = ⨆ m, μ (f '' Kk (Function.update b k m) (k+1)) := by
      rw [hU, image_iUnion]; exact hmono.measure_iUnion
    set S := μ (f '' Kk b k) with hSdef
    by_cases hS0 : S = 0
    · exact ⟨0, by rw [hS0]; exact bot_le⟩
    have hlt : S - δ k < S :=
      ENNReal.sub_lt_self (measure_ne_top _ _) hS0 (by simpa using (hδpos k).ne')
    rw [hS] at hlt
    obtain ⟨m, hm⟩ := lt_iSup_iff.1 hlt
    refine ⟨m, ?_⟩
    rw [hS]
    exact (tsub_le_iff_right).1 hm.le |>.trans_eq' (by rw [← hS])
  choose g hg using step
  let B := auSeqB g
  let b : ℕ → ℕ := fun i => B (i+1) i
  have hKB : ∀ k, Kk (B k) k = Kk b k := by
    intro k; ext σ
    simp only [Kk, mem_setOf_eq]
    constructor
    · intro h i hi; exact le_of_le_of_eq (h i hi) (auSeqB_agree g k i hi)
    · intro h i hi; exact le_of_le_of_eq (h i hi) (auSeqB_agree g k i hi).symm
  have tele : ∀ k, μ (range f) ≤ μ (f '' Kk b k) + ∑ i ∈ Finset.range k, (δ i : ℝ≥0∞) := by
    intro k
    induction k with
    | zero =>
      have : Kk b 0 = univ := by ext σ; simp [Kk]
      simp [this, image_univ]
    | succ k ih =>
      refine ih.trans ?_
      rw [Finset.sum_range_succ, ← hKB k]
      have := hg (B k) k
      have hBk : B (k+1) = Function.update (B k) k (g (B k) k) := rfl
      rw [← hBk, hKB (k+1)] at this
      calc μ (f '' Kk (B k) k) + ∑ i ∈ Finset.range k, (δ i : ℝ≥0∞)
          ≤ (μ (f '' Kk b (k+1)) + δ k) + ∑ i ∈ Finset.range k, (δ i : ℝ≥0∞) :=
            add_le_add this le_rfl
        _ = _ := by ring
  have hsumle : ∀ k, ∑ i ∈ Finset.range k, (δ i : ℝ≥0∞) ≤ ε :=
    fun k => (ENNReal.sum_le_tsum _).trans hδsum.le
  refine ⟨⋂ k, closure (f '' Kk b k), MeasurableSet.iInter
    (fun k => isClosed_closure.measurableSet), ?_, ?_⟩
  · -- inclusion
    intro y hy
    by_contra hyA
    have hKc := au_Kinf_compact b
    have hyK : y ∉ f '' {σ : ℕ → ℕ | ∀ i, σ i ≤ b i} := fun h => hyA (image_subset_range _ _ h)
    obtain ⟨U, V, hUo, hVo, hyU, hKV, hUV⟩ :=
      SeparatedNhds.of_isCompact_isCompact isCompact_singleton (hKc.image hf)
        (disjoint_singleton_left.2 hyK)
    obtain ⟨k, hk⟩ := au_eventually_sub b (hVo.preimage hf)
      (fun σ hσ => hKV (mem_image_of_mem f hσ))
    have h1 : f '' Kk b k ⊆ V := by
      rintro _ ⟨σ, hσ, rfl⟩; exact hk hσ
    have hd : Disjoint U (closure (f '' Kk b k)) :=
      (hUV.mono_right h1).closure_right hUo
    have hyc : y ∈ closure (f '' Kk b k) := mem_iInter.1 hy k
    exact hd.ne_of_mem (hyU rfl) hyc rfl
  · have hanti : Antitone (fun k => closure (f '' Kk b k)) := by
      intro k k' hkk'
      apply closure_mono
      rintro _ ⟨σ, hσ, rfl⟩
      exact ⟨σ, fun i hi => hσ i (lt_of_lt_of_le hi hkk'), rfl⟩
    rw [hanti.measure_iInter (fun k => isClosed_closure.measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩, ENNReal.iInf_add]
    refine le_iInf fun k => ?_
    exact (tele k).trans (add_le_add (measure_mono subset_closure) (hsumle k))

lemma au_null_of_inner {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (A : Set X)
    (h : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ C, MeasurableSet C ∧ C ⊆ A ∧ μ A ≤ μ C + ε) :
    NullMeasurableSet A μ := by
  have h' : ∀ n : ℕ, ∃ C, MeasurableSet C ∧ C ⊆ A ∧ μ A ≤ μ C + (n : ℝ≥0∞)⁻¹ :=
    fun n => h _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n))
  choose C hCm hCA hCμ using h'
  let S := ⋃ n, C n
  have hSm : MeasurableSet S := MeasurableSet.iUnion hCm
  have hSA : S ⊆ A := iUnion_subset hCA
  have hle : μ A ≤ μ S := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by simpa using hε.ne')
    calc μ A ≤ μ (C n) + (n : ℝ≥0∞)⁻¹ := hCμ n
      _ ≤ μ S + ε := add_le_add (measure_mono (subset_iUnion C n)) hn.le
  have h0 : μ (A \ S) = 0 := by
    have hT : μ (toMeasurable μ A \ S) = 0 := by
      rw [measure_diff ((subset_toMeasurable μ A).trans' hSA |> fun h => h)
        hSm.nullMeasurableSet (measure_ne_top _ _), measure_toMeasurable]
      exact tsub_eq_zero_of_le hle
    exact measure_mono_null (diff_subset_diff_left (subset_toMeasurable μ A)) hT
  have : A = S ∪ (A \ S) := (union_diff_cancel hSA).symm
  rw [this]
  exact hSm.nullMeasurableSet.union (NullMeasurableSet.of_null h0)

lemma au_t2 {X : Type*} [TopologicalSpace X] [IsBorelSpace X] : T2Space X := by
  obtain ⟨Z, _, _, _, B, _, ⟨e⟩⟩ := IsBorelSpace.exists_homeomorph_borel (X := X)
  exact e.isEmbedding.t2Space

theorem analytic_universallyMeasurable_core {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    (A : Set X) (hA : AnalyticSet A) : IsUniversallyMeasurable A := by
  have := au_t2 (X := X)
  intro p hp
  rw [AnalyticSet] at hA
  rcases hA with hA | ⟨f, hf, rfl⟩
  · subst hA; exact nullMeasurableSet_empty
  · exact au_null_of_inner p _ (fun ε hε => au_analytic_inner p f hf ε hε)

end BertsekasShreve.AnalyticSelection

open BertsekasShreve.AnalyticSelection


theorem solution {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    (A : Set X) (hA : AnalyticSet A) : IsUniversallyMeasurable A := by
  exact analytic_universallyMeasurable_core A hA
