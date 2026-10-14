-- Prove2me | solution 1 for BertsekasShreve.BorelFinite.lemma8_4_Tmu_limits
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:26:00.463843+00:00
-- url     : https://prove2.me/submissions/79c318bf-a9d9-47fe-ba9c-4cde8dc38c36

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy
import Definitions.Def_BertsekasShreve_BorelFinite_Operators



namespace BertsekasShreve.BorelFinite

open MeasureTheory Set Filter Topology ENNReal

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


lemma bf_t2 {X : Type*} [TopologicalSpace X] [BertsekasShreve.AnalyticSelection.IsBorelSpace X] :
    T2Space X := by
  obtain ⟨Z, _, _, _, B, _, ⟨e⟩⟩ :=
    BertsekasShreve.AnalyticSelection.IsBorelSpace.exists_homeomorph_borel (X := X)
  exact e.isEmbedding.t2Space

lemma bf_analytic_null {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (A : Set X)
    (hA : AnalyticSet A) : NullMeasurableSet A μ := by
  rw [AnalyticSet] at hA
  rcases hA with hA | ⟨f, hf, rfl⟩
  · subst hA; exact nullMeasurableSet_empty
  · exact au_null_of_inner μ _ (fun ε hε => au_analytic_inner μ f hf ε hε)

lemma bf_section_analytic {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    {A : Set (X × Y)} (hA : AnalyticSet A) (x : X) : AnalyticSet {y | (x, y) ∈ A} := by
  rw [AnalyticSet] at hA
  rcases hA with hA | ⟨φ, hφ, rfl⟩
  · subst hA; simp [AnalyticSet]
  · have hF : IsClosed {σ : ℕ → ℕ | (φ σ).1 = x} :=
      isClosed_eq (continuous_fst.comp hφ) continuous_const
    have := (hF.analyticSet).image_of_continuous (continuous_snd.comp hφ)
    convert this using 1
    ext y
    simp only [mem_setOf_eq, mem_range, mem_image, Function.comp_apply]
    constructor
    · rintro ⟨σ, hσ⟩; exact ⟨σ, by rw [hσ], by rw [hσ]⟩
    · rintro ⟨σ, h1, h2⟩; exact ⟨σ, Prod.ext h1 h2⟩

lemma bf_nullMeasurable_of_lt {X : Type*} [MeasurableSpace X] (ν : Measure X) (f : X → EReal)
    (h : ∀ c : ℝ, NullMeasurableSet {u | f u < (c : EReal)} ν) : NullMeasurable f ν := by
  have key : ∀ c : EReal, NullMeasurableSet (f ⁻¹' Iio c) ν := by
    intro c
    induction c using EReal.rec with
    | bot => simp only [Iio_bot, preimage_empty]; exact nullMeasurableSet_empty
    | top =>
      have : f ⁻¹' Iio ⊤ = ⋃ n : ℕ, {u | f u < ((n : ℝ) : EReal)} := by
        ext u; simp only [mem_preimage, mem_Iio, mem_iUnion, mem_setOf_eq]
        constructor
        · intro hu
          induction h' : f u using EReal.rec with
          | bot => exact ⟨0, by simp⟩
          | top => rw [h'] at hu; exact absurd hu (lt_irrefl _)
          | coe r =>
            obtain ⟨n, hn⟩ := exists_nat_gt r
            exact ⟨n, by exact_mod_cast hn⟩
        · rintro ⟨n, hn⟩; exact hn.trans (EReal.coe_lt_top _)
      rw [this]; exact NullMeasurableSet.iUnion (fun n => h n)
    | coe c => exact h c
  exact measurable_of_Iio (f := (f : NullMeasurableSpace X ν → EReal)) key

lemma bf_umeas_null {X : Type*} [MeasurableSpace X] {J : X → EReal} (hJ : UMeasurable J)
    (Q : Measure X) [IsProbabilityMeasure Q] : NullMeasurable J Q :=
  fun _ hs => hJ hs Q inferInstance

lemma bf_umeas_pos {X : Type*} [MeasurableSpace X] {J : X → EReal} (hJ : UMeasurable J)
    (Q : Measure X) [IsProbabilityMeasure Q] : AEMeasurable (posPart J) Q :=
  (EReal.continuous_toENNReal.measurable.comp_nullMeasurable (bf_umeas_null hJ Q)).aemeasurable

lemma bf_umeas_neg {X : Type*} [MeasurableSpace X] {J : X → EReal} (hJ : UMeasurable J)
    (Q : Measure X) [IsProbabilityMeasure Q] : AEMeasurable (negPart J) Q :=
  ((EReal.continuous_toENNReal.comp continuous_neg).measurable.comp_nullMeasurable
    (bf_umeas_null hJ Q)).aemeasurable

variable {S C W : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [MeasurableSpace W]

lemma bf_t_meas (M : Model S C W) (x : S) : Measurable (fun u : C => M.t (x, u)) := by
  haveI := M.p_markov
  refine Measure.measurable_of_measurable_coe _ (fun B hB => ?_)
  have hf : ∀ u : C, Measurable (fun w => M.f (x, u, w)) :=
    fun u => M.f_measurable.comp (by fun_prop)
  have : (fun u => M.t (x, u) B) = fun u => (M.p.comap (fun u => (x, u)) (by fun_prop)) u
      (Prod.mk u ⁻¹' {q : C × W | M.f (x, q.1, q.2) ∈ B}) := by
    funext u; simp only [Model.t]; rw [Measure.map_apply (hf u) hB]; rfl
  rw [this]
  exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left
    (hB.preimage (M.f_measurable.comp (by fun_prop)))

instance bf_t_prob (M : Model S C W) (z : S × C) : IsProbabilityMeasure (M.t z) := by
  haveI := M.p_markov
  unfold Model.t
  exact Measure.isProbabilityMeasure_map (M.f_measurable.comp (by fun_prop)).aemeasurable

noncomputable def bfK (M : Model S C W) (x : S) : ProbabilityTheory.Kernel C S :=
  ⟨fun u => M.t (x, u), bf_t_meas M x⟩

instance (M : Model S C W) (x : S) : ProbabilityTheory.IsMarkovKernel (bfK M x) :=
  ⟨fun u => bf_t_prob M (x, u)⟩

open ProbabilityTheory in
lemma bf_aemeas_lint (M : Model S C W) (x : S) (ν : Measure C) [IsProbabilityMeasure ν]
    (h : S → ENNReal) (hh : ∀ Q : Measure S, IsProbabilityMeasure Q → AEMeasurable h Q) :
    AEMeasurable (fun u => ∫⁻ y, h y ∂(M.t (x, u))) ν := by
  have hQ := hh ((bfK M x) ∘ₘ ν) inferInstance
  have hae := Measure.ae_ae_of_ae_comp hQ.ae_eq_mk
  refine (Measurable.lintegral_kernel (κ := bfK M x) hQ.measurable_mk).aemeasurable.congr ?_
  filter_upwards [hae] with u hu
  exact (lintegral_congr_ae hu).symm


open BertsekasShreve.FiniteHorizon in
lemma bf_g_null (M : Model S C W) [T2Space S] [T2Space C] [OpensMeasurableSpace C] (x : S)
    (ν : Measure C) [IsProbabilityMeasure ν] (hν : ν (M.U x) = 1) :
    NullMeasurable (fun u => M.g (x, u)) ν := by
  have hU : NullMeasurableSet (M.U x) ν :=
    bf_analytic_null ν _ (bf_section_analytic M.g_lsa.1 x)
  have hc : ν (M.U x)ᶜ = 0 := (prob_compl_eq_zero_iff₀ hU).2 hν
  apply bf_nullMeasurable_of_lt
  intro c
  have hA := bf_analytic_null ν _ (bf_section_analytic (M.g_lsa.2 c) x)
  have : {u | M.g (x, u) < (c : EReal)} =
      {y | (x, y) ∈ {z : S × C | z ∈ {z : S × C | z.2 ∈ M.U z.1} ∧ M.g z < (c : EReal)}} ∪
      ({u | M.g (x, u) < (c : EReal)} ∩ (M.U x)ᶜ) := by
    ext u; by_cases hu : u ∈ M.U x <;> simp [hu]
  rw [this]
  exact hA.union (NullMeasurableSet.of_null (measure_mono_null inter_subset_right hc))

open BertsekasShreve.FiniteHorizon in
noncomputable def bfF (α : ℝ) (a : EReal) (P N : ℝ≥0∞) : EReal :=
  badd a ((α : EReal) * (if P = ⊤ then ⊤ else (P : EReal) - N))

lemma bf_H_eq (M : Model S C W) (J : S → EReal) (z : S × C) :
    H M J z = bfF M.α (M.g z) (∫⁻ y, posPart J y ∂(M.t z)) (∫⁻ y, negPart J y ∂(M.t z)) := rfl

open BertsekasShreve.FiniteHorizon in
lemma bf_badd_meas : Measurable (fun p : EReal × EReal => badd p.1 p.2) := by
  unfold badd
  refine Measurable.ite ?_ measurable_const (measurable_fst.add measurable_snd)
  exact ((measurableSet_singleton ⊤).preimage measurable_fst).union
    ((measurableSet_singleton ⊤).preimage measurable_snd)

lemma bf_F_meas (α : ℝ) :
    Measurable (fun q : EReal × ℝ≥0∞ × ℝ≥0∞ => bfF α q.1 q.2.1 q.2.2) := by
  unfold bfF
  refine bf_badd_meas.comp (measurable_fst.prodMk (measurable_const.mul ?_))
  refine Measurable.ite ((measurableSet_singleton ⊤).preimage (measurable_fst.comp measurable_snd))
    measurable_const ?_
  have : (fun q : EReal × ℝ≥0∞ × ℝ≥0∞ => ((q.2.1 : EReal) - (q.2.2 : EReal))) =
      fun q => (q.2.1 : EReal) + -(q.2.2 : EReal) := by funext q; rw [sub_eq_add_neg]
  rw [this]
  exact (measurable_coe_ennreal_ereal.comp (measurable_fst.comp measurable_snd)).add
    ((continuous_neg (G := EReal)).measurable.comp
      (measurable_coe_ennreal_ereal.comp (measurable_snd.comp measurable_snd)))

lemma bf_H_aemeas (M : Model S C W) [T2Space S] [T2Space C] [OpensMeasurableSpace C] (x : S)
    (ν : Measure C) [IsProbabilityMeasure ν] (hν : ν (M.U x) = 1) (J : S → EReal)
    (hJ : UMeasurable J) : AEMeasurable (fun u => H M J (x, u)) ν := by
  have h1 := (bf_g_null M x ν hν).aemeasurable
  have h2 := bf_aemeas_lint M x ν (posPart J) (fun Q _ => bf_umeas_pos hJ Q)
  have h3 := bf_aemeas_lint M x ν (negPart J) (fun Q _ => bf_umeas_neg hJ Q)
  simp_rw [bf_H_eq]
  exact (bf_F_meas M.α).comp_aemeasurable (h1.prodMk (h2.prodMk h3))

lemma bf_pos_ae {X : Type*} [MeasurableSpace X] {ν : Measure X} {f : X → EReal}
    (hf : AEMeasurable f ν) : AEMeasurable (posPart f) ν :=
  EReal.continuous_toENNReal.measurable.comp_aemeasurable hf

lemma bf_neg_ae {X : Type*} [MeasurableSpace X] {ν : Measure X} {f : X → EReal}
    (hf : AEMeasurable f ν) : AEMeasurable (negPart f) ν :=
  (EReal.continuous_toENNReal.comp continuous_neg).measurable.comp_aemeasurable hf


lemma bf_coe_ennreal_sub_top {N : ℝ≥0∞} (hN : N ≠ ⊤) : (⊤ : EReal) - (N : EReal) = ⊤ := by
  lift N to NNReal using hN
  have : ((N : ℝ≥0∞) : EReal) = ((N : ℝ) : EReal) := rfl
  rw [this, EReal.top_sub_coe]

lemma bf_extInt_eq {X : Type*} [MeasurableSpace X] (ν : Measure X) (f : X → EReal)
    (h : ∫⁻ y, posPart f y ∂ν ≠ ⊤ ∨ ∫⁻ y, negPart f y ∂ν ≠ ⊤) :
    extInt (fun h => ∫⁻ y, h y ∂ν) f =
      ((∫⁻ y, posPart f y ∂ν : ℝ≥0∞) : EReal) - ((∫⁻ y, negPart f y ∂ν : ℝ≥0∞) : EReal) := by
  unfold extInt
  split_ifs with hP
  · rcases h with h | h
    · exact absurd hP h
    · simp only at hP; rw [hP]; exact (bf_coe_ennreal_sub_top h).symm
  · rfl

lemma bf_sub_tendsto {P N : ℕ → ℝ≥0∞} {P' N' : ℝ≥0∞} (hP : Tendsto P atTop (𝓝 P'))
    (hN : Tendsto N atTop (𝓝 N')) (h : P' ≠ ⊤ ∨ N' ≠ ⊤) :
    Tendsto (fun k => (P k : EReal) - (N k : EReal)) atTop (𝓝 ((P' : EReal) - (N' : EReal))) := by
  simp_rw [sub_eq_add_neg]
  have h1 : ((P' : EReal), -(N' : EReal)).1 ≠ ⊤ ∨ ((P' : EReal), -(N' : EReal)).2 ≠ ⊥ := by
    rcases h with h | h
    · left; simpa [EReal.coe_ennreal_eq_top_iff] using h
    · right; simpa [EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff] using h
  have h2 : ((P' : EReal), -(N' : EReal)).1 ≠ ⊥ ∨ ((P' : EReal), -(N' : EReal)).2 ≠ ⊤ :=
    Or.inl (EReal.coe_ennreal_ne_bot _)
  have hc := (EReal.continuousAt_add h1 h2).tendsto
  exact hc.comp (((continuous_coe_ennreal_ereal.tendsto _).comp hP).prodMk_nhds
    (((continuous_neg (G := EReal)).tendsto _).comp ((continuous_coe_ennreal_ereal.tendsto _).comp hN)))

lemma bf_ext_anti {X : Type*} [MeasurableSpace X] (ν : Measure X) (f : ℕ → X → EReal)
    (F : X → EReal) (hm : ∀ k, AEMeasurable (f k) ν)
    (hanti : ∀ᵐ y ∂ν, Antitone (fun k => f k y))
    (hlim : ∀ᵐ y ∂ν, Tendsto (fun k => f k y) atTop (𝓝 (F y)))
    (h0 : ∫⁻ y, posPart (f 0) y ∂ν ≠ ⊤) :
    Tendsto (fun k => extInt (fun h => ∫⁻ y, h y ∂ν) (f k)) atTop
      (𝓝 (extInt (fun h => ∫⁻ y, h y ∂ν) F)) := by
  have hP : Tendsto (fun k => ∫⁻ y, posPart (f k) y ∂ν) atTop (𝓝 (∫⁻ y, posPart F y ∂ν)) :=
    lintegral_tendsto_of_tendsto_of_antitone (fun k => bf_pos_ae (hm k))
      (hanti.mono fun y hy => fun i j hij => EReal.toENNReal_le_toENNReal (hy hij)) h0
      (hlim.mono fun y hy => (EReal.continuous_toENNReal.tendsto _).comp hy)
  have hN : Tendsto (fun k => ∫⁻ y, negPart (f k) y ∂ν) atTop (𝓝 (∫⁻ y, negPart F y ∂ν)) :=
    lintegral_tendsto_of_tendsto_of_monotone (fun k => bf_neg_ae (hm k))
      (hanti.mono fun y hy => fun i j hij =>
        EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (hy hij)))
      (hlim.mono fun y hy =>
        ((EReal.continuous_toENNReal.comp continuous_neg).tendsto _).comp hy)
  have hPk : ∀ k, ∫⁻ y, posPart (f k) y ∂ν ≤ ∫⁻ y, posPart (f 0) y ∂ν := fun k =>
    lintegral_mono_ae (hanti.mono fun y hy => EReal.toENNReal_le_toENNReal (hy (Nat.zero_le k)))
  have hP' : ∫⁻ y, posPart F y ∂ν ≠ ⊤ :=
    ne_top_of_le_ne_top h0 (le_of_tendsto' hP hPk)
  have e1 : ∀ k, extInt (fun h => ∫⁻ y, h y ∂ν) (f k) = _ := fun k =>
    bf_extInt_eq ν (f k) (Or.inl (ne_top_of_le_ne_top h0 (hPk k)))
  rw [bf_extInt_eq ν F (Or.inl hP')]
  simp_rw [e1]
  exact bf_sub_tendsto hP hN (Or.inl hP')

lemma bf_ext_mono {X : Type*} [MeasurableSpace X] (ν : Measure X) (f : ℕ → X → EReal)
    (F : X → EReal) (hm : ∀ k, AEMeasurable (f k) ν)
    (hmono : ∀ᵐ y ∂ν, Monotone (fun k => f k y))
    (hlim : ∀ᵐ y ∂ν, Tendsto (fun k => f k y) atTop (𝓝 (F y)))
    (h0 : ∫⁻ y, negPart (f 0) y ∂ν ≠ ⊤) :
    Tendsto (fun k => extInt (fun h => ∫⁻ y, h y ∂ν) (f k)) atTop
      (𝓝 (extInt (fun h => ∫⁻ y, h y ∂ν) F)) := by
  have hP : Tendsto (fun k => ∫⁻ y, posPart (f k) y ∂ν) atTop (𝓝 (∫⁻ y, posPart F y ∂ν)) :=
    lintegral_tendsto_of_tendsto_of_monotone (fun k => bf_pos_ae (hm k))
      (hmono.mono fun y hy => fun i j hij => EReal.toENNReal_le_toENNReal (hy hij))
      (hlim.mono fun y hy => (EReal.continuous_toENNReal.tendsto _).comp hy)
  have hN : Tendsto (fun k => ∫⁻ y, negPart (f k) y ∂ν) atTop (𝓝 (∫⁻ y, negPart F y ∂ν)) :=
    lintegral_tendsto_of_tendsto_of_antitone (fun k => bf_neg_ae (hm k))
      (hmono.mono fun y hy => fun i j hij =>
        EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (hy hij))) h0
      (hlim.mono fun y hy =>
        ((EReal.continuous_toENNReal.comp continuous_neg).tendsto _).comp hy)
  have hNk : ∀ k, ∫⁻ y, negPart (f k) y ∂ν ≤ ∫⁻ y, negPart (f 0) y ∂ν := fun k =>
    lintegral_mono_ae (hmono.mono fun y hy =>
      EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (hy (Nat.zero_le k))))
  have hN' : ∫⁻ y, negPart F y ∂ν ≠ ⊤ :=
    ne_top_of_le_ne_top h0 (le_of_tendsto' hN hNk)
  have e1 : ∀ k, extInt (fun h => ∫⁻ y, h y ∂ν) (f k) = _ := fun k =>
    bf_extInt_eq ν (f k) (Or.inr (ne_top_of_le_ne_top h0 (hNk k)))
  rw [bf_extInt_eq ν F (Or.inr hN')]
  simp_rw [e1]
  exact bf_sub_tendsto hP hN (Or.inr hN')

lemma bf_ext_dom {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (f : ℕ → X → EReal) (F : X → EReal) (hm : ∀ k, AEMeasurable (f k) ν) (b : ℝ)
    (hb : ∀ k, ∀ᵐ y ∂ν, f k y ≤ (b : EReal) ∧ -(b : EReal) ≤ f k y)
    (hlim : ∀ᵐ y ∂ν, Tendsto (fun k => f k y) atTop (𝓝 (F y))) :
    Tendsto (fun k => extInt (fun h => ∫⁻ y, h y ∂ν) (f k)) atTop
      (𝓝 (extInt (fun h => ∫⁻ y, h y ∂ν) F)) := by
  have hfin : ∫⁻ _y, ((b : EReal).toENNReal) ∂ν ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  have hP : Tendsto (fun k => ∫⁻ y, posPart (f k) y ∂ν) atTop (𝓝 (∫⁻ y, posPart F y ∂ν)) :=
    tendsto_lintegral_of_dominated_convergence' _ (fun k => bf_pos_ae (hm k))
      (fun k => (hb k).mono fun y hy => EReal.toENNReal_le_toENNReal hy.1) hfin
      (hlim.mono fun y hy => (EReal.continuous_toENNReal.tendsto _).comp hy)
  have hN : Tendsto (fun k => ∫⁻ y, negPart (f k) y ∂ν) atTop (𝓝 (∫⁻ y, negPart F y ∂ν)) :=
    tendsto_lintegral_of_dominated_convergence' _ (fun k => bf_neg_ae (hm k))
      (fun k => (hb k).mono fun y hy => EReal.toENNReal_le_toENNReal (EReal.neg_le.2 hy.2)) hfin
      (hlim.mono fun y hy =>
        ((EReal.continuous_toENNReal.comp continuous_neg).tendsto _).comp hy)
  have hPk : ∀ k, ∫⁻ y, posPart (f k) y ∂ν ≤ ∫⁻ _y, ((b : EReal).toENNReal) ∂ν := fun k =>
    lintegral_mono_ae ((hb k).mono fun y hy => EReal.toENNReal_le_toENNReal hy.1)
  have hP' : ∫⁻ y, posPart F y ∂ν ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (le_of_tendsto' hP hPk)
  have e1 : ∀ k, extInt (fun h => ∫⁻ y, h y ∂ν) (f k) = _ := fun k =>
    bf_extInt_eq ν (f k) (Or.inl (ne_top_of_le_ne_top hfin (hPk k)))
  rw [bf_extInt_eq ν F (Or.inl hP')]
  simp_rw [e1]
  exact bf_sub_tendsto hP hN (Or.inl hP')

open BertsekasShreve.FiniteHorizon in
lemma bf_badd_tendsto {a : EReal} {y : ℕ → EReal} {y' : EReal} (ha : a ≠ ⊤)
    (hy : Tendsto y atTop (𝓝 y')) (hc : a ≠ ⊥ ∨ (y' ≠ ⊤ ∧ ∀ k, y k ≠ ⊤)) :
    Tendsto (fun k => badd a (y k)) atTop (𝓝 (badd a y')) := by
  by_cases hab : a = ⊥
  · subst hab
    rcases hc with hc | ⟨hy', hyk⟩
    · exact absurd rfl hc
    have e : ∀ z : EReal, z ≠ ⊤ → badd ⊥ z = ⊥ := fun z hz => by
      unfold badd; rw [if_neg (by simp [hz])]; exact EReal.bot_add z
    simp_rw [e _ (hyk _), e _ hy']
    exact tendsto_const_nhds
  · have e : ∀ z : EReal, badd a z = a + z := fun z => by
      unfold badd
      split_ifs with h
      · rcases h with h | h
        · exact absurd h ha
        · rw [h, EReal.add_top_of_ne_bot hab]
      · rfl
    simp_rw [e]
    exact (EReal.continuousAt_add (p := (a, y')) (Or.inl ha) (Or.inl hab)).tendsto.comp
      (tendsto_const_nhds.prodMk_nhds hy)

lemma bf_mul_tendsto {α : ℝ} (hα : 0 < α) {y : ℕ → EReal} {y' : EReal}
    (hy : Tendsto y atTop (𝓝 y')) :
    Tendsto (fun k => (α : EReal) * y k) atTop (𝓝 ((α : EReal) * y')) := by
  have h0 : (α : EReal) ≠ 0 := by exact_mod_cast hα.ne'
  exact (EReal.continuousAt_mul (p := ((α : EReal), y')) (Or.inl h0) (Or.inl h0)
    (Or.inl (EReal.coe_ne_bot α)) (Or.inl (EReal.coe_ne_top α))).tendsto.comp
    (tendsto_const_nhds.prodMk_nhds hy)


lemma bf_extInt_mono {X : Type*} [MeasurableSpace X] (ν : Measure X) {f f' : X → EReal}
    (h : ∀ y, f y ≤ f' y) :
    extInt (fun h => ∫⁻ y, h y ∂ν) f ≤ extInt (fun h => ∫⁻ y, h y ∂ν) f' := by
  have hP : ∫⁻ y, posPart f y ∂ν ≤ ∫⁻ y, posPart f' y ∂ν :=
    lintegral_mono fun y => EReal.toENNReal_le_toENNReal (h y)
  have hN : ∫⁻ y, negPart f' y ∂ν ≤ ∫⁻ y, negPart f y ∂ν :=
    lintegral_mono fun y => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (h y))
  unfold extInt
  simp only
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (top_le_iff.1 (h1 ▸ hP)) h2
  · exact le_top
  · exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.2 hP)
      (EReal.coe_ennreal_le_coe_ennreal_iff.2 hN)

open BertsekasShreve.FiniteHorizon in
lemma bf_badd_mono {a a' b b' : EReal} (ha : a ≤ a') (hb : b ≤ b') : badd a b ≤ badd a' b' := by
  unfold badd
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso; apply h2
    rcases h1 with h1 | h1
    · left; rw [h1] at ha; exact top_le_iff.1 ha
    · right; rw [h1] at hb; exact top_le_iff.1 hb
  · exact le_top
  · exact add_le_add ha hb

lemma bf_H_mono (M : Model S C W) {J J' : S → EReal} (h : ∀ y, J y ≤ J' y) (z : S × C) :
    H M J z ≤ H M J' z :=
  bf_badd_mono le_rfl (mul_le_mul_of_nonneg_left (bf_extInt_mono _ h)
    (by exact_mod_cast M.α_pos.le))

lemma bf_Tmu_mono (M : Model S C W) (μ : UCS M) {J J' : S → EReal} (h : ∀ y, J y ≤ J' y)
    (x : S) : Tmu M μ J x ≤ Tmu M μ J' x :=
  bf_extInt_mono _ (fun u => bf_H_mono M h (x, u))

open BertsekasShreve.FiniteHorizon in
lemma bf_badd_ne_top {a b : EReal} (h : badd a b ≠ ⊤) : a ≠ ⊤ ∧ b ≠ ⊤ := by
  unfold badd at h
  split_ifs at h with h1
  · exact absurd rfl h
  · push_neg at h1; exact h1

open BertsekasShreve.FiniteHorizon in
lemma bf_badd_ge {a b : EReal} (ha : 0 ≤ a) : b ≤ badd a b := by
  unfold badd
  split_ifs
  · exact le_top
  · simpa using add_le_add ha (le_refl b)

lemma bf_extInt_ne_top {X : Type*} [MeasurableSpace X] (ν : Measure X) {f : X → EReal}
    (h : extInt (fun h => ∫⁻ y, h y ∂ν) f ≠ ⊤) : ∫⁻ y, posPart f y ∂ν ≠ ⊤ := by
  intro hP; apply h; unfold extInt; simp only; rw [if_pos hP]

lemma bf_extInt_coe {X : Type*} [MeasurableSpace X] (ν : Measure X) (h : X → ℝ≥0∞) :
    extInt (fun h => ∫⁻ y, h y ∂ν) (fun y => (h y : EReal)) = ((∫⁻ y, h y ∂ν : ℝ≥0∞) : EReal) := by
  have e1 : posPart (fun y => (h y : EReal)) = h := by
    funext y; simp [posPart, EReal.toENNReal_coe]
  have e2 : negPart (fun y => (h y : EReal)) = 0 := by
    funext y; simp only [negPart, Pi.zero_apply]
    exact EReal.toENNReal_of_nonpos (by rw [EReal.neg_le, neg_zero]; exact EReal.coe_ennreal_nonneg _)
  unfold extInt
  simp only [e1, e2, Pi.zero_apply, lintegral_zero]
  split_ifs with hP
  · rw [hP]; rfl
  · simp

lemma bf_extInt_ge_neg {X : Type*} [MeasurableSpace X] (ν : Measure X) (f : X → EReal) :
    -((∫⁻ y, negPart f y ∂ν : ℝ≥0∞) : EReal) ≤ extInt (fun h => ∫⁻ y, h y ∂ν) f := by
  unfold extInt; simp only
  split_ifs
  · exact le_top
  · have := EReal.sub_le_sub (EReal.coe_ennreal_nonneg (∫⁻ y, posPart f y ∂ν))
      (le_refl ((∫⁻ y, negPart f y ∂ν : ℝ≥0∞) : EReal))
    simpa using this

lemma bf_extInt_bounds {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (f : X → EReal) (b : ℝ) (hb0 : 0 ≤ b) (h : ∀ y, f y ≤ (b : EReal) ∧ -(b : EReal) ≤ f y) :
    extInt (fun h => ∫⁻ y, h y ∂ν) f ≤ (b : EReal) ∧
      -(b : EReal) ≤ extInt (fun h => ∫⁻ y, h y ∂ν) f := by
  have hbE : (b : EReal).toENNReal = ENNReal.ofReal b := by
    rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top b), EReal.toReal_coe]
  have hP : ∫⁻ y, posPart f y ∂ν ≤ ENNReal.ofReal b := by
    calc ∫⁻ y, posPart f y ∂ν ≤ ∫⁻ _y, ENNReal.ofReal b ∂ν :=
          lintegral_mono fun y => hbE ▸ EReal.toENNReal_le_toENNReal (h y).1
      _ = ENNReal.ofReal b := by simp
  have hN : ∫⁻ y, negPart f y ∂ν ≤ ENNReal.ofReal b := by
    calc ∫⁻ y, negPart f y ∂ν ≤ ∫⁻ _y, ENNReal.ofReal b ∂ν :=
          lintegral_mono fun y => hbE ▸ EReal.toENNReal_le_toENNReal (EReal.neg_le.2 (h y).2)
      _ = ENNReal.ofReal b := by simp
  have hPt : ∫⁻ y, posPart f y ∂ν ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hP
  rw [bf_extInt_eq ν f (Or.inl hPt)]
  have hb' : ((ENNReal.ofReal b : ℝ≥0∞) : EReal) = (b : EReal) := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left hb0]
  have hP' : ((∫⁻ y, posPart f y ∂ν : ℝ≥0∞) : EReal) ≤ b :=
    hb' ▸ EReal.coe_ennreal_le_coe_ennreal_iff.2 hP
  have hN' : ((∫⁻ y, negPart f y ∂ν : ℝ≥0∞) : EReal) ≤ b :=
    hb' ▸ EReal.coe_ennreal_le_coe_ennreal_iff.2 hN
  constructor
  · have := EReal.sub_le_sub hP' (EReal.coe_ennreal_nonneg (∫⁻ y, negPart f y ∂ν))
    simpa using this
  · have := EReal.sub_le_sub (EReal.coe_ennreal_nonneg (∫⁻ y, posPart f y ∂ν)) hN'
    simpa using this

lemma bf_U_ae (M : Model S C W) [T2Space S] [T2Space C] [OpensMeasurableSpace C] (x : S)
    (ν : Measure C) [IsProbabilityMeasure ν] (hν : ν (M.U x) = 1) : ∀ᵐ u ∂ν, u ∈ M.U x := by
  have hU : NullMeasurableSet (M.U x) ν :=
    bf_analytic_null ν _ (bf_section_analytic M.g_lsa.1 x)
  rw [ae_iff]
  exact (prob_compl_eq_zero_iff₀ hU).2 hν


open BertsekasShreve.FiniteHorizon in
theorem lemma8_4_core {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (μ : UCS M) (Js : ℕ → S → EReal) (Jl : S → EReal) (hJs : ∀ k, UMeasurable (Js k)) :
    ((∀ x, Tmu M μ (Js 0) x < ⊤) → (∀ x, Antitone fun k => Js k x) →
        (∀ x, Tendsto (fun k => Js k x) atTop (𝓝 (Jl x))) →
        (∀ x, Antitone fun k => Tmu M μ (Js k) x) ∧
          ∀ x, Tendsto (fun k => Tmu M μ (Js k) x) atTop (𝓝 (Tmu M μ Jl x))) ∧
    ((∀ x, Tmu M μ (fun y => ((negPart (Js 0) y : ENNReal) : EReal)) x < ⊤) →
        (∀ z ∈ M.Γ, 0 ≤ M.g z) → (∀ x, Monotone fun k => Js k x) →
        (∀ x, Tendsto (fun k => Js k x) atTop (𝓝 (Jl x))) →
        (∀ x, Monotone fun k => Tmu M μ (Js k) x) ∧
          ∀ x, Tendsto (fun k => Tmu M μ (Js k) x) atTop (𝓝 (Tmu M μ Jl x))) ∧
    ((∃ b : ℝ, ∀ k x, Js k x ≤ b ∧ -(b : EReal) ≤ Js k x) →
        (∃ b : ℝ, ∀ z ∈ M.Γ, M.g z ≤ b ∧ -(b : EReal) ≤ M.g z) →
        (∀ x, Tendsto (fun k => Js k x) atTop (𝓝 (Jl x))) →
        ∀ x, Tendsto (fun k => Tmu M μ (Js k) x) atTop (𝓝 (Tmu M μ Jl x))) := by
  haveI : T2Space S := bf_t2
  haveI : T2Space C := bf_t2
  have hprob : ∀ x, IsProbabilityMeasure (μ.1.toFun x) := μ.1.isProb
  have hU : ∀ x, μ.1.toFun x (M.U x) = 1 := μ.2
  have hα0 : (M.α : EReal) ≠ 0 := by exact_mod_cast M.α_pos.ne'
  have hJae : ∀ k (z : S × C), AEMeasurable (Js k) (M.t z) :=
    fun k z => (bf_umeas_null (hJs k) _).aemeasurable
  refine ⟨?_, ?_, ?_⟩
  · -- (a)
    intro hT0 hanti hlim
    refine ⟨fun x i j hij => bf_Tmu_mono M μ (fun y => hanti y hij) x, fun x => ?_⟩
    haveI := hprob x
    set ν := μ.1.toFun x with hν
    have h0 : ∫⁻ u, posPart (fun u => H M (Js 0) (x, u)) u ∂ν ≠ ⊤ :=
      bf_extInt_ne_top ν (hT0 x).ne
    have hHae : ∀ k, AEMeasurable (fun u => H M (Js k) (x, u)) ν :=
      fun k => bf_H_aemeas M x ν (hU x) _ (hJs k)
    have hfin := ae_lt_top' (bf_pos_ae (hHae 0)) h0
    refine bf_ext_anti ν (fun k u => H M (Js k) (x, u)) (fun u => H M Jl (x, u)) hHae
      (ae_of_all _ fun u i j hij => bf_H_mono M (fun y => hanti y hij) (x, u)) ?_ h0
    filter_upwards [hfin] with u hu
    have hH0 : H M (Js 0) (x, u) ≠ ⊤ := EReal.toENNReal_ne_top_iff.1 hu.ne
    obtain ⟨hg, hE0⟩ := bf_badd_ne_top hH0
    have hE0' : extInt (fun h => ∫⁻ y, h y ∂(M.t (x, u))) (Js 0) ≠ ⊤ := by
      intro h; apply hE0; rw [h]; exact EReal.coe_mul_top_of_pos M.α_pos
    have hE := bf_ext_anti (M.t (x, u)) Js Jl (fun k => hJae k (x, u))
      (ae_of_all _ fun y => hanti y) (ae_of_all _ fun y => hlim y)
      (bf_extInt_ne_top _ hE0')
    have hle : ∀ (J : S → EReal), (∀ y, J y ≤ Js 0 y) →
        (M.α : EReal) * extInt (fun h => ∫⁻ y, h y ∂(M.t (x, u))) J ≠ ⊤ := by
      intro J hJ htop
      apply hE0
      exact top_le_iff.1 (htop ▸ mul_le_mul_of_nonneg_left (bf_extInt_mono _ hJ)
        (by exact_mod_cast M.α_pos.le))
    exact bf_badd_tendsto hg (bf_mul_tendsto M.α_pos hE)
      (Or.inr ⟨hle Jl (fun y => (hanti y).le_of_tendsto (hlim y) 0),
        fun k => hle (Js k) (fun y => hanti y (Nat.zero_le k))⟩)
  · -- (b)
    intro hT0 hg0 hmono hlim
    refine ⟨fun x i j hij => bf_Tmu_mono M μ (fun y => hmono y hij) x, fun x => ?_⟩
    haveI := hprob x
    set ν := μ.1.toFun x with hν
    set Jn : S → EReal := fun y => ((negPart (Js 0) y : ENNReal) : EReal) with hJn
    have hJnm : UMeasurable Jn :=
      measurable_coe_ennreal_ereal.comp
        ((EReal.continuous_toENNReal.comp continuous_neg).measurable.comp (hJs 0))
    have hHae : ∀ k, AEMeasurable (fun u => H M (Js k) (x, u)) ν :=
      fun k => bf_H_aemeas M x ν (hU x) _ (hJs k)
    have hPn : ∫⁻ u, posPart (fun u => H M Jn (x, u)) u ∂ν ≠ ⊤ :=
      bf_extInt_ne_top ν (hT0 x).ne
    have hfin := ae_lt_top' (bf_pos_ae (bf_H_aemeas M x ν (hU x) Jn hJnm)) hPn
    have hUae := bf_U_ae M x ν (hU x)
    have hEn : ∀ u, extInt (fun h => ∫⁻ y, h y ∂(M.t (x, u))) Jn =
        ((∫⁻ y, negPart (Js 0) y ∂(M.t (x, u)) : ℝ≥0∞) : EReal) := fun u =>
      bf_extInt_coe _ _
    have hcmp : ∀ u ∈ M.U x, negPart (fun u => H M (Js 0) (x, u)) u ≤
        posPart (fun u => H M Jn (x, u)) u := by
      intro u hu
      have hg : 0 ≤ M.g (x, u) := hg0 (x, u) hu
      have h1 : (M.α : EReal) * ((∫⁻ y, negPart (Js 0) y ∂(M.t (x, u)) : ℝ≥0∞) : EReal) ≤
          H M Jn (x, u) := by
        have := bf_badd_ge (b := (M.α : EReal) * extInt (fun h => ∫⁻ y, h y ∂(M.t (x, u))) Jn) hg
        refine le_trans (le_of_eq ?_) this
        rw [hEn u]
      have h2 : -((M.α : EReal) * ((∫⁻ y, negPart (Js 0) y ∂(M.t (x, u)) : ℝ≥0∞) : EReal)) ≤
          H M (Js 0) (x, u) := by
        rw [← mul_neg]
        exact (mul_le_mul_of_nonneg_left (bf_extInt_ge_neg _ (Js 0))
          (by exact_mod_cast M.α_pos.le)).trans (bf_badd_ge hg)
      exact EReal.toENNReal_le_toENNReal ((EReal.neg_le.2 h2).trans h1)
    have h0 : ∫⁻ u, negPart (fun u => H M (Js 0) (x, u)) u ∂ν ≠ ⊤ :=
      ne_top_of_le_ne_top hPn (lintegral_mono_ae (hUae.mono hcmp))
    refine bf_ext_mono ν (fun k u => H M (Js k) (x, u)) (fun u => H M Jl (x, u)) hHae
      (ae_of_all _ fun u i j hij => bf_H_mono M (fun y => hmono y hij) (x, u)) ?_ h0
    filter_upwards [hfin, hUae] with u hu hux
    have hHn : H M Jn (x, u) ≠ ⊤ := EReal.toENNReal_ne_top_iff.1 hu.ne
    obtain ⟨hg, hE0⟩ := bf_badd_ne_top hHn
    have hgb : M.g (x, u) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) (hg0 (x, u) hux)
    have hN0 : ∫⁻ y, negPart (Js 0) y ∂(M.t (x, u)) ≠ ⊤ := by
      intro h; apply hE0; rw [hEn u, h]; exact EReal.coe_mul_top_of_pos M.α_pos
    have hE := bf_ext_mono (M.t (x, u)) Js Jl (fun k => hJae k (x, u))
      (ae_of_all _ fun y => hmono y) (ae_of_all _ fun y => hlim y) hN0
    exact bf_badd_tendsto hg (bf_mul_tendsto M.α_pos hE) (Or.inl hgb)
  · -- (c)
    rintro ⟨b, hb⟩ ⟨bg, hbg⟩ hlim x
    haveI := hprob x
    set ν := μ.1.toFun x with hν
    have hb0 : 0 ≤ b := by
      obtain ⟨h1, h2⟩ := hb 0 (Classical.arbitrary S)
      have : -(b : EReal) ≤ (b : EReal) := h2.trans h1
      have : ((-b : ℝ) : EReal) ≤ (b : EReal) := by exact_mod_cast this
      have : -b ≤ b := by exact_mod_cast this
      linarith
    have hHae : ∀ k, AEMeasurable (fun u => H M (Js k) (x, u)) ν :=
      fun k => bf_H_aemeas M x ν (hU x) _ (hJs k)
    have hUae := bf_U_ae M x ν (hU x)
    have hgfin : ∀ u ∈ M.U x, ∃ r : ℝ, M.g (x, u) = r ∧ r ≤ bg ∧ -bg ≤ r := by
      intro u hu
      obtain ⟨h1, h2⟩ := hbg (x, u) hu
      have hnt : M.g (x, u) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top bg) h1
      have hnb : M.g (x, u) ≠ ⊥ := ne_bot_of_le_ne_bot (by
        rw [← EReal.coe_neg]; exact EReal.coe_ne_bot _) h2
      refine ⟨(M.g (x, u)).toReal, (EReal.coe_toReal hnt hnb).symm, ?_, ?_⟩
      · rw [← EReal.coe_toReal hnt hnb] at h1; exact_mod_cast h1
      · rw [← EReal.coe_toReal hnt hnb, ← EReal.coe_neg] at h2; exact_mod_cast h2
    refine bf_ext_dom ν (fun k u => H M (Js k) (x, u)) (fun u => H M Jl (x, u)) hHae
      (bg + M.α * b) (fun k => ?_) ?_
    · filter_upwards [hUae] with u hu
      obtain ⟨r, hr, hr1, hr2⟩ := hgfin u hu
      obtain ⟨he1, he2⟩ := bf_extInt_bounds (M.t (x, u)) (Js k) b hb0 (hb k)
      set E := extInt (fun h => ∫⁻ y, h y ∂(M.t (x, u))) (Js k) with hE
      have hEt : E ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top b) he1
      have hEb : E ≠ ⊥ := ne_bot_of_le_ne_bot (by
        rw [← EReal.coe_neg]; exact EReal.coe_ne_bot _) he2
      have he1' : E.toReal ≤ b := by
        rw [← EReal.coe_toReal hEt hEb] at he1; exact_mod_cast he1
      have he2' : -b ≤ E.toReal := by
        rw [← EReal.coe_toReal hEt hEb, ← EReal.coe_neg] at he2; exact_mod_cast he2
      have hH : H M (Js k) (x, u) = ((r + M.α * E.toReal : ℝ) : EReal) := by
        show badd (M.g (x, u)) ((M.α : EReal) * E) = _
        have hne : (M.α : EReal) * ((E.toReal : ℝ) : EReal) ≠ ⊤ := by
          rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
        rw [hr, ← EReal.coe_toReal hEt hEb]
        unfold badd
        rw [if_neg (by push_neg; exact ⟨EReal.coe_ne_top _, hne⟩)]
        norm_cast
      rw [hH, ← EReal.coe_neg]
      have hα := M.α_pos
      have k1 : M.α * E.toReal ≤ M.α * b := mul_le_mul_of_nonneg_left he1' hα.le
      have k2 : M.α * (-b) ≤ M.α * E.toReal := mul_le_mul_of_nonneg_left he2' hα.le
      constructor
      · exact_mod_cast (by linarith : r + M.α * E.toReal ≤ bg + M.α * b)
      · exact_mod_cast (by linarith : -(bg + M.α * b) ≤ r + M.α * E.toReal)
    · filter_upwards [hUae] with u hu
      obtain ⟨r, hr, -, -⟩ := hgfin u hu
      have hE := bf_ext_dom (M.t (x, u)) Js Jl (fun k => hJae k (x, u)) b
        (fun k => ae_of_all _ (hb k)) (ae_of_all _ hlim)
      have hgt : M.g (x, u) ≠ ⊤ := by rw [hr]; exact EReal.coe_ne_top r
      have hgb : M.g (x, u) ≠ ⊥ := by rw [hr]; exact EReal.coe_ne_bot r
      exact bf_badd_tendsto hgt (bf_mul_tendsto M.α_pos hE) (Or.inl hgb)

end BertsekasShreve.BorelFinite

open BertsekasShreve.BorelFinite
open Filter Topology

theorem solution {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (μ : UCS M) (Js : ℕ → S → EReal) (Jl : S → EReal) (hJs : ∀ k, UMeasurable (Js k)) :
    ((∀ x, Tmu M μ (Js 0) x < ⊤) → (∀ x, Antitone fun k => Js k x) →
        (∀ x, Tendsto (fun k => Js k x) atTop (𝓝 (Jl x))) →
        (∀ x, Antitone fun k => Tmu M μ (Js k) x) ∧
          ∀ x, Tendsto (fun k => Tmu M μ (Js k) x) atTop (𝓝 (Tmu M μ Jl x))) ∧
    ((∀ x, Tmu M μ (fun y => ((negPart (Js 0) y : ENNReal) : EReal)) x < ⊤) →
        (∀ z ∈ M.Γ, 0 ≤ M.g z) → (∀ x, Monotone fun k => Js k x) →
        (∀ x, Tendsto (fun k => Js k x) atTop (𝓝 (Jl x))) →
        (∀ x, Monotone fun k => Tmu M μ (Js k) x) ∧
          ∀ x, Tendsto (fun k => Tmu M μ (Js k) x) atTop (𝓝 (Tmu M μ Jl x))) ∧
    ((∃ b : ℝ, ∀ k x, Js k x ≤ b ∧ -(b : EReal) ≤ Js k x) →
        (∃ b : ℝ, ∀ z ∈ M.Γ, M.g z ≤ b ∧ -(b : EReal) ≤ M.g z) →
        (∀ x, Tendsto (fun k => Js k x) atTop (𝓝 (Jl x))) →
        ∀ x, Tendsto (fun k => Tmu M μ (Js k) x) atTop (𝓝 (Tmu M μ Jl x))) := by
  exact lemma8_4_core M μ Js Jl hJs
