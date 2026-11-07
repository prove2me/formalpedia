-- Prove2me | solution 1 for BertsekasShreve.BorelFinite.prop8_2_dp_algorithm
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T05:54:12.128921+00:00
-- url     : https://prove2.me/submissions/7b76608d-73ec-4294-9b11-85a1c726ae0b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy
import Definitions.Def_BertsekasShreve_BorelFinite_Operators
import Theorems.Thm_BertsekasShreve_BorelFinite_lemma8_1_markov_cost_eq_comp
import Theorems.Thm_BertsekasShreve_BorelFinite_cor8_1_1_markov_inf
import Theorems.Thm_BertsekasShreve_BorelFinite_lemma8_2_eps_selector
import Theorems.Thm_BertsekasShreve_BorelFinite_T_lowerSemianalytic



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


/-! ## Part 1: elementary facts on `extInt`, `T_μ`, `T` -/

lemma pp_pos_shift (a : EReal) (c : ℝ) :
    (a + (c : EReal)).toENNReal ≤ a.toENNReal + ENNReal.ofReal c := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe r =>
    rw [← EReal.coe_add]
    simp only [EReal.real_coe_toENNReal]
    exact ENNReal.ofReal_add_le

lemma pp_neg_shift (a : EReal) (c : ℝ) :
    (-a).toENNReal ≤ (-(a + (c : EReal))).toENNReal + ENNReal.ofReal c := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe r =>
    rw [← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_neg]
    simp only [EReal.real_coe_toENNReal]
    calc ENNReal.ofReal (-r) = ENNReal.ofReal (-(r + c) + c) := by ring_nf
      _ ≤ _ := ENNReal.ofReal_add_le

/-- Shifting the integrand by a constant `c ≥ 0` raises the extended integral by at most `2c`. -/
lemma extInt_shift_le {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (f : X → EReal) (c : ℝ) (hc : 0 ≤ c) :
    extInt (fun h => ∫⁻ y, h y ∂ν) (fun y => f y + (c : EReal)) ≤
      extInt (fun h => ∫⁻ y, h y ∂ν) f + ((2 * c : ℝ) : EReal) := by
  set P := ∫⁻ y, posPart f y ∂ν with hPdef
  set N := ∫⁻ y, negPart f y ∂ν with hNdef
  set P' := ∫⁻ y, posPart (fun y => f y + (c : EReal)) y ∂ν with hP'def
  set N' := ∫⁻ y, negPart (fun y => f y + (c : EReal)) y ∂ν with hN'def
  have hPP : P' ≤ P + ENNReal.ofReal c := by
    calc P' ≤ ∫⁻ y, (posPart f y + ENNReal.ofReal c) ∂ν :=
          lintegral_mono fun y => pp_pos_shift (f y) c
      _ = P + ENNReal.ofReal c := by
          rw [lintegral_add_right _ measurable_const]; simp [hPdef]
  have hNN : N ≤ N' + ENNReal.ofReal c := by
    calc N ≤ ∫⁻ y, (negPart (fun y => f y + (c : EReal)) y + ENNReal.ofReal c) ∂ν :=
          lintegral_mono fun y => pp_neg_shift (f y) c
      _ = N' + ENNReal.ofReal c := by
          rw [lintegral_add_right _ measurable_const]; simp [hN'def]
  unfold extInt
  simp only [← hPdef, ← hNdef, ← hP'def, ← hN'def]
  by_cases hP : P = ⊤
  · rw [if_pos hP, EReal.top_add_coe]; exact le_top
  rw [if_neg hP]
  have hP' : P' ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hP, ENNReal.ofReal_ne_top⟩) hPP
  rw [if_neg hP']
  by_cases hN' : N' = ⊤
  · rw [hN']
    have : ((P' : EReal)) - ((⊤ : ℝ≥0∞) : EReal) = ⊥ := by
      rw [EReal.coe_ennreal_top]
      exact EReal.sub_top _ 
    rw [this]; exact bot_le
  have hN : N ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hN', ENNReal.ofReal_ne_top⟩) hNN
  rw [← EReal.coe_ennreal_toReal hP, ← EReal.coe_ennreal_toReal hN,
    ← EReal.coe_ennreal_toReal hP', ← EReal.coe_ennreal_toReal hN']
  rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have h1 := (ENNReal.toReal_le_toReal hP' (ENNReal.add_ne_top.2 ⟨hP, ENNReal.ofReal_ne_top⟩)).2 hPP
  have h2 := (ENNReal.toReal_le_toReal hN (ENNReal.add_ne_top.2 ⟨hN', ENNReal.ofReal_ne_top⟩)).2 hNN
  rw [ENNReal.toReal_add hP ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc] at h1
  rw [ENNReal.toReal_add hN' ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc] at h2
  linarith

/-- If `f ≥ c` almost everywhere for a probability measure, then `∫ f ≥ c`. -/
lemma extInt_ge_of_ae {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (f : X → EReal) (c : EReal) (h : ∀ᵐ y ∂ν, c ≤ f y) :
    c ≤ extInt (fun h => ∫⁻ y, h y ∂ν) f := by
  induction c using EReal.rec with
  | bot => exact bot_le
  | top =>
    have hP : ∫⁻ y, posPart f y ∂ν = ⊤ := by
      have : ∀ᵐ y ∂ν, posPart f y = ⊤ := by
        filter_upwards [h] with y hy
        simp [posPart, top_le_iff.1 hy]
      rw [lintegral_congr_ae this]; simp
    unfold extInt; simp only; rw [if_pos hP]
  | coe r =>
    have hP : ENNReal.ofReal r ≤ ∫⁻ y, posPart f y ∂ν := by
      calc ENNReal.ofReal r = ∫⁻ _y, ENNReal.ofReal r ∂ν := by simp
        _ ≤ _ := lintegral_mono_ae (by
          filter_upwards [h] with y hy
          exact (EReal.real_coe_toENNReal r) ▸ EReal.toENNReal_le_toENNReal hy)
    have hN : ∫⁻ y, negPart f y ∂ν ≤ ENNReal.ofReal (-r) := by
      calc ∫⁻ y, negPart f y ∂ν ≤ ∫⁻ _y, ENNReal.ofReal (-r) ∂ν := lintegral_mono_ae (by
          filter_upwards [h] with y hy
          have := EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 hy)
          rw [← EReal.coe_neg, EReal.real_coe_toENNReal] at this
          exact this)
        _ = ENNReal.ofReal (-r) := by simp
    unfold extInt; simp only
    split_ifs with hPt
    · exact le_top
    have hNt : ∫⁻ y, negPart f y ∂ν ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hN
    rw [← EReal.coe_ennreal_toReal hPt, ← EReal.coe_ennreal_toReal hNt, ← EReal.coe_sub,
      EReal.coe_le_coe_iff]
    have h1 := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hPt).2 hP
    have h2 := (ENNReal.toReal_le_toReal hNt ENNReal.ofReal_ne_top).2 hN
    rw [ENNReal.toReal_ofReal'] at h1 h2
    have := le_max_left r 0
    have := le_max_left (-r) 0
    have : max (-r) 0 = max r 0 - r := by
      rcases le_total r 0 with h | h
      · rw [max_eq_left (by linarith), max_eq_right h]; ring
      · rw [max_eq_right (by linarith), max_eq_left h]; ring
    linarith

open BertsekasShreve.FiniteHorizon in
lemma badd_add_coe (a b : EReal) (d : ℝ) : badd a (b + (d : EReal)) ≤ badd a b + (d : EReal) := by
  unfold badd
  by_cases hb : b = ⊤
  · subst hb; simp
  by_cases ha : a = ⊤
  · subst ha; simp
  have hbd : b + (d : EReal) ≠ ⊤ := by
    induction b using EReal.rec with
    | bot => simp
    | top => exact absurd rfl hb
    | coe r => rw [← EReal.coe_add]; exact EReal.coe_ne_top _
  rw [if_neg (by tauto), if_neg (by tauto), add_assoc]

lemma ereal_mul_add_coe_le (a : ℝ) (ha : 0 < a) (E : EReal) (d : ℝ) :
    (a : EReal) * (E + (d : EReal)) ≤ (a : EReal) * E + ((a * d : ℝ) : EReal) := by
  induction E using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos ha]
  | top => rw [EReal.top_add_coe, EReal.coe_mul_top_of_pos ha, EReal.top_add_coe]
  | coe r =>
    rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith

lemma H_shift_le (M : Model S C W) (J : S → EReal) (c : ℝ) (hc : 0 ≤ c) (z : S × C) :
    H M (fun y => J y + (c : EReal)) z ≤ H M J z + ((M.α * (2 * c) : ℝ) : EReal) := by
  unfold H
  refine le_trans (bf_badd_mono le_rfl ?_) (badd_add_coe _ _ _)
  refine le_trans (mul_le_mul_of_nonneg_left (extInt_shift_le (M.t z) J c hc)
    (by exact_mod_cast M.α_pos.le)) ?_
  exact ereal_mul_add_coe_le M.α M.α_pos _ _

lemma Tmu_shift_le (M : Model S C W) (μ : UCS M) (J : S → EReal) (c : ℝ) (hc : 0 ≤ c) (x : S) :
    Tmu M μ (fun y => J y + (c : EReal)) x ≤ Tmu M μ J x + ((4 * M.α * c : ℝ) : EReal) := by
  haveI := μ.1.isProb x
  unfold Tmu
  refine le_trans (bf_extInt_mono _ (fun u => H_shift_le M J c hc (x, u))) ?_
  refine le_trans (extInt_shift_le _ _ _ (by have := M.α_pos; positivity)) (le_of_eq ?_)
  congr 2; ring

lemma T_mono (M : Model S C W) {J J' : S → EReal} (h : ∀ y, J y ≤ J' y) (x : S) :
    T M J x ≤ T M J' x :=
  iInf₂_mono fun u _ => bf_H_mono M h (x, u)

lemma T_le_Tmu (M : Model S C W) [T2Space S] [T2Space C] [OpensMeasurableSpace C]
    (μ : UCS M) (J : S → EReal) (x : S) : T M J x ≤ Tmu M μ J x := by
  haveI := μ.1.isProb x
  apply extInt_ge_of_ae
  filter_upwards [bf_U_ae M x _ (μ.2 x)] with u hu
  exact iInf₂_le u hu

/-! ## Part 2: analytic and universally measurable bookkeeping -/

lemma analyticSet_univ_of_isBorelSpace {X : Type*} [TopologicalSpace X]
    [BertsekasShreve.AnalyticSelection.IsBorelSpace X] : AnalyticSet (univ : Set X) := by
  obtain ⟨Z, mZ, cZ, sZ, B, hB, ⟨e⟩⟩ :=
    BertsekasShreve.AnalyticSelection.IsBorelSpace.exists_homeomorph_borel (X := X)
  letI : MeasurableSpace Z := borel Z
  haveI : BorelSpace Z := ⟨rfl⟩
  have hBa : AnalyticSet B := MeasurableSet.analyticSet hB
  obtain ⟨β, tβ, pβ, f, hf, hrange⟩ := analyticSet_iff_exists_polishSpace_range.1 hBa
  let g : β → X := fun b => e.symm ⟨f b, hrange ▸ mem_range_self b⟩
  have hg : Continuous g := e.symm.continuous.comp (hf.subtype_mk _)
  have hr : range g = univ := by
    refine eq_univ_of_forall fun x => ?_
    have hx : (e x).1 ∈ range f := hrange ▸ (e x).2
    obtain ⟨b, hb⟩ := hx
    refine ⟨b, ?_⟩
    simp only [g]
    rw [show (⟨f b, _⟩ : B) = e x from Subtype.ext hb]
    exact e.symm_apply_apply x
  rw [← hr]
  exact analyticSet_range_of_polishSpace hg

lemma J0_lsa (X : Type*) [TopologicalSpace X] [BertsekasShreve.AnalyticSelection.IsBorelSpace X] :
    IsLowerSemianalyticOn (univ : Set X) (J0 X) := by
  refine ⟨analyticSet_univ_of_isBorelSpace, fun c => ?_⟩
  by_cases hc : (0 : EReal) < (c : EReal)
  · have : {x : X | x ∈ (univ : Set X) ∧ J0 X x < (c : EReal)} = univ := by
      ext x; simp [J0, hc]
    rw [this]; exact analyticSet_univ_of_isBorelSpace
  · have : {x : X | x ∈ (univ : Set X) ∧ J0 X x < (c : EReal)} = ∅ := by
      ext x; simp [J0, hc]
    rw [this]; exact analyticSet_empty

lemma umeas_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {f : Y → ENNReal}
    (hf : UMeasurable f) {g : X → Y} (hg : Measurable g) : UMeasurable (f ∘ g) := by
  intro s hs p hp
  haveI : IsProbabilityMeasure (p.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  exact (hf hs (p.map g) inferInstance).preimage (hg.quasiMeasurePreserving p)

/-- The policy `(ν₀, …, ν_{N-1})` with `μ_k(·|x₀,…,x_k) = ν_k(·|x_k)`. -/
noncomputable def markovPolicy (M : Model S C W) (ν : Fin M.N → UCS M) : Policy M where
  μ k := ⟨fun h => (ν k).1.toFun h.2, fun h => (ν k).1.isProb h.2,
    fun B hB => umeas_comp ((ν k).1.um B hB) (measurable_snd (α := Fin k → S × C) (β := S))⟩
  feasible k h := (ν k).2 h.2

lemma markovPolicy_isMarkovWith (M : Model S C W) (ν : Fin M.N → UCS M) :
    (markovPolicy M ν).IsMarkovWith ν := fun _ _ => rfl

lemma exists_nu_of_isMarkov [Nonempty S] [Nonempty C] (M : Model S C W) (π : Policy M)
    (hπ : π.IsMarkov) : ∃ ν : Fin M.N → UCS M, π.IsMarkovWith ν := by
  let d : (k : ℕ) → Fin k → S × C := fun _ _ => (Classical.arbitrary S, Classical.arbitrary C)
  let ν : Fin M.N → UCS M := fun k =>
    ⟨⟨fun x => (π.μ k).toFun ((d k, x) : Hist S C k), fun x => (π.μ k).isProb _,
      fun B hB => umeas_comp ((π.μ k).um B hB)
        (measurable_prodMk_left (m := (inferInstance : MeasurableSpace (Fin k → S × C)))
          (x := d k))⟩,
      fun x => π.feasible k ((d k, x) : Hist S C k)⟩
  exact ⟨ν, fun k h => hπ k h ((d k, h.2) : Hist S C k) rfl⟩

/-! ## Part 3: the compositions `T_{μ₀} ⋯ T_{μ_{K-1}}` -/

lemma filter_finRange_lt_eq {n K : ℕ} (hKN : K ≤ n) :
    (List.finRange n).filter (fun k : Fin n => (k : ℕ) < K) =
      List.ofFn (fun i : Fin K => Fin.castLE hKN i) := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · exact (List.pairwise_lt_finRange n).filter _
  · exact List.pairwise_ofFn.2 (fun i j hij => Fin.lt_def.2 (Fin.lt_def.1 hij))
  · intro a
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, List.mem_ofFn]
    constructor
    · intro ha; exact ⟨⟨a, ha⟩, Fin.ext rfl⟩
    · rintro ⟨i, rfl⟩; simp

lemma TmuComp_eq (M : Model S C W) (ν : Fin M.N → UCS M) (K : ℕ) (hKN : K ≤ M.N) (J : S → EReal) :
    TmuComp M ν K J = (List.ofFn (fun i : Fin K => Fin.castLE hKN i)).foldr
      (fun k J' => Tmu M (ν k) J') J := by
  unfold TmuComp; rw [filter_finRange_lt_eq hKN]

/-- Eq. (19): `T_{μ₀} ⋯ T_{μ_{K-1}}(J₀) ≥ T^K(J₀)`. -/
lemma foldr_ge (M : Model S C W) [T2Space S] [T2Space C] [OpensMeasurableSpace C]
    (ν : Fin M.N → UCS M) (l : List (Fin M.N)) (x : S) :
    (T M)^[l.length] (J0 S) x ≤ l.foldr (fun k J' => Tmu M (ν k) J') (J0 S) x := by
  induction l generalizing x with
  | nil => exact le_rfl
  | cons k l ih =>
    rw [List.length_cons, Function.iterate_succ_apply', List.foldr_cons]
    exact (T_mono M ih x).trans (T_le_Tmu M (ν k) _ x)

/-- The constants `1 + 4α + (4α)² + ⋯` appearing in Eq. (21). -/
noncomputable def sC (α : ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => 1 + 4 * α * sC α m

lemma sC_nonneg (α : ℝ) (hα : 0 ≤ α) : ∀ m, 0 ≤ sC α m
  | 0 => le_rfl
  | m + 1 => by
    have := sC_nonneg α hα m
    simp only [sC]; positivity

/-- Eq. (21): with `ε`-optimal one-step selectors, `T_{μ₀} ⋯ T_{μ_{K-1}}(J₀) ≤ T^K(J₀) + ε·const`. -/
lemma foldr_le (M : Model S C W) (ν : Fin M.N → UCS M) (K : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hν : ∀ k : Fin M.N, (k : ℕ) < K → ∀ x,
      Tmu M (ν k) ((T M)^[K - 1 - k] (J0 S)) x ≤ (T M)^[K - k] (J0 S) x + (ε : EReal)) :
    ∀ (m : ℕ) (a : Fin m → Fin M.N), m ≤ K → (∀ i, (a i : ℕ) = K - m + i) → ∀ x,
      (List.ofFn a).foldr (fun k J' => Tmu M (ν k) J') (J0 S) x ≤
        (T M)^[m] (J0 S) x + ((ε * sC M.α m : ℝ) : EReal) := by
  intro m
  induction m with
  | zero => intro a _ _ x; simp [sC]
  | succ m ih =>
    intro a hm ha x
    rw [List.ofFn_succ, List.foldr_cons]
    have ih' := ih (fun i => a i.succ) (by omega) (fun i => by rw [ha]; simp; omega)
    have h0 := ha 0
    simp only [Fin.val_zero, add_zero] at h0
    have hs := sC_nonneg M.α M.α_pos.le m
    have hk : ((a 0 : Fin M.N) : ℕ) < K := by omega
    have e1 : K - 1 - ((a 0 : Fin M.N) : ℕ) = m := by omega
    have e2 : K - ((a 0 : Fin M.N) : ℕ) = m + 1 := by omega
    have hsel := hν (a 0) hk x
    rw [e1, e2] at hsel
    calc Tmu M (ν (a 0)) ((List.ofFn fun i => a i.succ).foldr (fun k J' => Tmu M (ν k) J')
            (J0 S)) x
        ≤ Tmu M (ν (a 0)) (fun y => (T M)^[m] (J0 S) y + ((ε * sC M.α m : ℝ) : EReal)) x :=
          bf_Tmu_mono M _ ih' x
      _ ≤ Tmu M (ν (a 0)) ((T M)^[m] (J0 S)) x + ((4 * M.α * (ε * sC M.α m) : ℝ) : EReal) :=
          Tmu_shift_le M _ _ _ (by positivity) x
      _ ≤ ((T M)^[m + 1] (J0 S) x + (ε : EReal)) + ((4 * M.α * (ε * sC M.α m) : ℝ) : EReal) :=
          add_le_add_left hsel _
      _ = (T M)^[m + 1] (J0 S) x + ((ε * sC M.α (m + 1) : ℝ) : EReal) := by
          rw [add_assoc, ← EReal.coe_add]; congr 2; simp only [sC]; ring

lemma ereal_le_of_forall_pos {a b : EReal} {Cc : ℝ} (hC : 0 ≤ Cc)
    (h : ∀ ε : ℝ, 0 < ε → a ≤ b + ((ε * Cc : ℝ) : EReal)) : a ≤ b := by
  induction b using EReal.rec with
  | top => exact le_top
  | bot => simpa using h 1 one_pos
  | coe r =>
    induction a using EReal.rec with
    | bot => exact bot_le
    | top =>
      have := h 1 one_pos
      rw [← EReal.coe_add] at this
      exact absurd this (not_le.2 (EReal.coe_lt_top _))
    | coe q =>
      rw [EReal.coe_le_coe_iff]
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      have := h (δ / (Cc + 1)) (by positivity)
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at this
      have h2 : δ / (Cc + 1) * Cc ≤ δ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
      linarith

end BertsekasShreve.BorelFinite

open BertsekasShreve.BorelFinite

theorem solution {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hF : FPlus M ∨ FMinus M) (K : ℕ) (hK1 : 1 ≤ K) (hKN : K ≤ M.N) :
    Jstar M K = (T M)^[K] (J0 S) := by
  haveI : T2Space S := bf_t2
  haveI : T2Space C := bf_t2
  have hlsa : ∀ j : ℕ, IsLowerSemianalyticOn Set.univ ((T M)^[j] (J0 S)) := by
    intro j
    induction j with
    | zero => exact J0_lsa S
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact T_lowerSemianalytic M _ ih
  funext x
  apply le_antisymm
  · -- Eq. (22): `J*_K ≤ T^K(J₀)`
    refine ereal_le_of_forall_pos (sC_nonneg M.α M.α_pos.le K) fun ε hε => ?_
    choose σ hσ using fun j : ℕ => lemma8_2_eps_selector M ((T M)^[j] (J0 S)) (hlsa j) ε hε
    let ν : Fin M.N → UCS M := fun k => σ (K - 1 - k)
    have hν : ∀ k : Fin M.N, (k : ℕ) < K → ∀ y,
        Tmu M (ν k) ((T M)^[K - 1 - k] (J0 S)) y ≤ (T M)^[K - k] (J0 S) y + (ε : EReal) := by
      intro k hk y
      rw [show K - (k : ℕ) = (K - 1 - k) + 1 by omega, Function.iterate_succ_apply']
      exact hσ (K - 1 - k) y
    calc Jstar M K x ≤ J M K (markovPolicy M ν) x := iInf_le (fun π => J M K π x) _
      _ = TmuComp M ν K (J0 S) x := by
          rw [lemma8_1_markov_cost_eq_comp M hF _ ν (markovPolicy_isMarkovWith M ν) K hK1 hKN]
      _ = (List.ofFn (fun i : Fin K => Fin.castLE hKN i)).foldr
            (fun k J' => Tmu M (ν k) J') (J0 S) x := by rw [TmuComp_eq M ν K hKN]
      _ ≤ _ := foldr_le M ν K ε hε hν K _ le_rfl (fun i => by simp) x
  · -- Eq. (20): `J*_K ≥ T^K(J₀)`, via Corollary 8.1.1 and Lemma 8.1
    rw [cor8_1_1_markov_inf M hF K hK1 hKN x]
    refine le_iInf₂ fun π hπ => ?_
    obtain ⟨ν, hν⟩ := exists_nu_of_isMarkov M π hπ
    rw [lemma8_1_markov_cost_eq_comp M hF π ν hν K hK1 hKN, TmuComp_eq M ν K hKN]
    have := foldr_ge M ν (List.ofFn (fun i : Fin K => Fin.castLE hKN i)) x
    rwa [List.length_ofFn] at this
