-- Prove2me | solution 1 for BertsekasShreve.BorelFinite.lemma8_2_eps_selector
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T06:05:09.254819+00:00
-- url     : https://prove2.me/submissions/24d3f8c2-8ec7-41be-903f-2e39c3fbf328
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy
import Definitions.Def_BertsekasShreve_BorelFinite_Operators
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_BertsekasShreve_AnalyticSelection_LowerSemianalytic
import Theorems.Thm_BertsekasShreve_AnalyticSelection_lower_semianalytic_selection
import Theorems.Thm_BertsekasShreve_BorelFinite_H_lowerSemianalytic



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

/-! ## Lemma 8.2 from Proposition 7.50 -/

/-- weights `2^{-(m+1)}` -/
noncomputable def wt (m : ℕ) : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ (m + 1)

lemma tsum_wt : ∑' m, wt m = 1 := by
  simp only [wt]
  rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two]
  exact ENNReal.mul_inv_cancel (by simp) (by simp)

lemma wt_mul_two_pow (m : ℕ) : wt m * 2 ^ m = 2⁻¹ := by
  simp only [wt, pow_succ, mul_comm _ (2⁻¹ : ℝ≥0∞), mul_assoc]
  rw [← mul_pow, ENNReal.inv_mul_cancel (by simp) (by simp), one_pow, mul_one]

lemma ereal_pos_sub_neg (a : EReal) (ha : a ≠ ⊤) :
    ((a.toENNReal : ℝ≥0∞) : EReal) - (((-a).toENNReal : ℝ≥0∞) : EReal) = a := by
  induction a using EReal.rec with
  | bot => simp
  | top => exact absurd rfl ha
  | coe r =>
    have hm : ∀ a b : ℝ, ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) :=
      fun a b => EReal.coe_strictMono.monotone.map_max
    rw [EReal.coe_toENNReal_eq_max, EReal.coe_toENNReal_eq_max, ← EReal.coe_neg,
      ← EReal.coe_zero, ← hm, ← hm, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
    rcases le_total r 0 with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring

lemma um_tsum_indicator {X : Type*} [MeasurableSpace X] (w : ℕ → ℝ≥0∞) (s : ℕ → Set X)
    (hs : ∀ m, MeasurableSet[universalSigma X] (s m)) :
    UMeasurable (fun x => ∑' m, w m * (s m).indicator 1 x) := by
  unfold UMeasurable
  exact Measurable.ennreal_tsum (fun m => (measurable_const.indicator (hs m)).const_mul (w m))

end BertsekasShreve.BorelFinite

open BertsekasShreve.BorelFinite BertsekasShreve.AnalyticSelection MeasureTheory
open scoped ENNReal

theorem solution {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (J : S → EReal) (hJ : IsLowerSemianalyticOn Set.univ J) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : UCS M, ∀ x : S, Tmu M μ J x ≤ T M J x + (ε : EReal) := by
  haveI : T2Space S := bf_t2
  haveI : T2Space C := bf_t2
  have hH := H_lowerSemianalytic M J hJ
  -- the data of Proposition 7.50
  let D : Set (S × C) := M.Γ
  have hD : AnalyticSet D := M.Γ_analytic
  let f : D → EReal := fun z => H M J z.1
  have hf : IsLowerSemianalytic D f := by
    refine ⟨hD, fun c => ?_⟩
    have e : Subtype.val '' {z : D | f z < (c : EReal)} = {z | z ∈ M.Γ ∧ H M J z < (c : EReal)} := by
      ext z; constructor
      · rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩
      · rintro ⟨hz, h⟩; exact ⟨⟨z, hz⟩, h, rfl⟩
    rw [e]; exact hH.2 c
  have hproj : ∀ x : S, x ∈ Prod.fst '' D := fun x =>
    ⟨(x, (M.U_nonempty x).some), (M.U_nonempty x).some_mem, rfl⟩
  let incl : S → Prod.fst '' D := fun x => ⟨x, hproj x⟩
  have hpi : ∀ x, partialInf D f (incl x) = T M J x := fun x => rfl
  -- the sets `{T(J) < c}` are analytic (Proposition 7.47), so `{T(J) = -∞}` is universally measurable
  have hTlt : ∀ c : ℝ, AnalyticSet {x : S | T M J x < (c : EReal)} := by
    intro c
    have e : {x : S | T M J x < (c : EReal)} =
        Prod.fst '' {z : S × C | z ∈ M.Γ ∧ H M J z < (c : EReal)} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_image, T, iInf_lt_iff]
      constructor
      · rintro ⟨u, hu, h⟩; exact ⟨(x, u), ⟨hu, h⟩, rfl⟩
      · rintro ⟨⟨x', u⟩, ⟨hu, h⟩, rfl⟩; exact ⟨u, hu, h⟩
    rw [e]; exact (hH.2 c).image_of_continuous continuous_fst
  have hE : MeasurableSet[universalSigma S] {x : S | T M J x = ⊥} := by
    intro p hp
    have e : {x : S | T M J x = ⊥} = ⋂ n : ℕ, {x : S | T M J x < ((-(n : ℝ) : ℝ) : EReal)} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h n; rw [h]; exact EReal.bot_lt_coe _
      · intro h
        by_contra hne
        induction hx : T M J x using EReal.rec with
        | bot => exact hne hx
        | top => have := h 0; rw [hx] at this; exact absurd this (not_lt.2 le_top)
        | coe r =>
          obtain ⟨n, hn⟩ := exists_nat_gt (-r)
          have := h n; rw [hx, EReal.coe_lt_coe_iff] at this; linarith
    rw [e]
    exact NullMeasurableSet.iInter fun n => bf_analytic_null p _ (hTlt _)
  -- the selectors of Proposition 7.50(b) with `ε_m = min ε 2^{-m}`
  have hsel := (lower_semianalytic_selection D hD f hf).2.2
  let εm : ℕ → ℝ := fun m => min ε ((2 : ℝ) ^ m)⁻¹
  have hεm : ∀ m, 0 < εm m := fun m => lt_min hε (by positivity)
  choose φ' hφ' hum hprop using fun m : ℕ => hsel (εm m) (hεm m)
  let φ : ℕ → S → C := fun m x => φ' m (incl x)
  have P1 : ∀ m x, φ m x ∈ M.U x := fun m x => hφ' m (incl x)
  have P2 : ∀ m x, T M J x ≠ ⊥ → H M J (x, φ m x) ≤ T M J x + (ε : EReal) := by
    intro m x hx
    have h := hprop m (incl x)
    rw [hpi] at h
    by_cases ha : (x : S) ∈ attainSet D f
    · have h1 : H M J (x, φ m x) = T M J x := h.1 ha
      rw [h1]
      exact le_add_of_nonneg_right (by exact_mod_cast hε.le)
    · have h2 : H M J (x, φ m x) ≤ T M J x + (εm m : EReal) := h.2.1 ha hx
      exact h2.trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 (min_le_left _ _)))
  have P3 : ∀ m x, T M J x = ⊥ → H M J (x, φ m x) ≤ ((-(2 : ℝ) ^ m : ℝ) : EReal) := by
    intro m x hx
    have h := hprop m (incl x)
    rw [hpi] at h
    by_cases ha : (x : S) ∈ attainSet D f
    · have h1 : H M J (x, φ m x) = T M J x := h.1 ha
      rw [h1, hx]; exact bot_le
    · have h2 : H M J (x, φ m x) ≤ ((-1 / εm m : ℝ) : EReal) := h.2.2 ha hx
      refine h2.trans (EReal.coe_le_coe_iff.2 ?_)
      have hle : εm m ≤ ((2 : ℝ) ^ m)⁻¹ := min_le_right _ _
      have hpos := hεm m
      have : (2 : ℝ) ^ m ≤ 1 / εm m := by
        rw [le_div_iff₀ hpos]
        calc (2 : ℝ) ^ m * εm m ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ m)⁻¹ :=
              mul_le_mul_of_nonneg_left hle (by positivity)
          _ = 1 := mul_inv_cancel₀ (by positivity)
      rw [neg_div]; linarith
  have P4 : ∀ m (B : Set C), MeasurableSet B →
      MeasurableSet[universalSigma S] {x : S | φ m x ∈ B} := by
    intro m B hB p hp
    have e : {x : S | φ m x ∈ B} = Subtype.val '' (φ' m ⁻¹' B) := by
      ext x; constructor
      · intro hx; exact ⟨incl x, hx, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        have : y = incl y.1 := Subtype.ext rfl
        show φ' m (incl y.1) ∈ B
        rw [← this]; exact hy
    rw [e]; exact (hum m).2 B hB p hp
  -- the randomized kernel of the book's proof
  let ψ : ℕ → S → C := fun m x => if T M J x = ⊥ then φ m x else φ 0 x
  have Pψ : ∀ m (B : Set C), MeasurableSet B →
      MeasurableSet[universalSigma S] {x : S | ψ m x ∈ B} := by
    intro m B hB
    have e : {x : S | ψ m x ∈ B} = ({x | T M J x = ⊥} ∩ {x | φ m x ∈ B}) ∪
        ({x | T M J x = ⊥}ᶜ ∩ {x | φ 0 x ∈ B}) := by
      ext x
      by_cases hx : T M J x = ⊥ <;> simp [ψ, hx]
    rw [e]
    exact (hE.inter (P4 m B hB)).union (hE.compl.inter (P4 0 B hB))
  let ν : S → Measure C := fun x => Measure.sum fun m => wt m • Measure.dirac (ψ m x)
  have hνB : ∀ x (B : Set C), MeasurableSet B → ν x B = ∑' m, wt m * B.indicator 1 (ψ m x) := by
    intro x B hB
    simp only [ν, Measure.sum_apply _ hB, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hB]
  have hνprob : ∀ x, IsProbabilityMeasure (ν x) := by
    intro x
    refine ⟨?_⟩
    rw [hνB x _ MeasurableSet.univ]
    simp [tsum_wt]
  have hνU : ∀ x, ν x (M.U x) = 1 := by
    intro x
    haveI := hνprob x
    let R : Set C := Set.range fun m => ψ m x
    have hR : MeasurableSet R := (Set.countable_range _).measurableSet
    have h0 : ν x Rᶜ = 0 := by
      rw [hνB x _ hR.compl]
      simp [R]
    have hsub : (M.U x)ᶜ ⊆ Rᶜ := by
      rintro u hu ⟨m, rfl⟩
      apply hu
      by_cases hx : T M J x = ⊥
      · simp only [ψ, hx, if_true]; exact P1 m x
      · simp only [ψ, hx, if_false]; exact P1 0 x
    have h1 : ν x (M.U x)ᶜ = 0 := measure_mono_null hsub h0
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞) = ν x Set.univ := measure_univ.symm
      _ ≤ ν x (M.U x) + ν x (M.U x)ᶜ := by
          rw [← Set.union_compl_self (M.U x)]; exact measure_union_le _ _
      _ = ν x (M.U x) := by rw [h1, add_zero]
  let μ : UCS M := ⟨⟨ν, hνprob, fun B hB => by
      have e : (fun x => ν x B) = fun x => ∑' m, wt m * ({x | ψ m x ∈ B}).indicator 1 x := by
        funext x; rw [hνB x B hB]; rfl
      rw [e]; exact um_tsum_indicator wt _ (fun m => Pψ m B hB)⟩, hνU⟩
  refine ⟨μ, fun x => ?_⟩
  have hint : ∀ h : C → ℝ≥0∞, ∫⁻ u, h u ∂(ν x) = ∑' m, wt m * h (ψ m x) := by
    intro h
    simp only [ν, lintegral_sum_measure, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  have hTmu : Tmu M μ J x = extInt (fun h => ∫⁻ u, h u ∂(ν x)) (fun u => H M J (x, u)) := rfl
  rw [hTmu]
  unfold extInt
  beta_reduce
  rw [hint, hint]
  by_cases hx : T M J x = ⊥
  · -- `T(J)(x) = -∞`: the kernel spreads mass `2^{-(m+1)}` on `φ_m(x)`, and `T_μ(J)(x) = -∞`
    have hψ : ∀ m, ψ m x = φ m x := fun m => by simp only [ψ, hx, if_true]
    have hpos : ∑' m, wt m * BertsekasShreve.BorelFinite.posPart (fun u => H M J (x, u)) (ψ m x) = 0 := by
      refine ENNReal.tsum_eq_zero.2 fun m => ?_
      rw [hψ]
      simp only [BertsekasShreve.BorelFinite.posPart]
      rw [EReal.toENNReal_of_nonpos ((P3 m x hx).trans (by exact_mod_cast
        (neg_nonpos.2 (by positivity : (0 : ℝ) ≤ 2 ^ m)))), mul_zero]
    have hneg : ∑' m, wt m * BertsekasShreve.BorelFinite.negPart (fun u => H M J (x, u)) (ψ m x) = ⊤ := by
      refine top_unique ?_
      calc (⊤ : ℝ≥0∞) = ∑' _m : ℕ, (2⁻¹ : ℝ≥0∞) :=
            (ENNReal.tsum_const_eq_top_of_ne_zero (by simp)).symm
        _ ≤ _ := ENNReal.tsum_le_tsum fun m => by
            rw [← wt_mul_two_pow m, hψ]
            refine mul_le_mul' le_rfl ?_
            simp only [BertsekasShreve.BorelFinite.negPart]
            have h3 : (((2 : ℝ) ^ m : ℝ) : EReal) ≤ -H M J (x, φ m x) := by
              have := EReal.neg_le_neg_iff.2 (P3 m x hx)
              rwa [← EReal.coe_neg, neg_neg] at this
            have h4 := EReal.toENNReal_le_toENNReal h3
            rw [EReal.real_coe_toENNReal, ENNReal.ofReal_pow (by norm_num),
              ENNReal.ofReal_ofNat] at h4
            exact h4
    rw [hpos, hneg, if_neg (by simp)]
    simp
  · -- `T(J)(x) > -∞`: the kernel is the point mass at `φ_0(x)`
    have hψ : ∀ m, ψ m x = φ 0 x := fun m => by simp only [ψ, hx, if_false]
    simp only [hψ, ENNReal.tsum_mul_right, tsum_wt, one_mul]
    have key : (if BertsekasShreve.BorelFinite.posPart (fun u => H M J (x, u)) (φ 0 x) = ⊤ then ⊤ else
        ((BertsekasShreve.BorelFinite.posPart (fun u => H M J (x, u)) (φ 0 x) : ℝ≥0∞) : EReal) -
          ((BertsekasShreve.BorelFinite.negPart (fun u => H M J (x, u)) (φ 0 x) : ℝ≥0∞) : EReal)) = H M J (x, φ 0 x) := by
      simp only [BertsekasShreve.BorelFinite.posPart, BertsekasShreve.BorelFinite.negPart]
      by_cases h : (H M J (x, φ 0 x)).toENNReal = ⊤
      · simp only [h, if_true]; exact (EReal.toENNReal_eq_top_iff.1 h).symm
      · simp only [h, if_false]; exact ereal_pos_sub_neg _ (fun h' => h (EReal.toENNReal_eq_top_iff.2 h'))
    rw [key]
    exact P2 0 x hx
