-- Prove2me | solution 1 for BertsekasShreve.AnalyticSelection.lower_semianalytic_selection
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:26:52.081977+00:00
-- url     : https://prove2.me/submissions/377a9f60-2db5-4cfb-b371-ae6f03eee484

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_BertsekasShreve_AnalyticSelection_LowerSemianalytic

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


lemma cm_second {X : Type*} [TopologicalSpace X] [IsBorelSpace X] : SecondCountableTopology X := by
  obtain ⟨Z, _, _, _, B, _, ⟨e⟩⟩ := IsBorelSpace.exists_homeomorph_borel (X := X)
  exact e.isEmbedding.secondCountableTopology

lemma cm_am_um {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [IsBorelSpace X] (E : Set X) (hE : IsAnalyticallyMeasurable E) :
    IsUniversallyMeasurable E := by
  intro p hp
  exact MeasurableSpace.generateFrom_induction _ (fun s _ => NullMeasurableSet s p)
    (fun t ht _ => analytic_universallyMeasurable_core t ht p hp) nullMeasurableSet_empty
    (fun t _ h => h.compl) (fun s _ h => NullMeasurableSet.iUnion h) E hE

lemma cm_preimage_um {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [IsBorelSpace Y]
    (D : Set X) (hD : IsUniversallyMeasurable D) (f : D → Y)
    (hf : ∀ B : Set Y, MeasurableSet B → IsUniversallyMeasurable (Subtype.val '' (f ⁻¹' B)))
    (A : Set Y) (hA : IsUniversallyMeasurable A) :
    IsUniversallyMeasurable (Subtype.val '' (f ⁻¹' A)) := by
  classical
  intro p hp
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y0⟩⟩
  · have : Subtype.val '' (f ⁻¹' A) = ∅ := by
      ext x; simp only [mem_image, mem_empty_iff_false, iff_false]
      rintro ⟨x', _, _⟩; exact hY.elim (f x')
    rw [this]; exact nullMeasurableSet_empty
  let F : X → Y := fun x => if h : x ∈ D then f ⟨x, h⟩ else y0
  have hset : ∀ B : Set Y, Subtype.val '' (f ⁻¹' B) = F ⁻¹' B ∩ D := by
    intro B; ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      refine ⟨?_, x'.2⟩
      show (if h : (x' : X) ∈ D then f ⟨x', h⟩ else y0) ∈ B
      rw [dif_pos x'.2]; exact hx'
    · rintro ⟨hx, hxD⟩
      refine ⟨⟨x, hxD⟩, ?_, rfl⟩
      have : F x = f ⟨x, hxD⟩ := dif_pos hxD
      show f ⟨x, hxD⟩ ∈ B
      rw [← this]; exact hx
  have hpre : ∀ B : Set Y, F ⁻¹' B = Subtype.val '' (f ⁻¹' B) ∪ {x | x ∉ D ∧ y0 ∈ B} := by
    intro B; ext x
    rw [hset B]
    by_cases hx : x ∈ D
    · simp [hx]
    · have : F x = y0 := dif_neg hx
      simp [hx, this]
  have hFn : NullMeasurable F p := by
    intro B hB
    rw [hpre B]
    refine (hf B hB p hp).union ?_
    by_cases hy : y0 ∈ B
    · have : {x | x ∉ D ∧ y0 ∈ B} = Dᶜ := by ext x; simp [hy]
      rw [this]; exact (hD p hp).compl
    · have : {x | x ∉ D ∧ y0 ∈ B} = ∅ := by ext x; simp [hy]
      rw [this]; exact nullMeasurableSet_empty
  haveI := cm_second (X := Y)
  have hFa : AEMeasurable F p := hFn.aemeasurable
  haveI : IsProbabilityMeasure (p.map F) := Measure.isProbabilityMeasure_map hFa
  have hA' := hA (p.map F) inferInstance
  rw [Measure.map_congr hFa.ae_eq_mk] at hA'
  have h1 : NullMeasurableSet (hFa.mk F ⁻¹' A) p :=
    hA'.preimage (hFa.measurable_mk.quasiMeasurePreserving p)
  have h2 : NullMeasurableSet (F ⁻¹' A) p := h1.congr (hFa.ae_eq_mk.preimage A).symm
  rw [hset A]
  exact h2.inter (hD p hp)

theorem comp_analyticallyMeasurable_core {X Y Z : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [IsBorelSpace Y]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [IsBorelSpace Z]
    (D : Set X) (E : Set Y) (hD : IsAnalyticallyMeasurable D) (hE : IsAnalyticallyMeasurable E)
    (f : D → Y) (g : E → Z)
    (hf : IsAnalyticallyMeasurableFun D f) (hg : IsAnalyticallyMeasurableFun E g)
    (hfE : ∀ x : D, f x ∈ E) :
    IsUniversallyMeasurableFun D (fun x : D => g ⟨f x, hfE x⟩) ∧
    ∀ A : Set Y, IsAnalyticallyMeasurable A →
      IsUniversallyMeasurable (Subtype.val '' (f ⁻¹' A)) := by
  have hDu := cm_am_um D hD
  have hf' : ∀ B : Set Y, MeasurableSet B → IsUniversallyMeasurable (Subtype.val '' (f ⁻¹' B)) :=
    fun B hB => cm_am_um _ (hf.2 B hB)
  have key : ∀ A : Set Y, IsUniversallyMeasurable A →
      IsUniversallyMeasurable (Subtype.val '' (f ⁻¹' A)) :=
    fun A hA => cm_preimage_um D hDu f hf' A hA
  refine ⟨⟨hDu, fun B hB => ?_⟩, fun A hA => key A (cm_am_um A hA)⟩
  have : Subtype.val '' ((fun x : D => g ⟨f x, hfE x⟩) ⁻¹' B) =
      Subtype.val '' (f ⁻¹' (Subtype.val '' (g ⁻¹' B))) := by
    ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact ⟨x', ⟨⟨f x', hfE x'⟩, hx', rfl⟩, rfl⟩
    · rintro ⟨x', ⟨e, he, hef⟩, rfl⟩
      refine ⟨x', ?_, rfl⟩
      show g ⟨f x', hfE x'⟩ ∈ B
      have : e = ⟨f x', hfE x'⟩ := Subtype.ext hef
      rw [← this]; exact he
  rw [this]
  exact key _ (cm_am_um _ (hg.2 B hB))


noncomputable def jvSeq (P : (ℕ → ℕ) → ℕ → Prop) : ℕ → (ℕ → ℕ)
  | 0 => 0
  | k+1 => Function.update (jvSeq P k) k (sInf {n | P (Function.update (jvSeq P k) k n) (k+1)})

lemma jvSeq_agree (P : (ℕ → ℕ) → ℕ → Prop) :
    ∀ n i, i < n → jvSeq P n i = jvSeq P (i+1) i := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    by_cases h : i = n
    · subst h; rfl
    · have hin : i < n := by omega
      show Function.update (jvSeq P n) n _ i = _
      rw [Function.update_of_ne h]
      exact ih i hin

section JV
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (G : (ℕ → ℕ) → X × Y)

def jvCyl (t : ℕ → ℕ) (k : ℕ) : Set (ℕ → ℕ) := {σ | ∀ i < k, σ i = t i}
def jvW (t : ℕ → ℕ) (k : ℕ) : Set X := (fun σ => (G σ).1) '' jvCyl t k
noncomputable def jvT (x : X) : ℕ → (ℕ → ℕ) := jvSeq (fun t k => x ∈ jvW G t k)
noncomputable def jvS (x : X) : ℕ → ℕ := fun i => jvT G x (i+1) i
def jvQ (k : ℕ) (t : ℕ → ℕ) : Set X :=
  (Prod.fst '' range G) ∩ {x | ∀ j < k, jvT G x k j = t j}
def jvExt (i : ℕ) (u : Fin (i+1) → ℕ) : ℕ → ℕ := fun j => if h : j < i+1 then u ⟨j, h⟩ else 0

lemma jvW_congr {t t' : ℕ → ℕ} {k : ℕ} (h : ∀ i < k, t i = t' i) :
    jvW G t k = jvW G t' k := by
  unfold jvW jvCyl
  congr 1
  ext σ
  simp only [mem_setOf_eq]
  constructor <;> intro hσ i hi
  · rw [hσ i hi, h i hi]
  · rw [hσ i hi, ← h i hi]

lemma jvW_zero (t : ℕ → ℕ) : jvW G t 0 = Prod.fst '' range G := by
  unfold jvW jvCyl
  ext x; simp

lemma jvT_mem (x : X) (hx : x ∈ Prod.fst '' range G) : ∀ k, x ∈ jvW G (jvT G x k) k := by
  intro k
  induction k with
  | zero => rw [jvW_zero]; exact hx
  | succ k ih =>
    obtain ⟨σ, hσ, hσx⟩ := ih
    have hne : σ k ∈ {n | x ∈ jvW G (Function.update (jvT G x k) k n) (k+1)} := by
      refine ⟨σ, fun i hi => ?_, hσx⟩
      by_cases hik : i = k
      · subst hik; simp
      · rw [Function.update_of_ne hik]; exact hσ i (by omega)
    exact Nat.sInf_mem ⟨_, hne⟩

lemma jvS_mem [T2Space X] (hG : Continuous G) (x : X) (hx : x ∈ Prod.fst '' range G) :
    (G (jvS G x)).1 = x := by
  have hcl : IsClosed {σ : ℕ → ℕ | (G σ).1 = x} :=
    isClosed_singleton.preimage (continuous_fst.comp hG)
  have : jvS G x ∈ closure {σ : ℕ → ℕ | (G σ).1 = x} := by
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨m, hm⟩ := au_cyl_of_nhds hU
    obtain ⟨σ, hσ, hσx⟩ := jvT_mem G x hx m
    refine ⟨σ, hm σ (fun i hi => ?_), hσx⟩
    rw [hσ i hi]; exact jvSeq_agree _ m i hi
  rw [hcl.closure_eq] at this; exact this

lemma jv_set_eq (x : X) (k : ℕ) (t : ℕ → ℕ) (hk : ∀ j < k, jvT G x k j = t j) :
    {n | x ∈ jvW G (Function.update (jvT G x k) k n) (k+1)} =
      {n | x ∈ jvW G (Function.update t k n) (k+1)} := by
  ext n
  simp only [mem_setOf_eq]
  rw [jvW_congr G (t' := Function.update t k n) (fun i hi => ?_)]
  by_cases hik : i = k
  · subst hik; simp
  · rw [Function.update_of_ne hik, Function.update_of_ne hik]; exact hk i (by omega)

lemma jvQ_succ (k : ℕ) (t : ℕ → ℕ) :
    jvQ G (k+1) t = jvQ G k t ∩ jvW G t (k+1) ∩
      ⋂ j ∈ Iio (t k), (jvW G (Function.update t k j) (k+1))ᶜ := by
  ext x
  simp only [jvQ, mem_inter_iff, mem_setOf_eq, mem_iInter, mem_Iio, mem_compl_iff]
  have hsucc : jvT G x (k+1) = Function.update (jvT G x k) k
      (sInf {n | x ∈ jvW G (Function.update (jvT G x k) k n) (k+1)}) := rfl
  constructor
  · rintro ⟨hx, h⟩
    have hk : ∀ j < k, jvT G x k j = t j := fun j hj => by
      have := h j (by omega); rwa [hsucc, Function.update_of_ne (by omega)] at this
    have hm := h k (by omega)
    rw [hsucc, Function.update_self, jv_set_eq G x k t hk] at hm
    refine ⟨⟨⟨hx, hk⟩, ?_⟩, fun j hj => ?_⟩
    · have := jvT_mem G x hx (k+1)
      rwa [jvW_congr G h] at this
    · exact Nat.notMem_of_lt_sInf (hm ▸ hj)
  · rintro ⟨⟨⟨hx, hk⟩, hW⟩, hlt⟩
    refine ⟨hx, fun j hj => ?_⟩
    rw [hsucc, jv_set_eq G x k t hk]
    have hmem : t k ∈ {n | x ∈ jvW G (Function.update t k n) (k+1)} := by
      simp only [mem_setOf_eq, Function.update_eq_self]; exact hW
    have hinf : sInf {n | x ∈ jvW G (Function.update t k n) (k+1)} = t k := by
      refine le_antisymm (Nat.sInf_le hmem) ?_
      by_contra hcon
      push_neg at hcon
      exact hlt _ hcon (Nat.sInf_mem ⟨_, hmem⟩)
    by_cases hjk : j = k
    · subst hjk; rw [Function.update_self, hinf]
    · rw [Function.update_of_ne hjk]; exact hk j (by omega)

lemma jvW_am (hG : Continuous G) (t : ℕ → ℕ) (k : ℕ) :
    MeasurableSet[analyticSigmaAlgebra X] (jvW G t k) :=
  MeasurableSpace.measurableSet_generateFrom
    ((au_cyl_open t k).analyticSet_image (continuous_fst.comp hG))

lemma jvQ_am (hG : Continuous G) : ∀ k t, MeasurableSet[analyticSigmaAlgebra X] (jvQ G k t) := by
  intro k
  induction k with
  | zero =>
    intro t
    have : jvQ G 0 t = jvW G t 0 := by
      rw [jvW_zero]; ext x; simp [jvQ]
    rw [this]; exact jvW_am G hG t 0
  | succ k ih =>
    intro t
    rw [jvQ_succ]
    exact MeasurableSet.inter (MeasurableSet.inter (ih t) (jvW_am G hG t (k+1)))
      (MeasurableSet.biInter (Set.to_countable _) fun j _ => (jvW_am G hG _ _).compl)

lemma jv_pre_am (hG : Continuous G) (C : Set (ℕ → ℕ)) (hC : MeasurableSet C) :
    MeasurableSet[analyticSigmaAlgebra X] ((Prod.fst '' range G) ∩ jvS G ⁻¹' C) := by
  have hC' : MeasurableSet[MeasurableSpace.generateFrom
      {B | ∃ (i : ℕ) (A : Set ℕ), MeasurableSet A ∧ Function.eval i ⁻¹' A = B}] C := by
    rw [← MeasurableSpace.pi_eq_generateFrom_projections]; exact hC
  have hP : MeasurableSet[analyticSigmaAlgebra X] (Prod.fst '' range G) := by
    rw [← jvW_zero G 0]; exact jvW_am G hG 0 0
  refine MeasurableSpace.generateFrom_induction _
    (fun C _ => MeasurableSet[analyticSigmaAlgebra X] ((Prod.fst '' range G) ∩ jvS G ⁻¹' C))
    ?_ ?_ ?_ ?_ C hC'
  · rintro _ ⟨i, T, -, rfl⟩ -
    have : (Prod.fst '' range G) ∩ jvS G ⁻¹' (Function.eval i ⁻¹' T) =
        ⋃ u ∈ {u : Fin (i+1) → ℕ | u (Fin.last i) ∈ T}, jvQ G (i+1) (jvExt i u) := by
      ext x
      simp only [mem_inter_iff, mem_preimage, Function.eval, mem_iUnion, mem_setOf_eq,
        exists_prop, jvQ]
      constructor
      · rintro ⟨hx, hT⟩
        refine ⟨fun j => jvS G x j, hT, hx, fun j hj => ?_⟩
        simp only [jvExt, dif_pos hj]
        exact jvSeq_agree _ (i+1) j hj
      · rintro ⟨u, hu, hx, hq⟩
        refine ⟨hx, ?_⟩
        have := hq i (Nat.lt_succ_self i)
        simp only [jvExt, dif_pos (Nat.lt_succ_self i)] at this
        show jvT G x (i+1) i ∈ T
        rw [this]; exact hu
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) (fun u _ => jvQ_am G hG _ _)
  · simp only [preimage_empty, inter_empty]; exact @MeasurableSet.empty X (analyticSigmaAlgebra X)
  · intro C _ h
    have : (Prod.fst '' range G) ∩ jvS G ⁻¹' Cᶜ =
        (Prod.fst '' range G) \ ((Prod.fst '' range G) ∩ jvS G ⁻¹' C) := by
      ext x; simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_diff]; tauto
    rw [this]; exact MeasurableSet.inter hP (MeasurableSet.compl h)
  · intro C _ h
    rw [preimage_iUnion, inter_iUnion]; exact MeasurableSet.iUnion h

end JV

theorem jankov_von_neumann_core {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [IsBorelSpace Y]
    (A : Set (X × Y)) (hA : AnalyticSet A) :
    ∃ φ : (Prod.fst '' A) → Y,
      IsAnalyticallyMeasurableFun (Prod.fst '' A) φ ∧
        ∀ x : Prod.fst '' A, ((x : X), φ x) ∈ A := by
  classical
  have hT2 := au_t2 (X := X)
  have hpA : IsAnalyticallyMeasurable (Prod.fst '' A) :=
    MeasurableSpace.measurableSet_generateFrom (hA.image_of_continuous continuous_fst)
  rw [AnalyticSet] at hA
  rcases hA with hA | ⟨G, hG, rfl⟩
  · subst hA
    refine ⟨fun x => False.elim (by simpa using x.2), ⟨hpA, fun B _ => ?_⟩,
      fun x => False.elim (by simpa using x.2)⟩
    have h0 : ∀ s : Set (Prod.fst '' (∅ : Set (X × Y))), Subtype.val '' s = ∅ := by
      intro s; ext y; simp
    rw [h0]; exact @MeasurableSet.empty X (analyticSigmaAlgebra X)
  · refine ⟨fun x => (G (jvS G x)).2, ⟨hpA, fun B hB => ?_⟩,
      fun x => ⟨jvS G x, Prod.ext (jvS_mem G hG x x.2) rfl⟩⟩
    have hH : Measurable (fun σ : ℕ → ℕ => (G σ).2) := (continuous_snd.comp hG).measurable
    have : Subtype.val '' ((fun x : Prod.fst '' range G => (G (jvS G x)).2) ⁻¹' B) =
        (Prod.fst '' range G) ∩ jvS G ⁻¹' ((fun σ => (G σ).2) ⁻¹' B) := by
      ext x
      constructor
      · rintro ⟨x', hx', rfl⟩; exact ⟨x'.2, hx'⟩
      · rintro ⟨hx, hB⟩; exact ⟨⟨x, hx⟩, hB, rfl⟩
    rw [this]
    exact jv_pre_am G hG _ (hH hB)


/-! ## General versions -/

lemma gl_um_of_analytic {W : Type*} [TopologicalSpace W] [T2Space W] [MeasurableSpace W]
    [OpensMeasurableSpace W] (A : Set W) (hA : AnalyticSet A) : IsUniversallyMeasurable A := by
  intro p hp
  rw [AnalyticSet] at hA
  rcases hA with hA | ⟨f, hf, rfl⟩
  · subst hA; exact nullMeasurableSet_empty
  · exact au_null_of_inner p _ (fun ε hε => au_analytic_inner p f hf ε hε)

lemma gl_um_of_am {W : Type*} [TopologicalSpace W] [T2Space W] [MeasurableSpace W]
    [OpensMeasurableSpace W] (E : Set W) (hE : MeasurableSet[analyticSigmaAlgebra W] E) :
    IsUniversallyMeasurable E := by
  intro p hp
  exact MeasurableSpace.generateFrom_induction _ (fun s _ => NullMeasurableSet s p)
    (fun t ht _ => gl_um_of_analytic t ht p hp) nullMeasurableSet_empty
    (fun t _ h => h.compl) (fun s _ h => NullMeasurableSet.iUnion h) E hE

lemma gl_um_inter {X : Type*} [MeasurableSpace X] {s t : Set X} (hs : IsUniversallyMeasurable s)
    (ht : IsUniversallyMeasurable t) : IsUniversallyMeasurable (s ∩ t) :=
  fun p hp => (hs p hp).inter (ht p hp)

lemma gl_um_union {X : Type*} [MeasurableSpace X] {s t : Set X} (hs : IsUniversallyMeasurable s)
    (ht : IsUniversallyMeasurable t) : IsUniversallyMeasurable (s ∪ t) :=
  fun p hp => (hs p hp).union (ht p hp)

lemma gl_um_diff {X : Type*} [MeasurableSpace X] {s t : Set X} (hs : IsUniversallyMeasurable s)
    (ht : IsUniversallyMeasurable t) : IsUniversallyMeasurable (s \ t) :=
  fun p hp => (hs p hp).diff (ht p hp)

lemma gl_um_iUnion {X : Type*} [MeasurableSpace X] {s : ℕ → Set X}
    (hs : ∀ n, IsUniversallyMeasurable (s n)) : IsUniversallyMeasurable (⋃ n, s n) :=
  fun p hp => NullMeasurableSet.iUnion (fun n => hs n p hp)

lemma gl_um_of_meas {X : Type*} [MeasurableSpace X] {s : Set X} (hs : MeasurableSet s) :
    IsUniversallyMeasurable s :=
  fun _ _ => hs.nullMeasurableSet

/-- preimage of a universally measurable set under a universally measurable total map
restricted to `P`. -/
lemma gl_preimage_um {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (P : Set X) (hP : IsUniversallyMeasurable P) (F : X → Y)
    (hF : ∀ B : Set Y, MeasurableSet B → IsUniversallyMeasurable (P ∩ F ⁻¹' B))
    (A : Set Y) (hA : IsUniversallyMeasurable A) :
    IsUniversallyMeasurable (P ∩ F ⁻¹' A) := by
  classical
  intro p hp
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x0⟩⟩
  · have : P ∩ F ⁻¹' A = ∅ := by ext x; exact hX.elim x
    rw [this]; exact nullMeasurableSet_empty
  let y0 := F x0
  let F' : X → Y := fun x => if x ∈ P then F x else y0
  have hset : ∀ B : Set Y, P ∩ F ⁻¹' B = P ∩ F' ⁻¹' B := by
    intro B; ext x
    by_cases hx : x ∈ P
    · simp [F', hx]
    · simp [hx]
  have hpre : ∀ B : Set Y, F' ⁻¹' B = (P ∩ F ⁻¹' B) ∪ {x | x ∉ P ∧ y0 ∈ B} := by
    intro B; ext x
    by_cases hx : x ∈ P
    · simp [F', hx]
    · simp [F', hx]
  have hFn : NullMeasurable F' p := by
    intro B hB
    rw [hpre B]
    refine (hF B hB p hp).union ?_
    by_cases hy : y0 ∈ B
    · have : {x | x ∉ P ∧ y0 ∈ B} = Pᶜ := by ext x; simp [hy]
      rw [this]; exact (hP p hp).compl
    · have : {x | x ∉ P ∧ y0 ∈ B} = ∅ := by ext x; simp [hy]
      rw [this]; exact nullMeasurableSet_empty
  have hFa : AEMeasurable F' p := hFn.aemeasurable
  haveI : IsProbabilityMeasure (p.map F') := Measure.isProbabilityMeasure_map hFa
  have hA' := hA (p.map F') inferInstance
  rw [Measure.map_congr hFa.ae_eq_mk] at hA'
  have h1 : NullMeasurableSet (hFa.mk F' ⁻¹' A) p :=
    hA'.preimage (hFa.measurable_mk.quasiMeasurePreserving p)
  have h2 : NullMeasurableSet (F' ⁻¹' A) p := h1.congr (hFa.ae_eq_mk.preimage A).symm
  rw [hset A]
  exact (hP p hp).inter h2

theorem gl_jvn {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (A : Set (X × Y)) (hA : AnalyticSet A) :
    ∃ φ : (Prod.fst '' A) → Y,
      IsAnalyticallyMeasurableFun (Prod.fst '' A) φ ∧
        ∀ x : Prod.fst '' A, ((x : X), φ x) ∈ A := by
  classical
  have hpA : IsAnalyticallyMeasurable (Prod.fst '' A) :=
    MeasurableSpace.measurableSet_generateFrom (hA.image_of_continuous continuous_fst)
  rw [AnalyticSet] at hA
  rcases hA with hA | ⟨G, hG, rfl⟩
  · subst hA
    refine ⟨fun x => False.elim (by simpa using x.2), ⟨hpA, fun B _ => ?_⟩,
      fun x => False.elim (by simpa using x.2)⟩
    have h0 : ∀ s : Set (Prod.fst '' (∅ : Set (X × Y))), Subtype.val '' s = ∅ := by
      intro s; ext y; simp
    rw [h0]; exact @MeasurableSet.empty X (analyticSigmaAlgebra X)
  · refine ⟨fun x => (G (jvS G x)).2, ⟨hpA, fun B hB => ?_⟩,
      fun x => ⟨jvS G x, Prod.ext (jvS_mem G hG x x.2) rfl⟩⟩
    have hH : Measurable (fun σ : ℕ → ℕ => (G σ).2) := (continuous_snd.comp hG).measurable
    have : Subtype.val '' ((fun x : Prod.fst '' range G => (G (jvS G x)).2) ⁻¹' B) =
        (Prod.fst '' range G) ∩ jvS G ⁻¹' ((fun σ => (G σ).2) ⁻¹' B) := by
      ext x
      constructor
      · rintro ⟨x', hx', rfl⟩; exact ⟨x'.2, hx'⟩
      · rintro ⟨hx, hB⟩; exact ⟨⟨x, hx⟩, hB, rfl⟩
    rw [this]
    exact jv_pre_am G hG _ (hH hB)

lemma gl_jvn_total {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (y0 : Y)
    (A : Set (X × Y)) (hA : AnalyticSet A) :
    ∃ ψ : X → Y, (∀ x ∈ Prod.fst '' A, (x, ψ x) ∈ A) ∧
      ∀ B : Set Y, MeasurableSet B →
        MeasurableSet[analyticSigmaAlgebra X] ((Prod.fst '' A) ∩ ψ ⁻¹' B) := by
  classical
  obtain ⟨φ, hφm, hφA⟩ := gl_jvn A hA
  refine ⟨fun x => if h : x ∈ Prod.fst '' A then φ ⟨x, h⟩ else y0, fun x hx => ?_,
    fun B hB => ?_⟩
  · simp only [dif_pos hx]; exact hφA ⟨x, hx⟩
  · have : (Prod.fst '' A) ∩ (fun x => if h : x ∈ Prod.fst '' A then φ ⟨x, h⟩ else y0) ⁻¹' B =
        Subtype.val '' (φ ⁻¹' B) := by
      ext x
      constructor
      · rintro ⟨hx, hxB⟩
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        simp only [mem_preimage, dif_pos hx] at hxB; exact hxB
      · rintro ⟨x', hx', rfl⟩
        refine ⟨x'.2, ?_⟩
        simp only [mem_preimage, dif_pos x'.2]; exact hx'
    rw [this]; exact hφm.2 B hB

/-- first-match patching over ℕ. -/
lemma gl_patch {X Y : Type*} [TopologicalSpace X] [MeasurableSpace Y]
    (E : ℕ → Set X) (ψ : ℕ → X → Y)
    (hE : ∀ n, MeasurableSet[analyticSigmaAlgebra X] (E n))
    (hψ : ∀ n (B : Set Y), MeasurableSet B →
      MeasurableSet[analyticSigmaAlgebra X] (E n ∩ ψ n ⁻¹' B))
    (hcov : ∀ x, ∃ n, x ∈ E n) :
    ∃ Ψ : X → Y, (∀ B : Set Y, MeasurableSet B →
      MeasurableSet[analyticSigmaAlgebra X] (Ψ ⁻¹' B)) ∧ ∀ x, ∃ n, x ∈ E n ∧ Ψ x = ψ n x := by
  classical
  refine ⟨fun x => ψ (Nat.find (hcov x)) x, fun B hB => ?_,
    fun x => ⟨Nat.find (hcov x), Nat.find_spec (hcov x), rfl⟩⟩
  have : (fun x => ψ (Nat.find (hcov x)) x) ⁻¹' B =
      ⋃ n, (E n ∩ ψ n ⁻¹' B) ∩ ⋂ m ∈ Iio n, (E m)ᶜ := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_iInter, mem_Iio, mem_compl_iff]
    constructor
    · intro hx
      exact ⟨Nat.find (hcov x), ⟨Nat.find_spec (hcov x), hx⟩,
        fun m hm => Nat.find_min (hcov x) hm⟩
    · rintro ⟨n, ⟨hxn, hxB⟩, hmin⟩
      have : Nat.find (hcov x) = n := (Nat.find_eq_iff (hcov x)).2 ⟨hxn, hmin⟩
      rw [this]; exact hxB
  rw [this]
  exact MeasurableSet.iUnion fun n => MeasurableSet.inter (hψ n B hB)
    (MeasurableSet.biInter (Set.to_countable _) fun m _ => (hE m).compl)

/-! ## lower semianalytic preliminaries -/

def glA {X Y : Type*} (D : Set (X × Y)) (f : D → EReal) (c : EReal) : Set (X × Y) :=
  Subtype.val '' {d : D | f d < c}

lemma glA_analytic {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (D : Set (X × Y)) (f : D → EReal) (hf : IsLowerSemianalytic D f) (c : EReal) :
    AnalyticSet (glA D f c) := by
  have : glA D f c = ⋃ q : {q : ℚ // (((q : ℝ)) : EReal) < c},
      Subtype.val '' {d : D | f d < (((q.1 : ℝ)) : EReal)} := by
    ext z
    simp only [glA, mem_image, mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_rat_btwn.1 hd
      exact ⟨⟨q, hq2⟩, d, hq1, rfl⟩
    · rintro ⟨q, d, hd, rfl⟩
      exact ⟨d, hd.trans q.2, rfl⟩
  rw [this]
  exact AnalyticSet.iUnion fun q => hf.2 _

lemma glA_sub {X Y : Type*} (D : Set (X × Y)) (f : D → EReal) (c : EReal) : glA D f c ⊆ D := by
  rintro _ ⟨d, _, rfl⟩; exact d.2

lemma glA_mono {X Y : Type*} (D : Set (X × Y)) (f : D → EReal) {c c' : EReal} (h : c ≤ c') :
    glA D f c ⊆ glA D f c' := by
  rintro _ ⟨d, hd, rfl⟩; exact ⟨d, lt_of_lt_of_le hd h, rfl⟩

lemma gl_pI_le {X Y : Type*} (D : Set (X × Y)) (f : D → EReal) (x : X) (hx : x ∈ Prod.fst '' D)
    (y : Y) (h : (x, y) ∈ D) : partialInf D f ⟨x, hx⟩ ≤ f ⟨(x, y), h⟩ := by
  unfold partialInf
  exact iInf₂_le_of_le y h le_rfl

lemma gl_pI_lt_iff {X Y : Type*} (D : Set (X × Y)) (f : D → EReal) (x : X)
    (hx : x ∈ Prod.fst '' D) (c : EReal) :
    partialInf D f ⟨x, hx⟩ < c ↔ x ∈ Prod.fst '' glA D f c := by
  unfold partialInf
  simp only [iInf_lt_iff]
  constructor
  · rintro ⟨y, h, hlt⟩
    exact ⟨(x, y), ⟨⟨(x, y), h⟩, hlt, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨d.1.2, d.2, hd⟩

lemma gl_fA {X Y : Type*} (D : Set (X × Y)) (f : D → EReal) (c : EReal) (x : X) (y : Y)
    (hA : (x, y) ∈ glA D f c) (h : (x, y) ∈ D) : f ⟨(x, y), h⟩ < c := by
  obtain ⟨d, hd, hdeq⟩ := hA
  have : d = ⟨(x, y), h⟩ := Subtype.ext hdeq
  rw [← this]; exact hd

lemma gl_ereal_top (ε : ℝ) (hε : 0 < ε) (a : EReal)
    (h : ∀ k : ℤ, (((k : ℝ) * ε : ℝ) : EReal) ≤ a) : a = ⊤ := by
  induction a using EReal.rec with
  | bot => have := h 0; simp at this
  | coe r =>
    obtain ⟨k, hk⟩ := exists_int_gt (r / ε)
    have h1 := h k
    rw [EReal.coe_le_coe_iff] at h1
    have : r < k * ε := by rwa [div_lt_iff₀ hε] at hk
    linarith
  | top => rfl

lemma gl_ereal_bot (ε : ℝ) (hε : 0 < ε) (a : EReal)
    (h : ∀ k : ℤ, a < (((k : ℝ) * ε : ℝ) : EReal)) : a = ⊥ := by
  induction a using EReal.rec with
  | bot => rfl
  | coe r =>
    obtain ⟨k, hk⟩ := exists_int_lt (r / ε)
    have h1 := h k
    rw [EReal.coe_lt_coe_iff] at h1
    have : (k : ℝ) * ε < r := by rwa [lt_div_iff₀ hε] at hk
    linarith
  | top => have := h 0; simp at this

def glPiece {α : Type*} (a0 a1 a2 : α) (g : ℕ → α) : ℕ → α
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | n+3 => g n

lemma gl_partA {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (y0 : Y)
    (D : Set (X × Y)) (hD : AnalyticSet D) (f : D → EReal) (hf : IsLowerSemianalytic D f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : X → Y,
      (∀ B : Set Y, MeasurableSet B → MeasurableSet[analyticSigmaAlgebra X] (ψ ⁻¹' B)) ∧
      ∀ x (hx : x ∈ Prod.fst '' D), ∃ h : (x, ψ x) ∈ D,
        (partialInf D f ⟨x, hx⟩ ≠ ⊥ → f ⟨(x, ψ x), h⟩ ≤ partialInf D f ⟨x, hx⟩ + (ε : EReal)) ∧
        (partialInf D f ⟨x, hx⟩ = ⊥ → f ⟨(x, ψ x), h⟩ ≤ ((-1 / ε : ℝ) : EReal)) := by
  classical
  let c : ℤ → EReal := fun k => (((k : ℝ) * ε : ℝ) : EReal)
  let cB : EReal := ((-1 / ε : ℝ) : EReal)
  let Pk : ℤ → Set X := fun k => Prod.fst '' glA D f (c k)
  have hPk : ∀ k, MeasurableSet[analyticSigmaAlgebra X] (Pk k) := fun k =>
    MeasurableSpace.measurableSet_generateFrom
      ((glA_analytic D f hf (c k)).image_of_continuous continuous_fst)
  have hpD : MeasurableSet[analyticSigmaAlgebra X] (Prod.fst '' D) :=
    MeasurableSpace.measurableSet_generateFrom (hD.image_of_continuous continuous_fst)
  have hPmono : ∀ k k', k ≤ k' → Pk k ⊆ Pk k' := fun k k' h => image_mono (glA_mono D f (by
      simp only [c]; rw [EReal.coe_le_coe_iff]
      exact mul_le_mul_of_nonneg_right (Int.cast_le.2 h) hε.le))
  obtain ⟨ψD, hψD, hψDm⟩ := gl_jvn_total y0 D hD
  obtain ⟨ψB, hψB, hψBm⟩ := gl_jvn_total y0 (glA D f cB) (glA_analytic D f hf cB)
  choose ψk hψk hψkm using fun k : ℤ =>
    gl_jvn_total y0 (glA D f (c k)) (glA_analytic D f hf (c k))
  obtain ⟨k0, hk0⟩ := exists_int_lt ((-1 / ε) / ε)
  have hck0 : c k0 ≤ cB := by
    simp only [c, cB]; rw [EReal.coe_le_coe_iff]
    have := (lt_div_iff₀ hε).1 hk0; linarith
  let e : ℕ → ℤ := fun n => Equiv.intEquivNat.symm n
  let E : ℕ → Set X := glPiece ((⋂ k, Pk k) ∩ Prod.fst '' glA D f cB)
    ((⋃ k, Pk k)ᶜ ∩ Prod.fst '' D) (Prod.fst '' D)ᶜ (fun n => Pk (e n) \ Pk (e n - 1))
  let ψ : ℕ → X → Y := glPiece ψB ψD (fun _ => y0) (fun n => ψk (e n))
  have hE : ∀ n, MeasurableSet[analyticSigmaAlgebra X] (E n) := by
    intro n
    rcases n with _ | _ | _ | n
    · exact MeasurableSet.inter (MeasurableSet.iInter hPk)
        (MeasurableSpace.measurableSet_generateFrom
          ((glA_analytic D f hf cB).image_of_continuous continuous_fst))
    · exact MeasurableSet.inter (MeasurableSet.compl (MeasurableSet.iUnion hPk)) hpD
    · exact MeasurableSet.compl hpD
    · exact MeasurableSet.inter (hPk _) (MeasurableSet.compl (hPk _))
  have hψ : ∀ n (B : Set Y), MeasurableSet B →
      MeasurableSet[analyticSigmaAlgebra X] (E n ∩ ψ n ⁻¹' B) := by
    intro n B hB
    rcases n with _ | _ | _ | n
    · show MeasurableSet[analyticSigmaAlgebra X]
        (((⋂ k, Pk k) ∩ Prod.fst '' glA D f cB) ∩ ψB ⁻¹' B)
      rw [inter_assoc]
      exact MeasurableSet.inter (MeasurableSet.iInter hPk) (hψBm B hB)
    · show MeasurableSet[analyticSigmaAlgebra X] (((⋃ k, Pk k)ᶜ ∩ Prod.fst '' D) ∩ ψD ⁻¹' B)
      rw [inter_assoc]
      exact MeasurableSet.inter (MeasurableSet.compl (MeasurableSet.iUnion hPk)) (hψDm B hB)
    · show MeasurableSet[analyticSigmaAlgebra X] ((Prod.fst '' D)ᶜ ∩ (fun _ => y0) ⁻¹' B)
      by_cases hy : y0 ∈ B
      · rw [preimage_const_of_mem hy, inter_univ]; exact MeasurableSet.compl hpD
      · rw [preimage_const_of_notMem hy, inter_empty]
        exact @MeasurableSet.empty X (analyticSigmaAlgebra X)
    · show MeasurableSet[analyticSigmaAlgebra X] ((Pk (e n) \ Pk (e n - 1)) ∩ ψk (e n) ⁻¹' B)
      have : (Pk (e n) \ Pk (e n - 1)) ∩ ψk (e n) ⁻¹' B =
          (Pk (e n) ∩ ψk (e n) ⁻¹' B) ∩ (Pk (e n - 1))ᶜ := by
        ext x; simp only [mem_inter_iff, mem_diff, mem_compl_iff]; tauto
      rw [this]
      exact MeasurableSet.inter (hψkm (e n) B hB) (MeasurableSet.compl (hPk _))
  have hcov : ∀ x, ∃ n, x ∈ E n := by
    intro x
    by_cases hxD : x ∈ Prod.fst '' D
    · by_cases hU : x ∈ ⋃ k, Pk k
      · by_cases hI : ∀ k, x ∈ Pk k
        · refine ⟨0, ?_⟩
          show x ∈ (⋂ k, Pk k) ∩ Prod.fst '' glA D f cB
          exact ⟨mem_iInter.2 hI, image_mono (glA_mono D f hck0) (hI k0)⟩
        · push_neg at hI
          obtain ⟨k1, hk1⟩ := hI
          obtain ⟨k2, hk2⟩ := mem_iUnion.1 hU
          obtain ⟨lb, hlb, hmin⟩ := Int.exists_least_of_bdd (P := fun z => x ∈ Pk z)
            ⟨k1, fun z hz => by
              by_contra hlt; push_neg at hlt
              exact hk1 (hPmono z k1 hlt.le hz)⟩ ⟨k2, hk2⟩
          refine ⟨Equiv.intEquivNat lb + 3, ?_⟩
          show x ∈ Pk (e (Equiv.intEquivNat lb)) \ Pk (e (Equiv.intEquivNat lb) - 1)
          have he : e (Equiv.intEquivNat lb) = lb := Equiv.symm_apply_apply _ _
          rw [he]
          refine ⟨hlb, fun h => ?_⟩
          have := hmin _ h; omega
      · exact ⟨1, show x ∈ (⋃ k, Pk k)ᶜ ∩ Prod.fst '' D from ⟨hU, hxD⟩⟩
    · exact ⟨2, show x ∈ (Prod.fst '' D)ᶜ from hxD⟩
  obtain ⟨Ψ, hΨm, hΨ⟩ := gl_patch E ψ hE hψ hcov
  refine ⟨Ψ, hΨm, fun x hx => ?_⟩
  obtain ⟨n, hxn, hΨx⟩ := hΨ x
  rw [hΨx]
  set a := partialInf D f ⟨x, hx⟩ with ha
  rcases n with _ | _ | _ | n
  · -- f* = ⊥
    obtain ⟨hI, hxB⟩ := (show x ∈ (⋂ k, Pk k) ∩ Prod.fst '' glA D f cB from hxn)
    have hbot : a = ⊥ := gl_ereal_bot ε hε a fun k =>
      (gl_pI_lt_iff D f x hx (c k)).2 (mem_iInter.1 hI k)
    have hmem : (x, ψB x) ∈ glA D f cB := hψB x hxB
    refine ⟨glA_sub D f cB hmem, fun h => absurd hbot h, fun _ => ?_⟩
    exact (gl_fA D f cB x (ψB x) hmem _).le
  · obtain ⟨hU, hxD⟩ := (show x ∈ (⋃ k, Pk k)ᶜ ∩ Prod.fst '' D from hxn)
    have htop : a = ⊤ := gl_ereal_top ε hε a fun k => by
      by_contra hlt; push_neg at hlt
      exact hU (mem_iUnion.2 ⟨k, (gl_pI_lt_iff D f x hx (c k)).1 hlt⟩)
    refine ⟨hψD x hxD, fun _ => ?_, fun h => ?_⟩
    · show f _ ≤ a + (ε : EReal)
      rw [htop, EReal.top_add_coe]; exact le_top
    · rw [htop] at h; exact absurd h (by simp)
  · exact absurd hx (show x ∈ (Prod.fst '' D)ᶜ from hxn)
  · obtain ⟨hk, hk1⟩ := (show x ∈ Pk (e n) \ Pk (e n - 1) from hxn)
    set k := e n
    have hmem : (x, ψk k x) ∈ glA D f (c k) := hψk k x hk
    have hlow : c (k - 1) ≤ a := by
      by_contra hlt; push_neg at hlt
      exact hk1 ((gl_pI_lt_iff D f x hx _).1 hlt)
    have hlt := gl_fA D f (c k) x (ψk k x) hmem (glA_sub D f _ hmem)
    have hck : c k = c (k - 1) + (ε : EReal) := by
      simp only [c]; rw [← EReal.coe_add]; congr 1; push_cast; ring
    refine ⟨glA_sub D f _ hmem, fun _ => ?_, fun h => ?_⟩
    · show f _ ≤ a + (ε : EReal)
      calc _ ≤ c k := hlt.le
        _ = c (k - 1) + (ε : EReal) := hck
        _ ≤ a + (ε : EReal) := add_le_add hlow le_rfl
    · rw [h] at hlow
      exact absurd (le_bot_iff.1 hlow) (EReal.coe_ne_bot _)

/-! ## Part (b) preliminaries -/

lemma gl_analytic_union {α : Type*} [TopologicalSpace α] {s t : Set α} (hs : AnalyticSet s)
    (ht : AnalyticSet t) : AnalyticSet (s ∪ t) := by
  rw [Set.union_eq_iUnion]
  exact AnalyticSet.iUnion fun b => by cases b <;> assumption

lemma gl_analytic_prod {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {s : Set α}
    {t : Set β} (hs : AnalyticSet s) (ht : AnalyticSet t) : AnalyticSet (s ×ˢ t) := by
  obtain ⟨β1, h1, p1, f, hf, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hs
  obtain ⟨β2, h2, p2, g, hg, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 ht
  rw [← range_prodMap]
  exact analyticSet_range_of_polishSpace (hf.prodMap hg)

def glR {X Y : Type*} (S : Set (X × Y)) (T : Set EReal) : Set ((X × EReal) × Y) :=
  (fun z : (X × Y) × EReal => ((z.1.1, z.2), z.1.2)) '' (S ×ˢ T)

lemma glR_analytic {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set (X × Y)}
    {T : Set EReal} (hS : AnalyticSet S) (hT : AnalyticSet T) : AnalyticSet (glR S T) :=
  (gl_analytic_prod hS hT).image_of_continuous (by fun_prop)

lemma mem_glR {X Y : Type*} (S : Set (X × Y)) (T : Set EReal) (x : X) (r : EReal) (y : Y) :
    ((x, r), y) ∈ glR S T ↔ (x, y) ∈ S ∧ r ∈ T := by
  constructor
  · rintro ⟨⟨⟨x', y'⟩, r'⟩, ⟨hS, hT⟩, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    exact ⟨hS, hT⟩
  · rintro ⟨hS, hT⟩; exact ⟨((x, y), r), ⟨hS, hT⟩, rfl⟩

def glH {X Y : Type*} (D : Set (X × Y)) (f : D → EReal) : Set ((X × EReal) × Y) :=
  {p | ∃ h : (p.1.1, p.2) ∈ D, f ⟨(p.1.1, p.2), h⟩ ≤ p.1.2}

lemma glH_eq {X Y : Type*} (D : Set (X × Y)) (f : D → EReal) :
    glH D f = ⋂ q : ℚ, (glR D (Ici (((q : ℝ)) : EReal)) ∪
      glR (glA D f (((q : ℝ)) : EReal)) univ) := by
  ext ⟨⟨x, r⟩, y⟩
  simp only [mem_iInter, mem_union, mem_glR, mem_Ici, mem_univ, and_true]
  constructor
  · rintro ⟨h, hle⟩ q
    by_cases hq : (((q : ℝ)) : EReal) ≤ r
    · left; exact ⟨h, hq⟩
    · right; push_neg at hq; exact ⟨⟨(x, y), h⟩, lt_of_le_of_lt hle hq, rfl⟩
  · intro H
    have hD : (x, y) ∈ D := by
      rcases H 0 with h | h
      · exact h.1
      · exact glA_sub D f _ h
    refine ⟨hD, ?_⟩
    by_contra hlt; push_neg at hlt
    obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_rat_btwn.1 hlt
    rcases H q with h | h
    · exact absurd h.2 (not_le.2 hq1)
    · exact absurd (gl_fA D f _ x y h hD) (not_lt.2 hq2.le)

lemma glH_analytic {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    [T2Space Y] (D : Set (X × Y)) (hD : AnalyticSet D) (f : D → EReal)
    (hf : IsLowerSemianalytic D f) : AnalyticSet (glH D f) := by
  rw [glH_eq]
  exact AnalyticSet.iInter fun q => gl_analytic_union
    (glR_analytic hD isClosed_Ici.analyticSet)
    (glR_analytic (glA_analytic D f hf _) isClosed_univ.analyticSet)

open Classical in
noncomputable def glF {X Y : Type*} (D : Set (X × Y)) (f : D → EReal) (x : X) : EReal :=
  if hx : x ∈ Prod.fst '' D then partialInf D f ⟨x, hx⟩ else ⊤

lemma glF_lt {X Y : Type*} (D : Set (X × Y)) (f : D → EReal) (c : EReal) :
    Prod.fst '' D ∩ glF D f ⁻¹' Iio c = Prod.fst '' glA D f c := by
  ext x
  constructor
  · rintro ⟨hx, hlt⟩
    simp only [mem_preimage, mem_Iio, glF, dif_pos hx] at hlt
    exact (gl_pI_lt_iff D f x hx c).1 hlt
  · intro h
    have hx : x ∈ Prod.fst '' D := image_mono (glA_sub D f c) h
    refine ⟨hx, ?_⟩
    simp only [mem_preimage, mem_Iio, glF, dif_pos hx]
    exact (gl_pI_lt_iff D f x hx c).2 h

lemma glF_am {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (D : Set (X × Y)) (hD : AnalyticSet D) (f : D → EReal) (hf : IsLowerSemianalytic D f)
    (B : Set EReal) (hB : MeasurableSet B) :
    MeasurableSet[analyticSigmaAlgebra X] (Prod.fst '' D ∩ glF D f ⁻¹' B) := by
  have hpD : MeasurableSet[analyticSigmaAlgebra X] (Prod.fst '' D) :=
    MeasurableSpace.measurableSet_generateFrom (hD.image_of_continuous continuous_fst)
  have hB' : MeasurableSet[MeasurableSpace.generateFrom (range Iio)] B := by
    rw [← borel_eq_generateFrom_Iio, ← BorelSpace.measurable_eq]; exact hB
  refine MeasurableSpace.generateFrom_induction _
    (fun B _ => MeasurableSet[analyticSigmaAlgebra X] (Prod.fst '' D ∩ glF D f ⁻¹' B))
    ?_ ?_ ?_ ?_ B hB'
  · rintro _ ⟨c, rfl⟩ _
    rw [glF_lt]
    exact MeasurableSpace.measurableSet_generateFrom
      ((glA_analytic D f hf c).image_of_continuous continuous_fst)
  · simp only [preimage_empty, inter_empty]; exact @MeasurableSet.empty X (analyticSigmaAlgebra X)
  · intro s _ h
    have : Prod.fst '' D ∩ glF D f ⁻¹' sᶜ = Prod.fst '' D ∩ (Prod.fst '' D ∩ glF D f ⁻¹' s)ᶜ := by
      ext x; simp only [mem_inter_iff, mem_preimage, mem_compl_iff]; tauto
    rw [this]; exact MeasurableSet.inter hpD (MeasurableSet.compl h)
  · intro s _ h
    rw [preimage_iUnion, inter_iUnion]; exact MeasurableSet.iUnion h

lemma glFF_um {X Y : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y]
    (D : Set (X × Y)) (hD : AnalyticSet D) (f : D → EReal) (hf : IsLowerSemianalytic D f)
    (S : Set (X × EReal)) (hS : MeasurableSet S) :
    IsUniversallyMeasurable (Prod.fst '' D ∩ (fun x => (x, glF D f x)) ⁻¹' S) := by
  have hpD : MeasurableSet[analyticSigmaAlgebra X] (Prod.fst '' D) :=
    MeasurableSpace.measurableSet_generateFrom (hD.image_of_continuous continuous_fst)
  have hpDu : IsUniversallyMeasurable (Prod.fst '' D) := gl_um_of_am _ hpD
  have hS' : MeasurableSet[MeasurableSpace.generateFrom (image2 (· ×ˢ ·)
      {s : Set X | MeasurableSet s} {t : Set EReal | MeasurableSet t})] S := by
    rw [generateFrom_prod]; exact hS
  refine MeasurableSpace.generateFrom_induction _
    (fun S _ => IsUniversallyMeasurable (Prod.fst '' D ∩ (fun x => (x, glF D f x)) ⁻¹' S))
    ?_ ?_ ?_ ?_ S hS'
  · rintro _ ⟨s, hs, t, ht, rfl⟩ _
    have : Prod.fst '' D ∩ (fun x => (x, glF D f x)) ⁻¹' (s ×ˢ t) =
        s ∩ (Prod.fst '' D ∩ glF D f ⁻¹' t) := by
      ext x; simp only [mem_inter_iff, mem_preimage, mem_prod]; tauto
    rw [this]
    exact gl_um_inter (gl_um_of_meas hs) (gl_um_of_am _ (glF_am D hD f hf t ht))
  · simp only [preimage_empty, inter_empty]; exact gl_um_of_meas MeasurableSet.empty
  · intro s _ h
    have : Prod.fst '' D ∩ (fun x => (x, glF D f x)) ⁻¹' sᶜ =
        Prod.fst '' D \ (Prod.fst '' D ∩ (fun x => (x, glF D f x)) ⁻¹' s) := by
      ext x; simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_diff]; tauto
    rw [this]; exact gl_um_diff hpDu h
  · intro s _ h
    rw [preimage_iUnion, inter_iUnion]; exact gl_um_iUnion h

lemma gl_val_preimage {X Y : Type*} (P : Set X) (ψ : X → Y) (B : Set Y) :
    Subtype.val '' ((fun x : P => ψ x) ⁻¹' B) = P ∩ ψ ⁻¹' B := by
  ext x
  constructor
  · rintro ⟨x', hx', rfl⟩; exact ⟨x'.2, hx'⟩
  · rintro ⟨hx, hB⟩; exact ⟨⟨x, hx⟩, hB, rfl⟩

lemma gl_f_congr {X Y : Type*} (D : Set (X × Y)) (f : D → EReal) (x : X) {y y' : Y}
    (hy : (x, y) ∈ D) (hy' : (x, y') ∈ D) (h : y = y') :
    f ⟨(x, y), hy⟩ = f ⟨(x, y'), hy'⟩ := by
  subst h; rfl

theorem lower_semianalytic_selection_core {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [IsBorelSpace Y]
    (D : Set (X × Y)) (hD : AnalyticSet D) (f : D → EReal) (hf : IsLowerSemianalytic D f) :
    -- (a)
    (∀ ε : ℝ, 0 < ε →
      ∃ (φ : (Prod.fst '' D) → Y) (hφ : ∀ x : Prod.fst '' D, ((x : X), φ x) ∈ D),
        IsAnalyticallyMeasurableFun (Prod.fst '' D) φ ∧
        ∀ x : Prod.fst '' D,
          (partialInf D f x ≠ ⊥ → f ⟨((x : X), φ x), hφ x⟩ ≤ partialInf D f x + (ε : EReal)) ∧
          (partialInf D f x = ⊥ → f ⟨((x : X), φ x), hφ x⟩ ≤ ((-1 / ε : ℝ) : EReal))) ∧
    -- (b)
    (IsUniversallyMeasurable (attainSet D f) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ (φ : (Prod.fst '' D) → Y) (hφ : ∀ x : Prod.fst '' D, ((x : X), φ x) ∈ D),
          IsUniversallyMeasurableFun (Prod.fst '' D) φ ∧
          ∀ x : Prod.fst '' D,
            ((x : X) ∈ attainSet D f → f ⟨((x : X), φ x), hφ x⟩ = partialInf D f x) ∧
            ((x : X) ∉ attainSet D f → partialInf D f x ≠ ⊥ →
              f ⟨((x : X), φ x), hφ x⟩ ≤ partialInf D f x + (ε : EReal)) ∧
            ((x : X) ∉ attainSet D f → partialInf D f x = ⊥ →
              f ⟨((x : X), φ x), hφ x⟩ ≤ ((-1 / ε : ℝ) : EReal))) := by
  classical
  have hT2X := au_t2 (X := X)
  have hT2Y := au_t2 (X := Y)
  have hscX := cm_second (X := X)
  have hpD : MeasurableSet[analyticSigmaAlgebra X] (Prod.fst '' D) :=
    MeasurableSpace.measurableSet_generateFrom (hD.image_of_continuous continuous_fst)
  have hpDu : IsUniversallyMeasurable (Prod.fst '' D) := gl_um_of_am _ hpD
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y0⟩⟩
  · have hE : ∀ s : Set (Prod.fst '' D), Subtype.val '' s = ∅ := by
      intro s; ext x
      simp only [mem_image, mem_empty_iff_false, iff_false]
      rintro ⟨x', _, _⟩
      obtain ⟨p, _, _⟩ := x'.2
      exact hY.false p.2
    have hI : attainSet D f = ∅ := by
      ext x
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨hx, _⟩
      obtain ⟨p, _, _⟩ := hx
      exact hY.false p.2
    let φ : (Prod.fst '' D) → Y := fun x => (hY.false x.2.choose.2).elim
    have hφ : ∀ x : Prod.fst '' D, ((x : X), φ x) ∈ D := fun x => (hY.false x.2.choose.2).elim
    refine ⟨fun ε _ => ⟨φ, hφ, ⟨hpD, fun B _ => ?_⟩, fun x => (hY.false x.2.choose.2).elim⟩,
      ?_, fun ε _ => ⟨φ, hφ, ⟨hpDu, fun B _ => ?_⟩, fun x => (hY.false x.2.choose.2).elim⟩⟩
    · rw [hE]; exact @MeasurableSet.empty X (analyticSigmaAlgebra X)
    · rw [hI]; exact fun p _ => nullMeasurableSet_empty
    · rw [hE]; exact fun p _ => nullMeasurableSet_empty
  -- (a)
  have partA : ∀ ε : ℝ, 0 < ε →
      ∃ (φ : (Prod.fst '' D) → Y) (hφ : ∀ x : Prod.fst '' D, ((x : X), φ x) ∈ D),
        IsAnalyticallyMeasurableFun (Prod.fst '' D) φ ∧
        ∀ x : Prod.fst '' D,
          (partialInf D f x ≠ ⊥ → f ⟨((x : X), φ x), hφ x⟩ ≤ partialInf D f x + (ε : EReal)) ∧
          (partialInf D f x = ⊥ → f ⟨((x : X), φ x), hφ x⟩ ≤ ((-1 / ε : ℝ) : EReal)) := by
    intro ε hε
    obtain ⟨ψ, hψm, hψ⟩ := gl_partA y0 D hD f hf ε hε
    refine ⟨fun x => ψ x, fun x => (hψ x x.2).1, ⟨hpD, fun B hB => ?_⟩, fun x => (hψ x x.2).2⟩
    rw [gl_val_preimage]; exact MeasurableSet.inter hpD (hψm B hB)
  refine ⟨partA, ?_⟩
  -- (b)
  have hH : AnalyticSet (glH D f) := glH_analytic D hD f hf
  obtain ⟨ψH, hψH, hψHm⟩ := gl_jvn_total (X := X × EReal) y0 (glH D f) hH
  let F : X → X × EReal := fun x => (x, glF D f x)
  have hFF := glFF_um D hD f hf
  have hattain : attainSet D f = Prod.fst '' D ∩ F ⁻¹' (Prod.fst '' glH D f) := by
    ext x
    constructor
    · rintro ⟨hx, y, h, heq⟩
      refine ⟨hx, ⟨((x, glF D f x), y), ⟨h, ?_⟩, rfl⟩⟩
      simp only [glF, dif_pos hx]; exact heq.le
    · rintro ⟨hx, ⟨⟨⟨x', r⟩, y⟩, ⟨h, hle⟩, hpeq⟩⟩
      simp only [F, Prod.mk.injEq] at hpeq
      obtain ⟨rfl, rfl⟩ := hpeq
      refine ⟨hx, y, h, le_antisymm ?_ (gl_pI_le D f x' hx y h)⟩
      have := hle
      simp only [glF, dif_pos hx] at this
      exact this
  have hI : IsUniversallyMeasurable (attainSet D f) := by
    rw [hattain]
    exact gl_preimage_um _ hpDu F hFF _
      (gl_um_of_analytic _ (hH.image_of_continuous continuous_fst))
  refine ⟨hI, fun ε hε => ?_⟩
  obtain ⟨ψa, hψam, hψa⟩ := gl_partA y0 D hD f hf ε hε
  let Φ : X → Y := fun x => if x ∈ attainSet D f then ψH (F x) else ψa x
  have hgraphI : ∀ x, x ∈ attainSet D f →
      ∃ h : (x, ψH (F x)) ∈ D, f ⟨(x, ψH (F x)), h⟩ ≤ glF D f x := by
    intro x hxI
    rw [hattain] at hxI
    exact hψH (F x) hxI.2
  have hφ : ∀ x : Prod.fst '' D, ((x : X), Φ x) ∈ D := by
    intro x
    by_cases hxI : (x : X) ∈ attainSet D f
    · simp only [Φ, if_pos hxI]; exact (hgraphI x hxI).1
    · simp only [Φ, if_neg hxI]; exact (hψa x x.2).1
  refine ⟨fun x => Φ x, hφ, ⟨hpDu, fun B hB => ?_⟩, fun x => ?_⟩
  · rw [gl_val_preimage]
    have : Prod.fst '' D ∩ Φ ⁻¹' B =
        (Prod.fst '' D ∩ F ⁻¹' (Prod.fst '' glH D f ∩ ψH ⁻¹' B)) ∪
          ((Prod.fst '' D ∩ ψa ⁻¹' B) \ attainSet D f) := by
      ext x
      constructor
      · rintro ⟨hx, hxB⟩
        by_cases hxI : x ∈ attainSet D f
        · left
          have hxI' := hxI
          rw [hattain] at hxI'
          simp only [mem_preimage, Φ, if_pos hxI] at hxB
          exact ⟨hx, hxI'.2, hxB⟩
        · right
          simp only [mem_preimage, Φ, if_neg hxI] at hxB
          exact ⟨⟨hx, hxB⟩, hxI⟩
      · rintro (⟨hx, hF, hB'⟩ | ⟨⟨hx, hxB⟩, hxI⟩)
        · have hxI : x ∈ attainSet D f := by rw [hattain]; exact ⟨hx, hF⟩
          refine ⟨hx, ?_⟩
          simp only [mem_preimage, Φ, if_pos hxI]; exact hB'
        · refine ⟨hx, ?_⟩
          simp only [mem_preimage, Φ, if_neg hxI]; exact hxB
    rw [this]
    refine gl_um_union ?_ (gl_um_diff (gl_um_of_am _ (MeasurableSet.inter hpD (hψam B hB))) hI)
    exact gl_preimage_um _ hpDu F hFF _ (gl_um_of_am _ (hψHm B hB))
  · obtain ⟨x, hx⟩ := x
    refine ⟨fun hxI => ?_, fun hxI h1 => ?_, fun hxI h1 => ?_⟩
    · obtain ⟨h, hle⟩ := hgraphI x hxI
      have hΦ : Φ x = ψH (F x) := if_pos hxI
      rw [gl_f_congr D f x (hφ ⟨x, hx⟩) h hΦ]
      refine le_antisymm ?_ (gl_pI_le D f x hx _ h)
      simp only [glF, dif_pos hx] at hle; exact hle
    · obtain ⟨h, hb1, _⟩ := hψa x hx
      have hΦ : Φ x = ψa x := if_neg hxI
      rw [gl_f_congr D f x (hφ ⟨x, hx⟩) h hΦ]
      exact hb1 h1
    · obtain ⟨h, _, hb2⟩ := hψa x hx
      have hΦ : Φ x = ψa x := if_neg hxI
      rw [gl_f_congr D f x (hφ ⟨x, hx⟩) h hΦ]
      exact hb2 h1

end BertsekasShreve.AnalyticSelection

open BertsekasShreve.AnalyticSelection


theorem solution {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [IsBorelSpace Y]
    (D : Set (X × Y)) (hD : AnalyticSet D) (f : D → EReal) (hf : IsLowerSemianalytic D f) :
    -- (a)
    (∀ ε : ℝ, 0 < ε →
      ∃ (φ : (Prod.fst '' D) → Y) (hφ : ∀ x : Prod.fst '' D, ((x : X), φ x) ∈ D),
        IsAnalyticallyMeasurableFun (Prod.fst '' D) φ ∧
        ∀ x : Prod.fst '' D,
          (partialInf D f x ≠ ⊥ → f ⟨((x : X), φ x), hφ x⟩ ≤ partialInf D f x + (ε : EReal)) ∧
          (partialInf D f x = ⊥ → f ⟨((x : X), φ x), hφ x⟩ ≤ ((-1 / ε : ℝ) : EReal))) ∧
    -- (b)
    (IsUniversallyMeasurable (attainSet D f) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ (φ : (Prod.fst '' D) → Y) (hφ : ∀ x : Prod.fst '' D, ((x : X), φ x) ∈ D),
          IsUniversallyMeasurableFun (Prod.fst '' D) φ ∧
          ∀ x : Prod.fst '' D,
            ((x : X) ∈ attainSet D f → f ⟨((x : X), φ x), hφ x⟩ = partialInf D f x) ∧
            ((x : X) ∉ attainSet D f → partialInf D f x ≠ ⊥ →
              f ⟨((x : X), φ x), hφ x⟩ ≤ partialInf D f x + (ε : EReal)) ∧
            ((x : X) ∉ attainSet D f → partialInf D f x = ⊥ →
              f ⟨((x : X), φ x), hφ x⟩ ≤ ((-1 / ε : ℝ) : EReal))) := by
  exact lower_semianalytic_selection_core D hD f hf
