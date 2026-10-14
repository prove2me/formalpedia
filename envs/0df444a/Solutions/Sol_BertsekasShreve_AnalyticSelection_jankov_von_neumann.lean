-- Prove2me | solution 1 for BertsekasShreve.AnalyticSelection.jankov_von_neumann
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:14:55.421588+00:00
-- url     : https://prove2.me/submissions/f9209e26-e215-4abd-86fc-ba3fa7ffd15a

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

end BertsekasShreve.AnalyticSelection

open BertsekasShreve.AnalyticSelection


theorem solution {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [IsBorelSpace Y]
    (A : Set (X × Y)) (hA : AnalyticSet A) :
    ∃ φ : (Prod.fst '' A) → Y,
      IsAnalyticallyMeasurableFun (Prod.fst '' A) φ ∧ ∀ x : Prod.fst '' A, ((x : X), φ x) ∈ A := by
  exact jankov_von_neumann_core A hA
