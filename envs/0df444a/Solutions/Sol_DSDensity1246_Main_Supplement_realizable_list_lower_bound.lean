-- Prove2me | solution 1 for DSDensity1246.Main.Supplement.realizable_list_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:38:13.801384+00:00
-- url     : https://prove2.me/submissions/1245b330-eb40-451b-ab3a-8c0fb89924c2

import Mathlib
import Definitions.Def_DSDensity1246_Main_dsModel
import Definitions.Def_DSDensity1246_Main_Supplement_learning

section
open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace DSDensity1246.Dev.LBReal

open DSDensity1246.Main DSDensity1246.Main.Supplement


open Classical in
theorem avg_exists {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Fc : Finset ι) (hne : Fc.Nonempty) (E : ι → Set Ω) (G : Set Ω) (hG : MeasurableSet G)
    (num den : ℕ)
    (h : ∀ x ∈ G, num * Fc.card ≤ den * (Fc.filter (fun f => x ∈ E f)).card) :
    ∃ f ∈ Fc, (num : ℝ≥0∞) * P G ≤ den * P (E f) := by
  classical
  by_contra hcon
  push Not at hcon
  have hlt : ∑ f ∈ Fc, (den : ℝ≥0∞) * P (E f) < ∑ f ∈ Fc, (num : ℝ≥0∞) * P G :=
    ENNReal.sum_lt_sum_of_nonempty hne hcon
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  -- hulls
  have hhull : ∀ f, ∃ M : Set Ω, E f ⊆ M ∧ MeasurableSet M ∧ P M = P (E f) :=
    fun f => ⟨toMeasurable P (E f), subset_toMeasurable _ _, measurableSet_toMeasurable _ _,
      measure_toMeasurable _⟩
  choose M hEM hMm hMP using hhull
  have key : (num : ℝ≥0∞) * Fc.card * P G ≤ ∑ f ∈ Fc, (den : ℝ≥0∞) * P (E f) := by
    have h1 : ∀ f ∈ Fc, (den : ℝ≥0∞) * P (E f) ≥
        ∫⁻ x in G, (den : ℝ≥0∞) * (M f).indicator 1 x ∂P := by
      intro f _
      rw [lintegral_const_mul _ (measurable_one.indicator (hMm f)),
        lintegral_indicator_one (hMm f), Measure.restrict_apply (hMm f), ← hMP f]
      gcongr
      exact Set.inter_subset_left
    calc (num : ℝ≥0∞) * Fc.card * P G
        = ∫⁻ x in G, (num : ℝ≥0∞) * Fc.card ∂P := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ x in G, ∑ f ∈ Fc, (den : ℝ≥0∞) * (M f).indicator 1 x ∂P := by
          apply setLIntegral_mono' hG
          intro x hx
          have := h x hx
          have h2 : ((num * Fc.card : ℕ) : ℝ≥0∞) ≤ ((den * (Fc.filter (fun f => x ∈ E f)).card : ℕ) : ℝ≥0∞) := by
            exact_mod_cast this
          calc (num : ℝ≥0∞) * Fc.card = ((num * Fc.card : ℕ) : ℝ≥0∞) := by push_cast; rfl
            _ ≤ _ := h2
            _ = ∑ f ∈ Fc, (den : ℝ≥0∞) * (E f).indicator 1 x := by
                rw [Nat.cast_mul, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro f _
                by_cases hx : x ∈ E f <;> simp [hx]
            _ ≤ _ := by
                apply Finset.sum_le_sum
                intro f _
                gcongr
                exact hEM f
      _ = ∑ f ∈ Fc, ∫⁻ x in G, (den : ℝ≥0∞) * (M f).indicator 1 x ∂P := by
          rw [lintegral_finsetSum]
          intro f _
          exact (measurable_one.indicator (hMm f)).const_mul _
      _ ≤ _ := Finset.sum_le_sum h1
  have : (num : ℝ≥0∞) * Fc.card * P G = Fc.card * ((num : ℝ≥0∞) * P G) := by ring
  rw [this] at key
  exact absurd (lt_of_le_of_lt key hlt) (lt_irrefl _)




def pt {X Y : Type*} {d : ℕ} (S : Fin d → X) (f : Fin d → Y) (a : Fin d) : X × Y := (S a, f a)

noncomputable def mkLaw {X Y : Type*} {d : ℕ} (S : Fin d → X) (f : Fin d → Y)
    (ν : ProbabilityMeasure (Fin d)) : DataLaw (X × Y) :=
  ⟨⊤, letI : MeasurableSpace (X × Y) := ⊤
    ProbabilityMeasure.map ν (f := pt S f) (Measurable.of_discrete).aemeasurable⟩

theorem failure_ge {X Y R : Type*} [MeasurableSpace R] {ℓ d : ℕ} (S : Fin d → X) (f : Fin d → Y)
    (ν : ProbabilityMeasure (Fin d)) (ρ : ProbabilityMeasure R) (A : ListLearner X Y R ℓ)
    (ε δ : ℝ) (m : ℕ) :
    ((Measure.pi (fun _ : Fin m => (ν : Measure (Fin d)))).prod (ρ : Measure R))
      {x | 0 + ENNReal.ofReal ε <
        listError (mkLaw S f ν) (A ε δ m (fun j => pt S f (x.1 j)) x.2)}
      ≤ failureProbability (mkLaw S f ν) ρ A ε δ m 0 := by
  letI : MeasurableSpace (X × Y) := ⊤
  have hmeas : Measurable (pt S f) := Measurable.of_discrete
  unfold failureProbability trainingLaw iidLaw
  simp only [mkLaw]
  have h1 : (Measure.pi fun _ : Fin m => ((ν.map hmeas.aemeasurable : ProbabilityMeasure (X × Y)) : Measure (X × Y)))
      = (Measure.pi fun _ : Fin m => (ν : Measure (Fin d))).map (fun s j => pt S f (s j)) := by
    rw [Measure.pi_map_pi (fun _ => hmeas.aemeasurable)]
    simp [ProbabilityMeasure.toMeasure_map]
  have h2 : Measurable (fun (s : Fin m → Fin d) (j : Fin m) => pt S f (s j)) := Measurable.of_discrete
  have h3 := Measure.map_prod_map (Measure.pi fun _ : Fin m => (ν : Measure (Fin d))) (ρ : Measure R) h2
    (measurable_id : Measurable (id : R → R))
  rw [Measure.map_id] at h3
  have h4 := Measure.le_map_apply (h2.prodMap measurable_id).aemeasurable
    (μ := (Measure.pi fun _ : Fin m => (ν : Measure (Fin d))).prod (ρ : Measure R))
    {t : (Fin m → X × Y) × R | 0 + ENNReal.ofReal ε < listError (mkLaw S f ν) (A ε δ m t.1 t.2)}
  rw [← h3, ← h1] at h4
  exact h4

theorem listError_ge {X Y : Type*} {ℓ d : ℕ} (S : Fin d → X) (f : Fin d → Y)
    (ν : ProbabilityMeasure (Fin d)) (μ : ListPredictor X Y ℓ) (Wr : Finset (Fin d))
    (hWr : ∀ i ∈ Wr, f i ∉ (μ (S i)).1) :
    ∑ i ∈ Wr, (ν : Measure (Fin d)) {i} ≤ listError (mkLaw S f ν) μ := by
  letI : MeasurableSpace (X × Y) := ⊤
  have hmeas : Measurable (pt S f) := Measurable.of_discrete
  have h1 : listError (mkLaw S f ν) μ
      = (ν : Measure (Fin d)) {a | f a ∉ (μ (S a)).1} := by
    unfold listError
    show (Measure.map (pt S f) (ν : Measure (Fin d))) _ = _
    rw [Measure.map_apply hmeas (MeasurableSpace.measurableSet_top)]
    rfl
  rw [h1]
  have : ((Wr : Set (Fin d))) ⊆ {a | f a ∉ (μ (S a)).1} := fun i hi => hWr i hi
  calc ∑ i ∈ Wr, (ν : Measure (Fin d)) {i} = (ν : Measure (Fin d)) (Wr : Set (Fin d)) := by
        rw [sum_measure_singleton]
    _ ≤ _ := measure_mono this

theorem realizable_mkLaw {X Y : Type*} {d : ℕ} (H : Set (X → Y)) (S : Fin d → X) (f : Fin d → Y)
    (hf : f ∈ MulticlassDS.Compress.proj H S) (ν : ProbabilityMeasure (Fin d)) :
    Realizable (mkLaw S f ν) H := by
  letI : MeasurableSpace (X × Y) := ⊤
  have hmeas : Measurable (pt S f) := Measurable.of_discrete
  obtain ⟨h, hH, rfl⟩ := hf
  unfold Realizable bestError
  apply le_antisymm _ zero_le
  refine iInf_le_of_le ⟨h, hH⟩ ?_
  unfold hypothesisError
  show (Measure.map (pt S (h ∘ S)) (ν : Measure (Fin d))) _ ≤ _
  rw [Measure.map_apply hmeas (MeasurableSpace.measurableSet_top)]
  have : (pt S (h ∘ S)) ⁻¹' {z : X × Y | h z.1 ≠ z.2} = ∅ := by
    ext a; simp [pt]
  rw [this]; simp




open Classical in
theorem line_count {Y : Type*} {d ℓ : ℕ} (Fc : Finset (Fin d → Y)) (i : Fin d)
    (L : (Fin d → Y) → Finset Y) (hL : ∀ f ∈ Fc, (L f).card ≤ ℓ)
    (hinv : ∀ f ∈ Fc, ∀ g ∈ Fc, (∀ j, j ≠ i → g j = f j) → L g = L f)
    (hline : ∀ f ∈ Fc, 2 * ℓ ≤ (Fc.filter (fun g => ∀ j, j ≠ i → g j = f j)).card) :
    Fc.card ≤ 2 * (Fc.filter (fun f => f i ∉ L f)).card := by
  rcases Fc.eq_empty_or_nonempty with rfl | ⟨f₀, hf₀⟩
  · simp
  let y₀ : Y := f₀ i
  let π : (Fin d → Y) → (Fin d → Y) := fun f => Function.update f i y₀
  have hπ : ∀ f g : Fin d → Y, π f = π g ↔ ∀ j, j ≠ i → f j = g j := by
    intro f g
    constructor
    · intro h j hj
      have := congrFun h j
      simpa [π, Function.update_of_ne hj] using this
    · intro h
      funext j
      by_cases hj : j = i
      · subst hj; simp [π]
      · simp [π, Function.update_of_ne hj, h j hj]
  have hfib : ∀ b ∈ Fc.image π,
      (Fc.filter (fun f => π f = b)).card ≤ 2 * ((Fc.filter (fun f => π f = b)).filter
        (fun f => f i ∉ L f)).card := by
    intro b hb
    obtain ⟨f₁, hf₁, rfl⟩ := Finset.mem_image.mp hb
    set Fib := Fc.filter (fun f => π f = π f₁) with hFib
    have hFibeq : Fib = Fc.filter (fun g => ∀ j, j ≠ i → g j = f₁ j) := by
      ext g; simp only [hFib, Finset.mem_filter, hπ]
    have h2l : 2 * ℓ ≤ Fib.card := by rw [hFibeq]; exact hline f₁ hf₁
    have hconst : ∀ g ∈ Fib, L g = L f₁ := by
      intro g hg
      rw [hFibeq] at hg
      rcases Finset.mem_filter.mp hg with ⟨hg1, hg2⟩
      exact hinv f₁ hf₁ g hg1 hg2
    have hgood : (Fib.filter (fun f => ¬ f i ∉ L f)).card ≤ ℓ := by
      calc (Fib.filter (fun f => ¬ f i ∉ L f)).card
          ≤ (L f₁).card := by
            apply Finset.card_le_card_of_injOn (fun g => g i)
            · intro g hg
              rcases Finset.mem_filter.mp hg with ⟨hg1, hg2⟩
              have := hconst g hg1
              simp only [Finset.coe_filter] at *
              push Not at hg2
              rw [← this]; exact hg2
            · intro g hg g' hg' hgg
              rcases Finset.mem_filter.mp hg with ⟨hg1, _⟩
              rcases Finset.mem_filter.mp hg' with ⟨hg1', _⟩
              have hp : π g = π g' := by
                have a1 := (Finset.mem_filter.mp hg1).2
                have a2 := (Finset.mem_filter.mp hg1').2
                rw [a1, a2]
              funext j
              by_cases hj : j = i
              · subst hj; exact hgg
              · exact (hπ g g').mp hp j hj
        _ ≤ ℓ := hL f₁ hf₁
    have hsplit := Finset.card_filter_add_card_filter_not (s := Fib) (fun f => f i ∉ L f)
    omega
  calc Fc.card = ∑ b ∈ Fc.image π, (Fc.filter (fun f => π f = b)).card :=
        Finset.card_eq_sum_card_image π Fc
    _ ≤ ∑ b ∈ Fc.image π, 2 * ((Fc.filter (fun f => π f = b)).filter
        (fun f => f i ∉ L f)).card := Finset.sum_le_sum hfib
    _ = 2 * ∑ b ∈ Fc.image π, ((Fc.filter (fun f => f i ∉ L f)).filter (fun f => π f = b)).card := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.filter_comm]
    _ = 2 * (Fc.filter (fun f => f i ∉ L f)).card := by
        rw [← Finset.card_eq_sum_card_fiberwise (f := π) (t := Fc.image π)]
        intro f hf
        exact Finset.mem_image_of_mem π (Finset.mem_filter.mp hf).1


theorem count_core (Fn N B : ℕ) (θ : ℝ) (SW : ℕ) (num den : ℕ)
    (hSW : (N : ℝ) * Fn ≤ 2 * SW)
    (hB : (SW : ℝ) ≤ B * N + (Fn - B) * θ)
    (hc1 : θ < N) (hc2 : (num : ℝ) * (N - θ) ≤ den * (N / 2 - θ)) :
    num * Fn ≤ den * B := by
  have h1 : (Fn : ℝ) * (N / 2 - θ) ≤ B * (N - θ) := by nlinarith
  have h2 : (num : ℝ) * Fn * (N - θ) ≤ den * B * (N - θ) := by
    have : (0:ℝ) ≤ den := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h1 this, mul_le_mul_of_nonneg_right hc2 (Nat.cast_nonneg Fn)]
  have h3 : (num : ℝ) * Fn ≤ den * B := le_of_mul_le_mul_right h2 (by linarith)
  exact_mod_cast h3

open Classical in
theorem pointwise {X Y R : Type*} {ℓ d : ℕ} (S : Fin d → X) (Fc : Finset (Fin d → Y))
    (I : Finset (Fin d))
    (hline : ∀ i ∈ I, ∀ f ∈ Fc,
      2 * ℓ ≤ (Fc.filter (fun g => ∀ j, j ≠ i → g j = f j)).card)
    (ν : ProbabilityMeasure (Fin d)) (q : ℝ) (hq : 0 < q)
    (hνI : ∀ i ∈ I, (ν : Measure (Fin d)) {i} = ENNReal.ofReal q)
    (A : ListLearner X Y R ℓ) (ε δ : ℝ) (m : ℕ) (θ : ℝ) (t : ℕ) (hθt : θ = t) (hεθ : ε < ((t : ℝ) + 1) * q) (T num den : ℕ)
    (hc : ∀ N : ℕ, I.card ≤ N + T → θ < N ∧ (num : ℝ) * (N - θ) ≤ den * (N / 2 - θ))
    (s : Fin m → Fin d) (hs : (Finset.univ.filter (fun j => s j ∈ I)).card ≤ T) (r : R) :
    num * Fc.card ≤ den * (Fc.filter (fun f => 0 + ENNReal.ofReal ε <
      listError (mkLaw S f ν) (A ε δ m (fun j => pt S f (s j)) r))).card := by
  set U : Finset (Fin d) := I.filter (fun i => ∀ j, s j ≠ i) with hUdef
  set Lst : (Fin d → Y) → Fin d → Finset Y :=
    fun f i => (A ε δ m (fun j => pt S f (s j)) r (S i)).1 with hLst
  set Wr : (Fin d → Y) → Finset (Fin d) :=
    fun f => U.filter (fun i => f i ∉ Lst f i) with hWr
  have hU : I.card ≤ U.card + T := by
    have h1 : I ⊆ U ∪ (Finset.univ.filter (fun j => s j ∈ I)).image s := by
      intro i hi
      by_cases h : ∀ j, s j ≠ i
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, h⟩)
      · push Not at h
        obtain ⟨j, hj⟩ := h
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, ?_, hj⟩)
        simp [hj, hi]
    calc I.card ≤ (U ∪ (Finset.univ.filter (fun j => s j ∈ I)).image s).card :=
          Finset.card_le_card h1
      _ ≤ U.card + ((Finset.univ.filter (fun j => s j ∈ I)).image s).card :=
          Finset.card_union_le _ _
      _ ≤ U.card + T := by
          have := Finset.card_image_le (s := Finset.univ.filter (fun j => s j ∈ I)) (f := s)
          omega
  have hcnt : ∀ i ∈ U, Fc.card ≤ 2 * (Fc.filter (fun f => i ∈ Wr f)).card := by
    intro i hi
    have hiI : i ∈ I := (Finset.mem_filter.mp hi).1
    have hiU : ∀ j, s j ≠ i := (Finset.mem_filter.mp hi).2
    have := line_count (ℓ := ℓ) Fc i (fun f => Lst f i)
      (fun f _ => (A ε δ m (fun j => pt S f (s j)) r (S i)).2)
      (by
        intro f _ g _ hfg
        have : (fun j => pt S g (s j)) = (fun j => pt S f (s j)) := by
          funext j
          simp [pt, hfg (s j) (hiU j)]
        simp only [hLst, this])
      (hline i hiI)
    convert this using 3
    ext f
    simp [hWr, hi]
  set N := U.card with hN
  set SW := ∑ f ∈ Fc, (Wr f).card with hSW
  have hSW2 : (N : ℝ) * Fc.card ≤ 2 * SW := by
    have h1 : SW = ∑ i ∈ U, (Fc.filter (fun f => i ∈ Wr f)).card := by
      simp only [hSW, hWr, Finset.card_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro f _
      simp [hWr, hi]
    have h2 : N * Fc.card ≤ 2 * SW := by
      rw [h1, Finset.mul_sum]
      calc N * Fc.card = ∑ i ∈ U, Fc.card := by simp [hN, mul_comm]
        _ ≤ _ := Finset.sum_le_sum hcnt
    exact_mod_cast h2
  set B := (Fc.filter (fun f => θ < ((Wr f).card : ℝ))).card with hB
  have hSWB : (SW : ℝ) ≤ B * N + (Fc.card - B) * θ := by
    have h1 : (SW : ℝ) ≤ ∑ f ∈ Fc, (if θ < ((Wr f).card : ℝ) then (N : ℝ) else θ) := by
      rw [hSW, Nat.cast_sum]
      apply Finset.sum_le_sum
      intro f _
      split_ifs with h
      · have : (Wr f).card ≤ N := Finset.card_le_card (Finset.filter_subset _ _)
        exact_mod_cast this
      · exact not_lt.mp h
    refine h1.trans (le_of_eq ?_)
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have := Finset.card_filter_add_card_filter_not (s := Fc) (fun f => θ < ((Wr f).card : ℝ))
    have h3 : ((Fc.filter (fun f => ¬ θ < ((Wr f).card : ℝ))).card : ℝ) = Fc.card - B := by
      rw [hB]; rw [eq_sub_iff_add_eq]; exact_mod_cast (by omega : _ + _ = _)
    rw [h3]
  obtain ⟨hc1, hc2⟩ := hc N hU
  have hmain := count_core Fc.card N B θ SW num den hSW2 hSWB hc1 hc2
  refine hmain.trans ?_
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro f hf
  rcases Finset.mem_filter.mp hf with ⟨hfF, hθW⟩
  refine Finset.mem_filter.mpr ⟨hfF, ?_⟩
  have hsum := listError_ge (ℓ := ℓ) S f ν (A ε δ m (fun j => pt S f (s j)) r) (Wr f)
    (by
      intro i hi
      exact (Finset.mem_filter.mp hi).2)
  have hsum2 : ∑ i ∈ Wr f, (ν : Measure (Fin d)) {i} = ((Wr f).card : ℝ≥0∞) * ENNReal.ofReal q := by
    rw [Finset.sum_congr rfl (g := fun _ => ENNReal.ofReal q), Finset.sum_const, nsmul_eq_mul]
    intro i hi
    exact hνI i (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  rw [hsum2] at hsum
  refine lt_of_lt_of_le ?_ hsum
  have hcard : (t : ℝ) + 1 ≤ ((Wr f).card : ℝ) := by
    have h1 : t < (Wr f).card := by
      have : (t : ℝ) < ((Wr f).card : ℝ) := by rw [← hθt]; exact hθW
      exact_mod_cast this
    exact_mod_cast h1
  have hpos : 0 < ((Wr f).card : ℝ) * q := by
    have : (0:ℝ) < ((Wr f).card : ℝ) := by linarith [(Nat.cast_nonneg t : (0:ℝ) ≤ t)]
    positivity
  rw [zero_add, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_lt_ofReal_iff hpos]
  nlinarith

open Classical in
theorem core {X Y R : Type*} [MeasurableSpace R] {ℓ d : ℕ} (H : Set (X → Y)) (S : Fin d → X)
    (Fc : Finset (Fin d → Y)) (hFc : (↑Fc : Set (Fin d → Y)) ⊆ MulticlassDS.Compress.proj H S)
    (hne : Fc.Nonempty) (I : Finset (Fin d))
    (hline : ∀ i ∈ I, ∀ f ∈ Fc,
      2 * ℓ ≤ (Fc.filter (fun g => ∀ j, j ≠ i → g j = f j)).card)
    (ν : ProbabilityMeasure (Fin d)) (q : ℝ) (hq : 0 < q)
    (hνI : ∀ i ∈ I, (ν : Measure (Fin d)) {i} = ENNReal.ofReal q)
    (ρ : ProbabilityMeasure R)
    (A : ListLearner X Y R ℓ) (ε δ : ℝ) (m : ℕ) (θ : ℝ) (t : ℕ) (hθt : θ = t) (hεθ : ε < ((t : ℝ) + 1) * q)
    (T num den : ℕ)
    (hc : ∀ N : ℕ, I.card ≤ N + T → θ < N ∧ (num : ℝ) * (N - θ) ≤ den * (N / 2 - θ)) :
    ∃ f ∈ Fc, Realizable (mkLaw S f ν) H ∧
      (num : ℝ≥0∞) * (Measure.pi (fun _ : Fin m => (ν : Measure (Fin d))))
          {s | (Finset.univ.filter (fun j => s j ∈ I)).card ≤ T}
        ≤ den * failureProbability (mkLaw S f ν) ρ A ε δ m 0 := by
  classical
  set Gs : Set (Fin m → Fin d) := {s | (Finset.univ.filter (fun j => s j ∈ I)).card ≤ T} with hGs
  set P : Measure ((Fin m → Fin d) × R) :=
    (Measure.pi (fun _ : Fin m => (ν : Measure (Fin d)))).prod (ρ : Measure R) with hP
  haveI : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hGm : MeasurableSet (Gs ×ˢ (Set.univ : Set R)) :=
    (MeasurableSet.of_discrete).prod MeasurableSet.univ
  obtain ⟨f, hf, hfin⟩ := avg_exists P Fc hne
    (fun f => {x : (Fin m → Fin d) × R | 0 + ENNReal.ofReal ε <
      listError (mkLaw S f ν) (A ε δ m (fun j => pt S f (x.1 j)) x.2)})
    (Gs ×ˢ Set.univ) hGm num den
    (by
      intro x hx
      convert pointwise S Fc I hline ν q hq hνI A ε δ m θ t hθt hεθ T num den hc x.1 hx.1 x.2 using 3
      ext f; simp)
  refine ⟨f, hf, realizable_mkLaw H S f (hFc hf) ν, ?_⟩
  have h1 : P (Gs ×ˢ Set.univ) = Measure.pi (fun _ : Fin m => (ν : Measure (Fin d))) Gs := by
    rw [hP, Measure.prod_prod]; simp
  rw [h1] at hfin
  exact hfin.trans (by gcongr; exact failure_ge S f ν ρ A ε δ m)

theorem mkNu {d : ℕ} (i0 : Fin d) (I : Finset (Fin d)) (hI : I.Nonempty) (hi0 : i0 ∉ I)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ ν : ProbabilityMeasure (Fin d),
      (∀ i ∈ I, (ν : Measure (Fin d)) {i} = ENNReal.ofReal (p / I.card)) ∧
      (ν : Measure (Fin d)) (I : Set (Fin d)) = ENNReal.ofReal p := by
  classical
  have hk : (0 : ℝ) < I.card := by exact_mod_cast hI.card_pos
  set μ : Measure (Fin d) := ENNReal.ofReal (1 - p) • Measure.dirac i0 +
    ∑ i ∈ I, ENNReal.ofReal (p / I.card) • Measure.dirac i with hμ
  have happ : ∀ s : Set (Fin d), μ s = ENNReal.ofReal (1 - p) * s.indicator 1 i0 +
      ∑ i ∈ I, ENNReal.ofReal (p / I.card) * s.indicator 1 i := by
    intro s
    simp [hμ, Measure.add_apply, Measure.smul_apply, Measure.finsetSum_apply,
      Measure.dirac_apply' _ (MeasurableSet.of_discrete : MeasurableSet s)]
  have hI' : (∑ i ∈ I, ENNReal.ofReal (p / I.card)) = ENNReal.ofReal p := by
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1; field_simp
  have hIset : μ (I : Set (Fin d)) = ENNReal.ofReal p := by
    rw [happ]
    have : ∀ i ∈ I, (I : Set (Fin d)).indicator (1 : Fin d → ℝ≥0∞) i = 1 := by
      intro i hi; simp [hi]
    rw [Finset.sum_congr rfl (fun i hi => by rw [this i hi, mul_one])]
    simp [hi0, hI']
  have hprob : IsProbabilityMeasure μ := by
    constructor
    rw [happ]
    simp only [Set.indicator_univ, Pi.one_apply, mul_one]
    rw [hI', ← ENNReal.ofReal_add (by linarith) hp0.le]
    simp
  refine ⟨⟨μ, hprob⟩, ?_, hIset⟩
  intro i hi
  show μ {i} = _
  rw [happ]
  have hne : i0 ≠ i := fun h => hi0 (h ▸ hi)
  simp [Set.indicator_apply, hne, hi]

theorem markov_hits {d : ℕ} (ν : ProbabilityMeasure (Fin d)) (I : Finset (Fin d)) (m T : ℕ) :
    ((T : ℝ≥0∞) + 1) * (Measure.pi (fun _ : Fin m => (ν : Measure (Fin d))))
        {s | T < (Finset.univ.filter (fun j => s j ∈ I)).card}
      ≤ m * (ν : Measure (Fin d)) (I : Set (Fin d)) := by
  classical
  set Pw := Measure.pi (fun _ : Fin m => (ν : Measure (Fin d))) with hPw
  have hf : ∀ s : Fin m → Fin d, ((Finset.univ.filter (fun j => s j ∈ I)).card : ℝ≥0∞) =
      ∑ j : Fin m, ((fun s : Fin m → Fin d => s j) ⁻¹' (I : Set (Fin d))).indicator 1 s := by
    intro s
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : s j ∈ I <;> simp [h]
  have h1 := mul_meas_ge_le_lintegral (μ := Pw)
    (f := fun s : Fin m → Fin d => ((Finset.univ.filter (fun j => s j ∈ I)).card : ℝ≥0∞))
    (Measurable.of_discrete) ((T : ℝ≥0∞) + 1)
  have h2 : ∫⁻ s, ((Finset.univ.filter (fun j => s j ∈ I)).card : ℝ≥0∞) ∂Pw
      = m * (ν : Measure (Fin d)) (I : Set (Fin d)) := by
    simp_rw [hf]
    rw [lintegral_finsetSum _ (fun j _ => (measurable_one.indicator
      (MeasurableSet.of_discrete)))]
    have : ∀ j : Fin m, ∫⁻ s, ((fun s : Fin m → Fin d => s j) ⁻¹' (I : Set (Fin d))).indicator
        (1 : (Fin m → Fin d) → ℝ≥0∞) s ∂Pw = (ν : Measure (Fin d)) (I : Set (Fin d)) := by
      intro j
      rw [lintegral_indicator_one MeasurableSet.of_discrete]
      exact (measurePreserving_eval (fun _ : Fin m => (ν : Measure (Fin d))) j).measure_preimage
        (MeasurableSet.of_discrete).nullMeasurableSet
    simp [this]
  rw [h2] at h1
  refine le_trans ?_ h1
  gcongr
  intro h
  exact_mod_cast h

open Classical in
theorem witness_lines {Y : Type*} {d ℓ : ℕ} (F : Finset (Fin d → Y)) (hℓ : 1 ≤ ℓ)
    (hW : IsListDSWitness (2 * ℓ - 1) F) (i0 : Fin d) (f0 : Fin d → Y) (hf0 : f0 ∈ F) :
    (F.filter (fun f => f i0 = f0 i0)).Nonempty ∧
    ∀ i, i ≠ i0 → ∀ f ∈ F.filter (fun f => f i0 = f0 i0),
      2 * ℓ ≤ ((F.filter (fun f => f i0 = f0 i0)).filter
        (fun g => ∀ j, j ≠ i → g j = f j)).card := by
  unfold IsListDSWitness at hW
  obtain ⟨_, hnb⟩ := hW
  refine ⟨⟨f0, Finset.mem_filter.mpr ⟨hf0, rfl⟩⟩, ?_⟩
  intro i hi f hf
  have hfF := (Finset.mem_filter.mp hf).1
  have hfc := (Finset.mem_filter.mp hf).2
  have h1 := hnb f hfF i
  have hsub : insert f (F.filter (fun g => DirectionalNeighbor i f g)) ⊆
      (F.filter (fun f => f i0 = f0 i0)).filter (fun g => ∀ j, j ≠ i → g j = f j) := by
    intro g hg
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact Finset.mem_filter.mpr ⟨hf, fun _ _ => rfl⟩
    · obtain ⟨hgF, hgn⟩ := Finset.mem_filter.mp hg
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hgF, ?_⟩,
        fun j hj => (hgn.2 j hj).symm⟩
      rw [← hgn.2 i0 (Ne.symm hi)]; exact hfc
  have hnot : f ∉ F.filter (fun g => DirectionalNeighbor i f g) := by
    intro h
    exact (Finset.mem_filter.mp h).2.1 rfl
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at h2
  omega

theorem lt_of_mul_le_aux (a f : ℝ≥0∞) (num den : ℕ) (x δ : ℝ) (hx : 0 ≤ x) (hδ : 0 ≤ δ)
    (ha : ENNReal.ofReal x ≤ a) (h : (num : ℝ≥0∞) * a ≤ den * f)
    (hlt : (den : ℝ) * δ < num * x) : ENNReal.ofReal δ < f := by
  by_contra hle
  push Not at hle
  have h1 : (num : ℝ≥0∞) * ENNReal.ofReal x ≤ den * ENNReal.ofReal δ :=
    calc (num : ℝ≥0∞) * ENNReal.ofReal x ≤ num * a := by gcongr
      _ ≤ den * f := h
      _ ≤ den * ENNReal.ofReal δ := by gcongr
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  linarith

theorem ndiv_aux (k : ℕ) : k < 4 * (k / 4 + 1) := by omega

theorem real_b (ε δ : ℝ) (m : ℕ) (hε : 0 < ε) (hε₁ : ε < 1 / 16) (hδ : 0 < δ) (hδ₁ : δ < 1 / 16)
    (hm : (m : ℝ) ≤ Real.log (1 / δ) / (64 * ε)) :
    2 * δ < (1 - 2 * ε) ^ m := by
  set L := Real.log (1 / δ) with hL
  have hL1 : Real.log 16 < L := by
    rw [hL, one_div, Real.log_inv]
    have := Real.log_lt_log hδ hδ₁
    rw [one_div, Real.log_inv] at this
    linarith
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hp : 0 < 1 - 2 * ε := by linarith
  have hlb : -(2 * ε) / (1 - 2 * ε) ≤ Real.log (1 - 2 * ε) := by
    have := Real.one_sub_inv_le_log_of_pos hp
    have e : 1 - (1 - 2 * ε)⁻¹ = -(2 * ε) / (1 - 2 * ε) := by field_simp; ring
    linarith
  have h8 : -(2 * ε) / (1 - 2 * ε) ≥ -(8 / 7) * (2 * ε) := by
    have e : -(2 * ε) / (1 - 2 * ε) = -(2 * ε) * (1 - 2 * ε)⁻¹ := by ring
    rw [ge_iff_le, e]
    have hinv : (1 - 2 * ε)⁻¹ ≤ 8 / 7 := by
      rw [inv_le_comm₀ hp (by norm_num)]; linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hinv) hε.le]
  have hmL : (m : ℝ) * (2 * ε) ≤ L / 32 := by
    have := mul_le_mul_of_nonneg_right hm (by positivity : (0:ℝ) ≤ 2 * ε)
    calc (m : ℝ) * (2 * ε) ≤ L / (64 * ε) * (2 * ε) := this
      _ = L / 32 := by field_simp; ring
  have hlogpow : Real.log ((1 - 2 * ε) ^ m) ≥ -(L / 28) := by
    rw [Real.log_pow]
    have : (m : ℝ) * Real.log (1 - 2 * ε) ≥ (m : ℝ) * (-(8 / 7) * (2 * ε)) :=
      mul_le_mul_of_nonneg_left (hlb.trans' h8) (Nat.cast_nonneg _)
    nlinarith
  have hlt : Real.log (2 * δ) < Real.log ((1 - 2 * ε) ^ m) := by
    rw [Real.log_mul (by norm_num) hδ.ne']
    have : Real.log δ = -L := by rw [hL, one_div, Real.log_inv]; ring
    rw [this]
    linarith
  exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp hlt

end DSDensity1246.Dev.LBReal

namespace DSDensity1246.Main.Supplement

open DSDensity1246.Dev.LBReal

/-- Theorem 5, pp.20–23: both lower-bound terms, with the source's stronger
shattering assumption. The constant 1/128 combines the two proof obstructions. -/
theorem chk_realizable_list_lower_bound {X Y R : Type*}
    [MeasurableSpace R]
    (H : Set (X → Y)) (ℓ d : ℕ) (hℓ : 1 ≤ ℓ) (hd₂ : 2 ≤ d)
    (hd : listDSDim ℓ H = d)
    (hrich : ∃ S : Fin d → X, ListDSShatters (2 * ℓ - 1) H S)
    (ρ : ProbabilityMeasure R) (A : ListLearner X Y R ℓ)
    (ε δ : ℝ) (hε : 0 < ε) (hε₁ : ε < 1 / 16)
    (hδ : 0 < δ) (hδ₁ : δ < 1 / 16) (m : ℕ)
    (hm : (m : ℝ) ≤ ((d : ℝ) + Real.log (1 / δ)) / (128 * ε)) :
    ∃ D : DataLaw (X × Y), D.1 = ⊤ ∧ Realizable D H ∧
      ENNReal.ofReal δ < failureProbability D ρ A ε δ m 0 := by
  classical
  obtain ⟨S, F, hFsub, hW⟩ := hrich
  have hFne : F.Nonempty := hW.1
  obtain ⟨f0, hf0⟩ := hFne
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  have hi10 : i1 ≠ i0 := by
    intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  obtain ⟨hne, hline⟩ := witness_lines F hℓ hW i0 f0 hf0
  set Fc := F.filter (fun f => f i0 = f0 i0) with hFc
  have hFcsub : (↑Fc : Set (Fin d → Y)) ⊆ MulticlassDS.Compress.proj H S :=
    fun f hf => hFsub (Finset.mem_filter.mp hf).1
  have hL0 : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hδ]; linarith
  by_cases hcase : (d : ℝ) ≤ Real.log (1 / δ)
  · -- obstruction (b): the confidence term
    have hm' : (m : ℝ) ≤ Real.log (1 / δ) / (64 * ε) := by
      refine hm.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.log_pos (show (1:ℝ) < 1 / δ by rw [lt_div_iff₀ hδ]; linarith)]
    set I : Finset (Fin d) := {i1} with hI
    obtain ⟨ν, hν1, hν2⟩ := mkNu i0 I ⟨i1, by simp [hI]⟩ (by simp [hI, Ne.symm hi10])
      (2 * ε) (by linarith) (by linarith)
    have hcard : I.card = 1 := by simp [hI]
    rw [hcard] at hν1
    simp only [Nat.cast_one, div_one] at hν1
    obtain ⟨f, hfFc, hreal, hcore⟩ := core H S Fc hFcsub hne I
      (by
        intro i hiI f' hf'
        have : i ≠ i0 := by
          intro h; rw [hI, Finset.mem_singleton] at hiI; exact hi10 (hiI ▸ h)
        exact hline i this f' hf')
      ν (2 * ε) (by linarith) hν1 ρ A ε δ m 0 0 (by simp) (by nlinarith) 0 1 2
      (by
        intro N hN
        rw [hcard] at hN
        have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
        constructor <;> push_cast <;> nlinarith)
    refine ⟨mkLaw S f ν, rfl, hreal, ?_⟩
    have hG : {s : Fin m → Fin d | (Finset.univ.filter (fun j => s j ∈ I)).card ≤ 0} =
        Set.pi Set.univ (fun _ : Fin m => ((I : Set (Fin d))ᶜ)) := by
      ext s
      simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Set.mem_pi]
    rw [hG, Measure.pi_pi] at hcore
    have hcompl : (ν : Measure (Fin d)) ((I : Set (Fin d))ᶜ) = ENNReal.ofReal (1 - 2 * ε) := by
      rw [prob_compl_eq_one_sub (MeasurableSet.of_discrete), hν2, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub _ (by linarith)]
    simp only [hcompl, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcore
    rw [← ENNReal.ofReal_pow (by linarith)] at hcore
    refine lt_of_mul_le_aux _ _ 1 2 ((1 - 2 * ε) ^ m) δ (pow_nonneg (by linarith) _) hδ.le le_rfl
      (by simpa using hcore) ?_
    have := real_b ε δ m hε hε₁ hδ hδ₁ hm'
    push_cast; linarith
  · -- obstruction (a): the dimension term
    push Not at hcase
    have hm' : (m : ℝ) ≤ (d : ℝ) / (64 * ε) := by
      refine hm.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    set I : Finset (Fin d) := Finset.univ.erase i0 with hI
    have hcard : I.card = d - 1 := by simp [hI]
    have hIne : I.Nonempty := ⟨i1, by simp [hI, hi10]⟩
    obtain ⟨ν, hν1, hν2⟩ := mkNu i0 I hIne (by simp [hI]) (4 * ε) (by linarith) (by linarith)
    set t := I.card / 4 with ht
    have hk : 0 < I.card := hIne.card_pos
    have hkd : I.card + 1 = d := by omega
    have hkt : I.card < 4 * (t + 1) := ndiv_aux _
    have hkR : (0 : ℝ) < I.card := by exact_mod_cast hk
    obtain ⟨f, hfFc, hreal, hcore⟩ := core H S Fc hFcsub hne I
      (by
        intro i hiI f' hf'
        exact hline i (Finset.ne_of_mem_erase hiI) f' hf')
      ν (4 * ε / I.card) (by positivity) hν1 ρ A ε δ m t t rfl
      (by
        rw [mul_div_assoc', lt_div_iff₀ hkR]
        have : (I.card : ℝ) < 4 * ((t : ℝ) + 1) := by exact_mod_cast hkt
        nlinarith)
      t 1 6
      (by
        intro N hN
        have h4 : 4 * t ≤ I.card := by omega
        have h1 : t < N := by omega
        have h2 : 5 * t ≤ 2 * N := by omega
        have h1' : (t : ℝ) < N := by exact_mod_cast h1
        have h2' : 5 * (t : ℝ) ≤ 2 * N := by exact_mod_cast h2
        refine ⟨h1', ?_⟩
        push_cast
        linarith)
    refine ⟨mkLaw S f ν, rfl, hreal, ?_⟩
    have hmark := markov_hits ν I m t
    rw [hν2] at hmark
    set Pw := Measure.pi (fun _ : Fin m => (ν : Measure (Fin d))) with hPw
    have hy : Pw {s | t < (Finset.univ.filter (fun j => s j ∈ I)).card} ≤ ENNReal.ofReal (1 / 2) := by
      by_contra hcon
      push Not at hcon
      have h1 : ((t : ℝ≥0∞) + 1) * ENNReal.ofReal (1 / 2) <
          ((t : ℝ≥0∞) + 1) * Pw {s | t < (Finset.univ.filter (fun j => s j ∈ I)).card} :=
        (ENNReal.mul_lt_mul_iff_right (by simp) (by simp)).mpr hcon
      have h2 := lt_of_lt_of_le h1 hmark
      have e0 : ((t : ℝ≥0∞) + 1) = ENNReal.ofReal ((t : ℝ) + 1) := by
        rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one]; simp
      have e1 : ((t : ℝ≥0∞) + 1) * ENNReal.ofReal (1 / 2) = ENNReal.ofReal (((t : ℝ) + 1) * (1 / 2)) := by
        rw [e0, ← ENNReal.ofReal_mul (by positivity)]
      have e2 : (m : ℝ≥0∞) * ENNReal.ofReal (4 * ε) = ENNReal.ofReal ((m : ℝ) * (4 * ε)) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        simp
      rw [e1, e2, ENNReal.ofReal_lt_ofReal_iff'] at h2
      replace h2 := h2.1
      have hd4 : (d : ℝ) ≤ 4 * ((t : ℝ) + 1) := by
        have : d ≤ 4 * (t + 1) := by omega
        exact_mod_cast this
      have : (m : ℝ) * (64 * ε) ≤ d := by
        rw [le_div_iff₀ (by positivity)] at hm'; exact hm'
      nlinarith
    have hG : ENNReal.ofReal (1 / 2) ≤ Pw {s | (Finset.univ.filter (fun j => s j ∈ I)).card ≤ t} := by
      have hc : {s : Fin m → Fin d | (Finset.univ.filter (fun j => s j ∈ I)).card ≤ t} =
          {s | t < (Finset.univ.filter (fun j => s j ∈ I)).card}ᶜ := by
        ext s; simp
      rw [hc, prob_compl_eq_one_sub (MeasurableSet.of_discrete)]
      calc ENNReal.ofReal (1 / 2) = 1 - ENNReal.ofReal (1 / 2) := by
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
            norm_num
        _ ≤ _ := tsub_le_tsub_left hy _
    refine lt_of_mul_le_aux _ _ 1 6 (1 / 2) δ (by norm_num) hδ.le hG
      (by simpa using hcore) ?_
    push_cast; linarith

end DSDensity1246.Main.Supplement
end

theorem solution : type_of% @DSDensity1246.Main.Supplement.chk_realizable_list_lower_bound := @DSDensity1246.Main.Supplement.chk_realizable_list_lower_bound
