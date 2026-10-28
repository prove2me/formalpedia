-- Prove2me | solution 1 for AvramDividend.Classical.finite_future_increment_sigma_indep_past
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:52:17.994958+00:00
-- url     : https://prove2.me/submissions/22a29b83-4734-4972-b5b9-ab3cf59536b1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_all_finite_prefix_increment_cylinder_product

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Consecutive increments along a monotone grid starting at `s` are jointly independent of `𝓕 s`. -/
lemma S107FI.grid_indep
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : NNReal)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (hst : s ≤ t 0) (n : ℕ) :
    Indep (⨆ i ∈ (Finset.range n : Set ℕ), MeasurableSpace.comap
        (fun ω => X.X (t (i + 1)) ω - X.X (t i) ω) inferInstance) (𝓕 s) P := by
  classical
  haveI := X.isProbability
  have hmeasX : ∀ r, Measurable (X.X r) := fun r => (X.adapted r).mono (𝓕.le r) le_rfl
  have hΔ : ∀ i, Measurable fun ω => X.X (t (i + 1)) ω - X.X (t i) ω :=
    fun i => (hmeasX _).sub (hmeasX _)
  let Δ : ℕ → Ω → ℝ := fun i ω => X.X (t (i + 1)) ω - X.X (t i) ω
  refine IndepSets.indep (p1 := piiUnionInter
      (fun i => {S | MeasurableSet[MeasurableSpace.comap (Δ i) inferInstance] S})
      (Finset.range n : Set ℕ)) (p2 := {S | MeasurableSet[𝓕 s] S})
    (iSup₂_le fun i _ => (hΔ i).comap_le) (𝓕.le s)
    (isPiSystem_piiUnionInter _
      (fun i => @MeasurableSpace.isPiSystem_measurableSet Ω (MeasurableSpace.comap (Δ i) inferInstance)) _)
    (@MeasurableSpace.isPiSystem_measurableSet Ω (𝓕 s))
    (generateFrom_piiUnionInter_measurableSet _ _).symm
    (@MeasurableSpace.generateFrom_measurableSet Ω (𝓕 s)).symm ?_
  rw [IndepSets_iff]
  rintro C A ⟨J, hJ, f, hf, rfl⟩ hA
  have hB : ∀ i ∈ J, ∃ B : Set ℝ, MeasurableSet B ∧
      (fun ω => X.X (t (i + 1)) ω - X.X (t i) ω) ⁻¹' B = f i := fun i hi => hf i hi
  choose! B hBm hBf using hB
  let B' : ℕ → Set ℝ := fun i => if i ∈ J then B i else Set.univ
  have hB'm : ∀ i, MeasurableSet (B' i) := by
    intro i; by_cases h : i ∈ J
    · simp only [B', if_pos h]; exact hBm i h
    · simp only [B', if_neg h]; exact MeasurableSet.univ
  have hC : (⋂ i ∈ J, f i) = {ω | ∀ i : ℕ, i < n →
      X.X (t (i + 1)) ω - X.X (t i) ω ∈ B' i} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h i _
      by_cases hi : i ∈ J
      · simp only [B', if_pos hi]
        have := h i hi; rw [← hBf i hi] at this; exact this
      · simp only [B', if_neg hi]; trivial
    · intro h i hi
      have hin : i < n := by
        have := hJ hi; simpa using this
      have := h i hin
      simp only [B', if_pos hi] at this
      rw [← hBf i hi]; exact this
  rw [hC, Set.inter_comm]
  have h1 := chat04_all_finite_prefix_increment_cylinder_product X s A hA t ht hst B' hB'm n
  have h2 := chat04_all_finite_prefix_increment_cylinder_product X s Set.univ MeasurableSet.univ
    t ht hst B' hB'm n
  rw [Set.univ_inter, measure_univ, one_mul] at h2
  rw [h1, h2, mul_comm]

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : NNReal) :
    ∀ I : Finset NNReal,
      ProbabilityTheory.Indep
        (⨆ t : NNReal, ⨆ (_ : t ∈ I), MeasurableSpace.comap
          (fun ω : Ω => X.X (s + t) ω - X.X s ω) inferInstance)
        (𝓕 s) P := by
  classical
  intro I
  haveI := X.isProbability
  have hmeasX : ∀ r, Measurable (X.X r) := fun r => (X.adapted r).mono (𝓕.le r) le_rfl
  rcases I.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.notMem_empty, iSup_false, iSup_bot]
    exact indep_bot_left _
  set n := I.card with hn
  have hn0 : 0 < n := Finset.card_pos.2 hne
  let e := I.orderEmbOfFin hn.symm
  let t : ℕ → ℝ≥0 := fun i => if i = 0 then s else s + e ⟨min (i - 1) (n - 1), by omega⟩
  have ht : Monotone t := by
    intro i j hij
    simp only [t]
    by_cases hi : i = 0
    · simp only [hi, if_true]; split_ifs <;> simp
    · have hj : j ≠ 0 := by omega
      simp only [hi, hj, if_false]
      gcongr
      exact Fin.mk_le_mk.2 (by omega)
  have hst : s ≤ t 0 := by simp [t]
  have key := S107FI.grid_indep X s t ht hst n
  refine indep_of_indep_of_le_left key ?_
  refine iSup₂_le fun u hu => ?_
  -- u = e k for some k
  obtain ⟨k, hk⟩ : ∃ k : Fin n, e k = u := by
    have : u ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hu
    exact this
  refine Measurable.comap_le ?_
  have htel : (fun ω : Ω => X.X (s + u) ω - X.X s ω) =
      fun ω => ∑ i ∈ Finset.range (k.1 + 1), (X.X (t (i + 1)) ω - X.X (t i) ω) := by
    funext ω
    rw [Finset.sum_range_sub (fun i => X.X (t i) ω)]
    have h0 : t 0 = s := by simp [t]
    have hk1 : t (k.1 + 1) = s + u := by
      simp only [t, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      rw [← hk]; congr 2; ext; simp; omega
    rw [h0, hk1]
  rw [htel]
  refine Finset.measurable_sum _ fun i hi => ?_
  have hi' : i ∈ (Finset.range n : Set ℕ) := by
    simp only [Finset.coe_range, Set.mem_Iio]; simp at hi; omega
  exact (comap_measurable _).mono (le_iSup₂_of_le i hi' le_rfl) le_rfl
