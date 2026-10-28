-- Prove2me | solution 1 for DataDrivenNV.LRS.propEC1_derivatives_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:38:48.095057+00:00
-- url     : https://prove2.me/submissions/56950b73-0385-416f-8bbf-ec6683462925

import Definitions.Def_DataDrivenNV_LRS_Setting
import Theorems.Thm_DataDrivenNV_LRS_theoremEC1_bernstein
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace DataDrivenNV.LRS.QuantileProof

lemma measure_lowerSet_le (μ : Measure ℝ) {s : Set ℝ} (hs : IsLowerSet s)
    (p : ℝ≥0∞) (hp : ∀ a ∈ s, μ (Set.Iic a) ≤ p) : μ s ≤ p := by
  letI : Set.OrdConnected s := hs.ordConnected
  have hmono : Monotone (fun a : s => Set.Iic (a : ℝ)) :=
    fun a b hab => Set.Iic_subset_Iic.mpr hab
  have heq : (⋃ a : s, Set.Iic (a : ℝ)) = s := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
      exact hs ha a.property
    · intro hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by change x ≤ x; exact le_rfl⟩
  rw [← heq, hmono.measure_iUnion]
  exact iSup_le fun a => hp a a.property

lemma measure_upperSet_le (μ : Measure ℝ) {s : Set ℝ} (hs : IsUpperSet s)
    (p : ℝ≥0∞) (hp : ∀ a ∈ s, μ (Set.Ici a) ≤ p) : μ s ≤ p := by
  letI : Set.OrdConnected s := hs.ordConnected
  have hanti : Antitone (fun a : s => Set.Ici (a : ℝ)) :=
    fun a b hab => Set.Ici_subset_Ici.mpr hab
  have heq : (⋃ a : s, Set.Ici (a : ℝ)) = s := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
      exact hs ha a.property
    · intro hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by change x ≤ x; exact le_rfl⟩
  rw [← heq, hanti.measure_iUnion]
  exact iSup_le fun a => hp a a.property

lemma sample_quantile_counts {N : ℕ} (x : Fin N → ℝ) (hN : 0 < N)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    let Q := sInf {q : ℝ | β ≤ empCdf x q}
    β ≤ empCdf x Q ∧
      ((Finset.univ.filter fun i => x i < Q).card : ℝ) / N < β := by
  classical
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have hfin : (Finset.univ : Finset (Fin N)).Nonempty := by
    exact ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hextract (q : ℝ) (hq : β ≤ empCdf x q) :
      ∃ i : Fin N, x i ≤ q ∧ β ≤ empCdf x (x i) := by
    let t := Finset.univ.filter fun i => x i ≤ q
    have ht : t.Nonempty := by
      apply Finset.card_pos.mp
      have hpos : (0 : ℝ) < t.card := by
        have := lt_of_lt_of_le hβ0 hq
        dsimp [empCdf] at this
        exact (div_pos_iff_of_pos_right hnR).mp this
      exact_mod_cast hpos
    obtain ⟨i, hi, hmax⟩ := t.exists_max_image x ht
    refine ⟨i, (Finset.mem_filter.mp hi).2, hq.trans ?_⟩
    apply div_le_div_of_nonneg_right _ hnR.le
    exact_mod_cast Finset.card_le_card (show t ⊆ Finset.univ.filter (fun j => x j ≤ x i) from
      fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmax j hj⟩)
  let s := Finset.univ.filter fun i => β ≤ empCdf x (x i)
  have hs : s.Nonempty := by
    obtain ⟨i, hi, hmax⟩ := Finset.univ.exists_max_image x hfin
    refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
    have hf : Finset.univ.filter (fun j => x j ≤ x i) = Finset.univ :=
      Finset.filter_eq_self.mpr hmax
    rw [empCdf, hf, Finset.card_univ, Fintype.card_fin, div_self hnR.ne']
    exact hβ1
  obtain ⟨i, hi, hmin⟩ := s.exists_min_image x hs
  have hleast : IsLeast {q : ℝ | β ≤ empCdf x q} (x i) := by
    refine ⟨(Finset.mem_filter.mp hi).2, ?_⟩
    intro q hq
    obtain ⟨j, hjq, hj⟩ := hextract q hq
    exact (hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)).trans hjq
  dsimp only
  rw [hleast.csInf_eq]
  refine ⟨hleast.1, ?_⟩
  by_contra hnlt
  have hle : β ≤ ((Finset.univ.filter fun j => x j < x i).card : ℝ) / N :=
    le_of_not_gt hnlt
  let t := Finset.univ.filter fun j => x j < x i
  have ht : t.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < t.card :=
      (div_pos_iff_of_pos_right hnR).mp (lt_of_lt_of_le hβ0 hle)
    exact_mod_cast hpos
  obtain ⟨j, hj, hmax⟩ := t.exists_max_image x ht
  have hjcdf : β ≤ empCdf x (x j) := by
    refine hle.trans ?_
    apply div_le_div_of_nonneg_right _ hnR.le
    exact_mod_cast Finset.card_le_card (show t ⊆ Finset.univ.filter (fun k => x k ≤ x j) from
      fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmax k hk⟩)
  exact (not_le_of_gt (Finset.mem_filter.mp hj).2)
    (hleast.2 hjcdf)

lemma sum_indicator_eq_card {N : ℕ} (s : Set ℝ) (x : Fin N → ℝ) :
    ∑ i, s.indicator (fun _ => (1 : ℝ)) (x i) =
      ((Finset.univ.filter fun i => x i ∈ s).card : ℝ) := by
  classical
  simp [Set.indicator, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]

lemma lowerSet_sample_count {N : ℕ} (x : Fin N → ℝ) (hN : 0 < N)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (s : Set ℝ) (hs : IsLowerSet s)
    (hq : sInf {q : ℝ | β ≤ empCdf x q} ∈ s) :
    β ≤ (1 / (N : ℝ)) * ∑ i, s.indicator (fun _ => (1 : ℝ)) (x i) := by
  classical
  have hcount := (sample_quantile_counts x hN β hβ0 hβ1).1
  rw [sum_indicator_eq_card, one_div, ← div_eq_inv_mul]
  refine hcount.trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N))
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hs (Finset.mem_filter.mp hi).2 hq⟩

lemma upperSet_sample_count {N : ℕ} (x : Fin N → ℝ) (hN : 0 < N)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (s : Set ℝ) (hs : IsUpperSet s)
    (hq : sInf {q : ℝ | β ≤ empCdf x q} ∈ s) :
    1 - β ≤ (1 / (N : ℝ)) * ∑ i, s.indicator (fun _ => (1 : ℝ)) (x i) := by
  classical
  let Q := sInf {q : ℝ | β ≤ empCdf x q}
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlt := (sample_quantile_counts x hN β hβ0 hβ1).2
  rw [sum_indicator_eq_card, one_div, ← div_eq_inv_mul]
  have hcards : (Finset.univ.filter (fun i => x i < Q)).card +
      (Finset.univ.filter (fun i => Q ≤ x i)).card = N := by
    simpa only [not_lt, Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun i => x i < Q)
  have hcR : ((Finset.univ.filter (fun i => x i < Q)).card : ℝ) +
      ((Finset.univ.filter (fun i => Q ≤ x i)).card : ℝ) = N := by exact_mod_cast hcards
  have hge : 1 - β ≤ ((Finset.univ.filter (fun i => Q ≤ x i)).card : ℝ) / N := by
    rw [le_div_iff₀ hnR]
    have := (div_lt_iff₀ hnR).mp hlt
    nlinarith
  refine hge.trans (div_le_div_of_nonneg_right ?_ hnR.le)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hs (Finset.mem_filter.mp hi).2 hq⟩

lemma indicator_bernstein (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : Set ℝ) (hs : MeasurableSet s) (N : ℕ) (hN : 1 ≤ N)
    (t : ℝ) (ht : 0 < t) :
    (Measure.pi fun _ : Fin N => μ)
      {x | t ≤ (1 / (N : ℝ)) * ∑ i, s.indicator (fun _ => (1 : ℝ)) (x i) - μ.real s} ≤
      ENNReal.ofReal (Real.exp (-((N : ℝ) * t ^ 2) /
        (2 * (μ.real s * (1 - μ.real s)) + 2 * t / 3))) := by
  classical
  let f : ℝ → ℝ := s.indicator fun _ => 1
  let p := μ.real s
  have hf : Measurable f := measurable_const.indicator hs
  have hfi : Integrable f μ := (integrable_const 1).indicator hs
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  have hfb : ∀ x, 0 ≤ f x ∧ f x ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [f, hx]
  have hfm : ∫ x, f x ∂μ = p := by
    dsimp [f, p]
    simp only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one]
  let ν := μ.map f
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hm : ∫ x, x ∂ν = p := by
    rw [show ν = μ.map f from rfl, integral_map (μ := μ) (f := fun x : ℝ => x)
      hf.aemeasurable measurable_id.aestronglyMeasurable]
    exact hfm
  have hb : ∀ᵐ x ∂ν, |x| ≤ 1 := by
    apply (ae_map_iff hf.aemeasurable (by measurability)).mpr
    filter_upwards with x
    rw [abs_of_nonneg (hfb x).1]
    exact (hfb x).2
  have hc : ∀ᵐ x ∂ν, |x - ∫ y, y ∂ν| ≤ 1 := by
    rw [hm]
    apply (ae_map_iff hf.aemeasurable (by measurability)).mpr
    filter_upwards with x
    rw [abs_le]
    constructor <;> linarith [(hfb x).1, (hfb x).2]
  have hv : ∫ x, (x - ∫ y, y ∂ν) ^ 2 ∂ν = (Real.sqrt (p * (1 - p))) ^ 2 := by
    rw [hm, show ν = μ.map f from rfl,
      integral_map hf.aemeasurable (by fun_prop), Real.sq_sqrt (by positivity)]
    have heq : (fun x => (f x - p) ^ 2) = (fun x => (1 - 2 * p) * f x + p ^ 2) := by
      funext x
      by_cases hx : x ∈ s <;> simp only [f, Set.indicator, hx, if_true, if_false]
      all_goals ring
    rw [heq, integral_add (hfi.const_mul _) (integrable_const _), integral_const_mul, hfm]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  have hB := theoremEC1_bernstein ν N hN 1 (Real.sqrt (p * (1 - p))) hb hc hv t ht
  rw [hm, Real.sq_sqrt (by positivity)] at hB
  change (Measure.pi fun _ : Fin N => μ.map f) _ ≤ _ at hB
  rw [← Measure.pi_map_pi (fun _ : Fin N => hf.aemeasurable),
    Measure.map_apply (by fun_prop) (by measurability)] at hB
  simpa only [Set.preimage_setOf_eq, mul_one] using hB

lemma bernstein_ratio (p β α : ℝ) (hp0 : 0 ≤ p) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα : 0 < α) (hgap : p ≤ β - α) :
    3 * α ^ 2 / (6 * β * (1 - β) + 8 * α) ≤
      (β - p) ^ 2 / (2 * (p * (1 - p)) + 2 * (β - p) / 3) := by
  have hp1 : p < 1 := by linarith
  have ht : 0 < β - p := by linarith
  have hta : α ≤ β - p := by linarith
  have hB : 0 ≤ β * (1 - β) := mul_nonneg hβ0.le (by linarith)
  have hpv : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  have hden : 0 < 2 * (p * (1 - p)) + 2 * (β - p) / 3 := by positivity
  have hden' : 0 < 6 * β * (1 - β) + 8 * α := by positivity
  rw [div_le_div_iff₀ hden' hden]
  have hv : p * (1 - p) ≤ β * (1 - β) + (β - p) := by
    nlinarith [sq_nonneg (β - p), mul_nonneg (show 0 ≤ 1 - β by linarith) ht.le]
  have hsq : 0 ≤ (β - p) ^ 2 - α ^ 2 := by nlinarith
  have hterm1 := mul_nonneg hB hsq
  have hterm2 := mul_nonneg (mul_nonneg hα.le ht.le) (sub_nonneg.mpr hta)
  have hterm3 := mul_le_mul_of_nonneg_left hv (sq_nonneg α)
  nlinarith

lemma indicator_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : Set ℝ) (hs : MeasurableSet s) (N : ℕ) (hN : 1 ≤ N)
    (β α : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hα : 0 < α)
    (hgap : μ.real s ≤ β - α) :
    (Measure.pi fun _ : Fin N => μ)
      {x | β ≤ (1 / (N : ℝ)) * ∑ i, s.indicator (fun _ => (1 : ℝ)) (x i)} ≤
      ENNReal.ofReal (Real.exp (-(3 * (N : ℝ) * α ^ 2) /
        (6 * β * (1 - β) + 8 * α))) := by
  have hp0 : 0 ≤ μ.real s := ENNReal.toReal_nonneg
  have ht : 0 < β - μ.real s := by linarith
  have hB := indicator_bernstein μ s hs N hN (β - μ.real s) ht
  have hevent : {x : Fin N → ℝ | β ≤ (1 / (N : ℝ)) *
      ∑ i, s.indicator (fun _ => (1 : ℝ)) (x i)} =
      {x | β - μ.real s ≤ (1 / (N : ℝ)) *
        ∑ i, s.indicator (fun _ => (1 : ℝ)) (x i) - μ.real s} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hx <;> linarith
  rw [hevent]
  refine hB.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  have hr := mul_le_mul_of_nonneg_left
    (bernstein_ratio (μ.real s) β α hp0 hβ0 hβ1 hα hgap) (Nat.cast_nonneg N)
  calc
    -((N : ℝ) * (β - μ.real s) ^ 2) /
        (2 * (μ.real s * (1 - μ.real s)) + 2 * (β - μ.real s) / 3) =
        -((N : ℝ) * ((β - μ.real s) ^ 2 /
          (2 * (μ.real s * (1 - μ.real s)) + 2 * (β - μ.real s) / 3))) := by ring
    _ ≤ -((N : ℝ) * (3 * α ^ 2 / (6 * β * (1 - β) + 8 * α))) := neg_le_neg hr
    _ = -(3 * (N : ℝ) * α ^ 2) / (6 * β * (1 - β) + 8 * α) := by ring

lemma lower_quantile_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) (β α : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hα : 0 < α) :
    (Measure.pi fun _ : Fin N => μ)
      {x | cdf μ (sInf {q : ℝ | β ≤ empCdf x q}) < β - α} ≤
      ENNReal.ofReal (Real.exp (-(3 * (N : ℝ) * α ^ 2) /
        (6 * β * (1 - β) + 8 * α))) := by
  let s : Set ℝ := {q | cdf μ q < β - α}
  have hs : IsLowerSet s := by
    intro a b hab hb
    exact lt_of_le_of_lt (monotone_cdf μ hab) hb
  by_cases hba : 0 ≤ β - α
  · have hmass : μ s ≤ ENNReal.ofReal (β - α) := by
      apply measure_lowerSet_le μ hs
      intro a ha
      rw [← ofReal_cdf]
      exact ENNReal.ofReal_le_ofReal ha.le
    have hgap : μ.real s ≤ β - α := ENNReal.toReal_le_of_le_ofReal hba hmass
    refine (measure_mono ?_).trans
      (indicator_tail μ s hs.ordConnected.measurableSet N hN β α hβ0 hβ1 hα hgap)
    intro x hx
    exact lowerSet_sample_count x (by omega) β hβ0 hβ1.le s hs hx
  · have he : {x : Fin N → ℝ | cdf μ (sInf {q : ℝ | β ≤ empCdf x q}) < β - α} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hba (cdf_nonneg μ _ |>.trans hx.le)
    rw [he, measure_empty]
    exact bot_le

lemma upper_quantile_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) (β α : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hα : 0 < α) :
    (Measure.pi fun _ : Fin N => μ)
      {x | μ.real (Set.Ici (sInf {q : ℝ | β ≤ empCdf x q})) < 1 - β - α} ≤
      ENNReal.ofReal (Real.exp (-(3 * (N : ℝ) * α ^ 2) /
        (6 * β * (1 - β) + 8 * α))) := by
  let s : Set ℝ := {q | μ.real (Set.Ici q) < 1 - β - α}
  have hs : IsUpperSet s := by
    intro a b hab ha
    exact lt_of_le_of_lt (measureReal_mono (Set.Ici_subset_Ici.mpr hab)) ha
  by_cases hba : 0 ≤ 1 - β - α
  · have hmass : μ s ≤ ENNReal.ofReal (1 - β - α) := by
      apply measure_upperSet_le μ hs
      intro a ha
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hba).mpr ha.le
    have hgap : μ.real s ≤ (1 - β) - α := ENNReal.toReal_le_of_le_ofReal hba hmass
    have hB := indicator_tail μ s hs.ordConnected.measurableSet N hN (1 - β) α
      (by linarith) (by linarith) hα hgap
    have hden : 6 * (1 - β) * (1 - (1 - β)) + 8 * α =
        6 * β * (1 - β) + 8 * α := by ring
    rw [hden] at hB
    refine (measure_mono ?_).trans hB
    intro x hx
    exact upperSet_sample_count x (by omega) β hβ0 hβ1.le s hs hx
  · have he : {x : Fin N → ℝ |
        μ.real (Set.Ici (sInf {q : ℝ | β ≤ empCdf x q})) < 1 - β - α} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hba (ENNReal.toReal_nonneg.trans hx.le)
    rw [he, measure_empty]
    exact bot_le

end DataDrivenNV.LRS.QuantileProof

open DataDrivenNV.LRS DataDrivenNV.LRS.QuantileProof

theorem solution (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (N : ℕ) (hN : 1 ≤ N) (γ : ℝ) (hγ : 0 < γ) :
    (Measure.pi fun _ : Fin N => μ)
        {x : Fin N → ℝ | ¬ (dMinus μ b h (saaQuantile b h x) ≤ γ ∧
          -γ ≤ dPlus μ b h (saaQuantile b h x))} ≤
      ENNReal.ofReal
        (2 * Real.exp (-(3 * (N : ℝ) * γ ^ 2) / (6 * b * h + 8 * γ * (b + h)))) := by
  let β := b / (b + h)
  let α := γ / (b + h)
  have hbh : 0 < b + h := add_pos hb hh
  have hβ0 : 0 < β := div_pos hb hbh
  have hβ1 : β < 1 := (div_lt_one hbh).mpr (by linarith)
  have hα : 0 < α := div_pos hγ hbh
  let A : Set (Fin N → ℝ) := {x | cdf μ (saaQuantile b h x) < β - α}
  let B : Set (Fin N → ℝ) := {x | μ.real (Set.Ici (saaQuantile b h x)) < 1 - β - α}
  have hsub : {x : Fin N → ℝ | ¬ (dMinus μ b h (saaQuantile b h x) ≤ γ ∧
      -γ ≤ dPlus μ b h (saaQuantile b h x))} ⊆ A ∪ B := by
    intro x hx
    by_cases hm : dMinus μ b h (saaQuantile b h x) ≤ γ
    · left
      have hp : dPlus μ b h (saaQuantile b h x) < -γ := by
        exact lt_of_not_ge fun hp => hx ⟨hm, hp⟩
      change cdf μ (saaQuantile b h x) < β - α
      dsimp [β, α]
      rw [← sub_div, lt_div_iff₀ hbh]
      dsimp [dPlus] at hp
      nlinarith
    · right
      have hm' : γ < dMinus μ b h (saaQuantile b h x) := lt_of_not_ge hm
      have hic : μ.real (Set.Ici (saaQuantile b h x)) =
          1 - (μ (Set.Iio (saaQuantile b h x))).toReal := by
        simpa only [Set.compl_Iio, measureReal_def] using
          (probReal_compl_eq_one_sub (μ := μ) (measurableSet_Iio (a := saaQuantile b h x)))
      have hth : 1 - β - α = (h - γ) / (b + h) := by
        dsimp [β, α]
        field_simp
        <;> ring
      change μ.real (Set.Ici (saaQuantile b h x)) < 1 - β - α
      rw [hic, hth, lt_div_iff₀ hbh]
      dsimp [dMinus] at hm'
      nlinarith
  have hA := lower_quantile_tail μ N hN β α hβ0 hβ1 hα
  have hB := upper_quantile_tail μ N hN β α hβ0 hβ1 hα
  change (Measure.pi fun _ : Fin N => μ) A ≤ _ at hA
  change (Measure.pi fun _ : Fin N => μ) B ≤ _ at hB
  have hden : 0 < 6 * β * (1 - β) + 8 * α := by positivity
  have hden' : 0 < 6 * b * h + 8 * γ * (b + h) := by positivity
  have hexp : -(3 * (N : ℝ) * α ^ 2) / (6 * β * (1 - β) + 8 * α) =
      -(3 * (N : ℝ) * γ ^ 2) / (6 * b * h + 8 * γ * (b + h)) := by
    apply (div_eq_div_iff hden.ne' hden'.ne').mpr
    dsimp [α, β]
    field_simp
    <;> ring
  rw [hexp] at hA hB
  refine (measure_mono hsub).trans ((measure_union_le A B).trans ((add_le_add hA hB).trans ?_))
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  linarith
