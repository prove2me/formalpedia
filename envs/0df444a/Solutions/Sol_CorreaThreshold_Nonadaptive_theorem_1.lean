-- Prove2me | solution 1 for CorreaThreshold.Nonadaptive.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-24T08:01:56.361987+00:00
-- url     : https://prove2.me/submissions/3fe1d0a5-e884-4f2e-9cee-328c25e1df60

import Definitions.Def_CorreaThreshold_Nonadaptive_Setting
set_option autoImplicit false


open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

namespace CTProof

lemma real_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ)
    (_hr : 0 < r) (hr1 : r < 1) (hzero : μ.real (Iic 0) < r) :
    ∃ a : ℝ, 0 < a ∧ μ.real (Iio a) ≤ r ∧ r ≤ μ.real (Iic a) := by
  let F := cdf μ
  let S : Set ℝ := {x | r ≤ F x}
  have hF0 : F 0 < r := by simpa [F, cdf_eq_real] using hzero
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds hr1)).exists
    exact ⟨x, le_of_lt hx⟩
  have hb : BddBelow S := by
    refine ⟨0, fun x hx => ?_⟩
    by_contra hn
    have := F.mono (le_of_lt (lt_of_not_ge hn))
    exact (not_lt_of_ge (le_trans hx this)) hF0
  let a := sInf S
  have haF : r ≤ F a := by
    rw [← F.iInf_Ioi_eq a]
    apply le_ciInf
    intro x
    obtain ⟨y, hy, hyx⟩ := (csInf_lt_iff hb hS).mp x.property
    exact le_trans hy (F.mono hyx.le)
  have ha : 0 < a := by
    by_contra hn
    have := F.mono (le_of_not_gt hn)
    exact (not_lt_of_ge (le_trans haF this)) hF0
  have hleft : Function.leftLim F a ≤ r := by
    rw [F.mono.leftLim_eq_sSup]
    apply csSup_le
    · exact ⟨F (a-1), a-1, (show a-1<a by linarith), rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      by_contra hn
      have hxS : x ∈ S := le_of_lt (lt_of_not_ge hn)
      have : a ≤ x := csInf_le hb hxS
      exact (not_lt_of_ge this) hx
  have hleft0 : 0 ≤ Function.leftLim F a :=
    le_trans (cdf_nonneg μ 0) (F.mono.le_leftLim ha)
  have hIio : μ.real (Iio a) = Function.leftLim F a := by
    rw [measureReal_def, ← measure_cdf μ, StieltjesFunction.measure_Iio _ (tendsto_cdf_atBot μ)]
    change (ENNReal.ofReal (Function.leftLim F a - 0)).toReal = _
    rw [sub_zero, ENNReal.toReal_ofReal hleft0]
  refine ⟨a, ha, hIio ▸ hleft, ?_⟩
  simpa [F, cdf_eq_real] using haF

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} [NeZero n]

lemma measurable_max (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) :
    Measurable (SamuelCahnProphet.Median.maxX X) := by
  have he : SamuelCahnProphet.Median.maxX X = Finset.univ.sup' Finset.univ_nonempty X := by
    funext ω
    exact (Finset.sup'_apply Finset.univ_nonempty X ω).symm
  rw [he]
  exact Finset.measurable_sup' Finset.univ_nonempty (fun i _ => hX i)

omit [MeasurableSpace Ω] in
lemma le_max (X : Fin n → Ω → ℝ) (i : Fin n) (ω : Ω) :
    X i ω ≤ SamuelCahnProphet.Median.maxX X ω :=
  Finset.le_sup' (fun j => X j ω) (Finset.mem_univ i)

omit [MeasurableSpace Ω] in
lemma max_le_sum (X : Fin n → Ω → ℝ) (hn : ∀ i ω, 0 ≤ X i ω) (ω : Ω) :
    SamuelCahnProphet.Median.maxX X ω ≤ ∑ i, X i ω := by
  apply Finset.sup'_le
  intro i _
  exact Finset.single_le_sum (fun j _ => hn j ω) (Finset.mem_univ i)

omit [MeasurableSpace Ω] in
lemma max_nonneg (X : Fin n → Ω → ℝ) (hn : ∀ i ω, 0 ≤ X i ω) (ω : Ω) :
    0 ≤ SamuelCahnProphet.Median.maxX X ω := le_trans (hn 0 ω) (le_max X 0 ω)

lemma max_quantile (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY : Measurable Y) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hzero : P.real {ω | Y ω ≤ 0} < r) :
    ∃ a : ℝ, 0 < a ∧ P.real {ω | Y ω < a} ≤ r ∧ r ≤ P.real {ω | Y ω ≤ a} := by
  have : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hm (a : ℝ) : (P.map Y).real (Iic a) = P.real {ω | Y ω ≤ a} := by
    rw [measureReal_def, Measure.map_apply hY measurableSet_Iic]
    rfl
  have hl (a : ℝ) : (P.map Y).real (Iio a) = P.real {ω | Y ω < a} := by
    rw [measureReal_def, Measure.map_apply hY measurableSet_Iio]
    rfl
  obtain ⟨a, ha, hla, hra⟩ := real_quantile (P.map Y) r hr hr1 (by simpa [hm] using hzero)
  exact ⟨a, ha, (hl a) ▸ hla, (hm a) ▸ hra⟩

omit [NeZero n] in
lemma measurable_ratio (τ : Fin n → ENNReal) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) : Measurable (CorreaThreshold.Nonadaptive.ratio τ X) := by
  classical
  unfold CorreaThreshold.Nonadaptive.ratio CorreaThreshold.Nonadaptive.accepted
  simp_rw [Finset.sum_filter, Finset.natCast_card_filter]
  apply Measurable.div
  · apply Finset.measurable_sum
    intro i _
    exact (hX i).ite (measurableSet_lt measurable_const (hX i).ennreal_ofReal) measurable_const
  · apply Finset.measurable_sum
    intro i _
    exact measurable_const.ite (measurableSet_lt measurable_const (hX i).ennreal_ofReal) measurable_const

omit [MeasurableSpace Ω] [NeZero n] in
lemma ratio_nonneg (τ : Fin n → ENNReal) (X : Fin n → Ω → ℝ)
    (hn : ∀ i ω, 0 ≤ X i ω) (ω : Ω) : 0 ≤ CorreaThreshold.Nonadaptive.ratio τ X ω := by
  unfold CorreaThreshold.Nonadaptive.ratio
  exact div_nonneg (Finset.sum_nonneg (fun i _ => hn i ω)) (Nat.cast_nonneg _)

omit [MeasurableSpace Ω] [NeZero n] in
lemma ratio_le_sum (τ : Fin n → ENNReal) (X : Fin n → Ω → ℝ)
    (hn : ∀ i ω, 0 ≤ X i ω) (ω : Ω) :
    CorreaThreshold.Nonadaptive.ratio τ X ω ≤ ∑ i, X i ω := by
  classical
  let A := CorreaThreshold.Nonadaptive.accepted τ X ω
  change (∑ i ∈ A, X i ω) / (A.card : ℝ) ≤ _
  by_cases he : A = ∅
  · simp [he, Finset.sum_nonneg (fun i _ => hn i ω)]
  have hcard : (1 : ℝ) ≤ A.card := by exact_mod_cast Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr he)
  calc
    (∑ i ∈ A, X i ω) / (A.card : ℝ) ≤ ∑ i ∈ A, X i ω :=
      div_le_self (Finset.sum_nonneg (fun i _ => hn i ω)) hcard
    _ ≤ ∑ i, X i ω := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun i _ _ => hn i ω)

omit [NeZero n] in
lemma integrable_ratio (P : Measure Ω) (τ : Fin n → ENNReal) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hn : ∀ i ω, 0 ≤ X i ω)
    (hi : ∀ i, Integrable (X i) P) : Integrable (CorreaThreshold.Nonadaptive.ratio τ X) P := by
  apply (integrable_finsetSum _ (fun i _ => hi i)).mono' (measurable_ratio τ X hX).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (ratio_nonneg τ X hn ω)]
  exact ratio_le_sum τ X hn ω

lemma max_le_product (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hind : iIndepFun X P) (a : ℝ) :
    P.real {ω | SamuelCahnProphet.Median.maxX X ω ≤ a} = ∏ i, P.real {ω | X i ω ≤ a} := by
  have he : {ω | SamuelCahnProphet.Median.maxX X ω ≤ a} =
      ⋂ i ∈ (Finset.univ : Finset (Fin n)), X i ⁻¹' Iic a := by
    ext ω
    simp [SamuelCahnProphet.Median.maxX, Finset.sup'_le_iff]
  have hh := hind.measure_inter_preimage_eq_mul Finset.univ (sets := fun _ => Iic a)
    (fun _ _ => measurableSet_Iic)
  rw [measureReal_def, he, hh, ENNReal.toReal_prod]
  rfl

lemma max_lt_product (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hind : iIndepFun X P) (a : ℝ) :
    P.real {ω | SamuelCahnProphet.Median.maxX X ω < a} = ∏ i, P.real {ω | X i ω < a} := by
  have he : {ω | SamuelCahnProphet.Median.maxX X ω < a} =
      ⋂ i ∈ (Finset.univ : Finset (Fin n)), X i ⁻¹' Iio a := by
    ext ω
    simp [SamuelCahnProphet.Median.maxX, Finset.sup'_lt_iff]
  have hh := hind.measure_inter_preimage_eq_mul Finset.univ (sets := fun _ => Iio a)
    (fun _ _ => measurableSet_Iio)
  rw [measureReal_def, he, hh, ENNReal.toReal_prod]
  rfl

lemma tail_partition (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY : Measurable Y) (a : ℝ) :
    (1 - P.real {ω | a < Y ω} = P.real {ω | Y ω ≤ a}) ∧
    (1 - (P.real {ω | a < Y ω} + P.real {ω | Y ω = a}) = P.real {ω | Y ω < a}) := by
  have hg := measureReal_add_measureReal_compl (μ := P) (s := {ω | a < Y ω}) (measurableSet_lt measurable_const hY)
  have hge := measureReal_add_measureReal_compl (μ := P) (s := {ω | a ≤ Y ω}) (measurableSet_le measurable_const hY)
  have hu : {ω | a ≤ Y ω} = {ω | a < Y ω} ∪ {ω | Y ω = a} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact h.le
      · exact h.ge
  have hd : Disjoint {ω | a < Y ω} {ω | Y ω = a} := by
    rw [Set.disjoint_left]
    intro ω h h'
    exact (ne_of_lt h) h'.symm
  have hsum := measureReal_union (μ := P) hd (measurableSet_eq_fun hY measurable_const)
  rw [← hu] at hsum
  simp only [compl_ofPred, not_lt, not_le] at hg hge
  have hun : P.real univ = 1 := by simp
  rw [hun] at hg hge
  constructor <;> linarith

lemma tie_probability (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) (a r : ℝ)
    (hlo : P.real {ω | SamuelCahnProphet.Median.maxX X ω < a} ≤ r)
    (hhi : r ≤ P.real {ω | SamuelCahnProphet.Median.maxX X ω ≤ a}) :
    ∃ s ∈ Icc (0 : ℝ) 1,
      (∏ i, (1 - (P.real {ω | a < X i ω} + s * P.real {ω | X i ω = a}))) = r := by
  let F : ℝ → ℝ := fun s => ∏ i, (1 - (P.real {ω | a < X i ω} + s * P.real {ω | X i ω = a}))
  have hc : ContinuousOn F (Icc 0 1) := by fun_prop
  have h0 : F 0 = P.real {ω | SamuelCahnProphet.Median.maxX X ω ≤ a} := by
    rw [max_le_product P X hind]
    simp only [F, zero_mul, add_zero]
    apply Finset.prod_congr rfl
    intro i _
    exact (tail_partition P (X i) (hX i) a).1
  have h1 : F 1 = P.real {ω | SamuelCahnProphet.Median.maxX X ω < a} := by
    rw [max_lt_product P X hind]
    simp only [F, one_mul]
    apply Finset.prod_congr rfl
    intro i _
    exact (tail_partition P (X i) (hX i) a).2
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hc
    (show r ∈ Icc (F 1) (F 0) by simpa [h0,h1] using And.intro hlo hhi)
  exact ⟨s, hs, he⟩

end CTProof

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory
namespace CTProof
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable def weight (p : I → ℝ) (S : Finset I) : ℝ :=
  (∏ i ∈ S, p i) * ∏ i ∈ Finset.univ \ S, (1 - p i)
noncomputable def coeff (p : I → ℝ) (i : I) : ℝ :=
  ∑ T ∈ (Finset.univ.erase i).powerset,
    ((∏ j ∈ T, p j) * ∏ j ∈ (Finset.univ.erase i) \ T, (1 - p j)) / ((T.card : ℝ) + 1)
noncomputable def rejectPoly (p : I → ℝ) (t : ℝ) : ℝ := ∏ i, (1 - t * p i)
theorem sum_weight (p : I → ℝ) : ∑ S : Finset I, weight p S = 1 := by
  have h := Finset.prod_add p (fun i => 1 - p i) Finset.univ
  simpa [weight] using h.symm
 theorem weight_nonneg (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset I) : 0 ≤ weight p S := by
  apply mul_nonneg
  · exact Finset.prod_nonneg fun i _ => (hp i).1
  · exact Finset.prod_nonneg fun i _ => sub_nonneg.mpr (hp i).2
 theorem coeff_nonneg (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : I) : 0 ≤ coeff p i := by
  apply Finset.sum_nonneg
  intro T _
  apply div_nonneg
  · exact mul_nonneg (Finset.prod_nonneg fun j _ => (hp j).1)
      (Finset.prod_nonneg fun j _ => sub_nonneg.mpr (hp j).2)
  · positivity

omit [Fintype I] in
theorem product_expansion (p : I → ℝ) (U : Finset I) (t : ℝ) :
    (∏ j ∈ U, (1 - p j + t * p j)) =
    ∑ T ∈ U.powerset, ((∏ j ∈ T, p j) * ∏ j ∈ U \ T, (1 - p j)) * t ^ T.card := by
  rw [show (∏ j ∈ U, (1 - p j + t * p j)) = ∏ j ∈ U, (t * p j + (1-p j)) by
    apply Finset.prod_congr rfl; intro j _; ring]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const]
  ring

theorem coeff_integral (p : I → ℝ) (i : I) :
    coeff p i = ∫ t in (0 : ℝ)..1, ∏ j ∈ Finset.univ.erase i, (1-t*p j) := by
  have hpoly : (fun t : ℝ => ∏ j ∈ Finset.univ.erase i, (1-t*p j)) =
      fun t => ∑ T ∈ (Finset.univ.erase i).powerset,
        ((∏ j ∈ T,p j) * ∏ j ∈ (Finset.univ.erase i) \ T, (1-p j)) * (1-t)^T.card := by
    funext t
    convert product_expansion p (Finset.univ.erase i) (1-t) using 1
    apply Finset.prod_congr rfl
    intro j _
    ring
  rw [hpoly, intervalIntegral.integral_finsetSum]
  · unfold coeff
    apply Finset.sum_congr rfl
    intro T _
    rw [intervalIntegral.integral_const_mul]
    have hp : (∫ t in (0 : ℝ)..1, (1-t)^T.card) = 1 / ((T.card : ℝ)+1) := by
      rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^T.card) 1]
      simp [integral_pow]
    rw [hp, div_eq_mul_inv, one_div]
  · intro T _
    exact (continuous_const.mul ((continuous_const.sub continuous_id).pow _)).intervalIntegrable _ _

theorem sum_marked (i : I) (f : Finset I → ℝ) :
    (∑ S : Finset I, if i ∈ S then f (S.erase i) else 0) =
      ∑ T ∈ (Finset.univ.erase i).powerset, f T := by
  have h := Finset.sum_powerset_insert (Finset.notMem_erase i Finset.univ)
    (fun S : Finset I => if i ∈ S then f (S.erase i) else 0)
  have hz : (∑ T ∈ (Finset.univ.erase i).powerset,
      if i ∈ T then f (T.erase i) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro T hT
    have hi : i ∉ T := fun hi => (Finset.mem_erase.mp (Finset.mem_powerset.mp hT hi)).1 rfl
    simp [hi]
  have he : (∑ T ∈ (Finset.univ.erase i).powerset,
      if i ∈ insert i T then f ((insert i T).erase i) else 0) =
      ∑ T ∈ (Finset.univ.erase i).powerset, f T := by
    apply Finset.sum_congr rfl
    intro T hT
    have hi : i ∉ T := fun hi => (Finset.mem_erase.mp (Finset.mem_powerset.mp hT hi)).1 rfl
    simp [hi]
  rw [hz, he, zero_add] at h
  simpa only [Finset.insert_erase (Finset.mem_univ i), Finset.powerset_univ] using h

theorem marked_coordinate (p : I → ℝ) (i : I) :
    (∑ S : Finset I, if i ∈ S then
      ((∏ j ∈ S.erase i, p j) * ∏ j ∈ Finset.univ \ S, (1-p j)) / (S.card : ℝ)
      else 0) = coeff p i := by
  unfold coeff
  rw [← sum_marked i]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hi : i ∈ S
  · simp only [hi, if_true]
    have hd : (Finset.univ.erase i) \ (S.erase i) = Finset.univ \ S := by
      ext j
      by_cases hj : j = i
      · subst j; simp [hi]
      · simp [hj]
    rw [hd]
    congr 1
    have hc := Finset.card_erase_add_one hi
    exact_mod_cast hc.symm
  · simp [hi]

theorem marked_subset_expansion (p m : I → ℝ) :
    (∑ S : Finset I,
      (∑ i ∈ S, m i * (∏ j ∈ S.erase i, p j) *
        ∏ j ∈ Finset.univ \ S, (1-p j)) / (S.card : ℝ)) =
      ∑ i, m i * coeff p i := by
  simp_rw [Finset.sum_div]
  have h : ∀ S : Finset I,
      (∑ i ∈ S, m i * (∏ j ∈ S.erase i, p j) *
        (∏ j ∈ Finset.univ \ S, (1-p j)) / (S.card : ℝ)) =
      ∑ i : I, if i ∈ S then m i *
        (((∏ j ∈ S.erase i, p j) * ∏ j ∈ Finset.univ \ S, (1-p j)) / (S.card : ℝ)) else 0 := by
    intro S
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← marked_coordinate p i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

theorem sum_mul_coeff (p : I → ℝ) : ∑ i, p i * coeff p i = 1 - ∏ i, (1-p i) := by
  rw [← marked_subset_expansion p p]
  have h : ∀ S : Finset I,
      (∑ i ∈ S, p i * (∏ j ∈ S.erase i, p j) *
        ∏ j ∈ Finset.univ \ S, (1-p j)) / (S.card : ℝ) =
      weight p S - if S = ∅ then weight p S else 0 := by
    intro S
    by_cases he : S = ∅
    · subst S; simp
    · have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      have hs : (∑ i ∈ S, p i * (∏ j ∈ S.erase i, p j) *
          ∏ j ∈ Finset.univ \ S, (1-p j)) = (S.card : ℝ) * weight p S := by
        calc
          _ = ∑ _i ∈ S, weight p S := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_prod_erase S p hi]
            rfl
          _ = _ := by simp
      rw [hs]
      simp [he, hc]
  simp_rw [h]
  rw [Finset.sum_sub_distrib, sum_weight]
  simp [weight]
end CTProof

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory
namespace CTProof
variable {I : Type*} [Fintype I] [DecidableEq I]
omit [DecidableEq I] in
theorem rejection_strict_coords (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hQ : Real.exp (-1) ≤ ∏ i, (1-p i)) : ∀ i, p i < 1 := by
  intro i
  have hne : p i ≠ 1 := by
    intro hi
    have hz : (∏ j, (1-p j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi]; ring)
    rw [hz] at hQ
    exact (not_le_of_gt (Real.exp_pos _)) hQ
  exact lt_of_le_of_ne (hp i).2 hne
omit [Fintype I] [DecidableEq I] in
 theorem log_factor (p t : ℝ) (hp1 : p < 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t * Real.log (1-p) ≤ Real.log (1-t*p) := by
  have h := strictConcaveOn_log_Ioi.concaveOn.2 (show 1-p ∈ Set.Ioi (0:ℝ) by simpa using sub_pos.mpr hp1)
    (show (1:ℝ) ∈ Set.Ioi 0 by norm_num) ht (sub_nonneg.mpr ht1) (show t+(1-t)=1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at h
  have he : t * (1-p) + (1-t) * 1 = 1-t*p := by ring
  rw [he] at h
  exact h
omit [Fintype I] [DecidableEq I] in
 theorem log_factor_strict (p t : ℝ) (hp : 0 < p) (hp1 : p < 1) (ht : 0 < t) (ht1 : t < 1) :
    t * Real.log (1-p) < Real.log (1-t*p) := by
  have h := strictConcaveOn_log_Ioi.2 (show 1-p ∈ Set.Ioi (0:ℝ) by simpa using sub_pos.mpr hp1)
    (show (1:ℝ) ∈ Set.Ioi 0 by norm_num) (show 1-p ≠ 1 by linarith)
    ht (sub_pos.mpr ht1) (show t+(1-t)=1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at h
  have he : t * (1-p) + (1-t) * 1 = 1-t*p := by ring
  rw [he] at h
  exact h
omit [DecidableEq I] in
 theorem rejectPoly_lower (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hQ : Real.exp (-1) ≤ ∏ i, (1-p i)) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (-t) ≤ rejectPoly p t := by
  have hp1 := rejection_strict_coords p hp hQ
  have hpos : ∀ i, 0 < 1-t*p i := by intro i; nlinarith [(hp i).1, hp1 i]
  have hlog : -1 ≤ ∑ i, Real.log (1-p i) := by
    have h := Real.log_le_log (Real.exp_pos (-1)) hQ
    rw [Real.log_exp, Real.log_prod (fun i _ => ne_of_gt (sub_pos.mpr (hp1 i)))] at h
    exact h
  have hs : t * (∑ i, Real.log (1-p i)) ≤ ∑ i, Real.log (1-t*p i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => log_factor (p i) t (hp1 i) ht ht1
  have hl : -t ≤ Real.log (rejectPoly p t) := by
    rw [rejectPoly, Real.log_prod (fun i _ => ne_of_gt (hpos i))]
    nlinarith [mul_le_mul_of_nonneg_left hlog ht]
  have hh := Real.exp_le_exp.mpr hl
  rw [Real.exp_log (show 0 < rejectPoly p t from Finset.prod_pos fun i _ => hpos i)] at hh
  exact hh

omit [DecidableEq I] in
theorem rejectPoly_strict (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hQ : Real.exp (-1) ≤ ∏ i, (1-p i)) (hne : ∃ i, 0 < p i)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    Real.exp (-t) < rejectPoly p t := by
  have hp1 := rejection_strict_coords p hp hQ
  have hpos : ∀ i, 0 < 1-t*p i := by intro i; nlinarith [(hp i).1, hp1 i]
  have hlog : -1 ≤ ∑ i, Real.log (1-p i) := by
    have h := Real.log_le_log (Real.exp_pos (-1)) hQ
    rw [Real.log_exp, Real.log_prod (fun i _ => ne_of_gt (sub_pos.mpr (hp1 i)))] at h
    exact h
  have hs : t * (∑ i, Real.log (1-p i)) < ∑ i, Real.log (1-t*p i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum
    · intro i _; exact log_factor (p i) t (hp1 i) ht.le ht1.le
    · obtain ⟨i, hi⟩ := hne
      exact ⟨i, Finset.mem_univ i, log_factor_strict (p i) t hi (hp1 i) ht ht1⟩
  have hl : -t < Real.log (rejectPoly p t) := by
    rw [rejectPoly, Real.log_prod (fun i _ => ne_of_gt (hpos i))]
    nlinarith [mul_le_mul_of_nonneg_left hlog ht.le]
  have hh := Real.exp_lt_exp.mpr hl
  rw [Real.exp_log (show 0 < rejectPoly p t from Finset.prod_pos fun i _ => hpos i)] at hh
  exact hh

theorem coeff_strict (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hQ : Real.exp (-1) ≤ ∏ i, (1-p i)) (hne : ∃ i, 0 < p i) (i : I) :
    1 - Real.exp (-1) < coeff p i := by
  have hdrop : ∀ t ∈ Set.Icc (0:ℝ) 1,
      rejectPoly p t ≤ ∏ j ∈ Finset.univ.erase i, (1-t*p j) := by
    intro t ht
    have hn : 0 ≤ ∏ j ∈ Finset.univ.erase i, (1-t*p j) := by
      apply Finset.prod_nonneg
      intro j _
      nlinarith [(hp j).1, (hp j).2, ht.1, ht.2]
    rw [rejectPoly, ← Finset.mul_prod_erase Finset.univ (fun j => 1-t*p j) (Finset.mem_univ i)]
    exact mul_le_of_le_one_left hn (by nlinarith [mul_nonneg ht.1 (hp i).1])
  have hh := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (show (0:ℝ)<1 by norm_num)
    (Real.continuous_exp.comp continuous_neg).continuousOn
    (show Continuous (fun t : ℝ => ∏ j ∈ Finset.univ.erase i, (1-t*p j)) by fun_prop).continuousOn
    (fun t ht => (rejectPoly_lower p hp hQ ht.1.le ht.2).trans (hdrop t ⟨ht.1.le,ht.2⟩))
    (show ∃ t ∈ Set.Icc (0:ℝ) 1, Real.exp (-t) < ∏ j ∈ Finset.univ.erase i, (1-t*p j) from
      ⟨1/2, by norm_num, (rejectPoly_strict p hp hQ hne (by norm_num) (by norm_num)).trans_le
        (hdrop (1/2) (by norm_num))⟩)
  have he : (∫ t in (0:ℝ)..1, Real.exp (-t)) = 1-Real.exp (-1) := by
    rw [intervalIntegral.integral_comp_neg, integral_exp]
    simp
  change (∫ t in (0:ℝ)..1, Real.exp (-t)) < (∫ t in (0:ℝ)..1, ∏ j ∈ Finset.univ.erase i, (1-t*p j)) at hh
  rw [he, ← coeff_integral] at hh
  exact hh

theorem positive_linear_gap (p m : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hQ : Real.exp (-1) ≤ ∏ i, (1-p i)) (hne : ∃ i, 0 < p i)
    (hm : ∀ i, 0 ≤ m i) (hms : 0 < ∑ i, m i) :
    (1-Real.exp (-1)) * (∑ i, m i) < ∑ i, m i * coeff p i := by
  rw [Finset.mul_sum]
  apply Finset.sum_lt_sum
  · intro i _
    nlinarith [coeff_strict p hp hQ hne i, hm i]
  · have hex : ∃ i, 0 < m i := by
      by_contra h
      push Not at h
      have hz : (∑ i, m i) ≤ 0 := Finset.sum_nonpos fun i _ => h i
      linarith
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_univ i, by nlinarith [coeff_strict p hp hQ hne i]⟩

theorem revenue_surplus_gap (p u : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hQ : (∏ i, (1-p i)) = Real.exp (-1)) (a : ℝ)
    (hu : ∀ i, 0 ≤ u i) (hus : 0 < ∑ i, u i) :
    (1-Real.exp (-1)) * (a + ∑ i, u i) <
      a*(1-Real.exp (-1)) + ∑ i, u i * coeff p i := by
  have hne : ∃ i, 0 < p i := by
    by_contra h
    push Not at h
    have hz : p = fun _ => 0 := funext fun i => le_antisymm (h i) (hp i).1
    rw [hz] at hQ
    simp only [sub_zero, Finset.prod_const_one] at hQ
    have he : Real.exp (-1) < 1 := by simp
    linarith
  have h := positive_linear_gap p u hp hQ.ge hne hu hus
  nlinarith
end CTProof

set_option autoImplicit false
open scoped BigOperators
namespace CTProof
variable {I : Type*} [Fintype I] [DecidableEq I]
theorem sum_weight_prod (p f g : I → ℝ) :
    (∑ S : Finset I, weight p S * ∏ i, if i ∈ S then f i else g i) =
      ∏ i, (p i * f i + (1-p i)*g i) := by
  rw [Finset.prod_add]
  simp only [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_ite]
  have hs : Finset.univ.filter (fun i => i ∈ S) = S := by ext i; simp
  have hn : Finset.univ.filter (fun i => i ∉ S) = Finset.univ \ S := by ext i; simp
  rw [hs, hn, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  unfold weight
  ring

theorem prod_membership_indicator (A B : Finset I) :
    (∏ i : I, if (i ∈ B ↔ i ∈ A) then (1:ℝ) else 0) = if B = A then 1 else 0 := by
  by_cases h : B = A
  · subst B; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ B ↔ i ∈ A) := by
      by_contra hn
      push Not at hn
      exact h (Finset.ext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem coin_fiber (r : I → ℝ) (U V A : Finset I) (hUV : Disjoint U V) :
    (∑ S : Finset I, weight r S * (if U ∪ (S ∩ V) = A then (1:ℝ) else 0)) =
      weight (fun i => if i ∈ U then 1 else if i ∈ V then r i else 0) A := by
  simp_rw [← prod_membership_indicator]
  have he : ∀ S : Finset I,
      (∏ i : I, if (i ∈ U ∪ (S ∩ V) ↔ i ∈ A) then (1:ℝ) else 0) =
      ∏ i : I, if i ∈ S then
        (if (i ∈ U ∨ i ∈ V) ↔ i ∈ A then (1:ℝ) else 0)
        else (if (i ∈ U ↔ i ∈ A) then (1:ℝ) else 0) := by
    intro S
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [hi]
  simp_rw [he]
  rw [sum_weight_prod]
  have hi : ∀ i : I,
      r i * (if (i ∈ U ∨ i ∈ V) ↔ i ∈ A then (1:ℝ) else 0) +
      (1-r i)*(if (i ∈ U ↔ i ∈ A) then (1:ℝ) else 0) =
      if i ∈ A then (if i ∈ U then 1 else if i ∈ V then r i else 0)
      else 1-(if i ∈ U then 1 else if i ∈ V then r i else 0) := by
    intro i
    have hnot := Finset.disjoint_left.mp hUV
    by_cases hu : i ∈ U <;> by_cases hv : i ∈ V <;> by_cases ha : i ∈ A <;>
      simp_all
  simp_rw [hi]
  rw [Finset.prod_ite]
  have hs : Finset.univ.filter (fun i => i ∈ A) = A := by ext i; simp
  have hn : Finset.univ.filter (fun i => i ∉ A) = Finset.univ \ A := by ext i; simp
  rw [hs, hn]
  rfl

theorem coin_pushforward (r : I → ℝ) (U V : Finset I) (hUV : Disjoint U V)
    (g : Finset I → ℝ) :
    (∑ S : Finset I, weight r S * g (U ∪ (S ∩ V))) =
      ∑ A : Finset I, weight (fun i => if i ∈ U then 1 else if i ∈ V then r i else 0) A * g A := by
  have he : ∀ S : Finset I, g (U ∪ (S ∩ V)) =
      ∑ A : Finset I, (if U ∪ (S ∩ V) = A then (1:ℝ) else 0) * g A := by
    intro S
    simp [eq_comm]
  simp_rw [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  rw [← coin_fiber r U V A hUV, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S _
  ring
end CTProof

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace CTProof
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

lemma weight_le_one (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset (Fin n)) :
    weight p S ≤ 1 := by
  apply mul_le_one₀
  · exact Finset.prod_le_one (fun i _ => (hp i).1) (fun i _ => (hp i).2)
  · exact Finset.prod_nonneg fun i _ => sub_nonneg.mpr (hp i).2
  · exact Finset.prod_le_one (fun i _ => sub_nonneg.mpr (hp i).2) (fun i _ => by linarith [(hp i).1])

lemma weight_eq_prod (p : Fin n → ℝ) (S : Finset (Fin n)) :
    weight p S = ∏ i, if i ∈ S then p i else 1-p i := by
  classical
  rw [Finset.prod_ite]
  unfold weight
  congr 1 <;> apply Finset.prod_congr <;> try (ext j; simp)
  all_goals intros; rfl

lemma marked_prod (X : Fin n → ℝ) (w : Fin n → ℝ → ℝ) (S : Finset (Fin n)) (i : Fin n) :
    X i * weight (fun j => w j (X j)) S =
      ∏ j, (if j=i then X j else 1) * (if j∈S then w j (X j) else 1-w j (X j)) := by
  classical
  rw [Finset.prod_mul_distrib, ← weight_eq_prod]
  simp

lemma integral_marked (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (w : Fin n → ℝ → ℝ) (hw : ∀ i, Measurable (w i))
    (hwi : ∀ i x, 0 ≤ w i x ∧ w i x ≤ 1)
    (S : Finset (Fin n)) (i : Fin n) (his : i∈S) :
    (∫ ω, X i ω * weight (fun j => w j (X j ω)) S ∂P) =
      (∫ ω, X i ω * w i (X i ω) ∂P) *
      (∏ j ∈ S.erase i, ∫ ω, w j (X j ω) ∂P) *
      ∏ j ∈ Finset.univ \ S, (1 - ∫ ω, w j (X j ω) ∂P) := by
  classical
  let f : Fin n → ℝ → ℝ := fun j x => (if j=i then x else 1) * (if j∈S then w j x else 1-w j x)
  have hf : ∀ j, AEStronglyMeasurable (f j) (P.map (X j)) := by
    intro j
    apply Measurable.aestronglyMeasurable
    dsimp [f]
    split_ifs <;> fun_prop
  have he := hind.integral_fun_prod_comp (fun j => (hX j).aemeasurable) hf
  have hew (j : Fin n) : Integrable (fun ω => w j (X j ω)) P := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) ((hw j).comp (hX j)).aestronglyMeasurable
    filter_upwards [] with ω
    change ‖w j (X j ω)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (hwi j (X j ω)).1]
    exact (hwi j (X j ω)).2
  have hprod : (fun ω => X i ω * weight (fun j => w j (X j ω)) S) =
      (fun ω => ∏ j, f j (X j ω)) := by
    funext ω
    exact marked_prod (fun j => X j ω) w S i
  rw [hprod, he]
  have hfi : (∫ ω, f i (X i ω) ∂P) = ∫ ω, X i ω * w i (X i ω) ∂P := by simp [f,his]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hfi]
  have hrest : (∏ j ∈ Finset.univ.erase i, ∫ ω, f j (X j ω) ∂P) =
      (∏ j ∈ S.erase i, ∫ ω, w j (X j ω) ∂P) *
      ∏ j ∈ Finset.univ \ S, (1 - ∫ ω, w j (X j ω) ∂P) := by
    have hh : ∀ j∈Finset.univ.erase i, (∫ ω, f j (X j ω) ∂P) =
        if j∈S then (∫ ω, w j (X j ω) ∂P) else 1-(∫ ω, w j (X j ω) ∂P) := by
      intro j hj
      have hji : j≠i := (Finset.mem_erase.mp hj).1
      by_cases hjs : j∈S
      · simp [f,hji,hjs]
      · simp [f,hji,hjs, integral_sub (integrable_const _) (hew j)]
    rw [Finset.prod_congr rfl hh, Finset.prod_ite]
    congr 1 <;> congr 1 <;> ext j <;> simp_all
    intro hj hji
    subst j
    exact hj his
  rw [hrest, mul_assoc]

noncomputable def rewardOn (X : Fin n → Ω → ℝ) (A : Finset (Fin n)) (ω : Ω) : ℝ :=
  (∑ i ∈ A, X i ω) / (A.card : ℝ)

noncomputable def mixedSet (a : ℝ) (S : Finset (Fin n)) (X : Fin n → Ω → ℝ) (ω : Ω) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a < X i ω ∨ (i ∈ S ∧ X i ω = a))

noncomputable def mixedReward (a s : ℝ) (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ S : Finset (Fin n), weight (fun _ => s) S * rewardOn X (mixedSet a S X ω) ω

noncomputable def weightedReward (w : Fin n → ℝ → ℝ) (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ S : Finset (Fin n), weight (fun j => w j (X j ω)) S * rewardOn X S ω

lemma integrable_marked (P : Measure Ω) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hn : ∀ i ω, 0 ≤ X i ω)
    (hi : ∀ i, Integrable (X i) P) (w : Fin n → ℝ → ℝ) (hw : ∀ i, Measurable (w i))
    (hwi : ∀ i x, 0 ≤ w i x ∧ w i x ≤ 1) (S : Finset (Fin n)) (i : Fin n) :
    Integrable (fun ω => X i ω * weight (fun j => w j (X j ω)) S) P := by
  apply (hi i).mono'
  · apply Measurable.aestronglyMeasurable
    unfold weight
    fun_prop
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hn i ω) (weight_nonneg _ (fun j => hwi j (X j ω)) S))]
  exact mul_le_of_le_one_right (hn i ω) (weight_le_one _ (fun j => hwi j (X j ω)) S)

lemma weighted_expectation (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hn : ∀ i ω, 0 ≤ X i ω)
    (hi : ∀ i, Integrable (X i) P) (hind : iIndepFun X P)
    (w : Fin n → ℝ → ℝ) (hw : ∀ i, Measurable (w i))
    (hwi : ∀ i x, 0 ≤ w i x ∧ w i x ≤ 1) :
    (∫ ω, weightedReward w X ω ∂P) =
      ∑ i, (∫ ω, X i ω * w i (X i ω) ∂P) * coeff (fun j => ∫ ω, w j (X j ω) ∂P) i := by
  classical
  have he (S : Finset (Fin n)) (ω : Ω) :
      weight (fun j => w j (X j ω)) S * rewardOn X S ω =
      (∑ i ∈ S, X i ω * weight (fun j => w j (X j ω)) S) / (S.card : ℝ) := by
    rw [rewardOn, ← Finset.sum_mul]
    ring
  have hint (S : Finset (Fin n)) : Integrable
      (fun ω => (∑ i ∈ S, X i ω * weight (fun j => w j (X j ω)) S) / (S.card : ℝ)) P :=
    (integrable_finsetSum _ (fun i _ => integrable_marked P X hX hn hi w hw hwi S i)).div_const _
  simp_rw [weightedReward, he]
  rw [integral_finsetSum _ (fun S _ => hint S)]
  simp_rw [integral_div]
  have hmark (S : Finset (Fin n)) :
      (∫ ω, ∑ i ∈ S, X i ω * weight (fun j => w j (X j ω)) S ∂P) =
      ∑ i ∈ S, (∫ ω, X i ω * w i (X i ω) ∂P) *
        (∏ j ∈ S.erase i, ∫ ω, w j (X j ω) ∂P) *
        ∏ j ∈ Finset.univ \ S, (1 - ∫ ω, w j (X j ω) ∂P) := by
    rw [integral_finsetSum _ (fun i _ => integrable_marked P X hX hn hi w hw hwi S i)]
    apply Finset.sum_congr rfl
    intro i his
    exact integral_marked P X hX hind w hw hwi S i his
  simp_rw [hmark]
  exact marked_subset_expansion _ _


noncomputable def tailWeight (a s x : ℝ) : ℝ := if a < x then 1 else if x = a then s else 0

lemma tailWeight_measurable (a s : ℝ) : Measurable (tailWeight a s) := by
  unfold tailWeight
  exact measurable_const.ite (measurableSet_lt measurable_const measurable_id)
    (measurable_const.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const)

lemma tailWeight_bounds (a s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (x : ℝ) :
    0 ≤ tailWeight a s x ∧ tailWeight a s x ≤ 1 := by
  unfold tailWeight
  split_ifs <;> simp_all

lemma tailWeight_mark (a s x : ℝ) :
    x * tailWeight a s x = a * tailWeight a s x + max (x-a) 0 := by
  unfold tailWeight
  split_ifs with h h'
  · rw [max_eq_left (by linarith)]
    ring
  · subst x
    simp
  · rw [max_eq_right (by linarith)]
    simp

lemma tailWeight_integral (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY : Measurable Y) (a s : ℝ) :
    (∫ ω, tailWeight a s (Y ω) ∂P) = P.real {ω | a < Y ω} + s * P.real {ω | Y ω = a} := by
  have hA : MeasurableSet {ω | a < Y ω} := measurableSet_lt measurable_const hY
  have hB : MeasurableSet {ω | Y ω = a} := measurableSet_eq_fun hY measurable_const
  have he : (fun ω => tailWeight a s (Y ω)) =
      (fun ω => ({ω | a < Y ω}.indicator (fun _ => (1:ℝ)) ω) +
        ({ω | Y ω = a}.indicator (fun _ => s) ω)) := by
    funext ω
    simp only [tailWeight, Set.indicator_apply, mem_ofPred_eq]
    split_ifs <;> simp_all
  rw [he, integral_add ((integrable_const (1:ℝ)).indicator hA)
    ((integrable_const s).indicator hB), integral_indicator_const _ hA,
    integral_indicator_const _ hB]
  simp [smul_eq_mul, mul_comm]

omit [MeasurableSpace Ω] in
lemma mixed_eq_weighted (a s : ℝ) (X : Fin n → Ω → ℝ) (ω : Ω) :
    mixedReward a s X ω = weightedReward (fun _ => tailWeight a s) X ω := by
  classical
  let U := Finset.univ.filter (fun i => a < X i ω)
  let V := Finset.univ.filter (fun i => X i ω = a)
  have hd : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [U, V, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    linarith
  have he (S : Finset (Fin n)) : mixedSet a S X ω = U ∪ (S ∩ V) := by
    ext i
    simp [mixedSet, U, V]
  unfold mixedReward weightedReward
  simp_rw [he]
  convert coin_pushforward (fun _ : Fin n => s) U V hd (fun A => rewardOn X A ω) using 1
  congr 1
  funext A
  congr 2
  funext i
  simp [U, V, tailWeight]


lemma mixed_expectation (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hn : ∀ i ω, 0 ≤ X i ω)
    (hi : ∀ i, Integrable (X i) P) (hind : iIndepFun X P)
    (a s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    let p := fun i => P.real {ω | a < X i ω} + s * P.real {ω | X i ω = a}
    let u := fun i => ∫ ω, max (X i ω-a) 0 ∂P
    (∫ ω, mixedReward a s X ω ∂P) =
      a * (1 - ∏ i, (1-p i)) + ∑ i, u i * coeff p i := by
  dsimp only
  simp_rw [mixed_eq_weighted]
  rw [weighted_expectation P X hX hn hi hind (fun _ => tailWeight a s)
    (fun _ => tailWeight_measurable a s) (fun _ x => tailWeight_bounds a s hs x)]
  have hm (i : Fin n) :
      (∫ ω, X i ω * tailWeight a s (X i ω) ∂P) =
      a * (P.real {ω | a < X i ω} + s * P.real {ω | X i ω = a}) +
        ∫ ω, max (X i ω-a) 0 ∂P := by
    have ht : Integrable (fun ω => tailWeight a s (X i ω)) P := by
      apply (integrable_const (1:ℝ)).mono' ((tailWeight_measurable a s).comp (hX i)).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun ω => by
        change |tailWeight a s (X i ω)| ≤ 1
        rw [abs_of_nonneg (tailWeight_bounds a s hs _).1]
        exact (tailWeight_bounds a s hs _).2
    have hu : Integrable (fun ω => max (X i ω-a) 0) P := ((hi i).sub (integrable_const a)).pos_part
    simp_rw [tailWeight_mark]
    rw [integral_add (ht.const_mul a) hu,
      integral_const_mul, tailWeight_integral P (X i) (hX i) a s]
  simp_rw [hm, tailWeight_integral P _ (hX _) a s, add_mul, Finset.sum_add_distrib]
  rw [show (∑ i, a * (P.real {ω | a < X i ω} + s * P.real {ω | X i ω = a}) *
    coeff (fun j => P.real {ω | a < X j ω} + s * P.real {ω | X j ω = a}) i) =
    a * (∑ i, (P.real {ω | a < X i ω} + s * P.real {ω | X i ω = a}) *
    coeff (fun j => P.real {ω | a < X j ω} + s * P.real {ω | X j ω = a}) i) by
      rw [Finset.mul_sum]; congr 1; funext i; ring]
  rw [sum_mul_coeff]

end CTProof

set_option autoImplicit false
open Filter
open scoped Topology
namespace CTPeer
noncomputable def approxThreshold {n : ℕ} (a : ℝ) (S : Finset (Fin n)) (m : ℕ) : Fin n → ENNReal :=
  fun i => ENNReal.ofReal (if i ∈ S then max 0 (a-1/((m:ℝ)+1)) else a)
theorem cutoff_eventually (a x : ℝ) (ha : 0 < a) :
    ∀ᶠ m : ℕ in atTop,
      (ENNReal.ofReal (max 0 (a-1/((m:ℝ)+1))) < ENNReal.ofReal x ↔ a ≤ x) := by
  have hc : Tendsto (fun m : ℕ => max 0 (a-1/((m:ℝ)+1))) atTop (𝓝 a) := by
    have hd : Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h := (tendsto_const_nhds (x := (0:ℝ))).max ((tendsto_const_nhds (x := a)).sub hd)
    simpa [max_eq_right ha.le] using h
  by_cases hx : a ≤ x
  · apply Filter.Eventually.of_forall
    intro m
    have hd : 0 < 1/((m:ℝ)+1) := by positivity
    have hl : max 0 (a-1/((m:ℝ)+1)) < x := max_lt (lt_of_lt_of_le ha hx) (by linarith)
    simp only [ENNReal.ofReal_lt_ofReal_iff (lt_of_lt_of_le ha hx), hx, iff_true]
    exact hl
  · have hh := hc.eventually (eventually_gt_nhds (lt_of_not_ge hx))
    filter_upwards [hh] with m hm
    exact iff_of_false (not_lt_of_ge (ENNReal.ofReal_le_ofReal hm.le)) hx

theorem accepted_approx_eventually {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ)
    (a : ℝ) (ha : 0 < a) (S : Finset (Fin n)) (ω : Ω) :
    ∀ᶠ m : ℕ in atTop, CorreaThreshold.Nonadaptive.accepted (approxThreshold a S m) X ω =
      Finset.univ.filter (fun i => a < X i ω ∨ (i ∈ S ∧ X i ω = a)) := by
  classical
  have hi : ∀ i : Fin n, ∀ᶠ m : ℕ in atTop,
      (approxThreshold a S m i < ENNReal.ofReal (X i ω) ↔
        a < X i ω ∨ (i ∈ S ∧ X i ω = a)) := by
    intro i
    by_cases hs : i ∈ S
    · filter_upwards [cutoff_eventually a (X i ω) ha] with m hm
      simp only [approxThreshold, hs, if_true, true_and]
      rw [hm]
      constructor
      · intro h; exact (lt_or_eq_of_le h).imp_right Eq.symm
      · rintro (h | h); exact h.le; exact h.ge
    · apply Filter.Eventually.of_forall
      intro m
      simp only [approxThreshold, hs, if_false, false_and, or_false]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le
  filter_upwards [Filter.eventually_all.mpr hi] with m hm
  ext i
  simp only [CorreaThreshold.Nonadaptive.accepted, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hm i
end CTPeer

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace CTPeer
noncomputable def singleThreshold {n : ℕ} (i : Fin n) : Fin n → ENNReal :=
  fun j => if j = i then 0 else ⊤
 theorem ratio_single {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (i : Fin n) (ω : Ω) :
    CorreaThreshold.Nonadaptive.ratio (singleThreshold i) X ω = max (X i ω) 0 := by
  classical
  have hset : CorreaThreshold.Nonadaptive.accepted (singleThreshold i) X ω =
      if 0 < X i ω then {i} else ∅ := by
    ext j
    simp only [CorreaThreshold.Nonadaptive.accepted, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j = i
    · subst j
      split_ifs <;> simp_all [singleThreshold]
    · split_ifs <;> simp_all [singleThreshold]
  unfold CorreaThreshold.Nonadaptive.ratio
  rw [hset]
  by_cases hi : 0 < X i ω
  · simp [hi, max_eq_left hi.le]
  · simp [hi, max_eq_right (le_of_not_gt hi)]
 theorem single_expectation {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Fin n → Ω → ℝ) (i : Fin n) :
    (∫⁻ ω, ENNReal.ofReal (CorreaThreshold.Nonadaptive.ratio (singleThreshold i) X ω) ∂P) =
      ∫⁻ ω, ENNReal.ofReal (X i ω) ∂P := by
  apply lintegral_congr
  intro ω
  rw [ratio_single]
  by_cases hi : 0 ≤ X i ω
  · rw [max_eq_left hi]
  · rw [max_eq_right (le_of_not_ge hi), ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos (le_of_not_ge hi)]


end CTPeer

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace CTPeer
 theorem constant_coordinate {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} [NeZero n]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hind : iIndepFun X P) (a : ℝ) (hupper : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ a)
    (hmax : ∀ᵐ ω ∂P, SamuelCahnProphet.Median.maxX X ω = a) :
    ∃ i, ∀ᵐ ω ∂P, X i ω = a := by
  have hz : P {ω | SamuelCahnProphet.Median.maxX X ω < a} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hmax] with ω hω
    simp [hω]
  have hr : P.real {ω | SamuelCahnProphet.Median.maxX X ω < a} = 0 := by
    rw [measureReal_def, hz, ENNReal.toReal_zero]
  rw [CTProof.max_lt_product P X hind] at hr
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hr
  have hi0 : P {ω | X i ω < a} = 0 := (measureReal_eq_zero_iff (μ := P) (s := {ω | X i ω < a})).mp hi
  refine ⟨i, ?_⟩
  filter_upwards [hupper i, measure_eq_zero_iff_ae_notMem.mp hi0] with ω hu hl
  exact le_antisymm hu (le_of_not_gt hl)

 theorem degenerate_threshold {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} [NeZero n]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hind : iIndepFun X P) (a : ℝ) (ha : 0 ≤ a)
    (hupper : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ a)
    (hmax : ∀ᵐ ω ∂P, SamuelCahnProphet.Median.maxX X ω = a) :
    ∃ i, (∀ᵐ ω ∂P, X i ω = a) ∧
      (∫ ω, CorreaThreshold.Nonadaptive.ratio (singleThreshold i) X ω ∂P) = a := by
  obtain ⟨i, hi⟩ := constant_coordinate P X hind a hupper hmax
  refine ⟨i, hi, ?_⟩
  calc
    _ = ∫ _ω, a ∂P := by
      apply integral_congr_ae
      filter_upwards [hi] with ω hω
      rw [ratio_single, hω, max_eq_left ha]
    _ = a := by simp
end CTPeer

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace CTProof
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

lemma measurable_config (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (a : ℝ) (S : Finset (Fin n)) :
    Measurable (fun ω => rewardOn X (mixedSet a S X ω) ω) := by
  classical
  unfold rewardOn mixedSet
  simp_rw [Finset.sum_filter, Finset.natCast_card_filter]
  have hm (i : Fin n) : MeasurableSet {ω | a < X i ω ∨ (i ∈ S ∧ X i ω = a)} := by
    by_cases hs : i ∈ S
    · have he : {ω | a < X i ω ∨ (i ∈ S ∧ X i ω = a)} =
          {ω | a < X i ω} ∪ {ω | X i ω = a} := by ext ω; simp [hs]
      rw [he]
      exact (measurableSet_lt measurable_const (hX i)).union (measurableSet_eq_fun (hX i) measurable_const)
    · have he : {ω | a < X i ω ∨ (i ∈ S ∧ X i ω = a)} = {ω | a < X i ω} := by ext ω; simp [hs]
      rw [he]
      exact measurableSet_lt measurable_const (hX i)
  apply Measurable.div
  · exact Finset.measurable_sum _ fun i _ => (hX i).ite (hm i) measurable_const
  · exact Finset.measurable_sum _ fun i _ => measurable_const.ite (hm i) measurable_const

omit [MeasurableSpace Ω] in
lemma rewardOn_bounds (X : Fin n → Ω → ℝ) (hn : ∀ i ω, 0 ≤ X i ω)
    (A : Finset (Fin n)) (ω : Ω) : 0 ≤ rewardOn X A ω ∧ rewardOn X A ω ≤ ∑ i, X i ω := by
  classical
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => hn i ω) (Nat.cast_nonneg _)
  · by_cases he : A = ∅
    · simp [rewardOn, he, Finset.sum_nonneg (fun i _ => hn i ω)]
    have hc : (1:ℝ) ≤ A.card := by exact_mod_cast Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    exact (div_le_self (Finset.sum_nonneg (fun i _ => hn i ω)) hc).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun i _ _ => hn i ω))

lemma integrable_config (P : Measure Ω) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hn : ∀ i ω, 0 ≤ X i ω)
    (hi : ∀ i, Integrable (X i) P) (a : ℝ) (S : Finset (Fin n)) :
    Integrable (fun ω => rewardOn X (mixedSet a S X ω) ω) P := by
  apply (integrable_finsetSum _ (fun i _ => hi i)).mono' (measurable_config X hX a S).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (rewardOn_bounds X hn _ ω).1]
    exact (rewardOn_bounds X hn _ ω).2

lemma approximate_expectation (P : Measure Ω) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hn : ∀ i ω, 0 ≤ X i ω)
    (hi : ∀ i, Integrable (X i) P) (a : ℝ) (ha : 0 < a) (S : Finset (Fin n)) :
    Tendsto (fun m => ∫ ω, CorreaThreshold.Nonadaptive.ratio (CTPeer.approxThreshold a S m) X ω ∂P)
      atTop (𝓝 (∫ ω, rewardOn X (mixedSet a S X ω) ω ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun ω => ∑ i, X i ω)
  · intro m
    exact (measurable_ratio _ X hX).aestronglyMeasurable
  · exact integrable_finsetSum _ (fun i _ => hi i)
  · intro m
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ratio_nonneg _ X hn ω)]
      exact ratio_le_sum _ X hn ω
  · apply Filter.Eventually.of_forall
    intro ω
    apply tendsto_const_nhds.congr'
    filter_upwards [CTPeer.accepted_approx_eventually X a ha S ω] with m hm
    unfold CorreaThreshold.Nonadaptive.ratio rewardOn
    rw [hm]
    rfl

lemma mixed_derandomize (P : Measure Ω) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hn : ∀ i ω, 0 ≤ X i ω)
    (hi : ∀ i, Integrable (X i) P) (a s b : ℝ) (hs : s ∈ Icc (0:ℝ) 1)
    (hb : b < ∫ ω, mixedReward a s X ω ∂P) :
    ∃ S : Finset (Fin n), b < ∫ ω, rewardOn X (mixedSet a S X ω) ω ∂P := by
  classical
  by_contra! h
  have he : (∫ ω, mixedReward a s X ω ∂P) =
      ∑ S : Finset (Fin n), weight (fun _ => s) S * ∫ ω, rewardOn X (mixedSet a S X ω) ω ∂P := by
    unfold mixedReward
    rw [integral_finsetSum _ (fun S _ => (integrable_config P X hX hn hi a S).const_mul _)]
    simp_rw [integral_const_mul]
  have hh : (∫ ω, mixedReward a s X ω ∂P) ≤ b := by
    rw [he]
    calc
      _ ≤ ∑ S : Finset (Fin n), weight (fun _ => s) S * b :=
        Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (h S) (weight_nonneg _ (fun _ => hs) S)
      _ = b := by rw [← Finset.sum_mul, sum_weight]; simp
  linarith

lemma strict_mixed_to_threshold (P : Measure Ω) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hn : ∀ i ω, 0 ≤ X i ω)
    (hi : ∀ i, Integrable (X i) P) (a s b : ℝ) (ha : 0 < a) (hs : s ∈ Icc (0:ℝ) 1)
    (hb : b < ∫ ω, mixedReward a s X ω ∂P) :
    ∃ τ : Fin n → ENNReal, b ≤ ∫ ω, CorreaThreshold.Nonadaptive.ratio τ X ω ∂P := by
  obtain ⟨S, hS⟩ := mixed_derandomize P X hX hn hi a s b hs hb
  obtain ⟨m, hm⟩ := ((approximate_expectation P X hX hn hi a ha S).eventually (eventually_gt_nhds hS)).exists
  exact ⟨CTPeer.approxThreshold a S m, hm.le⟩
end CTProof

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace CTProof
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} [NeZero n]
lemma integrable_max (P : Measure Ω) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hn : ∀ i ω, 0 ≤ X i ω)
    (hi : ∀ i, Integrable (X i) P) : Integrable (SamuelCahnProphet.Median.maxX X) P := by
  apply (integrable_finsetSum _ (fun i _ => hi i)).mono' (measurable_max X hX).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (max_nonneg X hn ω)]
    exact max_le_sum X hn ω

lemma max_surplus_bound (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hn : ∀ i ω, 0 ≤ X i ω)
    (hi : ∀ i, Integrable (X i) P) (a : ℝ) :
    (∫ ω, SamuelCahnProphet.Median.maxX X ω ∂P) ≤ a + ∑ i, ∫ ω, max (X i ω-a) 0 ∂P := by
  have hu (i : Fin n) : Integrable (fun ω => max (X i ω-a) 0) P := ((hi i).sub (integrable_const a)).pos_part
  have hb (ω : Ω) : SamuelCahnProphet.Median.maxX X ω ≤ a + ∑ i, max (X i ω-a) 0 := by
    apply Finset.sup'_le
    intro i _
    have hh := Finset.single_le_sum (f := fun i => max (X i ω-a) 0) (fun i _ => le_max_right _ _) (Finset.mem_univ i)
    linarith [le_max_left (X i ω-a) 0]
  have hh := integral_mono (integrable_max P X hX hn hi) ((integrable_const a).add (integrable_finsetSum _ (fun i _ => hu i))) hb
  change (∫ ω, SamuelCahnProphet.Median.maxX X ω ∂P) ≤ (∫ ω, a + ∑ i, max (X i ω-a) 0 ∂P) at hh
  rw [integral_add (integrable_const a) (integrable_finsetSum _ (fun i _ => hu i)),
    integral_finsetSum _ (fun i _ => hu i)] at hh
  simpa using hh

omit [NeZero n] in
lemma tail_prob_bounds (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (a s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (i : Fin n) :
    0 ≤ P.real {ω | a < X i ω} + s * P.real {ω | X i ω = a} ∧
    P.real {ω | a < X i ω} + s * P.real {ω | X i ω = a} ≤ 1 := by
  constructor
  · exact add_nonneg measureReal_nonneg (mul_nonneg hs.1 measureReal_nonneg)
  · have ht := (tail_partition P (X i) (hX i) a).2
    have hm : s * P.real {ω | X i ω = a} ≤ P.real {ω | X i ω = a} :=
      mul_le_of_le_one_left (measureReal_nonneg) hs.2
    linarith [measureReal_nonneg (μ := P) (s := {ω | X i ω < a})]

omit [MeasurableSpace Ω] [NeZero n] in
lemma zero_mixed (X : Fin n → Ω → ℝ) (ω : Ω) :
    mixedReward 0 0 X ω = CorreaThreshold.Nonadaptive.ratio (fun _ => 0) X ω := by
  classical
  unfold mixedReward
  have hw : ∀ S : Finset (Fin n), weight (fun _ => (0:ℝ)) S = if S = ∅ then 1 else 0 := by
    intro S
    by_cases hs : S = ∅
    · simp [hs, weight]
    · have hn := Finset.nonempty_iff_ne_empty.mpr hs
      obtain ⟨i, hi⟩ := hn
      have hp : (∏ _i ∈ S, (0:ℝ)) = 0 := Finset.prod_eq_zero hi rfl
      simp [weight, hp, hs]
  simp_rw [hw]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have he : mixedSet 0 ∅ X ω = CorreaThreshold.Nonadaptive.accepted (fun _ => 0) X ω := by
    ext i
    simp [mixedSet, CorreaThreshold.Nonadaptive.accepted]
  unfold rewardOn CorreaThreshold.Nonadaptive.ratio
  rw [he]

omit [NeZero n] in
lemma zero_expectation (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hn : ∀ i ω, 0 ≤ X i ω)
    (hi : ∀ i, Integrable (X i) P) (hind : iIndepFun X P) :
    (∫ ω, CorreaThreshold.Nonadaptive.ratio (fun _ => 0) X ω ∂P) =
    ∑ i, (∫ ω, X i ω ∂P) * coeff (fun j => P.real {ω | 0 < X j ω}) i := by
  have hh := mixed_expectation P X hX hn hi hind 0 0 (by simp)
  simp only [zero_mixed, zero_mul, add_zero, sub_zero, max_eq_left (hn _ _), zero_add] at hh
  exact hh


omit [NeZero n] in
lemma positive_tail_of_mean (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hn : ∀ ω, 0 ≤ Y ω) (hi : Integrable Y P) (hm : 0 < ∫ ω, Y ω ∂P) :
    0 < P.real {ω | 0 < Y ω} := by
  have hh := (integral_pos_iff_support_of_nonneg hn hi).mp hm
  have he : Function.support Y = {ω | 0 < Y ω} := by
    ext ω
    simp only [Function.mem_support, mem_ofPred_eq]
    constructor
    · intro h; exact lt_of_le_of_ne (hn ω) (Ne.symm h)
    · exact ne_of_gt
  rw [he] at hh
  exact ENNReal.toReal_pos (ne_of_gt hh) (measure_ne_top P _)

lemma finite_positive_exists (P : Measure Ω) [IsProbabilityMeasure P] (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hn : ∀ i ω, 0 ≤ X i ω)
    (hind : iIndepFun X P) (hi : ∀ i, Integrable (X i) P)
    (hM : 0 < ∫ ω, SamuelCahnProphet.Median.maxX X ω ∂P) :
    ∃ τ : Fin n → ENNReal,
      (1-Real.exp (-1)) * (∫ ω, SamuelCahnProphet.Median.maxX X ω ∂P) ≤
        ∫ ω, CorreaThreshold.Nonadaptive.ratio τ X ω ∂P := by
  classical
  let M := ∫ ω, SamuelCahnProphet.Median.maxX X ω ∂P
  let c := 1-Real.exp (-1)
  have hc : 0 < c := by dsimp [c]; have := Real.exp_lt_one_iff.mpr (show (-1:ℝ)<0 by norm_num); linarith
  have hmi := integrable_max P X hX hn hi
  let p0 := fun i => P.real {ω | 0 < X i ω}
  by_cases hQ0 : Real.exp (-1) ≤ ∏ i, (1-p0 i)
  · have hsum : M ≤ ∑ i, ∫ ω, X i ω ∂P := by
      have hh := integral_mono hmi (integrable_finsetSum _ (fun i _ => hi i)) (max_le_sum X hn)
      simpa only [integral_finsetSum _ (fun i _ => hi i)] using hh
    have hm : ∀ i, 0 ≤ ∫ ω, X i ω ∂P := fun i => integral_nonneg (hn i)
    have hsp : 0 < ∑ i, ∫ ω, X i ω ∂P := lt_of_lt_of_le hM hsum
    have hex : ∃ i, 0 < ∫ ω, X i ω ∂P := by
      by_contra! h
      have := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
      linarith
    obtain ⟨i, hxi⟩ := hex
    have hp : ∀ j, 0 ≤ p0 j ∧ p0 j ≤ 1 := fun j => ⟨measureReal_nonneg, measureReal_le_one⟩
    have hgap := positive_linear_gap p0 (fun j => ∫ ω, X j ω ∂P) hp hQ0
      ⟨i, positive_tail_of_mean P (X i) (hn i) (hi i) hxi⟩ hm hsp
    refine ⟨fun _ => 0, ?_⟩
    rw [zero_expectation P X hX hn hi hind]
    exact (mul_le_mul_of_nonneg_left hsum hc.le).trans hgap.le
  · have hz : P.real {ω | SamuelCahnProphet.Median.maxX X ω ≤ 0} < Real.exp (-1) := by
      rw [max_le_product P X hind]
      have he : (∏ i, P.real {ω | X i ω ≤ 0}) = ∏ i, (1-p0 i) := by
        apply Finset.prod_congr rfl
        intro i _
        exact (tail_partition P (X i) (hX i) 0).1.symm
      rw [he]
      exact lt_of_not_ge hQ0
    obtain ⟨a, ha, hlo, hhi⟩ := max_quantile P (SamuelCahnProphet.Median.maxX X) (measurable_max X hX)
      (Real.exp (-1)) (Real.exp_pos _) (by simp) hz
    obtain ⟨s, hs, hQ⟩ := tie_probability P X hX hind a (Real.exp (-1)) hlo hhi
    let p := fun i => P.real {ω | a < X i ω} + s * P.real {ω | X i ω = a}
    let u := fun i => ∫ ω, max (X i ω-a) 0 ∂P
    have hu : ∀ i, 0 ≤ u i := fun i => integral_nonneg fun ω => le_max_right _ _
    have hui (i : Fin n) : Integrable (fun ω => max (X i ω-a) 0) P := ((hi i).sub (integrable_const a)).pos_part
    have hbound : M ≤ a + ∑ i, u i := max_surplus_bound P X hX hn hi a
    have he : (∫ ω, mixedReward a s X ω ∂P) = a*c + ∑ i, u i * coeff p i := by
      rw [mixed_expectation P X hX hn hi hind a s hs, hQ]
    by_cases hsu : 0 < ∑ i, u i
    · have hg := revenue_surplus_gap p u (tail_prob_bounds P X hX a s hs) hQ a hu hsu
      apply strict_mixed_to_threshold P X hX hn hi a s (c*M) ha hs
      rw [he]
      exact (mul_le_mul_of_nonneg_left hbound hc.le).trans_lt hg
    · have hzero : ∑ i, u i = 0 := le_antisymm (le_of_not_gt hsu) (Finset.sum_nonneg fun i _ => hu i)
      have huz (i : Fin n) : u i = 0 := by
        have hh := Finset.single_le_sum (fun j _ => hu j) (Finset.mem_univ i)
        rw [hzero] at hh
        exact le_antisymm hh (hu i)
      have hup (i : Fin n) : ∀ᵐ ω ∂P, X i ω ≤ a := by
        have hh := (integral_eq_zero_iff_of_nonneg (fun ω => le_max_right (X i ω-a) 0) (hui i)).mp (huz i)
        filter_upwards [hh] with ω hω
        have := le_max_left (X i ω-a) 0
        change max (X i ω-a) 0 = 0 at hω
        linarith
      have hmaxle : ∀ᵐ ω ∂P, SamuelCahnProphet.Median.maxX X ω ≤ a := by
        filter_upwards [ae_all_iff.mpr hup] with ω hω
        exact Finset.sup'_le _ _ (fun i _ => hω i)
      have hMa : M ≤ a := by simpa [hzero] using hbound
      by_cases hlt : M < a
      · apply strict_mixed_to_threshold P X hX hn hi a s (c*M) ha hs
        rw [he]
        have hzsum : (∑ i, u i * coeff p i) = 0 := by simp [huz]
        rw [hzsum, add_zero]
        simpa only [mul_comm a c] using mul_lt_mul_of_pos_left hlt hc
      · have hMeq : M = a := le_antisymm hMa (le_of_not_gt hlt)
        have hmaxeq : ∀ᵐ ω ∂P, SamuelCahnProphet.Median.maxX X ω = a := by
          apply (integral_eq_iff_of_ae_le hmi (integrable_const a) hmaxle).mp
          simpa [M] using hMeq
        obtain ⟨i, _, heq⟩ := CTPeer.degenerate_threshold P X hind a ha.le hup hmaxeq
        refine ⟨CTPeer.singleThreshold i, ?_⟩
        rw [heq]
        change c*M ≤ a
        rw [hMeq]
        have hc1 : c ≤ 1 := by dsimp [c]; linarith [Real.exp_pos (-1)]
        exact mul_le_of_le_one_left ha.le hc1

end CTProof

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace CTProof
lemma nonnegative_root {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hn : ∀ i ω, 0 ≤ X i ω) (hind : iIndepFun X P) :
    ∃ τ : Fin n → ENNReal, ENNReal.ofReal (1-Real.exp (-1)) *
      (∫⁻ ω, ENNReal.ofReal (SamuelCahnProphet.Median.maxX X ω) ∂P) ≤
      ∫⁻ ω, ENNReal.ofReal (CorreaThreshold.Nonadaptive.ratio τ X ω) ∂P := by
  classical
  by_cases hall : ∀ i, Integrable (X i) P
  · have hm := integrable_max P X hX hn hall
    have he := ofReal_integral_eq_lintegral_ofReal hm (Filter.Eventually.of_forall (max_nonneg X hn))
    by_cases hp : 0 < ∫ ω, SamuelCahnProphet.Median.maxX X ω ∂P
    · obtain ⟨τ, hτ⟩ := finite_positive_exists P X hX hn hind hall hp
      refine ⟨τ, ?_⟩
      have hc : 0 ≤ 1-Real.exp (-1) := by
        have h : Real.exp (-1) ≤ 1 := by simp
        linarith
      have hg := ENNReal.ofReal_le_ofReal hτ
      rw [ENNReal.ofReal_mul hc, he,
        ofReal_integral_eq_lintegral_ofReal (integrable_ratio P τ X hX hn hall)
          (Filter.Eventually.of_forall (ratio_nonneg τ X hn))] at hg
      exact hg
    · refine ⟨fun _ => ⊤, ?_⟩
      rw [← he, ENNReal.ofReal_of_nonpos (le_of_not_gt hp), mul_zero]
      exact zero_le
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have ht : (∫⁻ ω, ENNReal.ofReal (X i ω) ∂P) = ⊤ := by
      by_contra h
      exact hi ((lintegral_ofReal_ne_top_iff_integrable (hX i).aestronglyMeasurable
        (Filter.Eventually.of_forall (hn i))).mp h)
    refine ⟨CTPeer.singleThreshold i, ?_⟩
    rw [CTPeer.single_expectation, ht]
    exact le_top
end CTProof

namespace CorreaThreshold.Nonadaptive
open MeasureTheory ProbabilityTheory
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} [NeZero n]
    (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω)
    (hind : iIndepFun X P) :
    ∃ τ : Fin n → ENNReal,
      ENNReal.ofReal (1 - Real.exp (-1)) *
        (∫⁻ ω, ENNReal.ofReal (SamuelCahnProphet.Median.maxX X ω) ∂P) ≤
      (∫⁻ ω, ENNReal.ofReal (ratio τ X ω) ∂P) := by
  let Y : Fin n → Ω → ℝ := fun i ω => max (X i ω) 0
  have hym : ∀ i, Measurable (Y i) := fun i => (hXm i).max measurable_const
  have hyn : ∀ i ω, 0 ≤ Y i ω := fun i ω => le_max_right _ _
  have hy : ∀ i, X i =ᵐ[P] Y i := by
    intro i
    filter_upwards [hXnn i] with ω hω
    exact (max_eq_left hω).symm
  have hyind := hind.congr hy
  obtain ⟨τ, hτ⟩ := CTProof.nonnegative_root P Y hym hyn hyind
  have hall : ∀ᵐ ω ∂P, ∀ i, X i ω = Y i ω := Filter.eventually_all.mpr hy
  have hm : (∫⁻ ω, ENNReal.ofReal (SamuelCahnProphet.Median.maxX X ω) ∂P) =
      ∫⁻ ω, ENNReal.ofReal (SamuelCahnProphet.Median.maxX Y ω) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hall] with ω hω
    unfold SamuelCahnProphet.Median.maxX
    simp only [hω]
  have hr : (∫⁻ ω, ENNReal.ofReal (ratio τ X ω) ∂P) =
      ∫⁻ ω, ENNReal.ofReal (ratio τ Y ω) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hall] with ω hω
    unfold ratio accepted
    simp only [hω]
  exact ⟨τ, by rw [hm, hr]; exact hτ⟩
end CorreaThreshold.Nonadaptive

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} [NeZero n]
    (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω)
    (hind : iIndepFun X P) :
    ∃ τ : Fin n → ENNReal,
      ENNReal.ofReal (1 - Real.exp (-1)) *
        (∫⁻ ω, ENNReal.ofReal (SamuelCahnProphet.Median.maxX X ω) ∂P) ≤
      (∫⁻ ω, ENNReal.ofReal (CorreaThreshold.Nonadaptive.ratio τ X ω) ∂P) :=
  CorreaThreshold.Nonadaptive.theorem_1 P X hXm hXnn hind
