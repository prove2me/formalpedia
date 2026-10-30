-- Prove2me | solution 1 for BudgetMgmt.Profit.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:19:13.598028+00:00
-- url     : https://prove2.me/submissions/f2ca7cae-e12a-4051-9767-2cdc09d1940b

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model
import Theorems.Thm_BudgetMgmt_Profit_G1_thresholding_strictAntiOn
import Theorems.Thm_BudgetMgmt_Profit_items_sold_shading_identity

open BudgetMgmt.Profit MeasureTheory

theorem solution_aux_law_univ {n : ℕ} (P : SymInstance n) : P.law Set.univ = 1 := by
  have hint : Integrable P.f := by
    by_contra h
    have := integral_undef h
    rw [P.f_integral] at this
    exact one_ne_zero this
  unfold SymInstance.law
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall P.f_nonneg),
    P.f_integral, ENNReal.ofReal_one]

theorem solution_aux_isProb {n : ℕ} (P : SymInstance n) : IsProbabilityMeasure P.law :=
  ⟨solution_aux_law_univ P⟩

theorem solution_aux_measurable_fold {n : ℕ} (s : Finset (Fin n))
    (g : Fin n → (Fin n → ℝ) → ℝ) (hg : ∀ j, Measurable (g j)) :
    Measurable (fun x => s.fold max 0 (fun j => g j x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.fold_insert ha]
    exact (hg a).max ih

theorem solution_aux_fold_eq' {n : ℕ} {s t : Finset (Fin n)} {f g : Fin n → ℝ}
    (h : ∀ y, 0 ≤ y → ((∀ j ∈ s, f j ≤ y) ↔ (∀ j ∈ t, g j ≤ y))) :
    s.fold max 0 f = t.fold max 0 g := by
  have key : ∀ y, s.fold max 0 f ≤ y ↔ t.fold max 0 g ≤ y := by
    intro y
    rw [Finset.fold_max_le, Finset.fold_max_le]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨h0, (h y h0).1 h1⟩
    · rintro ⟨h0, h1⟩; exact ⟨h0, (h y h0).2 h1⟩
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

theorem solution_aux_compQual_meas {n : ℕ} (s : Fin n → ℝ) (i : Fin n) :
    Measurable (fun x => compQual s x i) := by
  classical
  have : (fun x => compQual s x i) = fun x => (Finset.univ.filter (fun j => j ≠ i)).fold max 0
      (fun j => if s j ≤ x j then x j else 0) := by
    funext x
    unfold compQual
    apply solution_aux_fold_eq'
    intro y hy
    constructor
    · intro h j hj
      rw [Finset.mem_filter] at hj
      split_ifs with h'
      · exact h j (Finset.mem_filter.2 ⟨hj.1, hj.2, h'⟩)
      · exact hy
    · intro h j hj
      rw [Finset.mem_filter] at hj
      have := h j (Finset.mem_filter.2 ⟨hj.1, hj.2.1⟩)
      rwa [if_pos hj.2.2] at this
  rw [this]
  apply solution_aux_measurable_fold
  intro j
  exact Measurable.ite (measurableSet_le measurable_const (measurable_pi_apply j))
    (measurable_pi_apply j) measurable_const

theorem solution_aux_compShaded_meas {n : ℕ} (s : Fin n → ℝ) (i : Fin n) :
    Measurable (fun x => compShaded s x i) := by
  unfold compShaded
  apply solution_aux_measurable_fold
  intro j
  exact (measurable_pi_apply j).div_const _

theorem solution_aux_wins_meas {n : ℕ} (c : ℝ) (m : Mech) (s : Fin n → ℝ) (i : Fin n) :
    MeasurableSet {x | wins c m s x i} := by
  cases m
  · exact measurableSet_le ((solution_aux_compQual_meas s i).max measurable_const)
      (measurable_pi_apply i)
  · exact measurableSet_le ((solution_aux_compQual_meas s i).max measurable_const)
      (measurable_pi_apply i)
  · exact measurableSet_le ((solution_aux_compShaded_meas s i).max measurable_const)
      ((measurable_pi_apply i).div_const _)

open Classical in
theorem solution_aux_alloc_meas {n : ℕ} (c : ℝ) (m : Mech) (s : Fin n → ℝ) (i : Fin n) :
    Measurable (fun x => alloc c m s x i) := by
  unfold alloc
  refine Measurable.ite ?_ measurable_const measurable_const
  have : {x | wins c m s x i ∧ ∀ j, j < i → ¬ wins c m s x j} =
      {x | wins c m s x i} ∩ ⋂ j ∈ Finset.univ.filter (fun j => j < i), {x | wins c m s x j}ᶜ := by
    ext x; simp
  rw [this]
  exact (solution_aux_wins_meas c m s i).inter
    (Finset.measurableSet_biInter _ fun j _ => (solution_aux_wins_meas c m s j).compl)


theorem solution_aux_compQual_le {n : ℕ} (s x : Fin n → ℝ) (i : Fin n) :
    compQual s x i ≤ ∑ j, |x j| := by
  unfold compQual
  rw [Finset.fold_max_le]
  refine ⟨Finset.sum_nonneg fun j _ => abs_nonneg _, fun j _ => ?_⟩
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |x j|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ j))

theorem solution_aux_compQual_nonneg {n : ℕ} (s x : Fin n → ℝ) (i : Fin n) :
    0 ≤ compQual s x i := by
  unfold compQual
  rw [Finset.le_fold_max]; exact Or.inl le_rfl

theorem solution_aux_compShaded_nonneg {n : ℕ} (s x : Fin n → ℝ) (i : Fin n) :
    0 ≤ compShaded s x i := by
  unfold compShaded
  rw [Finset.le_fold_max]; exact Or.inl le_rfl

theorem solution_aux_sumabs_int {n : ℕ} (P : SymInstance n) :
    Integrable (fun x : Fin n → ℝ => ∑ j, |x j|) P.law :=
  integrable_finset_sum _ fun j _ => (P.moment j).abs

open Classical in
theorem solution_aux_alloc_bound {n : ℕ} (c : ℝ) (m : Mech) (s x : Fin n → ℝ) (i : Fin n) :
    0 ≤ alloc c m s x i ∧ alloc c m s x i ≤ 1 := by
  unfold alloc; split_ifs <;> simp

/-- the box of value vectors where buyer `0`'s value lies in `(lo, hi)` and every rival's in `(0, lo)`
has positive probability. -/
theorem solution_aux_box_pos {n : ℕ} [NeZero n] (P : SymInstance n) (lo hi : ℝ) (hlo : 0 < lo)
    (hlh : lo < hi) (hhi : ENNReal.ofReal hi ≤ P.vbar) :
    P.law (Set.univ.pi (fun j : Fin n => if j = 0 then Set.Ioo lo hi else Set.Ioo 0 lo)) ≠ 0 := by
  set S := Set.univ.pi (fun j : Fin n => if j = 0 then Set.Ioo lo hi else Set.Ioo 0 lo) with hS
  have hmeasf : Measurable (fun x => ENNReal.ofReal (P.f x)) :=
    ENNReal.measurable_ofReal.comp P.f_measurable
  unfold SymInstance.law
  rw [Ne, withDensity_apply_eq_zero hmeasf]
  have hsub : S ⊆ {x | ENNReal.ofReal (P.f x) ≠ 0} := by
    intro x hx
    have hx' : ∀ j, x j ∈ (if j = 0 then Set.Ioo lo hi else Set.Ioo 0 lo) := fun j =>
      hx j (Set.mem_univ j)
    have hpos : 0 < P.f x := by
      apply P.f_pos
      intro j
      have hj := hx' j
      have hlt : x j < hi := by
        split_ifs at hj with h
        · exact hj.2
        · exact hj.2.trans hlh
      have h0 : 0 < x j := by
        split_ifs at hj with h
        · exact hlo.trans hj.1
        · exact hj.1
      exact ⟨h0, lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (h0.trans hlt)).2 hlt) hhi⟩
    simp only [Set.mem_setOf_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hpos
  rw [Set.inter_eq_right.2 hsub, hS, volume_pi_pi]
  rw [Finset.prod_eq_zero_iff]
  rintro ⟨j, -, hj⟩
  split_ifs at hj with h
  · rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hj; linarith
  · rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hj; linarith

/-- strict comparison of integrals from a pointwise inequality, strict by `c` on a non-null set. -/
theorem solution_aux_strict {n : ℕ} (P : SymInstance n) (g h : (Fin n → ℝ) → ℝ)
    (hg : Integrable g P.law) (hh : Integrable h P.law) (hle : ∀ x, h x ≤ g x)
    (S : Set (Fin n → ℝ)) (hS : MeasurableSet S) (hS0 : P.law S ≠ 0) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ x ∈ S, h x + c ≤ g x) : ∫ x, h x ∂P.law < ∫ x, g x ∂P.law := by
  have hprob := solution_aux_isProb P
  have h1 : ∫ x, (g x - h x) ∂P.law ≥ ∫ x, S.indicator (fun _ => c) x ∂P.law := by
    apply integral_mono ((integrable_const c).indicator hS) (hg.sub hh)
    intro x
    show S.indicator (fun _ => c) x ≤ g x - h x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]; linarith [hgap x hx]
    · rw [Set.indicator_of_notMem hx]; linarith [hle x]
  rw [integral_indicator_const _ hS, integral_sub hg hh] at h1
  have hpos : 0 < P.law.real S := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hS0 (measure_ne_top _ _)
  have : 0 < P.law.real S • c := by rw [smul_eq_mul]; positivity
  linarith

open Classical in
theorem solution_aux_alloc0 {n : ℕ} [NeZero n] (c : ℝ) (m : Mech) (s x : Fin n → ℝ) :
    alloc c m s x 0 = if wins c m s x 0 then 1 else 0 := by
  unfold alloc
  exact if_congr ⟨fun h => h.1, fun h => ⟨h, fun j hj => absurd hj (Fin.not_lt_zero j)⟩⟩ rfl rfl

theorem solution_aux_pay_int {n : ℕ} (P : SymInstance n) (m : Mech) (s : Fin n → ℝ) (i : Fin n)
    (hm : m ≠ .shading) :
    Integrable (fun x => payment P.c m s x i) P.law := by
  have hprob := solution_aux_isProb P
  have hmeasp : Measurable (fun x => price P.c m s x i) := by
    cases m
    · exact (solution_aux_compQual_meas s i).max measurable_const
    · exact (solution_aux_compQual_meas s i).max measurable_const
    · exact absurd rfl hm
  refine Integrable.mono' ((solution_aux_sumabs_int P).add (integrable_const (|P.c| + |s i|)))
    ((solution_aux_alloc_meas P.c m s i).mul hmeasp).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  unfold payment
  obtain ⟨a0, a1⟩ := solution_aux_alloc_bound P.c m s x i
  have hq := solution_aux_compQual_le s x i
  have hq0 := solution_aux_compQual_nonneg s x i
  have hmax : ∀ t : ℝ, |t| ≤ |P.c| + |s i| →
      |max (compQual s x i) t| ≤ (∑ j, |x j|) + (|P.c| + |s i|) := by
    intro t ht
    have hB : 0 ≤ |P.c| + |s i| := by positivity
    rw [abs_le]; constructor
    · have := le_max_left (compQual s x i) t; linarith
    · exact max_le (by linarith) (by linarith [le_abs_self t])
  have hpr : |price P.c m s x i| ≤ (∑ j, |x j|) + (|P.c| + |s i|) := by
    cases m
    · exact hmax P.c (by linarith [abs_nonneg (s i)])
    · exact hmax (s i) (by linarith [abs_nonneg P.c])
    · exact absurd rfl hm
  show ‖alloc P.c m s x i * price P.c m s x i‖ ≤ (∑ j, |x j|) + (|P.c| + |s i|)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg a0]
  calc alloc P.c m s x i * |price P.c m s x i| ≤ 1 * |price P.c m s x i| :=
        mul_le_mul_of_nonneg_right a1 (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hpr


theorem solution_aux_ae_supp {n : ℕ} (P : SymInstance n) :
    ∀ᵐ x ∂P.law, ∀ j, ENNReal.ofReal (x j) < P.vbar := by
  have hmeasf : Measurable (fun x => ENNReal.ofReal (P.f x)) :=
    ENNReal.measurable_ofReal.comp P.f_measurable
  unfold SymInstance.law
  rw [ae_withDensity_iff hmeasf]
  refine Filter.Eventually.of_forall fun x hx j => ?_
  by_contra hj
  have : P.f x = 0 := P.f_zero_off x (fun h => hj (h j).2)
  exact hx (by simp [this])

theorem solution_aux_cdf_le_one {n : ℕ} (P : SymInstance n) (z : Fin n → ℝ) : cdf P z ≤ 1 := by
  have := solution_aux_isProb P
  exact measureReal_le_one

theorem solution_aux_cdf_mono {n : ℕ} (P : SymInstance n) (a b : ℝ) (hab : a ≤ b) :
    cdf P (sym a) ≤ cdf P (sym b) := by
  have := solution_aux_isProb P
  unfold cdf
  apply measureReal_mono _ (measure_ne_top _ _)
  intro x hx j
  exact (hx j).trans hab

theorem solution_aux_cdf_top {n : ℕ} (P : SymInstance n) (t : ℝ)
    (ht : P.vbar ≤ ENNReal.ofReal t) : cdf P (sym t) = 1 := by
  have := solution_aux_isProb P
  set S := {x : Fin n → ℝ | ∀ j, x j ≤ sym t j} with hS
  have hmeas : MeasurableSet S := by
    have : S = ⋂ j, {x | x j ≤ t} := by ext; simp [hS, sym]
    rw [this]
    exact MeasurableSet.iInter fun j => measurableSet_le (measurable_pi_apply j) measurable_const
  have hnull : P.law Sᶜ = 0 := by
    have h := solution_aux_ae_supp P
    rw [ae_iff] at h
    refine measure_mono_null ?_ h
    intro x hx
    simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le, sym] at hx ⊢
    obtain ⟨j, hj⟩ := hx
    refine ⟨j, fun h => ?_⟩
    have : P.vbar ≤ ENNReal.ofReal (x j) := ht.trans (ENNReal.ofReal_le_ofReal hj.le)
    exact absurd (h.trans_le this) (lt_irrefl _)
  have hc := measureReal_compl (μ := P.law) hmeas
  rw [probReal_univ] at hc
  have h0 : P.law.real Sᶜ = 0 := by rw [measureReal_def, hnull]; rfl
  unfold cdf
  rw [← hS]
  linarith

theorem solution_aux_G1T_zero {n : ℕ} [NeZero n] (P : SymInstance n) (t : ℝ)
    (ht : P.vbar ≤ ENNReal.ofReal t) : G1 P .thresholding t = 0 := by
  unfold G1 expend
  have : (∫ x, payment P.c .thresholding (sym t) x 0 ∂P.law) = 0 := by
    rw [← integral_zero (Fin n → ℝ) ℝ (μ := P.law)]
    apply integral_congr_ae
    filter_upwards [solution_aux_ae_supp P] with x hx
    unfold payment
    rw [solution_aux_alloc0, if_neg]
    · simp
    · intro hw
      have hw' : max (compQual (sym t) x 0) t ≤ x 0 := hw
      have : P.vbar ≤ ENNReal.ofReal (x 0) :=
        ht.trans (ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans hw'))
      exact absurd ((hx 0).trans_le this) (lt_irrefl _)
  rw [this, mul_zero]

/-- thresholding pays at most reserve pricing at the same symmetric parameter `r ≥ c`. -/
theorem solution_aux_GT_le_GR {n : ℕ} [NeZero n] (P : SymInstance n) (r : ℝ) (hr : P.c ≤ r) :
    G1 P .thresholding r ≤ G1 P .reserve r := by
  unfold G1 expend
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply integral_mono (solution_aux_pay_int P _ _ 0 (by decide))
    (solution_aux_pay_int P _ _ 0 (by decide))
  intro x
  show alloc P.c .thresholding (sym r) x 0 * max (compQual (sym r) x 0) P.c ≤
    alloc P.c .reserve (sym r) x 0 * max (compQual (sym r) x 0) (sym r 0)
  have : alloc P.c .reserve (sym r) x 0 = alloc P.c .thresholding (sym r) x 0 := rfl
  rw [this]
  exact mul_le_mul_of_nonneg_left (max_le_max le_rfl hr)
    (solution_aux_alloc_bound P.c _ _ x 0).1

/-- `G^T₁(τ) < G^T₁(r)` for `c ≤ r < τ` whenever `F(r 1⃗) < 1`. -/
theorem solution_aux_GT_strict {n : ℕ} [NeZero n] (P : SymInstance n) (r τ : ℝ) (hr : P.c ≤ r)
    (hrt : r < τ) (hF : cdf P (sym r) < 1) : G1 P .thresholding τ < G1 P .thresholding r := by
  by_cases hτv : ENNReal.ofReal τ ≤ P.vbar
  · exact G1_thresholding_strictAntiOn P ⟨hr, (ENNReal.ofReal_le_ofReal hrt.le).trans hτv⟩
      ⟨hr.trans hrt.le, hτv⟩ hrt
  · push Not at hτv
    have hvt : P.vbar ≠ ⊤ := ne_top_of_lt hτv
    set v := P.vbar.toReal with hv
    have hov : ENNReal.ofReal v = P.vbar := ENNReal.ofReal_toReal hvt
    have hcv : P.c ≤ v := by
      have := P.c_lt_vbar
      rw [← hov] at this
      exact ((ENNReal.ofReal_lt_ofReal_iff'.1 this).1).le
    have hrv : r < v := by
      by_contra h
      push Not at h
      have := solution_aux_cdf_top P r (by rw [← hov]; exact ENNReal.ofReal_le_ofReal h)
      linarith
    rw [solution_aux_G1T_zero P τ hτv.le, ← solution_aux_G1T_zero P v hov.ge]
    exact G1_thresholding_strictAntiOn P ⟨hr, (ENNReal.ofReal_le_ofReal hrv.le).trans hov.le⟩
      ⟨hcv, hov.le⟩ hrv

theorem solution {n : ℕ} [NeZero n] (P : SymInstance n) (r τ : ℝ) (hr : P.c ≤ r)
    (hτ : P.c ≤ τ)
    (hI : itemsSold P .thresholding (sym τ) < itemsSold P .reserve (sym r)) :
    G1 P .thresholding τ < G1 P .reserve r := by
  obtain ⟨hIT, hIR, -, -⟩ := items_sold_shading_identity P
  have hc := P.c_pos
  rw [hIT τ (hc.le.trans hτ), hIR r (hc.le.trans hr)] at hI
  have hT : (0 : ℝ) < P.T := Nat.cast_pos.2 P.T_pos
  have hF : cdf P (sym r) < cdf P (sym τ) := by
    by_contra h; push Not at h; nlinarith
  have hrt : r < τ := by
    by_contra h; push Not at h
    linarith [solution_aux_cdf_mono P τ r h]
  exact (solution_aux_GT_strict P r τ hr hrt
    (hF.trans_le (solution_aux_cdf_le_one P _))).trans_le (solution_aux_GT_le_GR P r hr)
