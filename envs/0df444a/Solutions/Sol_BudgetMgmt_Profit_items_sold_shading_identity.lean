-- Prove2me | solution 1 for BudgetMgmt.Profit.items_sold_shading_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:12:35.359587+00:00
-- url     : https://prove2.me/submissions/53332269-eda8-4304-a205-baa7a028589b

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model

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

open Classical in
theorem solution_aux_sum_first {n : ℕ} (W : Fin n → Prop) :
    (∑ i, (if W i ∧ ∀ j, j < i → ¬ W j then (1 : ℝ) else 0)) = if ∃ i, W i then 1 else 0 := by
  by_cases h : ∃ i, W i
  · rw [if_pos h]
    have hne : (Finset.univ.filter W).Nonempty := by
      obtain ⟨i, hi⟩ := h; exact ⟨i, by simp [hi]⟩
    set i0 := (Finset.univ.filter W).min' hne with hi0
    have hW0 : W i0 := by
      have := Finset.min'_mem _ hne
      rw [← hi0, Finset.mem_filter] at this
      exact this.2
    have hmin : ∀ j, W j → i0 ≤ j := fun j hj =>
      Finset.min'_le _ _ (by simp [hj])
    rw [Finset.sum_eq_single i0]
    · rw [if_pos ⟨hW0, fun j hj hWj => absurd (hmin j hWj) (not_le.mpr hj)⟩]
    · intro b _ hb
      rw [if_neg]
      rintro ⟨hWb, hfirst⟩
      exact hfirst i0 (lt_of_le_of_ne (hmin b hWb) (Ne.symm hb)) hW0
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    rintro ⟨hWi, -⟩
    exact h ⟨i, hWi⟩

open Classical in
theorem solution_aux_itemsSold {n : ℕ} (P : SymInstance n) (m : Mech) (s : Fin n → ℝ)
    (θ : ℝ) (hW : ∀ x, (∃ i, wins P.c m s x i) ↔ ∃ j, θ ≤ x j) :
    itemsSold P m s = P.T * (1 - cdf P (fun _ => θ)) := by
  have hprob := solution_aux_isProb P
  unfold itemsSold cdf
  congr 1
  have hint : ∀ i, Integrable (fun x => alloc P.c m s x i) P.law := by
    intro i
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (solution_aux_alloc_meas P.c m s i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    unfold alloc
    split_ifs <;> simp
  rw [← integral_finset_sum _ (fun i _ => hint i)]
  have hsum : ∀ x, (∑ i, alloc P.c m s x i) =
      Set.indicator {x | ∃ j, θ ≤ x j} (1 : (Fin n → ℝ) → ℝ) x := by
    intro x
    unfold alloc
    rw [solution_aux_sum_first (fun i => wins P.c m s x i)]
    simp only [Set.indicator, Set.mem_setOf_eq, hW x, Pi.one_apply]
  simp_rw [hsum]
  have hmeasS : MeasurableSet {x : Fin n → ℝ | ∃ j, θ ≤ x j} := by
    have : {x : Fin n → ℝ | ∃ j, θ ≤ x j} = ⋃ j, {x | θ ≤ x j} := by ext; simp
    rw [this]
    exact MeasurableSet.iUnion fun j => measurableSet_le measurable_const (measurable_pi_apply j)
  rw [integral_indicator_one hmeasS]
  have hcompl : {x : Fin n → ℝ | ∃ j, θ ≤ x j} = {x | ∀ j, x j < θ}ᶜ := by
    ext x; simp
  have hmeasL : MeasurableSet {x : Fin n → ℝ | ∀ j, x j < θ} := by
    have : {x : Fin n → ℝ | ∀ j, x j < θ} = ⋂ j, {x | x j < θ} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun j => measurableSet_lt (measurable_pi_apply j) measurable_const
  rw [hcompl, measureReal_compl hmeasL, probReal_univ]
  congr 1
  apply measureReal_congr
  have hac : P.law ≪ volume := withDensity_absolutelyContinuous _ _
  have hne : ∀ᵐ x ∂P.law, ∀ j, x j ≠ θ := by
    rw [ae_all_iff]
    intro j
    apply hac.ae_le
    rw [volume_pi]
    exact Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) j θ
  filter_upwards [hne] with x hx
  simp only [eq_iff_iff]
  constructor
  · intro h j; exact (h j).le
  · intro h j; exact lt_of_le_of_ne (h j) (hx j)

theorem solution_aux_W_thr {n : ℕ} (c τ : ℝ) (hτ : 0 ≤ τ) (x : Fin n → ℝ) :
    (∃ i, wins c .thresholding (sym τ) x i) ↔ ∃ j, τ ≤ x j := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (max_le_iff.1 hi).2⟩
  · rintro ⟨j, hj⟩
    cases n with
    | zero => exact j.elim0
    | succ k =>
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ x ⟨j, Finset.mem_univ _⟩
    refine ⟨i, ?_⟩
    show max (compQual (sym τ) x i) τ ≤ x i
    have hτi : τ ≤ x i := hj.trans (hi j (Finset.mem_univ _))
    refine max_le ?_ hτi
    unfold compQual
    rw [Finset.fold_max_le]
    exact ⟨hτ.trans hτi, fun k _ => hi k (Finset.mem_univ _)⟩

theorem solution_aux_W_sh {n : ℕ} (c μ : ℝ) (hc : 0 < c) (hμ : 0 ≤ μ) (x : Fin n → ℝ) :
    (∃ i, wins c .shading (sym μ) x i) ↔ ∃ j, (1 + μ) * c ≤ x j := by
  have h1μ : 0 < 1 + μ := by linarith
  constructor
  · rintro ⟨i, hi⟩
    have hi' : max (compShaded (sym μ) x i) c ≤ x i / (1 + μ) := hi
    refine ⟨i, ?_⟩
    have := (max_le_iff.1 hi').2
    rw [le_div_iff₀ h1μ] at this
    linarith
  · rintro ⟨j, hj⟩
    cases n with
    | zero => exact j.elim0
    | succ k =>
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ x ⟨j, Finset.mem_univ _⟩
    refine ⟨i, ?_⟩
    show max (compShaded (sym μ) x i) c ≤ x i / (1 + μ)
    have hci : (1 + μ) * c ≤ x i := hj.trans (hi j (Finset.mem_univ _))
    have hc' : c ≤ x i / (1 + μ) := by rw [le_div_iff₀ h1μ]; linarith
    refine max_le ?_ hc'
    unfold compShaded
    rw [Finset.fold_max_le]
    refine ⟨hc.le.trans hc', fun k _ => ?_⟩
    simp only [sym]
    exact div_le_div_of_nonneg_right (hi k (Finset.mem_univ _)) h1μ.le

/-- pointwise: bid shading with `μ` is reserve pricing at `(1+μ)c` with payments scaled by `1/(1+μ)` -/
theorem solution_aux_maxeq {n : ℕ} (c μ : ℝ) (hc : 0 < c) (hμ : 0 ≤ μ) (x : Fin n → ℝ)
    (i : Fin n) :
    max (compShaded (sym μ) x i) c =
      max (compQual (sym ((1 + μ) * c)) x i) ((1 + μ) * c) / (1 + μ) := by
  have h1μ : 0 < 1 + μ := by linarith
  have key : ∀ y : ℝ, max (compShaded (sym μ) x i) c ≤ y ↔
      max (compQual (sym ((1 + μ) * c)) x i) ((1 + μ) * c) / (1 + μ) ≤ y := by
    intro y
    rw [div_le_iff₀ h1μ]
    unfold compShaded compQual
    rw [max_le_iff, max_le_iff, Finset.fold_max_le, Finset.fold_max_le]
    constructor
    · rintro ⟨⟨h0, h⟩, hcy⟩
      refine ⟨⟨by nlinarith, fun j hj => ?_⟩, by nlinarith⟩
      rw [Finset.mem_filter] at hj
      have := h j (Finset.mem_filter.2 ⟨hj.1, hj.2.1⟩)
      simp only [sym] at this
      rw [div_le_iff₀ h1μ] at this
      linarith
    · rintro ⟨⟨h0, h⟩, hcy⟩
      have hcy' : c ≤ y := by nlinarith
      refine ⟨⟨hc.le.trans hcy', fun j hj => ?_⟩, hcy'⟩
      rw [Finset.mem_filter] at hj
      simp only [sym]
      rw [div_le_iff₀ h1μ]
      by_cases hj' : (1 + μ) * c ≤ x j
      · have := h j (Finset.mem_filter.2 ⟨hj.1, hj.2, hj'⟩)
        linarith
      · push Not at hj'
        linarith
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

open Classical in
theorem solution_aux_payment_sh {n : ℕ} (c μ : ℝ) (hc : 0 < c) (hμ : 0 ≤ μ) (x : Fin n → ℝ)
    (i : Fin n) :
    payment c .shading (sym μ) x i = payment c .reserve (sym ((1 + μ) * c)) x i / (1 + μ) := by
  have h1μ : 0 < 1 + μ := by linarith
  have hw : ∀ j, wins c .shading (sym μ) x j ↔ wins c .reserve (sym ((1 + μ) * c)) x j := by
    intro j
    show max (compShaded (sym μ) x j) c ≤ x j / (1 + μ) ↔
      max (compQual (sym ((1 + μ) * c)) x j) ((1 + μ) * c) ≤ x j
    rw [solution_aux_maxeq c μ hc hμ x j, div_le_div_iff_of_pos_right h1μ]
  have ha : alloc c .shading (sym μ) x i = alloc c .reserve (sym ((1 + μ) * c)) x i := by
    unfold alloc
    exact if_congr (and_congr (hw i) (forall_congr' fun j => imp_congr_right fun _ =>
      not_congr (hw j))) rfl rfl
  unfold payment
  rw [ha, mul_div_assoc]
  congr 1
  exact solution_aux_maxeq c μ hc hμ x i

theorem solution {n : ℕ} [NeZero n] (P : SymInstance n) :
    (∀ τ : ℝ, 0 ≤ τ → itemsSold P .thresholding (sym τ) = P.T * (1 - cdf P (sym τ))) ∧
    (∀ r : ℝ, 0 ≤ r → itemsSold P .reserve (sym r) = P.T * (1 - cdf P (sym r))) ∧
    (∀ μ : ℝ, 0 ≤ μ →
      itemsSold P .shading (sym μ) = P.T * (1 - cdf P (sym ((1 + μ) * P.c)))) ∧
    (∀ μ : ℝ, 0 ≤ μ → G1 P .shading μ = G1 P .reserve ((1 + μ) * P.c) / (1 + μ)) := by
  refine ⟨fun τ hτ => ?_, fun r hr => ?_, fun μ hμ => ?_, fun μ hμ => ?_⟩
  · exact solution_aux_itemsSold P _ _ τ (solution_aux_W_thr P.c τ hτ)
  · exact solution_aux_itemsSold P _ _ r (solution_aux_W_thr P.c r hr)
  · exact solution_aux_itemsSold P _ _ _ (solution_aux_W_sh P.c μ P.c_pos hμ)
  · unfold G1 expend
    rw [mul_div_assoc, ← integral_div]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
      solution_aux_payment_sh P.c μ P.c_pos hμ x 0)
