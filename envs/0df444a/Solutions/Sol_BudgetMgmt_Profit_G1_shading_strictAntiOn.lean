-- Prove2me | solution 1 for BudgetMgmt.Profit.G1_shading_strictAntiOn
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:16:59.648269+00:00
-- url     : https://prove2.me/submissions/2043eb46-aea7-422a-8bf5-3a41609ab471

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

theorem solution_aux_compShaded_le {n : ℕ} (μ : ℝ) (hμ : 0 ≤ μ) (x : Fin n → ℝ) (i : Fin n) :
    compShaded (sym μ) x i ≤ ∑ j, |x j| := by
  unfold compShaded
  rw [Finset.fold_max_le]
  refine ⟨Finset.sum_nonneg fun j _ => abs_nonneg _, fun j _ => ?_⟩
  have h1 : x j / (1 + sym μ j) ≤ |x j| := by
    simp only [sym]
    rw [div_le_iff₀ (by linarith)]
    nlinarith [le_abs_self (x j), abs_nonneg (x j)]
  exact h1.trans (Finset.single_le_sum (f := fun j => |x j|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ j))

theorem solution_aux_pay_int_sh {n : ℕ} (P : SymInstance n) (μ : ℝ) (hμ : 0 ≤ μ) (i : Fin n) :
    Integrable (fun x => payment P.c .shading (sym μ) x i) P.law := by
  have hprob := solution_aux_isProb P
  have hmeasp : Measurable (fun x => price P.c .shading (sym μ) x i) :=
    (solution_aux_compShaded_meas _ i).max measurable_const
  refine Integrable.mono' ((solution_aux_sumabs_int P).add (integrable_const (|P.c|)))
    ((solution_aux_alloc_meas P.c _ _ i).mul hmeasp).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  unfold payment
  obtain ⟨a0, a1⟩ := solution_aux_alloc_bound P.c .shading (sym μ) x i
  have hq := solution_aux_compShaded_le μ hμ x i
  have hq0 := solution_aux_compShaded_nonneg (sym μ) x i
  have hpr : |price P.c .shading (sym μ) x i| ≤ (∑ j, |x j|) + |P.c| := by
    show |max (compShaded (sym μ) x i) P.c| ≤ _
    rw [abs_le]; constructor
    · have := le_max_left (compShaded (sym μ) x i) P.c; linarith [abs_nonneg P.c]
    · exact max_le (by linarith [abs_nonneg P.c]) (by linarith [le_abs_self P.c])
  show ‖alloc P.c .shading (sym μ) x i * price P.c .shading (sym μ) x i‖ ≤ (∑ j, |x j|) + |P.c|
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg a0]
  calc alloc P.c .shading (sym μ) x i * |price P.c .shading (sym μ) x i|
      ≤ 1 * |price P.c .shading (sym μ) x i| := mul_le_mul_of_nonneg_right a1 (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hpr

theorem solution_aux_wins_sh {n : ℕ} [NeZero n] (c μ : ℝ) (hc : 0 < c) (hμ : 0 ≤ μ)
    (x : Fin n → ℝ) :
    wins c .shading (sym μ) x 0 ↔ (1 + μ) * c ≤ x 0 ∧ ∀ j, j ≠ 0 → x j ≤ x 0 := by
  have h1μ : 0 < 1 + μ := by linarith
  show max (compShaded (sym μ) x 0) c ≤ x 0 / (1 + sym μ 0) ↔ _
  simp only [sym]
  unfold compShaded
  rw [max_le_iff, Finset.fold_max_le]
  constructor
  · rintro ⟨⟨-, h⟩, hc'⟩
    refine ⟨by have := (le_div_iff₀ h1μ).1 hc'; linarith, fun j hj => ?_⟩
    have := h j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
    simp only [sym] at this
    exact (div_le_div_iff_of_pos_right h1μ).1 this
  · rintro ⟨hc', h⟩
    refine ⟨⟨?_, fun j hj => ?_⟩, (le_div_iff₀ h1μ).2 (by linarith)⟩
    · apply div_nonneg _ h1μ.le; nlinarith
    · rw [Finset.mem_filter] at hj
      simp only [sym]
      exact (div_le_div_iff_of_pos_right h1μ).2 (h j hj.2)

theorem solution {n : ℕ} [NeZero n] (P : SymInstance n) :
    StrictAntiOn (G1 P .shading) {μ | 0 ≤ μ ∧ ENNReal.ofReal ((1 + μ) * P.c) ≤ P.vbar} := by
  intro a ha b hb hab
  have hc := P.c_pos
  have ha0 : 0 < (1 + a) * P.c := by have := ha.1; positivity
  have hlh : (1 + a) * P.c < (1 + b) * P.c := by nlinarith
  have hb0 : 0 ≤ b := ha.1.trans hab.le
  unfold G1 expend
  have hT : (0 : ℝ) < P.T := Nat.cast_pos.2 P.T_pos
  apply mul_lt_mul_of_pos_left _ hT
  set S := Set.univ.pi (fun j : Fin n => if j = 0 then Set.Ioo ((1 + a) * P.c) ((1 + b) * P.c)
    else Set.Ioo 0 ((1 + a) * P.c)) with hS
  apply solution_aux_strict P _ _ (solution_aux_pay_int_sh P a ha.1 0)
    (solution_aux_pay_int_sh P b hb0 0) _ S
    (MeasurableSet.univ_pi fun j => by split_ifs <;> exact measurableSet_Ioo)
    (solution_aux_box_pos P _ _ ha0 hlh hb.2) P.c hc
  · intro x hx
    have hx' : ∀ j, x j ∈ (if j = 0 then Set.Ioo ((1 + a) * P.c) ((1 + b) * P.c)
        else Set.Ioo 0 ((1 + a) * P.c)) := fun j => hx j (Set.mem_univ j)
    have h0 : (1 + a) * P.c < x 0 ∧ x 0 < (1 + b) * P.c := by simpa using hx' 0
    have hj : ∀ j, j ≠ 0 → x j < (1 + a) * P.c := by
      intro j hj; have := hx' j; rw [if_neg hj] at this; exact this.2
    unfold payment
    rw [solution_aux_alloc0, solution_aux_alloc0]
    have hwa : wins P.c .shading (sym a) x 0 :=
      (solution_aux_wins_sh P.c a hc ha.1 x).2 ⟨h0.1.le, fun j hj' => ((hj j hj').trans h0.1).le⟩
    have hwb : ¬ wins P.c .shading (sym b) x 0 := by
      rw [solution_aux_wins_sh P.c b hc hb0 x]
      rintro ⟨h, -⟩; linarith [h0.2]
    rw [if_pos hwa, if_neg hwb]
    show 0 * _ + P.c ≤ 1 * max (compShaded (sym a) x 0) P.c
    rw [zero_mul, zero_add, one_mul]; exact le_max_right _ _
  · intro x
    unfold payment
    rw [solution_aux_alloc0, solution_aux_alloc0]
    by_cases hwb : wins P.c .shading (sym b) x 0
    · have hwb' := (solution_aux_wins_sh P.c b hc hb0 x).1 hwb
      have hwa : wins P.c .shading (sym a) x 0 :=
        (solution_aux_wins_sh P.c a hc ha.1 x).2
          ⟨le_trans (by nlinarith) hwb'.1, hwb'.2⟩
      rw [if_pos hwb, if_pos hwa]
      show 1 * max (compShaded (sym b) x 0) P.c ≤ 1 * max (compShaded (sym a) x 0) P.c
      rw [one_mul, one_mul]
      have key : ∀ y, max (compShaded (sym a) x 0) P.c ≤ y →
          max (compShaded (sym b) x 0) P.c ≤ y := by
        intro y hy
        unfold compShaded at hy ⊢
        rw [max_le_iff, Finset.fold_max_le] at hy ⊢
        obtain ⟨⟨h0, h⟩, hcy⟩ := hy
        refine ⟨⟨h0, fun j hj => ?_⟩, hcy⟩
        have := h j hj
        simp only [sym] at this ⊢
        by_cases hxj : 0 ≤ x j
        · exact le_trans (div_le_div_of_nonneg_left hxj (by linarith [ha.1]) (by linarith)) this
        · have : x j / (1 + b) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
          linarith
      exact key _ le_rfl
    · rw [if_neg hwb, zero_mul]
      split_ifs
      · show 0 ≤ 1 * max (compShaded (sym a) x 0) P.c
        rw [one_mul]; exact le_max_of_le_right hc.le
      · simp
