-- Prove2me | solution 1 for BudgetMgmt.Profit.proposition_4_1_TS
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:35:24.716258+00:00
-- url     : https://prove2.me/submissions/fed7be9c-6afc-4a77-9e34-b9e045ac1497

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model
import Theorems.Thm_BudgetMgmt_Profit_G1_thresholding_strictAntiOn
import Theorems.Thm_BudgetMgmt_Profit_G1_shading_strictAntiOn

open BudgetMgmt.Profit MeasureTheory Filter Topology

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

/-- invariance of the law under permuting coordinates -/
theorem solution_aux_perm {n : ℕ} (P : SymInstance n) (σ : Equiv.Perm (Fin n))
    (g : (Fin n → ℝ) → ℝ) : ∫ x, g (x ∘ σ) ∂P.law = ∫ x, g x ∂P.law := by
  let φ := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have hφ : MeasurePreserving φ volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have hφx : ∀ y : Fin n → ℝ, φ y = y ∘ σ := by
    intro y; funext b
    simp [φ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  have hmeas : Measurable (fun x => ENNReal.ofReal (P.f x)) :=
    ENNReal.measurable_ofReal.comp P.f_measurable
  have hlt : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), ENNReal.ofReal (P.f x) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold SymInstance.law
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hlt,
    integral_withDensity_eq_integral_toReal_smul hmeas hlt]
  have h1 : ∀ x : Fin n → ℝ, (ENNReal.ofReal (P.f x)).toReal • g (x ∘ σ) =
      (fun y => (ENNReal.ofReal (P.f y)).toReal • g y) (φ x) := by
    intro x
    simp only [hφx]
    rw [P.f_exch]
  simp_rw [h1]
  exact hφ.integral_comp' (f := φ) (fun y => (ENNReal.ofReal (P.f y)).toReal • g y)


theorem solution_aux_noties_w {n : ℕ} (P : SymInstance n) (w : Fin n → ℝ) (hw : ∀ k, w k ≠ 0) :
    ∀ᵐ x ∂P.law, ∀ j k : Fin n, j ≠ k → w j * x j ≠ w k * x k := by
  have hac : P.law ≪ volume := withDensity_absolutelyContinuous _ _
  apply hac.ae_le
  have : ∀ j k : Fin n, j ≠ k → ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), w j * x j ≠ w k * x k := by
    intro j k hjk
    let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := w j • LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j -
      w k • LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k
    have hne : LinearMap.ker L ≠ ⊤ := by
      intro h
      have : Pi.single j (1 : ℝ) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
      simp [L, LinearMap.mem_ker, Pi.single_apply, hjk.symm, hw j] at this
    have h0 := Measure.addHaar_submodule volume (LinearMap.ker L) hne
    rw [ae_iff]
    refine measure_mono_null ?_ h0
    intro x hx
    simp only [Set.mem_setOf_eq, not_not] at hx
    simp [L, LinearMap.mem_ker, hx]
  have hall : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
      ∀ j k : Fin n, j ≠ k → w j * x j ≠ w k * x k := by
    refine ae_all_iff.2 fun j => ae_all_iff.2 fun k => ?_
    by_cases hjk : j = k
    · exact Filter.Eventually.of_forall fun _ h => absurd hjk h
    · filter_upwards [this j k hjk] with x hx _ using hx
  exact hall

theorem solution_aux_compQual_perm {n : ℕ} (p x : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : Fin n) : compQual (p ∘ σ) (x ∘ σ) j = compQual p x (σ j) := by
  unfold compQual
  apply solution_aux_fold_eq'
  intro y _
  constructor
  · intro h k' hk'
    rw [Finset.mem_filter] at hk'
    have := h (σ.symm k') (Finset.mem_filter.2 ⟨Finset.mem_univ _,
      fun e => hk'.2.1 (by rw [← e]; simp), by simpa using hk'.2.2⟩)
    simpa using this
  · intro h k hk
    rw [Finset.mem_filter] at hk
    exact h (σ k) (Finset.mem_filter.2 ⟨Finset.mem_univ _, fun e => hk.2.1 (σ.injective e),
      hk.2.2⟩)

theorem solution_aux_compShaded_perm {n : ℕ} (p x : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : Fin n) : compShaded (p ∘ σ) (x ∘ σ) j = compShaded p x (σ j) := by
  unfold compShaded
  apply solution_aux_fold_eq'
  intro y _
  constructor
  · intro h k' hk'
    rw [Finset.mem_filter] at hk'
    have := h (σ.symm k') (Finset.mem_filter.2 ⟨Finset.mem_univ _,
      fun e => hk'.2 (by rw [← e]; simp)⟩)
    simpa using this
  · intro h k hk
    rw [Finset.mem_filter] at hk
    exact h (σ k) (Finset.mem_filter.2 ⟨Finset.mem_univ _, fun e => hk.2 (σ.injective e)⟩)

theorem solution_aux_wins_perm {n : ℕ} (c : ℝ) (m : Mech) (p x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    wins c m (p ∘ σ) (x ∘ σ) j ↔ wins c m p x (σ j) := by
  cases m
  · show max (compQual (p ∘ σ) (x ∘ σ) j) (p (σ j)) ≤ x (σ j) ↔
      max (compQual p x (σ j)) (p (σ j)) ≤ x (σ j)
    rw [solution_aux_compQual_perm]
  · show max (compQual (p ∘ σ) (x ∘ σ) j) (p (σ j)) ≤ x (σ j) ↔
      max (compQual p x (σ j)) (p (σ j)) ≤ x (σ j)
    rw [solution_aux_compQual_perm]
  · show max (compShaded (p ∘ σ) (x ∘ σ) j) c ≤ x (σ j) / (1 + p (σ j)) ↔
      max (compShaded p x (σ j)) c ≤ x (σ j) / (1 + p (σ j))
    rw [solution_aux_compShaded_perm]

theorem solution_aux_price_perm {n : ℕ} (c : ℝ) (m : Mech) (p x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    price c m (p ∘ σ) (x ∘ σ) j = price c m p x (σ j) := by
  cases m
  · show max (compQual (p ∘ σ) (x ∘ σ) j) c = max (compQual p x (σ j)) c
    rw [solution_aux_compQual_perm]
  · show max (compQual (p ∘ σ) (x ∘ σ) j) (p (σ j)) = max (compQual p x (σ j)) (p (σ j))
    rw [solution_aux_compQual_perm]
  · show max (compShaded (p ∘ σ) (x ∘ σ) j) c = max (compShaded p x (σ j)) c
    rw [solution_aux_compShaded_perm]

/-- at most one winner -/
def solution_aux_Good {n : ℕ} (c : ℝ) (m : Mech) (p x : Fin n → ℝ) : Prop :=
  ∀ i j, wins c m p x i → wins c m p x j → i = j

open Classical in
theorem solution_aux_alloc_good {n : ℕ} (c : ℝ) (m : Mech) (p x : Fin n → ℝ)
    (hG : solution_aux_Good c m p x) (i : Fin n) :
    alloc c m p x i = if wins c m p x i then 1 else 0 := by
  unfold alloc
  by_cases hw : wins c m p x i
  · rw [if_pos hw, if_pos ⟨hw, fun j hj hwj => (ne_of_lt hj) (hG j i hwj hw)⟩]
  · rw [if_neg hw, if_neg (fun h => hw h.1)]

theorem solution_aux_good_perm {n : ℕ} (c : ℝ) (m : Mech) (p x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (hG : solution_aux_Good c m p x) :
    solution_aux_Good c m (p ∘ σ) (x ∘ σ) := by
  intro i j hi hj
  rw [solution_aux_wins_perm] at hi hj
  exact σ.injective (hG _ _ hi hj)

open Classical in
theorem solution_aux_alloc_perm {n : ℕ} (c : ℝ) (m : Mech) (p x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (hG : solution_aux_Good c m p x) (j : Fin n) :
    alloc c m (p ∘ σ) (x ∘ σ) j = alloc c m p x (σ j) := by
  rw [solution_aux_alloc_good c m _ _ (solution_aux_good_perm c m p x σ hG),
    solution_aux_alloc_good c m _ _ hG]
  exact if_congr (solution_aux_wins_perm c m p x σ j) rfl rfl

theorem solution_aux_aeGood_thr {n : ℕ} (P : SymInstance n) (m : Mech) (hm : m ≠ .shading)
    (p : Fin n → ℝ) : ∀ᵐ x ∂P.law, solution_aux_Good P.c m p x := by
  filter_upwards [solution_aux_noties_w P (fun _ => 1) (fun _ => one_ne_zero)] with x hx
  intro i j hi hj
  by_contra hij
  have hQ : ∀ i j : Fin n, i ≠ j → p j ≤ x j → x j ≤ compQual p x i := by
    intro i j hij hj
    unfold compQual
    rw [Finset.le_fold_max]
    exact Or.inr ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, Ne.symm hij, hj⟩, le_rfl⟩
  have key : max (compQual p x i) (p i) ≤ x i ∧ max (compQual p x j) (p j) ≤ x j := by
    cases m
    · exact ⟨hi, hj⟩
    · exact ⟨hi, hj⟩
    · exact absurd rfl hm
  obtain ⟨hi', hj'⟩ := key
  rw [max_le_iff] at hi' hj'
  have h1 := hQ i j hij hj'.2
  have h2 := hQ j i (Ne.symm hij) hi'.2
  have := hx i j hij
  simp only [one_mul] at this
  exact this (le_antisymm (h2.trans hj'.1) (h1.trans hi'.1))

theorem solution_aux_aeGood_sh {n : ℕ} (P : SymInstance n) (p : Fin n → ℝ)
    (hp : ∀ k, 0 ≤ p k) : ∀ᵐ x ∂P.law, solution_aux_Good P.c .shading p x := by
  have hw : ∀ k, 1 / (1 + p k) ≠ 0 := fun k => by
    have := hp k; positivity
  filter_upwards [solution_aux_noties_w P (fun k => 1 / (1 + p k)) hw] with x hx
  intro i j hi hj
  by_contra hij
  have hS : ∀ i j : Fin n, i ≠ j → x j / (1 + p j) ≤ compShaded p x i := by
    intro i j hij
    unfold compShaded
    rw [Finset.le_fold_max]
    exact Or.inr ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, Ne.symm hij⟩, le_rfl⟩
  have hi' : max (compShaded p x i) P.c ≤ x i / (1 + p i) := hi
  have hj' : max (compShaded p x j) P.c ≤ x j / (1 + p j) := hj
  rw [max_le_iff] at hi' hj'
  have he : x i / (1 + p i) = x j / (1 + p j) :=
    le_antisymm ((hS j i (Ne.symm hij)).trans hj'.1) ((hS i j hij).trans hi'.1)
  apply hx i j hij
  simp only [one_div_mul_eq_div]
  exact he

theorem solution_aux_expend_perm {n : ℕ} (P : SymInstance n) (m : Mech) (p : Fin n → ℝ)
    (hG : ∀ᵐ x ∂P.law, solution_aux_Good P.c m p x) (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    expend P m (p ∘ σ) j = expend P m p (σ j) := by
  unfold expend
  congr 1
  rw [← solution_aux_perm P σ (fun y => payment P.c m (p ∘ σ) y j)]
  apply integral_congr_ae
  filter_upwards [hG] with x hx
  unfold payment
  rw [solution_aux_alloc_perm P.c m p x σ hx, solution_aux_price_perm]

theorem solution_aux_gross_perm {n : ℕ} (P : SymInstance n) (m : Mech) (p : Fin n → ℝ)
    (hG : ∀ᵐ x ∂P.law, solution_aux_Good P.c m p x) (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    grossValue P m (p ∘ σ) j = grossValue P m p (σ j) := by
  unfold grossValue
  congr 1
  rw [← solution_aux_perm P σ (fun y => y j * alloc P.c m (p ∘ σ) y j)]
  apply integral_congr_ae
  filter_upwards [hG] with x hx
  show x (σ j) * alloc P.c m (p ∘ σ) (x ∘ σ) j = x (σ j) * alloc P.c m p x (σ j)
  rw [solution_aux_alloc_perm P.c m p x σ hx]

theorem solution_aux_update_swap {n : ℕ} [NeZero n] (s t : ℝ) (i : Fin n) :
    Function.update (sym s) i t = Function.update (sym s) 0 t ∘ Equiv.swap 0 i := by
  funext k
  simp only [Function.comp, Function.update, sym]
  by_cases hk : k = i
  · subst hk; simp
  · by_cases hk0 : k = 0
    · subst hk0
      have : (0 : Fin n) ≠ i := fun h => hk h
      simp [hk, Equiv.swap_apply_left, this.symm, this]
    · simp [hk, hk0, Equiv.swap_apply_of_ne_of_ne hk0 hk]

/-- symmetric reduction of a unilateral deviation of buyer `i` to one of buyer `0`. -/
theorem solution_aux_dev_sym {n : ℕ} [NeZero n] (P : SymInstance n) (m : Mech) (s t : ℝ)
    (hG : ∀ᵐ x ∂P.law, solution_aux_Good P.c m (Function.update (sym s) 0 t) x) (i : Fin n) :
    expend P m (Function.update (sym s) i t) i = expend P m (Function.update (sym s) 0 t) 0 ∧
    utility P m (Function.update (sym s) i t) i = utility P m (Function.update (sym s) 0 t) 0 := by
  rw [solution_aux_update_swap s t i]
  have h0 : (Equiv.swap (0 : Fin n) i) i = 0 := Equiv.swap_apply_right _ _
  refine ⟨?_, ?_⟩
  · rw [solution_aux_expend_perm P m _ hG, h0]
  · unfold utility
    rw [solution_aux_expend_perm P m _ hG, solution_aux_gross_perm P m _ hG, h0]

/-! ### Buyer-0 deviations: a winning threshold `θ` and a price `π` -/

theorem solution_aux_dev_expend {n : ℕ} [NeZero n] (P : SymInstance n) (m : Mech)
    (p : Fin n → ℝ) (θ π : (Fin n → ℝ) → ℝ)
    (hwin : ∀ x, wins P.c m p x 0 ↔ θ x ≤ x 0) (hpr : ∀ x, price P.c m p x 0 = π x) :
    expend P m p 0 = P.T * ∫ x, (if θ x ≤ x 0 then π x else 0) ∂P.law := by
  unfold expend
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  show payment P.c m p x 0 = (if θ x ≤ x 0 then π x else 0)
  unfold payment
  rw [solution_aux_alloc0, hpr]
  by_cases h : θ x ≤ x 0
  · rw [if_pos ((hwin x).2 h), if_pos h, one_mul]
  · rw [if_neg (fun h' => h ((hwin x).1 h')), if_neg h, zero_mul]

theorem solution_aux_dev_gross {n : ℕ} [NeZero n] (P : SymInstance n) (m : Mech)
    (p : Fin n → ℝ) (θ : (Fin n → ℝ) → ℝ)
    (hwin : ∀ x, wins P.c m p x 0 ↔ θ x ≤ x 0) :
    grossValue P m p 0 = P.T * ∫ x, (if θ x ≤ x 0 then x 0 else 0) ∂P.law := by
  unfold grossValue
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  show x 0 * alloc P.c m p x 0 = (if θ x ≤ x 0 then x 0 else 0)
  rw [solution_aux_alloc0]
  by_cases h : θ x ≤ x 0
  · rw [if_pos ((hwin x).2 h), if_pos h, mul_one]
  · rw [if_neg (fun h' => h ((hwin x).1 h')), if_neg h, mul_zero]

theorem solution_aux_ind_int {n : ℕ} [NeZero n] (P : SymInstance n) (θ g : (Fin n → ℝ) → ℝ)
    (hθ : Measurable θ) (hg : Measurable g) (hb : ∀ x, θ x ≤ x 0 → |g x| ≤ |x 0|) :
    Integrable (fun x => if θ x ≤ x 0 then g x else 0) P.law := by
  have hprob := solution_aux_isProb P
  refine Integrable.mono' (P.moment 0).abs ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (Measurable.ite (measurableSet_le hθ (measurable_pi_apply 0)) hg
      measurable_const).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    split_ifs with h
    · exact hb x h
    · simp

/-- the three integrands used below are integrable when `0 ≤ π ≤ θ` -/
theorem solution_aux_ind_ints {n : ℕ} [NeZero n] (P : SymInstance n) (θ π : (Fin n → ℝ) → ℝ)
    (hθ : Measurable θ) (hπ : Measurable π) (hπ0 : ∀ x, 0 ≤ π x) (hπθ : ∀ x, π x ≤ θ x) :
    Integrable (fun x => if θ x ≤ x 0 then π x else 0) P.law ∧
    Integrable (fun x => if θ x ≤ x 0 then x 0 else 0) P.law ∧
    Integrable (fun x => if θ x ≤ x 0 then x 0 - π x else 0) P.law := by
  refine ⟨solution_aux_ind_int P θ π hθ hπ fun x h => ?_,
    solution_aux_ind_int P θ _ hθ (measurable_pi_apply 0) fun x h => le_rfl,
    solution_aux_ind_int P θ _ hθ ((measurable_pi_apply 0).sub hπ) fun x h => ?_⟩
  · have := hπ0 x; have := hπθ x
    rw [abs_of_nonneg (hπ0 x), abs_of_nonneg (by linarith)]; linarith
  · have := hπ0 x; have := hπθ x
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

theorem solution_aux_dev_utility {n : ℕ} [NeZero n] (P : SymInstance n) (m : Mech)
    (p : Fin n → ℝ) (θ π : (Fin n → ℝ) → ℝ)
    (hwin : ∀ x, wins P.c m p x 0 ↔ θ x ≤ x 0) (hpr : ∀ x, price P.c m p x 0 = π x)
    (hθ : Measurable θ) (hπ : Measurable π) (hπ0 : ∀ x, 0 ≤ π x) (hπθ : ∀ x, π x ≤ θ x) :
    utility P m p 0 = P.T * ∫ x, (if θ x ≤ x 0 then x 0 - π x else 0) ∂P.law := by
  obtain ⟨i1, i2, -⟩ := solution_aux_ind_ints P θ π hθ hπ hπ0 hπθ
  unfold utility
  rw [solution_aux_dev_gross P m p θ hwin, solution_aux_dev_expend P m p θ π hwin hpr,
    ← mul_sub, ← integral_sub i2 i1]
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  show (if θ x ≤ x 0 then x 0 else 0) - (if θ x ≤ x 0 then π x else 0) =
    (if θ x ≤ x 0 then x 0 - π x else 0)
  split_ifs <;> ring

theorem solution_aux_dev_mono {n : ℕ} [NeZero n] (P : SymInstance n) (θ₁ θ₂ π : (Fin n → ℝ) → ℝ)
    (h₁ : Measurable θ₁) (h₂ : Measurable θ₂) (hπ : Measurable π) (hπ0 : ∀ x, 0 ≤ π x)
    (hπθ : ∀ x, π x ≤ θ₁ x) (h12 : ∀ x, θ₁ x ≤ θ₂ x) :
    (∫ x, (if θ₂ x ≤ x 0 then π x else 0) ∂P.law) ≤ ∫ x, (if θ₁ x ≤ x 0 then π x else 0) ∂P.law ∧
    (∫ x, (if θ₂ x ≤ x 0 then x 0 - π x else 0) ∂P.law) ≤
      ∫ x, (if θ₁ x ≤ x 0 then x 0 - π x else 0) ∂P.law := by
  obtain ⟨a1, -, a3⟩ := solution_aux_ind_ints P θ₁ π h₁ hπ hπ0 hπθ
  obtain ⟨b1, -, b3⟩ := solution_aux_ind_ints P θ₂ π h₂ hπ hπ0 fun x => (hπθ x).trans (h12 x)
  refine ⟨integral_mono b1 a1 fun x => ?_, integral_mono b3 a3 fun x => ?_⟩
  · show (if θ₂ x ≤ x 0 then π x else 0) ≤ (if θ₁ x ≤ x 0 then π x else 0)
    by_cases h : θ₂ x ≤ x 0
    · rw [if_pos h, if_pos ((h12 x).trans h)]
    · rw [if_neg h]; split_ifs <;> simp [hπ0 x]
  · show (if θ₂ x ≤ x 0 then x 0 - π x else 0) ≤ (if θ₁ x ≤ x 0 then x 0 - π x else 0)
    by_cases h : θ₂ x ≤ x 0
    · rw [if_pos h, if_pos ((h12 x).trans h)]
    · rw [if_neg h]
      split_ifs with h'
      · linarith [hπθ x]
      · exact le_rfl

theorem solution_aux_dev_strict {n : ℕ} [NeZero n] (P : SymInstance n)
    (θ₁ θ₂ π : (Fin n → ℝ) → ℝ)
    (h₁ : Measurable θ₁) (h₂ : Measurable θ₂) (hπ : Measurable π) (hπ0 : ∀ x, 0 ≤ π x)
    (hπθ : ∀ x, π x ≤ θ₁ x) (h12 : ∀ x, θ₁ x ≤ θ₂ x)
    (S : Set (Fin n → ℝ)) (hS : MeasurableSet S) (hS0 : P.law S ≠ 0) (c δ : ℝ) (hc : 0 < c)
    (hδ : 0 < δ) (hSx : ∀ x ∈ S, θ₁ x ≤ x 0 ∧ x 0 < θ₂ x ∧ c ≤ π x ∧ δ ≤ x 0 - π x) :
    (∫ x, (if θ₂ x ≤ x 0 then π x else 0) ∂P.law) < ∫ x, (if θ₁ x ≤ x 0 then π x else 0) ∂P.law ∧
    (∫ x, (if θ₂ x ≤ x 0 then x 0 - π x else 0) ∂P.law) <
      ∫ x, (if θ₁ x ≤ x 0 then x 0 - π x else 0) ∂P.law := by
  obtain ⟨a1, -, a3⟩ := solution_aux_ind_ints P θ₁ π h₁ hπ hπ0 hπθ
  obtain ⟨b1, -, b3⟩ := solution_aux_ind_ints P θ₂ π h₂ hπ hπ0 fun x => (hπθ x).trans (h12 x)
  have hm : ∀ x, (if θ₂ x ≤ x 0 then π x else 0) ≤ (if θ₁ x ≤ x 0 then π x else 0) ∧
      (if θ₂ x ≤ x 0 then x 0 - π x else 0) ≤ (if θ₁ x ≤ x 0 then x 0 - π x else 0) := by
    intro x
    by_cases h : θ₂ x ≤ x 0
    · simp only [if_pos h, if_pos ((h12 x).trans h)]; exact ⟨le_rfl, le_rfl⟩
    · rw [if_neg h, if_neg h]
      split_ifs with h'
      · exact ⟨hπ0 x, by linarith [hπθ x]⟩
      · exact ⟨le_rfl, le_rfl⟩
  refine ⟨solution_aux_strict P _ _ a1 b1 (fun x => (hm x).1) S hS hS0 c hc fun x hx => ?_,
    solution_aux_strict P _ _ a3 b3 (fun x => (hm x).2) S hS hS0 δ hδ fun x hx => ?_⟩
  · obtain ⟨e1, e2, e3, -⟩ := hSx x hx
    rw [if_neg (not_le.2 e2), if_pos e1]; linarith
  · obtain ⟨e1, e2, -, e4⟩ := hSx x hx
    rw [if_neg (not_le.2 e2), if_pos e1]; linarith

theorem solution_aux_dev_lim {n : ℕ} [NeZero n] (P : SymInstance n) (θ : ℝ → (Fin n → ℝ) → ℝ)
    (π : (Fin n → ℝ) → ℝ) (s : ℝ) (hπ : Measurable π) (hπ0 : ∀ x, 0 ≤ π x)
    (hev : ∀ᶠ t in 𝓝[<] s, Measurable (θ t) ∧ (∀ x, π x ≤ θ t x) ∧ ∀ x, θ t x ≤ θ s x)
    (hcont : ∀ x, Tendsto (fun t => θ t x) (𝓝[<] s) (𝓝 (θ s x))) :
    Tendsto (fun t => ∫ x, (if θ t x ≤ x 0 then π x else 0) ∂P.law) (𝓝[<] s)
      (𝓝 (∫ x, (if θ s x ≤ x 0 then π x else 0) ∂P.law)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => |x 0|)
  · filter_upwards [hev] with t ht
    exact (Measurable.ite (measurableSet_le ht.1 (measurable_pi_apply 0)) hπ
      measurable_const).aestronglyMeasurable
  · filter_upwards [hev] with t ht
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs]
    split_ifs with h
    · have := ht.2.1 x
      rw [abs_of_nonneg (hπ0 x), abs_of_nonneg (by linarith [hπ0 x])]; linarith
    · simp
  · exact (P.moment 0).abs
  · refine Filter.Eventually.of_forall fun x => ?_
    by_cases h : θ s x ≤ x 0
    · apply tendsto_const_nhds.congr'
      filter_upwards [hev] with t ht
      rw [if_pos h, if_pos ((ht.2.2 x).trans h)]
    · apply tendsto_const_nhds.congr'
      have : ∀ᶠ t in 𝓝[<] s, x 0 < θ t x :=
        (hcont x).eventually (lt_mem_nhds (not_le.1 h))
      filter_upwards [this] with t ht
      rw [if_neg h, if_neg (not_le.2 ht)]

/-! ### The one-variable complementarity characterization, abstractly -/

theorem solution_aux_abstract {n : ℕ} [NeZero n] (P : SymInstance n) (m : Mech) (lo hi : ℝ)
    (hsym : ∀ s t (i : Fin n), s ∈ Set.Icc lo hi → t ∈ Set.Icc lo hi →
      expend P m (Function.update (sym s) i t) i = expend P m (Function.update (sym s) 0 t) 0 ∧
      utility P m (Function.update (sym s) i t) i = utility P m (Function.update (sym s) 0 t) 0)
    (hmonoU : ∀ s t, s ∈ Set.Icc lo hi → t ∈ Set.Icc lo hi → s ≤ t →
      utility P m (Function.update (sym s) 0 t) 0 ≤ utility P m (Function.update (sym s) 0 s) 0)
    (hstrictD : ∀ s t, s ∈ Set.Icc lo hi → t ∈ Set.Icc lo hi → t < s →
      expend P m (Function.update (sym s) 0 s) 0 < expend P m (Function.update (sym s) 0 t) 0)
    (hgain : ∀ s, s ∈ Set.Icc lo hi → lo < s → expend P m (Function.update (sym s) 0 s) 0 < P.B →
      ∃ t ∈ Set.Icc lo hi, expend P m (Function.update (sym s) 0 t) 0 ≤ P.B ∧
        utility P m (Function.update (sym s) 0 s) 0 < utility P m (Function.update (sym s) 0 t) 0)
    (s : ℝ) :
    IsSymSysEq P m lo hi s ↔
      (s ∈ Set.Icc lo hi ∧ G1 P m s ≤ P.B ∧ (G1 P m s = P.B ∨ s = lo)) := by
  have hself : ∀ (s : ℝ) (i : Fin n), Function.update (sym s) i s = sym s := fun s i =>
    Function.update_eq_self i (sym s)
  constructor
  · rintro ⟨hs, h⟩
    have hs0 : s ∈ Set.Icc lo hi := hs 0
    obtain ⟨hB, hopt⟩ := h 0
    refine ⟨hs0, hB, ?_⟩
    by_contra hc
    push Not at hc
    have hlo : lo < s := lt_of_le_of_ne hs0.1 (Ne.symm hc.2)
    have hlt : expend P m (Function.update (sym s) 0 s) 0 < P.B := by
      rw [hself]; exact lt_of_le_of_ne hB hc.1
    obtain ⟨t, ht, htB, htU⟩ := hgain s hs0 hlo hlt
    have := hopt t ht htB
    rw [hself s 0] at htU
    linarith
  · rintro ⟨hs, hB, hor⟩
    refine ⟨fun _ => hs, fun i => ⟨?_, fun t ht htB => ?_⟩⟩
    · have e1 : expend P m (sym s) i = expend P m (Function.update (sym s) 0 s) 0 := by
        rw [← (hsym s s i hs hs).1, hself]
      rw [e1, hself]; exact hB
    · rw [(hsym s t i hs ht).1] at htB
      have e2 : utility P m (sym s) i = utility P m (Function.update (sym s) 0 s) 0 := by
        rw [← (hsym s s i hs hs).2, hself]
      rw [(hsym s t i hs ht).2, e2]
      rcases le_or_gt s t with hst | hst
      · exact hmonoU s t hs ht hst
      · exfalso
        have h1 := hstrictD s t hs ht hst
        rw [hself] at h1
        have hGB : G1 P m s < P.B := lt_of_lt_of_le h1 htB
        rcases hor with h | h
        · exact absurd h (ne_of_lt hGB)
        · linarith [ht.1]

theorem solution_aux_exists_unique {n : ℕ} [NeZero n] (P : SymInstance n) (m : Mech) (lo hi : ℝ)
    (hlohi : lo ≤ hi)
    (hiff : ∀ s, IsSymSysEq P m lo hi s ↔
      (s ∈ Set.Icc lo hi ∧ G1 P m s ≤ P.B ∧ (G1 P m s = P.B ∨ s = lo)))
    (hcont : ContinuousOn (G1 P m) (Set.Icc lo hi)) (hhi : G1 P m hi ≤ P.B)
    (hanti : StrictAntiOn (G1 P m) (Set.Icc lo hi)) :
    ∃! s, IsSymSysEq P m lo hi s := by
  have hex : ∃ s, IsSymSysEq P m lo hi s := by
    by_cases hlo : G1 P m lo ≤ P.B
    · exact ⟨lo, (hiff lo).2 ⟨⟨le_rfl, hlohi⟩, hlo, Or.inr rfl⟩⟩
    · push Not at hlo
      obtain ⟨s, hs, hsB⟩ := intermediate_value_Icc' hlohi hcont ⟨hhi, hlo.le⟩
      exact ⟨s, (hiff s).2 ⟨hs, hsB.le, Or.inl hsB⟩⟩
  obtain ⟨s, hs⟩ := hex
  refine ⟨s, hs, fun s' hs' => ?_⟩
  obtain ⟨h1, h1B, h1or⟩ := (hiff s).1 hs
  obtain ⟨h2, h2B, h2or⟩ := (hiff s').1 hs'
  rcases lt_trichotomy s' s with h | h | h
  · exfalso
    have := hanti h2 h1 h
    rcases h1or with e | e
    · linarith
    · linarith [h2.1]
  · exact h
  · exfalso
    have := hanti h1 h2 h
    rcases h2or with e | e
    · linarith
    · linarith [h1.1]

/-! ### Boxes of positive probability -/

theorem solution_aux_box_pos2 {n : ℕ} [NeZero n] (P : SymInstance n) (a b l : ℝ) (ha : 0 < a)
    (hab : a < b) (hl : 0 < l) (hlb : l ≤ b) (hb : ENNReal.ofReal b ≤ P.vbar) :
    P.law (Set.univ.pi (fun j : Fin n => if j = 0 then Set.Ioo a b else Set.Ioo 0 l)) ≠ 0 := by
  set S := Set.univ.pi (fun j : Fin n => if j = 0 then Set.Ioo a b else Set.Ioo 0 l) with hS
  have hmeasf : Measurable (fun x => ENNReal.ofReal (P.f x)) :=
    ENNReal.measurable_ofReal.comp P.f_measurable
  unfold SymInstance.law
  rw [Ne, withDensity_apply_eq_zero hmeasf]
  have hsub : S ⊆ {x | ENNReal.ofReal (P.f x) ≠ 0} := by
    intro x hx
    have hx' : ∀ j, x j ∈ (if j = 0 then Set.Ioo a b else Set.Ioo 0 l) := fun j =>
      hx j (Set.mem_univ j)
    have hpos : 0 < P.f x := by
      apply P.f_pos
      intro j
      have hj := hx' j
      have hlt : x j < b := by
        split_ifs at hj with h
        · exact hj.2
        · exact lt_of_lt_of_le hj.2 hlb
      have h0 : 0 < x j := by
        split_ifs at hj with h
        · exact ha.trans hj.1
        · exact hj.1
      exact ⟨h0, lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (h0.trans hlt)).2 hlt) hb⟩
    simp only [Set.mem_setOf_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hpos
  rw [Set.inter_eq_right.2 hsub, hS, volume_pi_pi]
  rw [Finset.prod_eq_zero_iff]
  rintro ⟨j, -, hj⟩
  split_ifs at hj with h
  · rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hj; linarith
  · rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hj; linarith

theorem solution_aux_box_meas {n : ℕ} [NeZero n] (a b l : ℝ) :
    MeasurableSet (Set.univ.pi (fun j : Fin n => if j = 0 then Set.Ioo a b else Set.Ioo 0 l)) :=
  MeasurableSet.univ_pi fun j => by split_ifs <;> exact measurableSet_Ioo

theorem solution_aux_box_mem {n : ℕ} [NeZero n] {a b l : ℝ} {x : Fin n → ℝ}
    (hx : x ∈ Set.univ.pi (fun j : Fin n => if j = 0 then Set.Ioo a b else Set.Ioo 0 l)) :
    (a < x 0 ∧ x 0 < b) ∧ ∀ j, j ≠ 0 → 0 < x j ∧ x j < l := by
  have hx' : ∀ j, x j ∈ (if j = 0 then Set.Ioo a b else Set.Ioo 0 l) := fun j =>
    hx j (Set.mem_univ j)
  refine ⟨by simpa using hx' 0, fun j hj => ?_⟩
  have := hx' j
  rw [if_neg hj] at this
  exact this

/-! ### Thresholding -/

theorem solution_aux_compQual_upd {n : ℕ} [NeZero n] (s t : ℝ) (x : Fin n → ℝ) :
    compQual (Function.update (sym s) 0 t) x 0 = compQual (sym s) x 0 := by
  unfold compQual
  congr 1
  apply Finset.filter_congr
  intro j _
  constructor
  · rintro ⟨hj, h⟩; exact ⟨hj, by rwa [Function.update_of_ne hj] at h⟩
  · rintro ⟨hj, h⟩; exact ⟨hj, by rwa [Function.update_of_ne hj]⟩

theorem solution_aux_thr_win {n : ℕ} [NeZero n] (c s t : ℝ) (x : Fin n → ℝ) :
    wins c .thresholding (Function.update (sym s) 0 t) x 0 ↔
      max (compQual (sym s) x 0) t ≤ x 0 := by
  show max (compQual (Function.update (sym s) 0 t) x 0) (Function.update (sym s) 0 t 0) ≤ x 0 ↔ _
  rw [solution_aux_compQual_upd, Function.update_self]

theorem solution_aux_thr_price {n : ℕ} [NeZero n] (c s t : ℝ) (x : Fin n → ℝ) :
    price c .thresholding (Function.update (sym s) 0 t) x 0 = max (compQual (sym s) x 0) c := by
  show max (compQual (Function.update (sym s) 0 t) x 0) c = _
  rw [solution_aux_compQual_upd]

theorem solution_aux_thr_D {n : ℕ} [NeZero n] (P : SymInstance n) (s t : ℝ) :
    expend P .thresholding (Function.update (sym s) 0 t) 0 = P.T * ∫ x,
      (if max (compQual (sym s) x 0) t ≤ x 0 then max (compQual (sym s) x 0) P.c else 0) ∂P.law :=
  solution_aux_dev_expend P _ _ (fun x => max (compQual (sym s) x 0) t)
    (fun x => max (compQual (sym s) x 0) P.c) (solution_aux_thr_win P.c s t)
    (solution_aux_thr_price P.c s t)

theorem solution_aux_thr_U {n : ℕ} [NeZero n] (P : SymInstance n) (s t : ℝ) (ht : P.c ≤ t) :
    utility P .thresholding (Function.update (sym s) 0 t) 0 = P.T * ∫ x,
      (if max (compQual (sym s) x 0) t ≤ x 0 then x 0 - max (compQual (sym s) x 0) P.c
        else 0) ∂P.law :=
  solution_aux_dev_utility P _ _ (fun x => max (compQual (sym s) x 0) t)
    (fun x => max (compQual (sym s) x 0) P.c) (solution_aux_thr_win P.c s t)
    (solution_aux_thr_price P.c s t) ((solution_aux_compQual_meas _ 0).max measurable_const)
    ((solution_aux_compQual_meas _ 0).max measurable_const)
    (fun x => le_max_of_le_right P.c_pos.le) (fun x => max_le_max le_rfl ht)

theorem solution_aux_thr_strict {n : ℕ} [NeZero n] (P : SymInstance n) (s t : ℝ) (ht : P.c ≤ t)
    (hts : t < s) (hs : ENNReal.ofReal s ≤ P.vbar) :
    expend P .thresholding (Function.update (sym s) 0 s) 0 <
      expend P .thresholding (Function.update (sym s) 0 t) 0 ∧
    utility P .thresholding (Function.update (sym s) 0 s) 0 <
      utility P .thresholding (Function.update (sym s) 0 t) 0 := by
  have hc := P.c_pos
  have hT : (0 : ℝ) < P.T := Nat.cast_pos.2 P.T_pos
  have hq := solution_aux_compQual_meas (sym (n := n) s) 0
  obtain ⟨h1, h2⟩ := solution_aux_dev_strict P (fun x => max (compQual (sym s) x 0) t)
    (fun x => max (compQual (sym s) x 0) s) (fun x => max (compQual (sym s) x 0) P.c)
    (hq.max measurable_const) (hq.max measurable_const) (hq.max measurable_const)
    (fun x => le_max_of_le_right hc.le) (fun x => max_le_max le_rfl ht)
    (fun x => max_le_max le_rfl hts.le)
    _ (solution_aux_box_meas ((t + s) / 2) s t)
    (solution_aux_box_pos2 P ((t + s) / 2) s t (by linarith) (by linarith) (by linarith)
      hts.le hs) P.c ((s - t) / 2) hc (by linarith) (by
      intro x hx
      obtain ⟨⟨h0a, h0b⟩, hj⟩ := solution_aux_box_mem hx
      have hq0 : compQual (sym s) x 0 = 0 := by
        unfold compQual
        rw [Finset.filter_false_of_mem]
        · rfl
        · intro j _ hjq
          exact absurd hjq.2 (not_le.2 ((hj j hjq.1).2.trans hts))
      simp only [hq0]
      refine ⟨max_le (by linarith) (by linarith), lt_max_of_lt_right h0b, le_max_right _ _, ?_⟩
      rw [max_eq_right hc.le]; linarith)
  refine ⟨?_, ?_⟩
  · rw [solution_aux_thr_D, solution_aux_thr_D]; exact mul_lt_mul_of_pos_left h1 hT
  · rw [solution_aux_thr_U P s s (ht.trans hts.le), solution_aux_thr_U P s t ht]
    exact mul_lt_mul_of_pos_left h2 hT

theorem solution_aux_thr_monoU {n : ℕ} [NeZero n] (P : SymInstance n) (s t : ℝ) (hs : P.c ≤ s)
    (hst : s ≤ t) :
    utility P .thresholding (Function.update (sym s) 0 t) 0 ≤
      utility P .thresholding (Function.update (sym s) 0 s) 0 := by
  have hq := solution_aux_compQual_meas (sym (n := n) s) 0
  rw [solution_aux_thr_U P s s hs, solution_aux_thr_U P s t (hs.trans hst)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact (solution_aux_dev_mono P (fun x => max (compQual (sym s) x 0) s)
    (fun x => max (compQual (sym s) x 0) t) (fun x => max (compQual (sym s) x 0) P.c)
    (hq.max measurable_const) (hq.max measurable_const) (hq.max measurable_const)
    (fun x => le_max_of_le_right P.c_pos.le) (fun x => max_le_max le_rfl hs)
    (fun x => max_le_max le_rfl hst)).2

theorem solution_aux_thr_gain {n : ℕ} [NeZero n] (P : SymInstance n) (s : ℝ) (hcs : P.c < s)
    (hs : ENNReal.ofReal s ≤ P.vbar)
    (hB : expend P .thresholding (Function.update (sym s) 0 s) 0 < P.B) :
    ∃ t, P.c ≤ t ∧ t < s ∧ expend P .thresholding (Function.update (sym s) 0 t) 0 ≤ P.B ∧
      utility P .thresholding (Function.update (sym s) 0 s) 0 <
        utility P .thresholding (Function.update (sym s) 0 t) 0 := by
  have hq := solution_aux_compQual_meas (sym (n := n) s) 0
  have hlim := solution_aux_dev_lim P (fun t x => max (compQual (sym s) x 0) t)
    (fun x => max (compQual (sym s) x 0) P.c) s (hq.max measurable_const)
    (fun x => le_max_of_le_right P.c_pos.le)
    (by
      filter_upwards [Ioo_mem_nhdsLT hcs] with t ht
      exact ⟨hq.max measurable_const, fun x => max_le_max le_rfl ht.1.le,
        fun x => max_le_max le_rfl ht.2.le⟩)
    (fun x => ((continuous_const.max continuous_id).tendsto s).mono_left nhdsWithin_le_nhds)
  have hlim' := hlim.const_mul (P.T : ℝ)
  rw [← solution_aux_thr_D] at hlim'
  have hev : ∀ᶠ t in 𝓝[<] s, (P.T : ℝ) * ∫ x, (if max (compQual (sym s) x 0) t ≤ x 0 then
      max (compQual (sym s) x 0) P.c else 0) ∂P.law < P.B :=
    hlim'.eventually (gt_mem_nhds hB)
  obtain ⟨t, ht1, ht2⟩ := (hev.and (Ioo_mem_nhdsLT hcs)).exists
  refine ⟨t, ht2.1.le, ht2.2, ?_, (solution_aux_thr_strict P s t ht2.1.le ht2.2 hs).2⟩
  rw [solution_aux_thr_D]; exact ht1.le

theorem solution_aux_price_bound {n : ℕ} (c q : ℝ) (x : Fin n → ℝ) (hq0 : 0 ≤ q)
    (hq : q ≤ ∑ j, |x j|) : |max q c| ≤ (∑ j, |x j|) + |c| := by
  rw [abs_le]; constructor
  · have := le_max_left q c; linarith [abs_nonneg c]
  · exact max_le (by linarith [abs_nonneg c]) (by linarith [le_abs_self c])

theorem solution_aux_thr_cont {n : ℕ} [NeZero n] (P : SymInstance n) (lo hi : ℝ) :
    ContinuousOn (G1 P .thresholding) (Set.Icc lo hi) := by
  intro τ _
  have := solution_aux_isProb P
  have hac : P.law ≪ volume := withDensity_absolutelyContinuous _ _
  unfold G1 expend
  apply ContinuousWithinAt.const_mul
  apply continuousWithinAt_of_dominated (bound := fun x => (∑ j, |x j|) + |P.c|)
  · refine Filter.Eventually.of_forall fun τ' => ?_
    exact ((solution_aux_alloc_meas P.c _ _ 0).mul
      ((solution_aux_compQual_meas _ 0).max measurable_const)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun τ' => Filter.Eventually.of_forall fun x => ?_
    show ‖alloc P.c .thresholding (sym τ') x 0 * max (compQual (sym τ') x 0) P.c‖ ≤ _
    obtain ⟨a0, a1⟩ := solution_aux_alloc_bound P.c .thresholding (sym τ') x 0
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg a0]
    calc alloc P.c .thresholding (sym τ') x 0 * |max (compQual (sym τ') x 0) P.c|
        ≤ 1 * |max (compQual (sym τ') x 0) P.c| := mul_le_mul_of_nonneg_right a1 (abs_nonneg _)
      _ ≤ _ := by
        rw [one_mul]
        exact solution_aux_price_bound _ _ x (solution_aux_compQual_nonneg _ _ _)
          (solution_aux_compQual_le _ _ _)
  · exact (solution_aux_sumabs_int P).add (integrable_const _)
  · have hne : ∀ᵐ x ∂P.law, ∀ j, x j ≠ τ := by
      rw [ae_all_iff]
      intro j
      apply hac.ae_le
      rw [volume_pi]
      exact Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) j τ
    filter_upwards [hne] with x hx
    apply ContinuousAt.continuousWithinAt
    have hev : ∀ᶠ τ' in 𝓝 τ, ∀ j, (τ' ≤ x j ↔ τ ≤ x j) := by
      rw [Filter.eventually_all]
      intro j
      rcases lt_or_gt_of_ne (hx j) with h | h
      · filter_upwards [eventually_gt_nhds h] with τ' h'
        exact ⟨fun e => absurd (e.trans_lt h') (lt_irrefl _), fun e => absurd e (not_le.2 h)⟩
      · filter_upwards [eventually_lt_nhds h] with τ' h'
        exact ⟨fun _ => h.le, fun _ => h'.le⟩
    apply (continuousAt_const (y := payment P.c .thresholding (sym τ) x 0)).congr
    filter_upwards [hev] with τ' h'
    have hq : compQual (sym τ') x 0 = compQual (sym τ) x 0 := by
      unfold compQual
      congr 1
      apply Finset.filter_congr
      intro j _
      simp only [sym, h' j]
    unfold payment
    rw [solution_aux_alloc0, solution_aux_alloc0]
    show (if max (compQual (sym τ) x 0) τ ≤ x 0 then (1 : ℝ) else 0) *
        max (compQual (sym τ) x 0) P.c =
      (if max (compQual (sym τ') x 0) τ' ≤ x 0 then (1 : ℝ) else 0) *
        max (compQual (sym τ') x 0) P.c
    rw [hq]
    congr 2
    simp only [max_le_iff, h' 0]

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


/-! ### Bid shading -/

theorem solution_aux_compShaded_upd {n : ℕ} [NeZero n] (s t : ℝ) (x : Fin n → ℝ) :
    compShaded (Function.update (sym s) 0 t) x 0 = compShaded (sym s) x 0 := by
  unfold compShaded
  apply Finset.fold_congr
  intro j hj
  rw [Finset.mem_filter] at hj
  rw [Function.update_of_ne hj.2]

theorem solution_aux_compShaded_hom {n : ℕ} (μ : ℝ) (hμ : 0 < 1 + μ) (x : Fin n → ℝ) (i : Fin n) :
    compShaded (sym μ) x i = compShaded (sym 0) x i / (1 + μ) := by
  have key : ∀ y, compShaded (sym μ) x i ≤ y ↔ compShaded (sym 0) x i / (1 + μ) ≤ y := by
    intro y
    rw [div_le_iff₀ hμ]
    unfold compShaded
    rw [Finset.fold_max_le, Finset.fold_max_le]
    constructor
    · rintro ⟨h0, h⟩
      refine ⟨by nlinarith, fun j hj => ?_⟩
      have := h j hj
      simp only [sym, add_zero, div_one] at this ⊢
      rwa [div_le_iff₀ hμ] at this
    · rintro ⟨h0, h⟩
      refine ⟨by nlinarith, fun j hj => ?_⟩
      have := h j hj
      simp only [sym, add_zero, div_one] at this ⊢
      rwa [div_le_iff₀ hμ]
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

theorem solution_aux_sh_win {n : ℕ} [NeZero n] (c s t : ℝ) (ht : 0 ≤ t) (x : Fin n → ℝ) :
    wins c .shading (Function.update (sym s) 0 t) x 0 ↔
      (1 + t) * max (compShaded (sym s) x 0) c ≤ x 0 := by
  show max (compShaded (Function.update (sym s) 0 t) x 0) c ≤
    x 0 / (1 + Function.update (sym s) 0 t 0) ↔ _
  rw [solution_aux_compShaded_upd, Function.update_self, le_div_iff₀ (by linarith), mul_comm]

theorem solution_aux_sh_price {n : ℕ} [NeZero n] (c s t : ℝ) (x : Fin n → ℝ) :
    price c .shading (Function.update (sym s) 0 t) x 0 = max (compShaded (sym s) x 0) c := by
  show max (compShaded (Function.update (sym s) 0 t) x 0) c = _
  rw [solution_aux_compShaded_upd]

theorem solution_aux_sh_πθ {n : ℕ} (c q t : ℝ) (hc : 0 < c) (ht : 0 ≤ t) :
    max q c ≤ (1 + t) * max q c := by
  have : 0 < max q c := lt_max_of_lt_right hc
  nlinarith

theorem solution_aux_sh_D {n : ℕ} [NeZero n] (P : SymInstance n) (s t : ℝ) (ht : 0 ≤ t) :
    expend P .shading (Function.update (sym s) 0 t) 0 = P.T * ∫ x,
      (if (1 + t) * max (compShaded (sym s) x 0) P.c ≤ x 0 then max (compShaded (sym s) x 0) P.c
        else 0) ∂P.law :=
  solution_aux_dev_expend P _ _ (fun x => (1 + t) * max (compShaded (sym s) x 0) P.c)
    (fun x => max (compShaded (sym s) x 0) P.c) (solution_aux_sh_win P.c s t ht)
    (solution_aux_sh_price P.c s t)

theorem solution_aux_sh_U {n : ℕ} [NeZero n] (P : SymInstance n) (s t : ℝ) (ht : 0 ≤ t) :
    utility P .shading (Function.update (sym s) 0 t) 0 = P.T * ∫ x,
      (if (1 + t) * max (compShaded (sym s) x 0) P.c ≤ x 0 then
        x 0 - max (compShaded (sym s) x 0) P.c else 0) ∂P.law :=
  solution_aux_dev_utility P _ _ (fun x => (1 + t) * max (compShaded (sym s) x 0) P.c)
    (fun x => max (compShaded (sym s) x 0) P.c) (solution_aux_sh_win P.c s t ht)
    (solution_aux_sh_price P.c s t)
    (measurable_const.mul ((solution_aux_compShaded_meas _ 0).max measurable_const))
    ((solution_aux_compShaded_meas _ 0).max measurable_const)
    (fun x => le_max_of_le_right P.c_pos.le)
    (fun x => solution_aux_sh_πθ (n := n) P.c _ t P.c_pos ht)

theorem solution_aux_sh_strict {n : ℕ} [NeZero n] (P : SymInstance n) (s t : ℝ) (ht : 0 ≤ t)
    (hts : t < s) (hs : ENNReal.ofReal ((1 + s) * P.c) ≤ P.vbar) :
    expend P .shading (Function.update (sym s) 0 s) 0 <
      expend P .shading (Function.update (sym s) 0 t) 0 ∧
    utility P .shading (Function.update (sym s) 0 s) 0 <
      utility P .shading (Function.update (sym s) 0 t) 0 := by
  have hc := P.c_pos
  have hT : (0 : ℝ) < P.T := Nat.cast_pos.2 P.T_pos
  have hs0 : 0 ≤ s := ht.trans hts.le
  have hq := solution_aux_compShaded_meas (sym (n := n) s) 0
  have hlt1 : (1 + t) * P.c < (1 + (t + s) / 2) * P.c := by nlinarith
  have hlt2 : (1 + (t + s) / 2) * P.c < (1 + s) * P.c := by nlinarith
  obtain ⟨h1, h2⟩ := solution_aux_dev_strict P
    (fun x => (1 + t) * max (compShaded (sym s) x 0) P.c)
    (fun x => (1 + s) * max (compShaded (sym s) x 0) P.c)
    (fun x => max (compShaded (sym s) x 0) P.c)
    (measurable_const.mul (hq.max measurable_const))
    (measurable_const.mul (hq.max measurable_const)) (hq.max measurable_const)
    (fun x => le_max_of_le_right hc.le) (fun x => solution_aux_sh_πθ (n := n) P.c _ t hc ht)
    (fun x => mul_le_mul_of_nonneg_right (by linarith) (le_max_of_le_right hc.le))
    _ (solution_aux_box_meas ((1 + (t + s) / 2) * P.c) ((1 + s) * P.c) ((1 + t) * P.c))
    (solution_aux_box_pos2 P _ _ _ (by nlinarith) hlt2 (by nlinarith) (by nlinarith) hs)
    P.c (s * P.c / 2) hc (by have : 0 < s := ht.trans_lt hts; positivity) (by
      intro x hx
      obtain ⟨⟨h0a, h0b⟩, hj⟩ := solution_aux_box_mem hx
      have hq0 : compShaded (sym s) x 0 ≤ P.c := by
        unfold compShaded
        rw [Finset.fold_max_le]
        refine ⟨hc.le, fun j hjm => ?_⟩
        rw [Finset.mem_filter] at hjm
        simp only [sym]
        rw [div_le_iff₀ (by linarith)]
        have := (hj j hjm.2).2
        nlinarith
      simp only [max_eq_right hq0]
      refine ⟨by linarith, h0b, le_rfl, ?_⟩
      nlinarith)
  refine ⟨?_, ?_⟩
  · rw [solution_aux_sh_D P s s hs0, solution_aux_sh_D P s t ht]
    exact mul_lt_mul_of_pos_left h1 hT
  · rw [solution_aux_sh_U P s s hs0, solution_aux_sh_U P s t ht]
    exact mul_lt_mul_of_pos_left h2 hT

theorem solution_aux_sh_monoU {n : ℕ} [NeZero n] (P : SymInstance n) (s t : ℝ) (hs : 0 ≤ s)
    (hst : s ≤ t) :
    utility P .shading (Function.update (sym s) 0 t) 0 ≤
      utility P .shading (Function.update (sym s) 0 s) 0 := by
  have hq := solution_aux_compShaded_meas (sym (n := n) s) 0
  rw [solution_aux_sh_U P s s hs, solution_aux_sh_U P s t (hs.trans hst)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact (solution_aux_dev_mono P (fun x => (1 + s) * max (compShaded (sym s) x 0) P.c)
    (fun x => (1 + t) * max (compShaded (sym s) x 0) P.c)
    (fun x => max (compShaded (sym s) x 0) P.c)
    (measurable_const.mul (hq.max measurable_const))
    (measurable_const.mul (hq.max measurable_const)) (hq.max measurable_const)
    (fun x => le_max_of_le_right P.c_pos.le)
    (fun x => solution_aux_sh_πθ (n := n) P.c _ s P.c_pos hs)
    (fun x => mul_le_mul_of_nonneg_right (by linarith) (le_max_of_le_right P.c_pos.le))).2

theorem solution_aux_sh_gain {n : ℕ} [NeZero n] (P : SymInstance n) (s : ℝ) (hs0 : 0 < s)
    (hs : ENNReal.ofReal ((1 + s) * P.c) ≤ P.vbar)
    (hB : expend P .shading (Function.update (sym s) 0 s) 0 < P.B) :
    ∃ t, 0 ≤ t ∧ t < s ∧ expend P .shading (Function.update (sym s) 0 t) 0 ≤ P.B ∧
      utility P .shading (Function.update (sym s) 0 s) 0 <
        utility P .shading (Function.update (sym s) 0 t) 0 := by
  have hc := P.c_pos
  have hq := solution_aux_compShaded_meas (sym (n := n) s) 0
  have hlim := solution_aux_dev_lim P (fun t x => (1 + t) * max (compShaded (sym s) x 0) P.c)
    (fun x => max (compShaded (sym s) x 0) P.c) s (hq.max measurable_const)
    (fun x => le_max_of_le_right hc.le)
    (by
      filter_upwards [Ioo_mem_nhdsLT hs0] with t ht
      exact ⟨measurable_const.mul (hq.max measurable_const),
        fun x => solution_aux_sh_πθ (n := n) P.c _ t hc ht.1.le,
        fun x => mul_le_mul_of_nonneg_right (by linarith [ht.2]) (le_max_of_le_right hc.le)⟩)
    (fun x => (((continuous_const.add continuous_id).mul continuous_const).tendsto s).mono_left
      nhdsWithin_le_nhds)
  have hlim' := hlim.const_mul (P.T : ℝ)
  rw [← solution_aux_sh_D P s s hs0.le] at hlim'
  have hev := hlim'.eventually (gt_mem_nhds hB)
  obtain ⟨t, ht1, ht2⟩ := (hev.and (Ioo_mem_nhdsLT hs0)).exists
  refine ⟨t, ht2.1.le, ht2.2, ?_, (solution_aux_sh_strict P s t ht2.1.le ht2.2 hs).2⟩
  rw [solution_aux_sh_D P s t ht2.1.le]; exact ht1.le

open Classical in
theorem solution_aux_sh_cont {n : ℕ} [NeZero n] (P : SymInstance n) (hi : ℝ) :
    ContinuousOn (G1 P .shading) (Set.Icc 0 hi) := by
  intro μ hμ
  have := solution_aux_isProb P
  have hc := P.c_pos
  have hac : P.law ≪ volume := withDensity_absolutelyContinuous _ _
  unfold G1 expend
  apply ContinuousWithinAt.const_mul
  apply continuousWithinAt_of_dominated (bound := fun x => (∑ j, |x j|) + |P.c|)
  · refine Filter.Eventually.of_forall fun μ' => ?_
    exact ((solution_aux_alloc_meas P.c _ _ 0).mul
      ((solution_aux_compShaded_meas _ 0).max measurable_const)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with μ' hμ'
    refine Filter.Eventually.of_forall fun x => ?_
    show ‖alloc P.c .shading (sym μ') x 0 * max (compShaded (sym μ') x 0) P.c‖ ≤ _
    obtain ⟨a0, a1⟩ := solution_aux_alloc_bound P.c .shading (sym μ') x 0
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg a0]
    calc alloc P.c .shading (sym μ') x 0 * |max (compShaded (sym μ') x 0) P.c|
        ≤ 1 * |max (compShaded (sym μ') x 0) P.c| := mul_le_mul_of_nonneg_right a1 (abs_nonneg _)
      _ ≤ _ := by
        rw [one_mul]
        exact solution_aux_price_bound _ _ x (solution_aux_compShaded_nonneg _ _ _)
          (solution_aux_compShaded_le μ' hμ'.1 x 0)
  · exact (solution_aux_sumabs_int P).add (integrable_const _)
  · have hne : ∀ᵐ x ∂P.law, x 0 ≠ (1 + μ) * P.c := by
      apply hac.ae_le
      rw [volume_pi]
      exact Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) 0 _
    filter_upwards [hne] with x hx
    set A : Prop := ∀ j, j ≠ 0 → x j ≤ x 0
    set Q := compShaded (sym (n := n) 0) x 0
    have h1μ : 0 < 1 + μ := by linarith [hμ.1]
    have hform : ∀ μ' : ℝ, 0 ≤ μ' → payment P.c .shading (sym μ') x 0 =
        (if (1 + μ') * P.c ≤ x 0 ∧ A then (1 : ℝ) else 0) * max (Q / (1 + μ')) P.c := by
      intro μ' h0
      unfold payment
      rw [solution_aux_alloc0]
      show (if wins P.c .shading (sym μ') x 0 then (1 : ℝ) else 0) *
        max (compShaded (sym μ') x 0) P.c = _
      rw [solution_aux_compShaded_hom μ' (by linarith) x 0]
      congr 1
      exact if_congr (solution_aux_wins_sh P.c μ' hc h0 x) rfl rfl
    have hevk : ∀ᶠ μ' in 𝓝 μ, ((1 + μ') * P.c ≤ x 0 ↔ (1 + μ) * P.c ≤ x 0) := by
      have hcont : Continuous (fun μ' : ℝ => (1 + μ') * P.c) :=
        (continuous_const.add continuous_id).mul continuous_const
      rcases lt_or_gt_of_ne hx with h | h
      · filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds h)] with μ' h'
        exact ⟨fun e => absurd e (not_le.2 h'), fun e => absurd e (not_le.2 h)⟩
      · filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds h)] with μ' h'
        exact ⟨fun _ => h.le, fun _ => h'.le⟩
    set k : ℝ := if (1 + μ) * P.c ≤ x 0 ∧ A then 1 else 0
    have hg : ContinuousWithinAt (fun μ' => k * max (Q / (1 + μ')) P.c) (Set.Icc 0 hi) μ := by
      apply ContinuousAt.continuousWithinAt
      apply continuousAt_const.mul
      exact ContinuousAt.sup (continuousAt_const.div (continuousAt_const.add continuousAt_id)
        h1μ.ne') continuousAt_const
    refine hg.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hevk] with μ' hμ' hk
      rw [hform μ' hμ'.1]
      congr 1
      exact if_congr (and_congr hk Iff.rfl) rfl rfl
    · exact hform μ hμ.1

theorem solution {n : ℕ} [NeZero n] (P : SymInstance n) :
    (∀ taubar : ℝ, AdmissibleT P taubar →
      (∃! τ : ℝ, IsSymSysEq P .thresholding P.c taubar τ) ∧
      ∀ τ : ℝ, IsSymSysEq P .thresholding P.c taubar τ ↔
        (τ ∈ Set.Icc P.c taubar ∧ G1 P .thresholding τ ≤ P.B ∧
          (G1 P .thresholding τ = P.B ∨ τ = P.c))) ∧
    (∀ mubar : ℝ, AdmissibleS P mubar →
      (∃! μ : ℝ, IsSymSysEq P .shading 0 mubar μ) ∧
      ∀ μ : ℝ, IsSymSysEq P .shading 0 mubar μ ↔
        (μ ∈ Set.Icc 0 mubar ∧ G1 P .shading μ ≤ P.B ∧
          (G1 P .shading μ = P.B ∨ μ = 0))) := by
  refine ⟨fun taubar hT => ?_, fun mubar hS => ?_⟩
  · have hv : ∀ s, s ∈ Set.Icc P.c taubar → ENNReal.ofReal s ≤ P.vbar := fun s hs =>
      (ENNReal.ofReal_le_ofReal hs.2).trans hT.2.1
    have hiff := solution_aux_abstract P .thresholding P.c taubar
      (fun s t i _ _ => solution_aux_dev_sym P .thresholding s t
        (solution_aux_aeGood_thr P _ (by decide) _) i)
      (fun s t hs _ hst => solution_aux_thr_monoU P s t hs.1 hst)
      (fun s t hs ht hts => (solution_aux_thr_strict P s t ht.1 hts (hv s hs)).1)
      (fun s hs hlo hB => by
        obtain ⟨t, ht1, ht2, hD, hU⟩ := solution_aux_thr_gain P s hlo (hv s hs) hB
        exact ⟨t, ⟨ht1, ht2.le.trans hs.2⟩, hD, hU⟩)
    refine ⟨solution_aux_exists_unique P .thresholding P.c taubar hT.1 hiff
      (solution_aux_thr_cont P _ _) ?_ ?_, hiff⟩
    · have := hT.2.2 (sym taubar) (fun _ => ⟨hT.1, le_rfl⟩) 0
      have e : Function.update (sym taubar) 0 taubar = sym (n := n) taubar :=
        Function.update_eq_self 0 _
      rw [e] at this
      exact this
    · exact (G1_thresholding_strictAntiOn P).mono fun τ hτ => ⟨hτ.1, hv τ hτ⟩
  · have hv : ∀ s, s ∈ Set.Icc 0 mubar → ENNReal.ofReal ((1 + s) * P.c) ≤ P.vbar := fun s hs =>
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith [hs.2]) P.c_pos.le)).trans
        hS.2.1
    have hiff := solution_aux_abstract P .shading 0 mubar
      (fun s t i hs ht => solution_aux_dev_sym P .shading s t
        (solution_aux_aeGood_sh P _ (fun k => by
          by_cases hk : k = 0
          · subst hk; rw [Function.update_self]; exact ht.1
          · rw [Function.update_of_ne hk]; exact hs.1)) i)
      (fun s t hs _ hst => solution_aux_sh_monoU P s t hs.1 hst)
      (fun s t hs ht hts => (solution_aux_sh_strict P s t ht.1 hts (hv s hs)).1)
      (fun s hs hlo hB => by
        obtain ⟨t, ht1, ht2, hD, hU⟩ := solution_aux_sh_gain P s hlo (hv s hs) hB
        exact ⟨t, ⟨ht1, ht2.le.trans hs.2⟩, hD, hU⟩)
    refine ⟨solution_aux_exists_unique P .shading 0 mubar hS.1 hiff
      (solution_aux_sh_cont P _) ?_ ?_, hiff⟩
    · have := hS.2.2 (sym mubar) (fun _ => ⟨hS.1, le_rfl⟩) 0
      have e : Function.update (sym mubar) 0 mubar = sym (n := n) mubar :=
        Function.update_eq_self 0 _
      rw [e] at this
      exact this
    · exact (G1_shading_strictAntiOn P).mono fun μ hμ => ⟨hμ.1, hv μ hμ⟩
