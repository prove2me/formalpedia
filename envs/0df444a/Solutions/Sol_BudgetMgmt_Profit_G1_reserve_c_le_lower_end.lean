-- Prove2me | solution 1 for BudgetMgmt.Profit.G1_reserve_c_le_lower_end
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:38:34.359505+00:00
-- url     : https://prove2.me/submissions/d3fb5c4f-b65a-4635-8cef-2d7e75349b2a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model
import Theorems.Thm_BudgetMgmt_Profit_G1_reserve_deriv

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

theorem solution_aux_price_bound {n : ℕ} (c q : ℝ) (x : Fin n → ℝ) (hq0 : 0 ≤ q)
    (hq : q ≤ ∑ j, |x j|) : |max q c| ≤ (∑ j, |x j|) + |c| := by
  rw [abs_le]; constructor
  · have := le_max_left q c; linarith [abs_nonneg c]
  · exact max_le (by linarith [abs_nonneg c]) (by linarith [le_abs_self c])


open Classical in
theorem solution_aux_alloc0 {n : ℕ} [NeZero n] (c : ℝ) (m : Mech) (s x : Fin n → ℝ) :
    alloc c m s x 0 = if wins c m s x 0 then 1 else 0 := by
  unfold alloc
  exact if_congr ⟨fun h => h.1, fun h => ⟨h, fun j hj => absurd hj (Fin.not_lt_zero j)⟩⟩ rfl rfl

/-- invariance of probabilities under the transposition of two buyers -/
theorem solution_aux_perm_set {n : ℕ} (P : SymInstance n) (σ : Equiv.Perm (Fin n))
    (S : Set (Fin n → ℝ)) (hS : MeasurableSet S) :
    P.law.real ((fun x => x ∘ σ) ⁻¹' S) = P.law.real S := by
  have hm : Measurable (fun x : Fin n → ℝ => x ∘ σ) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (σ j)
  rw [← integral_indicator_one hS, ← integral_indicator_one (hm hS)]
  rw [← solution_aux_perm P σ (S.indicator 1)]
  rfl

/-- `ξ_i(r 1⃗) = ξ_1(r 1⃗)` by exchangeability -/
theorem solution_aux_xi_sym {n : ℕ} [NeZero n] (P : SymInstance n) (i : Fin n) (r : ℝ) :
    xi P i (sym r) = xi P 0 (sym r) := by
  let σ : Equiv.Perm (Fin n) := Equiv.swap 0 i
  have key : ∀ (k : Fin n) (A : ℝ → Prop) (hA : MeasurableSet {y : ℝ | A y}),
      P.law.real {x : Fin n → ℝ | A (x i) ∧ ∀ j, j ≠ i → x j ≤ r} =
      P.law.real {x : Fin n → ℝ | A (x 0) ∧ ∀ j, j ≠ 0 → x j ≤ r} := by
    intro _ A hA
    have hmeas : MeasurableSet {x : Fin n → ℝ | A (x 0) ∧ ∀ j, j ≠ 0 → x j ≤ r} := by
      have : {x : Fin n → ℝ | A (x 0) ∧ ∀ j, j ≠ 0 → x j ≤ r} =
          ((fun x : Fin n → ℝ => x 0) ⁻¹' {y | A y}) ∩ ⋂ j ∈ Finset.univ.filter (· ≠ 0),
            {x | x j ≤ r} := by ext x; simp
      rw [this]
      exact (measurable_pi_apply 0 hA).inter (Finset.measurableSet_biInter _ fun j _ =>
        measurableSet_le (measurable_pi_apply j) measurable_const)
    rw [← solution_aux_perm_set P σ _ hmeas]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Function.comp]
    have hσ0 : σ 0 = i := Equiv.swap_apply_left _ _
    rw [hσ0]
    refine and_congr Iff.rfl ⟨fun h j hj => ?_, fun h k hk => ?_⟩
    · apply h
      intro e; apply hj
      have := congrArg σ e
      simpa [σ] using this
    · have := h (σ k) (fun e => hk (by
        have := congrArg σ e
        simpa [σ, hσ0] using this))
      simpa [σ] using this
  unfold xi
  simp only [sym]
  have h1 : (fun t => P.law.real {x : Fin n → ℝ | x i ≤ t ∧ ∀ j, j ≠ i → x j ≤ r}) =
      fun t => P.law.real {x : Fin n → ℝ | x 0 ≤ t ∧ ∀ j, j ≠ 0 → x j ≤ r} := by
    funext t
    exact key 0 (fun y => y ≤ t) measurableSet_Iic
  rw [h1, key 0 (fun y => r ≤ y) measurableSet_Ici]

theorem solution_aux_res_cont {n : ℕ} [NeZero n] (P : SymInstance n) (D : Set ℝ) :
    ContinuousOn (G1 P .reserve) D := by
  intro r0 _
  have := solution_aux_isProb P
  have hac : P.law ≪ volume := withDensity_absolutelyContinuous _ _
  unfold G1 expend
  apply ContinuousWithinAt.const_mul
  apply continuousWithinAt_of_dominated (bound := fun x => (∑ j, |x j|) + (|r0| + 1))
  · refine Filter.Eventually.of_forall fun r => ?_
    exact ((solution_aux_alloc_meas P.c _ _ 0).mul
      ((solution_aux_compQual_meas _ 0).max measurable_const)).aestronglyMeasurable
  · have hnear : ∀ᶠ r in 𝓝[D] r0, |r| ≤ |r0| + 1 := by
      apply nhdsWithin_le_nhds
      have : Set.Ioo (r0 - 1) (r0 + 1) ∈ 𝓝 r0 := Ioo_mem_nhds (by linarith) (by linarith)
      filter_upwards [this] with r hr
      rw [abs_le]; constructor <;> cases abs_cases r0 <;> linarith [hr.1, hr.2]
    filter_upwards [hnear] with r hr
    refine Filter.Eventually.of_forall fun x => ?_
    show ‖alloc P.c .reserve (sym r) x 0 * max (compQual (sym r) x 0) (sym r 0)‖ ≤ _
    obtain ⟨a0, a1⟩ := solution_aux_alloc_bound P.c .reserve (sym r) x 0
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg a0]
    calc alloc P.c .reserve (sym r) x 0 * |max (compQual (sym r) x 0) (sym r 0)|
        ≤ 1 * |max (compQual (sym r) x 0) (sym r 0)| :=
          mul_le_mul_of_nonneg_right a1 (abs_nonneg _)
      _ ≤ (∑ j, |x j|) + |r| := by
        rw [one_mul]
        exact solution_aux_price_bound _ _ x (solution_aux_compQual_nonneg _ _ _)
          (solution_aux_compQual_le _ _ _)
      _ ≤ _ := by linarith
  · exact (solution_aux_sumabs_int P).add (integrable_const _)
  · have hne : ∀ᵐ x ∂P.law, ∀ j, x j ≠ r0 := by
      rw [ae_all_iff]
      intro j
      apply hac.ae_le
      rw [volume_pi]
      exact Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) j r0
    filter_upwards [hne] with x hx
    apply ContinuousAt.continuousWithinAt
    have hev : ∀ᶠ r in 𝓝 r0, ∀ j, (r ≤ x j ↔ r0 ≤ x j) := by
      rw [Filter.eventually_all]
      intro j
      rcases lt_or_gt_of_ne (hx j) with h | h
      · filter_upwards [eventually_gt_nhds h] with r h'
        exact ⟨fun e => absurd (e.trans_lt h') (lt_irrefl _), fun e => absurd e (not_le.2 h)⟩
      · filter_upwards [eventually_lt_nhds h] with r h'
        exact ⟨fun _ => h.le, fun _ => h'.le⟩
    set q := compQual (sym (n := n) r0) x 0
    set k : ℝ := if max q r0 ≤ x 0 then 1 else 0
    have hg : ContinuousAt (fun r : ℝ => k * max q r) r0 :=
      continuousAt_const.mul (ContinuousAt.sup continuousAt_const continuousAt_id)
    have hform : ∀ r, (∀ j, (r ≤ x j ↔ r0 ≤ x j)) →
        payment P.c .reserve (sym r) x 0 = k * max q r := by
      intro r h'
      have hq : compQual (sym r) x 0 = q := by
        show compQual (sym r) x 0 = compQual (sym r0) x 0
        unfold compQual
        congr 1
        apply Finset.filter_congr
        intro j _
        simp only [sym, h' j]
      unfold payment
      rw [solution_aux_alloc0]
      show (if max (compQual (sym r) x 0) r ≤ x 0 then (1 : ℝ) else 0) *
        max (compQual (sym r) x 0) r = _
      rw [hq]
      congr 1
      simp only [k, max_le_iff, h' 0]
    refine hg.congr ?_
    filter_upwards [hev] with r hr using (hform r hr).symm

theorem solution {n : ℕ} [NeZero n] (P : SymInstance n) (hA : Assumption1 P)
    (rbar : ℝ) (hR : AdmissibleR P rbar) :
    G1 P .reserve P.c ≤ G1 P .reserve (sInf (ShatR P rbar)) := by
  have hc := P.c_pos
  -- `r̄ ∈ Ŝ₁`, so `Ŝ₁` is nonempty and bounded below by `c`
  have hmem : rbar ∈ ShatR P rbar := by
    refine ⟨⟨hR.1, le_rfl⟩, fun i => ?_⟩
    have := (hR.2.2 (sym rbar) (fun _ => ⟨hR.1, le_rfl⟩) i).1
    have e : Function.update (sym rbar) i rbar = sym (n := n) rbar :=
      Function.update_eq_self i _
    rwa [e] at this
  have hbdd : BddBelow (ShatR P rbar) := ⟨P.c, fun r hr => hr.1.1⟩
  set rh := sInf (ShatR P rbar) with hrh
  have hcr : P.c ≤ rh := le_csInf ⟨rbar, hmem⟩ fun r hr => hr.1.1
  have hrr : rh ≤ rbar := csInf_le hbdd hmem
  have hderiv := (G1_reserve_deriv P).1
  have hmono : MonotoneOn (G1 P .reserve) (Set.Icc P.c rh) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (solution_aux_res_cont P _)
    · rw [interior_Icc]
      intro r hr
      have hrv : ENNReal.ofReal r < P.vbar :=
        lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith [hr.2, hr.1])).2
          (hr.2.trans_le hrr)) hR.2.1
      exact (hderiv r hr.1 hrv).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro r hr
      have hrv : ENNReal.ofReal r < P.vbar :=
        lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith [hr.2, hr.1])).2
          (hr.2.trans_le hrr)) hR.2.1
      rw [(hderiv r hr.1 hrv).deriv]
      -- below the lower end of `Ŝ₁` the constraint fails, so `ξ₁(r 1⃗) < 1`
      have hnot : r ∉ ShatR P rbar := notMem_of_lt_csInf hr.2 hbdd
      have hxi : xi P 0 (sym r) ≤ 1 := by
        by_contra hgt
        push Not at hgt
        apply hnot
        refine ⟨⟨hr.1.le, (hr.2.trans_le hrr).le⟩, fun i _ => ?_⟩
        have e : diagPt i (sym (n := n) r i) (sym r) = sym r := by
          funext j; simp [diagPt, sym]
        rw [e, solution_aux_xi_sym]
        exact hgt.le
      have hT : (0 : ℝ) ≤ P.T := Nat.cast_nonneg _
      have hm : 0 ≤ P.law.real {x | r ≤ x 0 ∧ ∀ j, j ≠ 0 → x j ≤ r} := measureReal_nonneg
      have : 0 ≤ 1 - xi P 0 (sym r) := by linarith
      positivity
  exact hmono ⟨le_rfl, hcr⟩ ⟨hcr, le_rfl⟩ hcr
