-- Prove2me | solution 1 for BurkholderDFI.NonnegExp.lemma_18_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:26:30.424984+00:00
-- url     : https://prove2.me/submissions/140c62ad-3e64-4c77-856a-b9297c0831fd

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale



namespace BurkholderDFI.NonnegExp

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

section L181

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : Ω → ℝ≥0∞}

lemma tailm_antitone (P : Measure Ω) (g : Ω → ℝ≥0∞) :
    Antitone (fun x : ℝ => P {ω | ENNReal.ofReal x < g ω}) := by
  intro x y hxy
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at *
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hxy) hω

lemma tailm_measurable (P : Measure Ω) (g : Ω → ℝ≥0∞) :
    Measurable (fun x : ℝ => P {ω | ENNReal.ofReal x < g ω}) :=
  (tailm_antitone P g).measurable

lemma ae_ne_top_of_tail [IsProbabilityMeasure P] (g : Ω → ℝ≥0∞) (α : ℝ)
    (h184 : ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < g ω}
        ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal a < g ω}) :
    ∀ᵐ ω ∂P, g ω ≠ ⊤ := by
  have hsub : ∀ x : ℝ, {ω | g ω = ⊤} ⊆ {ω | ENNReal.ofReal x < g ω} := fun x ω hω => by
    simp only [Set.mem_setOf_eq] at *
    rw [hω]; exact ENNReal.ofReal_lt_top
  have hfin : ∫⁻ x in Set.Ioi (1:ℝ), P {ω | ENNReal.ofReal x < g ω} < ⊤ := by
    calc _ ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal 1 < g ω} := h184 1 one_pos
      _ ≤ ENNReal.ofReal α * 1 := by gcongr; exact prob_le_one
      _ < ⊤ := by simp
  by_contra hcon
  rw [ae_iff] at hcon
  simp only [ne_eq, not_not] at hcon
  have hpos : 0 < P {ω | g ω = ⊤} := pos_iff_ne_zero.mpr hcon
  have : ∫⁻ x in Set.Ioi (1:ℝ), P {ω | g ω = ⊤}
      ≤ ∫⁻ x in Set.Ioi (1:ℝ), P {ω | ENNReal.ofReal x < g ω} :=
    lintegral_mono (fun x => measure_mono (hsub x))
  rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top hpos.ne'] at this
  exact absurd (lt_of_le_of_lt this hfin) (lt_irrefl _)

lemma tail_int_zero_le [IsProbabilityMeasure P] (g : Ω → ℝ≥0∞) (α : ℝ)
    (h184 : ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < g ω}
        ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal a < g ω}) :
    ∫⁻ x in Set.Ioi (0:ℝ), P {ω | ENNReal.ofReal x < g ω} ≤ ENNReal.ofReal α := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε' : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioc 0 (ε:ℝ) ∪ Set.Ioi (ε:ℝ) :=
    (Set.Ioc_union_Ioi_eq_Ioi hε'.le).symm
  rw [hsplit]
  calc ∫⁻ x in Set.Ioc 0 (ε:ℝ) ∪ Set.Ioi (ε:ℝ), P {ω | ENNReal.ofReal x < g ω}
      ≤ (∫⁻ x in Set.Ioc 0 (ε:ℝ), P {ω | ENNReal.ofReal x < g ω})
          + ∫⁻ x in Set.Ioi (ε:ℝ), P {ω | ENNReal.ofReal x < g ω} := lintegral_union_le _ _ _
    _ ≤ (∫⁻ _ in Set.Ioc 0 (ε:ℝ), (1:ℝ≥0∞))
          + ENNReal.ofReal α * P {ω | ENNReal.ofReal (ε:ℝ) < g ω} := by
        gcongr
        · exact prob_le_one
        · exact h184 ε hε'
    _ ≤ ε + ENNReal.ofReal α := by
        rw [setLIntegral_const, Real.volume_Ioc]
        gcongr
        · simp
        · calc ENNReal.ofReal α * P {ω | ENNReal.ofReal (ε:ℝ) < g ω}
              ≤ ENNReal.ofReal α * 1 := by gcongr; exact prob_le_one
            _ = _ := mul_one _
    _ = ENNReal.ofReal α + ε := add_comm _ _

lemma hasDerivAt_exp_mul (t x : ℝ) :
    HasDerivAt (fun s => Real.exp (t * s)) (t * Real.exp (t * x)) x := by
  have h := ((hasDerivAt_id x).const_mul t).exp
  simpa [mul_comm] using h

lemma integral_t_exp (t r : ℝ) :
    ∫ s in (0:ℝ)..r, t * Real.exp (t * s) = Real.exp (t * r) - 1 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => Real.exp (t * s))
    (fun x _ => hasDerivAt_exp_mul t x)]
  · simp
  · exact (by fun_prop : Continuous fun s => t * Real.exp (t * s)).intervalIntegrable _ _

/-- (B1) -/
lemma ofReal_exp_sub_one_eq (t : ℝ) (ht : 0 < t) {y : ℝ} (hy : 0 < y) :
    ENNReal.ofReal (Real.exp (t * y) - 1)
      = ∫⁻ x in Set.Ioo 0 y, ENNReal.ofReal (t * Real.exp (t * x)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hy.le, integral_t_exp]
  · exact ((by fun_prop : Continuous fun s => t * Real.exp (t * s)).integrableOn_Icc).mono_set
      Set.Ioo_subset_Icc_self
  · exact ae_of_all _ (fun x => by positivity)

/-- (B2) the Tonelli swap. -/
lemma swap_bound [IsProbabilityMeasure P] (g : Ω → ℝ≥0∞) (α : ℝ) (hα : 0 < α)
    (h184 : ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < g ω}
        ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal a < g ω})
    (t : ℝ) (ht : 0 < t) (N : ℝ) :
    ∫⁻ y in Set.Ioo 0 N, P {ω | ENNReal.ofReal y < g ω} * ENNReal.ofReal (Real.exp (t * y) - 1)
      ≤ ENNReal.ofReal (α * t) *
        ∫⁻ x in Set.Ioo 0 N, ENNReal.ofReal (Real.exp (t * x)) * P {ω | ENNReal.ofReal x < g ω} := by
  set m : ℝ → ℝ≥0∞ := fun x => P {ω | ENNReal.ofReal x < g ω} with hm
  have hmm : Measurable m := tailm_measurable P g
  set G : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (t * Real.exp (t * x)) with hG
  have hGm : Measurable G := by fun_prop
  let H : ℝ → ℝ → ℝ≥0∞ := fun x y => if 0 < x ∧ x < y ∧ y < N then G x * m y else 0
  have hH : Measurable (Function.uncurry H) := by
    have hS : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < N} :=
      (measurableSet_lt measurable_const measurable_fst).inter
        ((measurableSet_lt measurable_fst measurable_snd).inter
          (measurableSet_lt measurable_snd measurable_const))
    exact Measurable.ite hS ((hGm.comp measurable_fst).mul (hmm.comp measurable_snd))
      measurable_const
  -- step 1: LHS = ∫⁻ y, ∫⁻ x, H x y
  have h1 : ∫⁻ y in Set.Ioo 0 N, m y * ENNReal.ofReal (Real.exp (t * y) - 1)
      = ∫⁻ y, ∫⁻ x, H x y := by
    rw [← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ Set.Ioo 0 N
    · rw [Set.indicator_of_mem hy, ofReal_exp_sub_one_eq t ht hy.1, ← lintegral_const_mul' _ _
        (measure_ne_top _ _), ← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ Set.Ioo 0 y
      · rw [Set.indicator_of_mem hx]
        simp only [H, hx.1, hx.2, hy.2, and_self, if_true]
        ring
      · rw [Set.indicator_of_notMem hx]
        simp only [H]
        rw [if_neg]
        rintro ⟨h0, hxy, -⟩
        exact hx ⟨h0, hxy⟩
    · rw [Set.indicator_of_notMem hy]
      symm
      calc ∫⁻ x, H x y = ∫⁻ _x, (0:ℝ≥0∞) := lintegral_congr (fun x => by
              simp only [H]
              rw [if_neg]
              rintro ⟨h0, hxy, hyN⟩
              exact hy ⟨h0.trans hxy, hyN⟩)
        _ = 0 := lintegral_zero
  -- step 2: swap
  have h2 : ∫⁻ y, ∫⁻ x, H x y = ∫⁻ x, ∫⁻ y, H x y :=
    (lintegral_lintegral_swap hH.aemeasurable).symm
  -- step 3: inner bound
  have h3 : ∀ x, ∫⁻ y, H x y ≤ (Set.Ioo 0 N).indicator (fun x => G x * (ENNReal.ofReal α * m x)) x := by
    intro x
    by_cases hx : x ∈ Set.Ioo 0 N
    · rw [Set.indicator_of_mem hx]
      have : ∫⁻ y, H x y = ∫⁻ y in Set.Ioo x N, G x * m y := by
        rw [← lintegral_indicator measurableSet_Ioo]
        apply lintegral_congr
        intro y
        by_cases hy : y ∈ Set.Ioo x N
        · rw [Set.indicator_of_mem hy]
          simp only [H, hx.1, hy.1, hy.2, and_self, if_true]
        · rw [Set.indicator_of_notMem hy]
          simp only [H]
          rw [if_neg]
          rintro ⟨-, hxy, hyN⟩
          exact hy ⟨hxy, hyN⟩
      rw [this, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      calc ∫⁻ y in Set.Ioo x N, m y ≤ ∫⁻ y in Set.Ioi x, m y :=
            lintegral_mono_set Set.Ioo_subset_Ioi_self
        _ ≤ ENNReal.ofReal α * m x := h184 x hx.1
    · rw [Set.indicator_of_notMem hx]
      apply le_of_eq
      calc ∫⁻ y, H x y = ∫⁻ _y, (0:ℝ≥0∞) := lintegral_congr (fun y => by
              simp only [H]
              rw [if_neg]
              rintro ⟨h0, hxy, hyN⟩
              exact hx ⟨h0, hxy.trans hyN⟩)
        _ = 0 := lintegral_zero
  rw [h1, h2]
  calc ∫⁻ x, ∫⁻ y, H x y
      ≤ ∫⁻ x, (Set.Ioo 0 N).indicator (fun x => G x * (ENNReal.ofReal α * m x)) x :=
        lintegral_mono h3
    _ = ∫⁻ x in Set.Ioo 0 N, G x * (ENNReal.ofReal α * m x) := lintegral_indicator measurableSet_Ioo _
    _ = ∫⁻ x in Set.Ioo 0 N, ENNReal.ofReal (α * t) * (ENNReal.ofReal (Real.exp (t * x)) * m x) := by
        apply lintegral_congr
        intro x
        simp only [G]
        rw [ENNReal.ofReal_mul ht.le, ENNReal.ofReal_mul hα.le]
        ring
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- (B) truncated bound. -/
lemma trunc_bound [IsProbabilityMeasure P] (g : Ω → ℝ≥0∞) (α : ℝ) (hα : 0 < α)
    (h184 : ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < g ω}
        ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal a < g ω})
    (t : ℝ) (ht : 0 < t) (htα : t < α⁻¹) (N : ℝ) :
    ∫⁻ x in Set.Ioo 0 N, ENNReal.ofReal (Real.exp (t * x)) * P {ω | ENNReal.ofReal x < g ω}
      ≤ ENNReal.ofReal (α / (1 - α * t)) := by
  set m : ℝ → ℝ≥0∞ := fun x => P {ω | ENNReal.ofReal x < g ω} with hm
  have hmm : Measurable m := tailm_measurable P g
  set J := ∫⁻ x in Set.Ioo 0 N, ENNReal.ofReal (Real.exp (t * x)) * m x with hJ
  have hαt : α * t < 1 := by
    have := mul_lt_mul_of_pos_right htα hα
    rwa [inv_mul_cancel₀ hα.ne', mul_comm] at this
  have hJfin : J < ⊤ := by
    calc J ≤ ∫⁻ _ in Set.Ioo 0 N, ENNReal.ofReal (Real.exp (t * N)) := by
          apply setLIntegral_mono measurable_const
          intro x hx
          calc ENNReal.ofReal (Real.exp (t * x)) * m x
              ≤ ENNReal.ofReal (Real.exp (t * N)) * 1 := by
                gcongr
                · exact hx.2.le
                · exact prob_le_one
            _ = _ := mul_one _
      _ < ⊤ := by
          rw [setLIntegral_const, Real.volume_Ioo]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hJle : J ≤ ENNReal.ofReal α + ENNReal.ofReal (α * t) * J := by
    have hsplit : ∀ x ∈ Set.Ioo (0:ℝ) N, ENNReal.ofReal (Real.exp (t * x)) * m x
        = m x + m x * ENNReal.ofReal (Real.exp (t * x) - 1) := by
      intro x hx
      have h1 : Real.exp (t * x) = 1 + (Real.exp (t * x) - 1) := by ring
      have h2 : 0 ≤ Real.exp (t * x) - 1 := by
        have : 1 ≤ Real.exp (t * x) := Real.one_le_exp (mul_nonneg ht.le hx.1.le)
        linarith
      rw [h1, ENNReal.ofReal_add zero_le_one h2, ENNReal.ofReal_one, add_mul, one_mul, mul_comm]
      congr 2
      ring
    calc J = ∫⁻ x in Set.Ioo 0 N, (m x + m x * ENNReal.ofReal (Real.exp (t * x) - 1)) :=
          setLIntegral_congr_fun measurableSet_Ioo hsplit
      _ = (∫⁻ x in Set.Ioo 0 N, m x)
            + ∫⁻ x in Set.Ioo 0 N, m x * ENNReal.ofReal (Real.exp (t * x) - 1) :=
          lintegral_add_left hmm _
      _ ≤ ENNReal.ofReal α + ENNReal.ofReal (α * t) * J := by
          gcongr
          · calc ∫⁻ x in Set.Ioo 0 N, m x ≤ ∫⁻ x in Set.Ioi 0, m x :=
                  lintegral_mono_set Set.Ioo_subset_Ioi_self
              _ ≤ ENNReal.ofReal α := tail_int_zero_le g α h184
          · exact swap_bound g α hα h184 t ht N
  -- solve in the reals
  have hR : J.toReal ≤ α + α * t * J.toReal := by
    have hfin2 : ENNReal.ofReal α + ENNReal.ofReal (α * t) * J ≠ ⊤ := by
      apply ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ?_⟩
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJfin.ne
    have := ENNReal.toReal_mono hfin2 hJle
    rwa [ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJfin.ne),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hα.le,
      ENNReal.toReal_ofReal (by positivity)] at this
  have hR2 : J.toReal ≤ α / (1 - α * t) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  calc J = ENNReal.ofReal J.toReal := (ENNReal.ofReal_toReal hJfin.ne).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hR2

/-- (C) untruncated bound. -/
lemma full_bound [IsProbabilityMeasure P] (g : Ω → ℝ≥0∞) (α : ℝ) (hα : 0 < α)
    (h184 : ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < g ω}
        ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal a < g ω})
    (t : ℝ) (ht : 0 < t) (htα : t < α⁻¹) :
    ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (Real.exp (t * x)) * P {ω | ENNReal.ofReal x < g ω}
      ≤ ENNReal.ofReal (α / (1 - α * t)) := by
  set h : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (t * x)) * P {ω | ENNReal.ofReal x < g ω}
    with hh
  have hhm : Measurable h := by
    apply Measurable.mul (by fun_prop) (tailm_measurable P g)
  have hpt : ∀ x, (Set.Ioi 0).indicator h x = ⨆ n : ℕ, (Set.Ioo 0 (n:ℝ)).indicator h x := by
    intro x
    apply le_antisymm
    · by_cases hx : x ∈ Set.Ioi (0:ℝ)
      · rw [Set.indicator_of_mem hx]
        refine le_iSup_of_le (⌈x⌉₊ + 1) ?_
        rw [Set.indicator_of_mem]
        refine ⟨hx, ?_⟩
        push_cast
        linarith [Nat.le_ceil x]
      · rw [Set.indicator_of_notMem hx]; exact zero_le
    · apply iSup_le
      intro n
      exact Set.indicator_le_indicator_of_subset Set.Ioo_subset_Ioi_self (fun _ => by simp) x
  have hpt' : (Set.Ioi 0).indicator h = fun x => ⨆ n : ℕ, (Set.Ioo 0 (n:ℝ)).indicator h x :=
    funext hpt
  rw [← lintegral_indicator measurableSet_Ioi, hpt']
  rw [lintegral_iSup (fun n => hhm.indicator measurableSet_Ioo)]
  · apply iSup_le
    intro n
    rw [lintegral_indicator measurableSet_Ioo]
    exact trunc_bound g α hα h184 t ht htα n
  · intro a b hab x
    exact Set.indicator_le_indicator_of_subset
      (Set.Ioo_subset_Ioo_right (by exact_mod_cast hab)) (fun _ => by simp) x

/-- (A) layer cake for the exponential moment. -/
lemma exp_moment_eq [IsProbabilityMeasure P] (g : Ω → ℝ≥0∞) (hg : Measurable g)
    (hfin : ∀ᵐ ω ∂P, g ω ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (g ω).toReal)) ∂P
      = 1 + ∫⁻ x in Set.Ioi 0,
          P {ω | ENNReal.ofReal x < g ω} * ENNReal.ofReal (t * Real.exp (t * x)) := by
  have h1 : ∀ ω, ENNReal.ofReal (Real.exp (t * (g ω).toReal))
      = 1 + ENNReal.ofReal (∫ s in (0:ℝ)..(g ω).toReal, t * Real.exp (t * s)) := by
    intro ω
    rw [integral_t_exp]
    have h2 : 0 ≤ Real.exp (t * (g ω).toReal) - 1 := by
      have : 1 ≤ Real.exp (t * (g ω).toReal) := Real.one_le_exp (by positivity)
      linarith
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one h2]
    congr 1; ring
  simp_rw [h1]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  congr 1
  rw [lintegral_comp_eq_lintegral_meas_lt_mul P (f := fun ω => (g ω).toReal)
    (g := fun s => t * Real.exp (t * s)) (ae_of_all _ (fun ω => ENNReal.toReal_nonneg))
    hg.ennreal_toReal.aemeasurable
    (fun r _ => (by fun_prop : Continuous fun s => t * Real.exp (t * s)).intervalIntegrable _ _)
    (ae_of_all _ (fun s => by positivity))]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s hs
  beta_reduce
  congr 1
  apply measure_congr
  filter_upwards [hfin] with ω hω
  show (s < (g ω).toReal) = (ENNReal.ofReal s < g ω)
  rw [eq_iff_iff]
  exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hs) hω).symm

theorem lemma_18_1_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → ℝ≥0∞) (hg : Measurable g) (α : ℝ) (hα : 0 < α)
    (h184 : ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < g ω}
        ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal a < g ω}) :
    (∀ᵐ ω ∂P, g ω ≠ ⊤) ∧
    ∀ t : ℝ, 0 < t → t < α⁻¹ →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (g ω).toReal)) ∂P
        ≤ ENNReal.ofReal (1 / (1 - α * t)) := by
  have hfin := ae_ne_top_of_tail g α h184
  refine ⟨hfin, ?_⟩
  intro t ht htα
  have hαt : α * t < 1 := by
    have := mul_lt_mul_of_pos_right htα hα
    rwa [inv_mul_cancel₀ hα.ne', mul_comm] at this
  rw [exp_moment_eq g hg hfin t ht]
  have hre : ∫⁻ x in Set.Ioi 0, P {ω | ENNReal.ofReal x < g ω} * ENNReal.ofReal (t * Real.exp (t * x))
      = ENNReal.ofReal t *
        ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (Real.exp (t * x)) * P {ω | ENNReal.ofReal x < g ω} := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_mul ht.le]
    ring
  rw [hre]
  calc 1 + ENNReal.ofReal t *
        ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (Real.exp (t * x)) * P {ω | ENNReal.ofReal x < g ω}
      ≤ 1 + ENNReal.ofReal t * ENNReal.ofReal (α / (1 - α * t)) := by
        gcongr
        exact full_bound g α hα h184 t ht htα
    _ = ENNReal.ofReal (1 + t * (α / (1 - α * t))) := by
        rw [ENNReal.ofReal_add zero_le_one (by
            have : 0 < 1 - α * t := by linarith
            positivity), ENNReal.ofReal_one, ENNReal.ofReal_mul ht.le]
    _ = ENNReal.ofReal (1 / (1 - α * t)) := by
        congr 1
        have : 1 - α * t ≠ 0 := by linarith
        rw [eq_div_iff this, add_mul, mul_assoc, div_mul_cancel₀ _ this]
        ring

end L181

end BurkholderDFI.NonnegExp

open BurkholderDFI.NonnegExp
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → ℝ≥0∞) (hg : Measurable g) (α : ℝ) (hα : 0 < α)
    (h184 : ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < g ω} ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal a < g ω}) :
    (∀ᵐ ω ∂P, g ω ≠ ⊤) ∧
    ∀ t : ℝ, 0 < t → t < α⁻¹ →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (g ω).toReal)) ∂P ≤ ENNReal.ofReal (1 / (1 - α * t)) := by
  exact lemma_18_1_core P g hg α hα h184
