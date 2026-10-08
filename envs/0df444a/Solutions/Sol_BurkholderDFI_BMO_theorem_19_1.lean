-- Prove2me | solution 1 for BurkholderDFI.BMO.theorem_19_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:12:11.954368+00:00
-- url     : https://prove2.me/submissions/8d66648f-6f39-48e4-8f44-fd6931a71e90

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Definitions.Def_BurkholderDFI_BMO_Condition



namespace BurkholderDFI.BMO

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


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

section Tail

open BurkholderDFI.SquareFnLp

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {ℱ : Filtration ℕ mΩ}
  {f : ℕ → Ω → ℝ}

lemma sqFnN_sq (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    sqFnN f n ω ^ 2 = ∑ k ∈ Finset.Icc 1 n, ENNReal.ofReal (dseq f k ω ^ 2) := by
  unfold sqFnN
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]

lemma Icc_sum_eq_range (g : ℕ → ℝ≥0∞) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, g k = ∑ k ∈ Finset.range n, g (k + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

lemma sqFn_sq_eq_tsum (f : ℕ → Ω → ℝ) (ω : Ω) :
    sqFn f ω ^ 2 = ∑' k : ℕ, ENNReal.ofReal (dseq f (k + 1) ω ^ 2) := by
  unfold sqFn
  rw [ENNReal.iSup_pow, ENNReal.tsum_eq_iSup_nat]
  congr 1
  ext n
  rw [sqFnN_sq, Icc_sum_eq_range]

lemma sqFn_sq_split (f : ℕ → Ω → ℝ) (ω : Ω) (m : ℕ) :
    sqFn f ω ^ 2 = sqFnN f m ω ^ 2 + ∑' j : ℕ, ENNReal.ofReal (dseq f (m + 1 + j) ω ^ 2) := by
  rw [sqFn_sq_eq_tsum, sqFnN_sq, Icc_sum_eq_range,
    ← Summable.sum_add_tsum_nat_add' (k := m) ENNReal.summable]
  congr 1
  apply tsum_congr
  intro j
  rw [show j + m + 1 = m + 1 + j by omega]

lemma measurable_f_filt (hf : Martingale f ℱ P) (n : ℕ) : Measurable[ℱ n] (f n) :=
  (hf.stronglyMeasurable n).measurable

lemma measurable_dseq_filt (hf : Martingale f ℱ P) {k n : ℕ} (hkn : k ≤ n) :
    Measurable[ℱ n] (dseq f k) := by
  by_cases h0 : k = 0
  · subst h0
    have : dseq f 0 = fun _ => (0:ℝ) := by ext ω; simp [dseq]
    rw [this]; exact measurable_const
  by_cases h1 : k = 1
  · subst h1
    have : dseq f 1 = f 1 := by ext ω; simp [dseq]
    rw [this]; exact (measurable_f_filt hf 1).mono (ℱ.mono hkn) le_rfl
  have : dseq f k = fun ω => f k ω - f (k - 1) ω := by ext ω; simp [dseq, h0, h1]
  rw [this]
  exact ((measurable_f_filt hf k).mono (ℱ.mono hkn) le_rfl).sub
    ((measurable_f_filt hf (k - 1)).mono (ℱ.mono (by omega)) le_rfl)

lemma measurable_sqFnN_filt (hf : Martingale f ℱ P) (n : ℕ) : Measurable[ℱ n] (sqFnN f n) := by
  unfold sqFnN
  exact (Finset.measurable_sum _ (fun k hk =>
    (measurable_dseq_filt hf (Finset.mem_Icc.mp hk).2).pow_const 2)).sqrt.ennreal_ofReal

lemma measurable_sqFnN (hf : Martingale f ℱ P) (n : ℕ) : Measurable (sqFnN f n) :=
  (measurable_sqFnN_filt hf n).mono (ℱ.le n) le_rfl

lemma measurable_sqFn (hf : Martingale f ℱ P) : Measurable (sqFn f) :=
  Measurable.iSup (fun n => measurable_sqFnN hf n)

lemma measurable_dseq (hf : Martingale f ℱ P) (k : ℕ) : Measurable (dseq f k) :=
  (measurable_dseq_filt hf le_rfl).mono (ℱ.le k) le_rfl

lemma measurable_tailSum (hf : Martingale f ℱ P) (n : ℕ) :
    Measurable (fun ω => ∑' j : ℕ, ENNReal.ofReal (dseq f (n + j) ω ^ 2)) :=
  Measurable.ennreal_tsum fun j => ((measurable_dseq hf (n + j)).pow_const 2).ennreal_ofReal

/-- first hitting event: `S_n² > a` and `S_k² ≤ a` for all `k < n`. -/
def hitSet (f : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) : Set Ω :=
  {ω | ENNReal.ofReal a < sqFnN f n ω ^ 2 ∧ ∀ k < n, sqFnN f k ω ^ 2 ≤ ENNReal.ofReal a}

lemma measurableSet_hitSet (hf : Martingale f ℱ P) (a : ℝ) (n : ℕ) :
    MeasurableSet[ℱ n] (hitSet f a n) := by
  have hT : ∀ k ≤ n, Measurable[ℱ n] (fun ω => sqFnN f k ω ^ 2) := fun k hk =>
    ((measurable_sqFnN_filt hf k).mono (ℱ.mono hk) le_rfl).pow_const 2
  unfold hitSet
  rw [Set.setOf_and, Set.setOf_forall]
  refine MeasurableSet.inter (measurableSet_lt measurable_const (hT n le_rfl))
    (MeasurableSet.iInter fun k => ?_)
  by_cases hk : k < n
  · simp only [hk, true_implies]
    exact measurableSet_le (hT k hk.le) measurable_const
  · simp only [hk, false_implies, Set.setOf_true]
    exact MeasurableSet.univ

lemma hitSet_disjoint (f : ℕ → Ω → ℝ) (a : ℝ) : Pairwise (fun m n => Disjoint (hitSet f a m) (hitSet f a n)) := by
  intro m n hmn
  rw [Set.disjoint_left]
  intro ω hm hn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact absurd (hn.2 m h) (not_le.mpr hm.1)
  · exact absurd (hm.2 n h) (not_le.mpr hn.1)

lemma iUnion_hitSet (f : ℕ → Ω → ℝ) (a : ℝ) :
    (⋃ n, hitSet f a n) = {ω | ENNReal.ofReal a < sqFn f ω ^ 2} := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, hitSet]
  constructor
  · rintro ⟨n, hn, -⟩
    refine lt_of_lt_of_le hn (pow_le_pow_left' ?_ 2)
    exact le_iSup (fun n => sqFnN f n ω) n
  · intro h
    have hex : ∃ n, ENNReal.ofReal a < sqFnN f n ω ^ 2 := by
      unfold sqFn at h
      rw [ENNReal.iSup_pow] at h
      exact lt_iSup_iff.mp h
    classical
    refine ⟨Nat.find hex, Nat.find_spec hex, fun k hk => ?_⟩
    exact not_lt.mp (Nat.find_min hex hk)

lemma hitSet_zero (f : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a) : hitSet f a 0 = ∅ := by
  ext ω
  simp only [hitSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h
  exfalso
  have : sqFnN f 0 ω = 0 := by simp [sqFnN]
  rw [this] at h
  simp at h

lemma volume_set_le (a : ℝ) (ha : 0 ≤ a) (c : ℝ≥0∞) :
    volume ({x : ℝ | ENNReal.ofReal x < ENNReal.ofReal a + c} ∩ Set.Ioi a) ≤ c := by
  by_cases hc : c = ⊤
  · rw [hc]; exact le_top
  · calc volume ({x : ℝ | ENNReal.ofReal x < ENNReal.ofReal a + c} ∩ Set.Ioi a)
        ≤ volume (Set.Ioo a (a + c.toReal)) := by
          apply measure_mono
          rintro x ⟨hx1, hx2⟩
          refine ⟨hx2, ?_⟩
          simp only [Set.mem_ofPred_eq] at hx1
          have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt ha hx2)
          rw [← ENNReal.ofReal_toReal hc, ← ENNReal.ofReal_add ha ENNReal.toReal_nonneg,
            ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx0] at hx1
          exact hx1
      _ = c := by rw [Real.volume_Ioo, add_sub_cancel_left, ENNReal.ofReal_toReal hc]

lemma pointwise_bound (f : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a) (ω : Ω) :
    volume ({x : ℝ | ENNReal.ofReal x < sqFn f ω ^ 2} ∩ Set.Ioi a)
      ≤ ∑' n : ℕ, (hitSet f a n).indicator
          (fun ω => ∑' j : ℕ, ENNReal.ofReal (dseq f (n + j) ω ^ 2)) ω := by
  by_cases hω : ω ∈ ⋃ n, hitSet f a n
  · rw [Set.mem_iUnion] at hω
    obtain ⟨n, hn⟩ := hω
    refine le_trans ?_ (ENNReal.le_tsum n)
    rw [Set.indicator_of_mem hn]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
      rcases n with _ | m
      · exfalso
        have := hn
        rw [hitSet_zero f a ha] at this
        exact this
      · exact ⟨m, rfl⟩
    have hle : sqFn f ω ^ 2
        ≤ ENNReal.ofReal a + ∑' j, ENNReal.ofReal (dseq f (m + 1 + j) ω ^ 2) := by
      rw [sqFn_sq_split f ω m]
      gcongr
      exact hn.2 m (Nat.lt_succ_self m)
    calc volume ({x : ℝ | ENNReal.ofReal x < sqFn f ω ^ 2} ∩ Set.Ioi a)
        ≤ volume ({x : ℝ | ENNReal.ofReal x
            < ENNReal.ofReal a + ∑' j, ENNReal.ofReal (dseq f (m + 1 + j) ω ^ 2)} ∩ Set.Ioi a) := by
          apply measure_mono
          rintro x ⟨hx1, hx2⟩
          exact ⟨lt_of_lt_of_le hx1 hle, hx2⟩
      _ ≤ _ := volume_set_le a ha.le _
  · rw [iUnion_hitSet] at hω
    simp only [Set.mem_ofPred_eq, not_lt] at hω
    have : {x : ℝ | ENNReal.ofReal x < sqFn f ω ^ 2} ∩ Set.Ioi a = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioi, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hx hax
      exact absurd (lt_of_lt_of_le hx hω) (not_lt.mpr (ENNReal.ofReal_le_ofReal hax.le))
    rw [this, measure_empty]
    exact zero_le

theorem tail_integral_bound_core [IsProbabilityMeasure P]
    (hf : Martingale f ℱ P) (h191 : BMOCondition ℱ P f) :
    ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < sqFn f ω ^ 2}
        ≤ P {ω | ENNReal.ofReal a < sqFn f ω ^ 2} := by
  intro a ha
  have hT : Measurable (fun ω => sqFn f ω ^ 2) := (measurable_sqFn hf).pow_const 2
  set R : ℕ → Ω → ℝ≥0∞ := fun n ω => ∑' j : ℕ, ENNReal.ofReal (dseq f (n + j) ω ^ 2) with hR
  have hRm : ∀ n, Measurable (R n) := fun n => measurable_tailSum hf n
  have hE : ∀ n, MeasurableSet (hitSet f a n) := fun n => ℱ.le n _ (measurableSet_hitSet hf a n)
  -- Step 1: Tonelli
  set S : Set (ℝ × Ω) := {p | ENNReal.ofReal p.1 < sqFn f p.2 ^ 2} with hSdef
  have hS : MeasurableSet S :=
    measurableSet_lt (measurable_fst.ennreal_ofReal) (hT.comp measurable_snd)
  have hswap := lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi a)) (ν := P)
    (f := fun x ω => S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω))
    (measurable_const.indicator hS).aemeasurable
  have h1 : ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < sqFn f ω ^ 2}
      = ∫⁻ ω, volume ({x : ℝ | ENNReal.ofReal x < sqFn f ω ^ 2} ∩ Set.Ioi a) ∂P := by
    have hl : ∀ x : ℝ, ∫⁻ ω, S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω) ∂P
        = P {ω | ENNReal.ofReal x < sqFn f ω ^ 2} := by
      intro x
      have : (fun ω => S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω))
          = {ω | ENNReal.ofReal x < sqFn f ω ^ 2}.indicator 1 := by
        ext ω
        simp [S, Set.indicator_apply]
      rw [this, lintegral_indicator_one (measurableSet_lt measurable_const hT)]
    have hr : ∀ ω : Ω, ∫⁻ x in Set.Ioi a, S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω)
        = volume ({x : ℝ | ENNReal.ofReal x < sqFn f ω ^ 2} ∩ Set.Ioi a) := by
      intro ω
      have : (fun x => S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω))
          = {x : ℝ | ENNReal.ofReal x < sqFn f ω ^ 2}.indicator 1 := by
        ext x
        simp [S, Set.indicator_apply]
      rw [this, lintegral_indicator_one (measurableSet_lt ENNReal.measurable_ofReal measurable_const),
        Measure.restrict_apply (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
    simp_rw [hl, hr] at hswap
    exact hswap
  rw [h1]
  calc ∫⁻ ω, volume ({x : ℝ | ENNReal.ofReal x < sqFn f ω ^ 2} ∩ Set.Ioi a) ∂P
      ≤ ∫⁻ ω, ∑' n : ℕ, (hitSet f a n).indicator (R n) ω ∂P :=
        lintegral_mono (fun ω => pointwise_bound f a ha ω)
    _ = ∑' n : ℕ, ∫⁻ ω, (hitSet f a n).indicator (R n) ω ∂P :=
        lintegral_tsum (fun n => ((hRm n).indicator (hE n)).aemeasurable)
    _ = ∑' n : ℕ, ∫⁻ ω in hitSet f a n, R n ω ∂P := by
        congr 1; ext n; exact lintegral_indicator (hE n) _
    _ = ∑' n : ℕ, ∫⁻ ω in hitSet f a n, condLExp (ℱ n) P (R n) ω ∂P := by
        congr 1; ext n
        exact (setLIntegral_condLExp (ℱ.le n) P (R n) (measurableSet_hitSet hf a n)).symm
    _ ≤ ∑' n : ℕ, ∫⁻ _ in hitSet f a n, (1 : ℝ≥0∞) ∂P := by
        apply ENNReal.tsum_le_tsum
        intro n
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          rw [hitSet_zero f a ha, Measure.restrict_empty, lintegral_zero_measure]
          exact zero_le
        · apply lintegral_mono_ae
          apply ae_restrict_of_ae
          exact h191 n hn
    _ = ∑' n : ℕ, P (hitSet f a n) := by
        congr 1; ext n; exact setLIntegral_one _
    _ = P (⋃ n, hitSet f a n) := (measure_iUnion (hitSet_disjoint f a) hE).symm
    _ = P {ω | ENNReal.ofReal a < sqFn f ω ^ 2} := by rw [iUnion_hitSet]

end Tail


section Goal

open BurkholderDFI.SquareFnLp

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {ℱ : Filtration ℕ mΩ}
  {f : ℕ → Ω → ℝ}

theorem theorem_19_1_core [IsProbabilityMeasure P]
    (hf : Martingale f ℱ P) (h191 : BMOCondition ℱ P f) :
    (∀ᵐ ω ∂P, sqFn f ω ≠ ⊤) ∧
    ∀ t : ℝ, 0 < t → t < 1 →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * ((sqFn f ω).toReal) ^ 2)) ∂P
        ≤ ENNReal.ofReal ((1 - t)⁻¹) := by
  have htail := tail_integral_bound_core hf h191
  have h184 : ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < sqFn f ω ^ 2}
        ≤ ENNReal.ofReal 1 * P {ω | ENNReal.ofReal a < sqFn f ω ^ 2} := by
    intro a ha
    rw [ENNReal.ofReal_one, one_mul]
    exact htail a ha
  obtain ⟨hfin, hexp⟩ := lemma_18_1_core P (fun ω => sqFn f ω ^ 2)
    ((measurable_sqFn hf).pow_const 2) 1 one_pos h184
  refine ⟨?_, ?_⟩
  · filter_upwards [hfin] with ω hω
    intro h
    apply hω
    simp only [h]
    simp
  · intro t ht ht1
    have := hexp t ht (by rwa [inv_one])
    rw [one_mul, one_div] at this
    have hre : ∀ ω, t * (sqFn f ω).toReal ^ 2 = t * (sqFn f ω ^ 2).toReal := fun ω => by
      rw [ENNReal.toReal_pow]
    simp_rw [hre]
    exact this

end Goal

end BurkholderDFI.BMO

open BurkholderDFI.BMO
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (h191 : BMOCondition ℱ P f) :
    (∀ᵐ ω ∂P, BurkholderDFI.SquareFnLp.sqFn f ω ≠ ⊤) ∧
    ∀ t : ℝ, 0 < t → t < 1 →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * ((BurkholderDFI.SquareFnLp.sqFn f ω).toReal) ^ 2)) ∂P
        ≤ ENNReal.ofReal ((1 - t)⁻¹) := by
  exact theorem_19_1_core hf h191
