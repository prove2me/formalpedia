-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_finitecap_true_fullcell_Hessian_coeff_measurable_bounded
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:21:37.860252+00:00
-- url     : https://prove2.me/submissions/1b599b29-ceda-48ee-9395-1d8e4db8c984

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
theorem AvramDividend.Classical.avram_ga_original_finitecap_true_fullcell_Hessian_coeff_measurable_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) (j : ℕ) :
    let H : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let b : ℝ := C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℝ := x + X.X s ω - rightLimit D s ω
      if s < ρ ω ∧ s + Δ ≤ ρ ω then
        Real.exp (-(q * (s : ℝ))) *
          (if Y ≤ b then iteratedDeriv 2 w Y else 0)
      else 0
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ m i : ℕ, Measurable (H m i) ∧
        ∀ ω : Ω, |H m i ω| ≤ K := by
  intro H
  obtain ⟨⟨⟨_, hDmono, _, hDad⟩, _⟩, _⟩ := hD
  have hXm : ∀ t, Measurable (X.X t) := fun t => (X.adapted t).mono (𝓕.le t) le_rfl
  have hDm : ∀ t, Measurable (D t) := fun t => (hDad t).mono (𝓕.le t) le_rfl
  -- right limits along a sequence
  have hbdd : ∀ (t : ℝ≥0) (ω : Ω), BddBelow (range fun s : Ioi t => D s ω) := by
    intro t ω
    refine ⟨D t ω, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact hDmono ω (le_of_lt s.2)
  have hRL : ∀ (t : ℝ≥0) (ω : Ω), rightLimit D t ω =
      ⨅ k : ℕ, D (t + 1 / ((k : ℝ≥0) + 1)) ω := by
    intro t ω
    unfold rightLimit
    have hpos : ∀ k : ℕ, t < t + 1 / ((k : ℝ≥0) + 1) := by
      intro k
      have : (0 : ℝ≥0) < 1 / ((k : ℝ≥0) + 1) := by positivity
      exact lt_add_of_pos_right t this
    have hbddk : BddBelow (range fun k : ℕ => D (t + 1 / ((k : ℝ≥0) + 1)) ω) := by
      refine ⟨D t ω, ?_⟩
      rintro _ ⟨k, rfl⟩
      exact hDmono ω (le_of_lt (hpos k))
    apply le_antisymm
    · exact le_ciInf (fun k => ciInf_le (hbdd t ω) ⟨_, hpos k⟩)
    · haveI : Nonempty (Ioi t) := ⟨⟨t + 1, lt_add_of_pos_right t one_pos⟩⟩
      refine le_ciInf (fun s => ?_)
      have hs : (0 : ℝ) < (s : ℝ≥0) - (t : ℝ) := by
        have := s.2; simp only [mem_Ioi] at this
        have : (t : ℝ) < ((s : ℝ≥0) : ℝ) := by exact_mod_cast this
        linarith
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hs
      refine (ciInf_le hbddk k).trans (hDmono ω ?_)
      rw [← NNReal.coe_le_coe]
      push_cast
      linarith
  have hRLm : ∀ t, Measurable (rightLimit D t) := by
    intro t
    have : rightLimit D t = fun ω => ⨅ k : ℕ, D (t + 1 / ((k : ℝ≥0) + 1)) ω :=
      funext (hRL t)
    rw [this]
    exact Measurable.iInf (fun k => hDm _)
  -- the post-jump reserve stays above the floor
  have hYδ : ∀ (ω : Ω) (s : ℝ≥0), s < ρ ω → δ ≤ x + X.X s ω - rightLimit D s ω := by
    intro ω s hs
    by_contra hcon
    push Not at hcon
    set ε := rightLimit D s ω - (x + X.X s ω - δ) with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    have hrc : Tendsto (fun t => X.X t ω) (𝓝[>] s) (𝓝 (X.X s ω)) :=
      (X.rightCont ω s).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have h1 : ∀ᶠ t in 𝓝[>] s, X.X t ω < X.X s ω + ε :=
      hrc (Iio_mem_nhds (by linarith))
    have h2 : ∀ᶠ t in 𝓝[>] s, t ∈ Ioo s (ρ ω) := Ioo_mem_nhdsGT hs
    obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
    have hfl := hFloor ω t (lt_of_le_of_lt bot_le ht2.1) ht2.2
    unfold riskProcess at hfl
    have hle : rightLimit D s ω ≤ D t ω := ciInf_le (hbdd s ω) ⟨t, ht2.1⟩
    linarith
  -- bound for the second derivative on the compact window
  set b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) with hb
  set U : Set ℝ := {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} with hUdef
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt ENNReal.continuous_ofReal continuous_const)
  have hCpos : 0 < C.toReal := ENNReal.toReal_pos hC.ne' hFiniteCap
  have hblt : b < C.toReal := by
    rw [hb]
    have h1 : ((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ) < 1 := by
      rw [div_lt_one (by positivity)]; push_cast; linarith
    nlinarith
  have hsub : Icc δ b ⊆ U := by
    intro y hy
    refine ⟨lt_of_lt_of_le hδ hy.1, ?_⟩
    rw [ENNReal.ofReal_lt_iff_lt_toReal (by linarith [hy.1]) hFiniteCap]
    linarith [hy.2]
  have hcont : ContinuousOn (iteratedDeriv 2 w) U := by
    have h1 := hw.continuousOn_iteratedDerivWithin (m := 2) (by norm_num) hUopen.uniqueDiffOn
    exact h1.congr (fun y hy => (iteratedDerivWithin_of_isOpen hUopen hy).symm)
  obtain ⟨Kw, hKw⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont.mono hsub)
  have hderm : Measurable (iteratedDeriv 2 w) := by
    rw [iteratedDeriv_succ]
    exact measurable_deriv _
  refine ⟨max Kw 0, le_max_right _ _, fun m i => ⟨?_, fun ω => ?_⟩⟩
  · simp only [H]
    set Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1) with hΔ
    set s : ℝ≥0 := (i : ℝ≥0) * Δ with hs
    have h1 : MeasurableSet {ω | s < ρ ω} := by
      have hm := hρstop.measurableSet_le s
      have h' : {ω | s < ρ ω} = {ω | (ρ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)}ᶜ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
        rw [WithTop.coe_le_coe, not_le]
      rw [h']
      exact (𝓕.rightCont.le s _ hm).compl
    have h2 : MeasurableSet {ω | s + Δ ≤ ρ ω} := by
      have hm := hρstop.measurableSet_ge (s + Δ)
      have h' : {ω | s + Δ ≤ ρ ω} =
          {ω | ((s + Δ : ℝ≥0) : WithTop ℝ≥0) ≤ (ρ ω : WithTop ℝ≥0)} := by
        ext ω
        simp only [Set.mem_setOf_eq]
        exact WithTop.coe_le_coe.symm
      rw [h']
      exact 𝓕.rightCont.le _ _ hm
    have hYm : Measurable (fun ω => x + X.X s ω - rightLimit D s ω) :=
      (measurable_const.add (hXm s)).sub (hRLm s)
    refine Measurable.ite (h1.inter h2) ?_ measurable_const
    exact measurable_const.mul
      (Measurable.ite (measurableSet_le hYm measurable_const) (hderm.comp hYm) measurable_const)
  · simp only [H]
    set Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1) with hΔ
    set s : ℝ≥0 := (i : ℝ≥0) * Δ with hs
    have hexp : Real.exp (-(q * (s : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ q * (s : ℝ) := mul_nonneg hq.le s.2
      linarith
    have hexp0 : 0 < Real.exp (-(q * (s : ℝ))) := Real.exp_pos _
    split_ifs with hc hY
    · have hδY := hYδ ω s hc.1
      have hK := hKw _ ⟨hδY, hY⟩
      rw [Real.norm_eq_abs] at hK
      rw [abs_mul, abs_of_pos hexp0]
      calc Real.exp (-(q * (s : ℝ))) * |iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)|
          ≤ 1 * Kw := by
            apply mul_le_mul hexp hK (abs_nonneg _) zero_le_one
        _ ≤ max Kw 0 := by rw [one_mul]; exact le_max_left _ _
    · simp
    · simp

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) (j : ℕ) :
    let H : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let b : ℝ := C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℝ := x + X.X s ω - rightLimit D s ω
      if s < ρ ω ∧ s + Δ ≤ ρ ω then
        Real.exp (-(q * (s : ℝ))) *
          (if Y ≤ b then iteratedDeriv 2 w Y else 0)
      else 0
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ m i : ℕ, Measurable (H m i) ∧
        ∀ ω : Ω, |H m i ω| ≤ K :=
  AvramDividend.Classical.avram_ga_original_finitecap_true_fullcell_Hessian_coeff_measurable_bounded X hX q hq w C hC hFiniteCap hw x D hD n hn ρ hρstop δ hδ hFloor j
