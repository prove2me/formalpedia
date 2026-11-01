-- Prove2me | solution 1 for ForkJoinCtrl.Tracking.lemma_EC_1_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T11:35:48.436449+00:00
-- url     : https://prove2.me/submissions/7d4138e1-6add-409d-9564-8fcb08741609

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace FJEC12

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Chernoff bound for a partial sum of the i.i.d. sequence `σ (X n - x)`. -/
theorem tail (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (x : ℝ)
    (hmeas : ∀ n, Measurable (X n))
    (hindep : iIndepFun (fun n : {n : ℕ // 1 ≤ n} => X n.1) P)
    (hident : ∀ n, 1 ≤ n → IdentDistrib (X n) (X 1) P P)
    (σ θ : ℝ) (hθ : 0 ≤ θ)
    (hint : Integrable (fun ω => Real.exp (θ * (σ * (X 1 ω - x)))) P)
    (Nn : ℕ) (hN : 1 ≤ Nn) (c : ℝ) :
    P.real {ω | c ≤ ∑ n ∈ Finset.Icc 1 Nn, σ * (X n ω - x)} ≤
      Real.exp (-θ * c) * (mgf (fun ω => σ * (X 1 ω - x)) P θ) ^ Nn := by
  classical
  let g : ℝ → ℝ := fun y => σ * (y - x)
  have hg : Measurable g := by fun_prop
  let Z : {n : ℕ // 1 ≤ n} → Ω → ℝ := fun n ω => σ * (X n.1 ω - x)
  have hZind : iIndepFun Z P := hindep.comp (fun _ => g) (fun _ => hg)
  have hZmeas : ∀ i, Measurable (Z i) := fun i => hg.comp (hmeas i.1)
  have hZid1 : ∀ i : {n : ℕ // 1 ≤ n}, IdentDistrib (Z i) (fun ω => σ * (X 1 ω - x)) P P :=
    fun i => (hident i.1 i.2).comp hg
  let s : Finset {n : ℕ // 1 ≤ n} := (Finset.Icc 1 Nn).subtype (fun n => 1 ≤ n)
  have hsum : ∀ ω, ∑ n ∈ Finset.Icc 1 Nn, σ * (X n ω - x) = (∑ i ∈ s, Z i) ω := by
    intro ω
    rw [Finset.sum_apply]
    simp only [s, Z]
    rw [Finset.sum_subtype_eq_sum_filter (f := fun n => σ * (X n ω - x))]
    rw [Finset.filter_true_of_mem (fun n hn => (Finset.mem_Icc.1 hn).1)]
  have hcard : s.card = Nn := by
    simp only [s]
    rw [Finset.card_subtype, Finset.filter_true_of_mem (fun n hn => (Finset.mem_Icc.1 hn).1)]
    simp
  have hset : {ω | c ≤ ∑ n ∈ Finset.Icc 1 Nn, σ * (X n ω - x)} = {ω | c ≤ (∑ i ∈ s, Z i) ω} := by
    ext ω; simp only [Set.mem_setOf_eq, hsum ω]
  have hintZ : ∀ i ∈ s, Integrable (fun ω => Real.exp (θ * Z i ω)) P := by
    intro i _
    have := (hZid1 i).comp (show Measurable (fun y : ℝ => Real.exp (θ * y)) by fun_prop)
    exact this.integrable_iff.2 hint
  rw [hset]
  refine (measure_ge_le_exp_mul_mgf c hθ (hZind.integrable_exp_mul_sum hZmeas hintZ)).trans ?_
  have h1 : (1 : ℕ) ≤ Nn := hN
  let j : {n : ℕ // 1 ≤ n} := ⟨1, le_rfl⟩
  have hj : j ∈ s := by
    simp only [s, j, Finset.mem_subtype, Finset.mem_Icc]; exact ⟨le_rfl, hN⟩
  rw [mgf_sum_of_identDistrib hZmeas hZind
    (fun i _ k _ => (hZid1 i).trans (hZid1 k).symm) hj, hcard]

end FJEC12

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (x : ℝ)
    (hmeas : ∀ n, Measurable (X n))
    (hnonneg : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, 0 ≤ X n ω)
    (hindep : iIndepFun (fun n : {n : ℕ // 1 ≤ n} => X n.1) P)
    (hident : ∀ n, 1 ≤ n → IdentDistrib (X n) (X 1) P P)
    (hint : Integrable (X 1) P) (hmean : ∫ ω, X 1 ω ∂P = x) (hx : 0 < x)
    (hmom : ∃ αbar : ℝ, 0 < αbar ∧ ∀ α ∈ Set.Ioo (-αbar) αbar,
      Integrable (fun ω => Real.exp (α * X 1 ω)) P)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ C34 : ℝ, 0 < C34 ∧ ∃ r14 : ℕ, 1 ≤ r14 ∧ ∀ r : ℕ, r14 ≤ r →
      P {ω | ∃ Nn ∈ Finset.Icc 1 ⌊a * r⌋₊, b * r < |∑ n ∈ Finset.Icc 1 Nn, (X n ω - x)|} ≤
        ENNReal.ofReal (2 * Real.exp (-C34 * r)) := by
  obtain ⟨αbar, hα, hmomα⟩ := hmom
  set Y : Ω → ℝ := fun ω => X 1 ω - x with hY
  -- integrability of exponential moments of `Y`
  have hYint : ∀ t ∈ Set.Ioo (-αbar) αbar, Integrable (fun ω => Real.exp (t * Y ω)) P := by
    intro t ht
    have := (hmomα t ht).const_mul (Real.exp (-(t * x)))
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hY]
    rw [← Real.exp_add]; ring_nf
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet Y P) := by
    rw [mem_interior]
    exact ⟨Set.Ioo (-αbar) αbar, fun t ht => hYint t ht, isOpen_Ioo, by simp [hα]⟩
  have hderiv := hasDerivAt_mgf h0
  have hmean0 : P[fun ω => Y ω * Real.exp (0 * Y ω)] = 0 := by
    simp only [zero_mul, Real.exp_zero, mul_one, hY]
    rw [integral_sub hint (integrable_const x), hmean]
    simp
  rw [hmean0] at hderiv
  -- choose θ with mgf Y (±θ) ≤ 1 + δ θ
  set δ : ℝ := b / (2 * a) with hδ
  have hδpos : 0 < δ := by positivity
  have hlo := (hasDerivAt_iff_isLittleO.1 hderiv).bound hδpos
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hlo
  set θ : ℝ := min ρ αbar / 2 with hθdef
  have hθpos : 0 < θ := by positivity
  have hθρ : θ < ρ := by
    have := min_le_left ρ αbar; rw [hθdef]; linarith
  have hθα : θ < αbar := by
    have := min_le_right ρ αbar; rw [hθdef]; linarith
  have hmgf_bd : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → mgf Y P (σ * θ) ≤ 1 + δ * θ := by
    intro σ hσ
    have habs : |σ * θ| = θ := by
      rcases hσ with rfl | rfl <;> simp [abs_of_pos hθpos]
    have hd : dist (σ * θ) 0 < ρ := by rw [Real.dist_eq, sub_zero, habs]; exact hθρ
    have := hball hd
    simp only [mgf_zero, sub_zero, smul_zero, Real.norm_eq_abs, habs] at this
    have := (abs_le.1 this).2
    linarith
  -- per-sum tail bound
  have htail : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ Nn : ℕ, 1 ≤ Nn → ∀ c : ℝ,
      P.real {ω | c ≤ ∑ n ∈ Finset.Icc 1 Nn, σ * (X n ω - x)} ≤
        Real.exp (-θ * c) * Real.exp (δ * θ * Nn) := by
    intro σ hσ Nn hN c
    have habs : |σ * θ| = θ := by
      rcases hσ with rfl | rfl <;> simp [abs_of_pos hθpos]
    have hint' : Integrable (fun ω => Real.exp (θ * (σ * (X 1 ω - x)))) P := by
      have := hYint (σ * θ) (by
        rw [Set.mem_Ioo, ← abs_lt, habs]; exact hθα)
      refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only [hY]; ring_nf
    refine (FJEC12.tail P X x hmeas hindep hident σ θ hθpos.le hint' Nn hN c).trans ?_
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have hm : mgf (fun ω => σ * (X 1 ω - x)) P θ = mgf Y P (σ * θ) := by
      have := mgf_const_mul (X := Y) (μ := P) (t := θ) σ
      simpa [hY] using this
    rw [hm]
    have hnn : 0 ≤ mgf Y P (σ * θ) := mgf_nonneg
    calc mgf Y P (σ * θ) ^ Nn ≤ (Real.exp (δ * θ)) ^ Nn := by
          apply pow_le_pow_left₀ hnn
          refine (hmgf_bd σ hσ).trans ?_
          have := Real.add_one_le_exp (δ * θ); linarith
      _ = Real.exp (δ * θ * Nn) := by rw [← Real.exp_nat_mul]; ring_nf
  -- the constant
  set C : ℝ := θ * b / 4 with hC
  have hCpos : 0 < C := by positivity
  -- eventually a r e^{-C r} ≤ 1
  have hev : ∀ᶠ r : ℕ in atTop, a * r * Real.exp (-C * r) ≤ 1 := by
    have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (Tendsto.const_mul_atTop hCpos tendsto_natCast_atTop_atTop)
    have := ht.eventually (ge_mem_nhds (show (0 : ℝ) < C / a by positivity))
    filter_upwards [this] with r hr
    simp only [Function.comp, pow_one] at hr
    have : a * r * Real.exp (-C * r) = (a / C) * (C * r * Real.exp (-(C * r))) := by
      field_simp
    rw [this]
    calc (a / C) * (C * r * Real.exp (-(C * r))) ≤ (a / C) * (C / a) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = 1 := by field_simp
  obtain ⟨r0, hr0⟩ := eventually_atTop.1 hev
  refine ⟨C, hCpos, max r0 1, le_max_right _ _, ?_⟩
  intro r hr
  have hr' : r0 ≤ r := le_trans (le_max_left _ _) hr
  have hfin := hr0 r hr'
  -- union bound
  set S := {ω | ∃ Nn ∈ Finset.Icc 1 ⌊a * r⌋₊, b * r < |∑ n ∈ Finset.Icc 1 Nn, (X n ω - x)|}
  have hsub : S ⊆ ⋃ Nn ∈ Finset.Icc 1 ⌊a * r⌋₊,
      ({ω | b * r ≤ ∑ n ∈ Finset.Icc 1 Nn, (1 : ℝ) * (X n ω - x)} ∪
       {ω | b * r ≤ ∑ n ∈ Finset.Icc 1 Nn, (-1 : ℝ) * (X n ω - x)}) := by
    intro ω hω
    obtain ⟨Nn, hN, hlt⟩ := hω
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq]
    refine ⟨Nn, hN, ?_⟩
    rcases lt_abs.1 hlt with h | h
    · left; simp only [one_mul]; exact h.le
    · right
      have : ∑ n ∈ Finset.Icc 1 Nn, (-1 : ℝ) * (X n ω - x) =
          -∑ n ∈ Finset.Icc 1 Nn, (X n ω - x) := by
        rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro n _; ring
      rw [this]; exact h.le
  have hbound : P.real S ≤ 2 * Real.exp (-C * r) := by
    have hfl : (⌊a * r⌋₊ : ℝ) ≤ a * r := Nat.floor_le (by positivity)
    have hterm : ∀ Nn ∈ Finset.Icc 1 ⌊a * r⌋₊,
        P.real ({ω | b * r ≤ ∑ n ∈ Finset.Icc 1 Nn, (1 : ℝ) * (X n ω - x)} ∪
          {ω | b * r ≤ ∑ n ∈ Finset.Icc 1 Nn, (-1 : ℝ) * (X n ω - x)}) ≤
        2 * Real.exp (-(2 * C) * r) := by
      intro Nn hN
      have hN1 := (Finset.mem_Icc.1 hN).1
      have hN2 : (Nn : ℝ) ≤ a * r := le_trans (by exact_mod_cast (Finset.mem_Icc.1 hN).2) hfl
      have hexp : Real.exp (-θ * (b * r)) * Real.exp (δ * θ * Nn) ≤ Real.exp (-(2 * C) * r) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have : δ * θ * Nn ≤ δ * θ * (a * r) :=
          mul_le_mul_of_nonneg_left hN2 (by positivity)
        have e : δ * θ * (a * r) = θ * b * r / 2 := by rw [hδ]; field_simp
        rw [hC]; nlinarith
      refine (measureReal_union_le _ _).trans ?_
      have := htail 1 (Or.inl rfl) Nn hN1 (b * r)
      have := htail (-1) (Or.inr rfl) Nn hN1 (b * r)
      linarith
    calc P.real S ≤ P.real (⋃ Nn ∈ Finset.Icc 1 ⌊a * r⌋₊,
          ({ω | b * r ≤ ∑ n ∈ Finset.Icc 1 Nn, (1 : ℝ) * (X n ω - x)} ∪
           {ω | b * r ≤ ∑ n ∈ Finset.Icc 1 Nn, (-1 : ℝ) * (X n ω - x)})) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ Nn ∈ Finset.Icc 1 ⌊a * r⌋₊,
          P.real ({ω | b * r ≤ ∑ n ∈ Finset.Icc 1 Nn, (1 : ℝ) * (X n ω - x)} ∪
           {ω | b * r ≤ ∑ n ∈ Finset.Icc 1 Nn, (-1 : ℝ) * (X n ω - x)}) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ Nn ∈ Finset.Icc 1 ⌊a * r⌋₊, 2 * Real.exp (-(2 * C) * r) := Finset.sum_le_sum hterm
      _ = (⌊a * r⌋₊ : ℝ) * (2 * Real.exp (-(2 * C) * r)) := by simp
      _ ≤ (a * r) * (2 * Real.exp (-(2 * C) * r)) :=
          mul_le_mul_of_nonneg_right hfl (by positivity)
      _ = 2 * Real.exp (-C * r) * (a * r * Real.exp (-C * r)) := by
          rw [show -(2 * C) * r = -C * r + -C * r by ring, Real.exp_add]; ring
      _ ≤ 2 * Real.exp (-C * r) * 1 := mul_le_mul_of_nonneg_left hfin (by positivity)
      _ = 2 * Real.exp (-C * r) := mul_one _
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top P S) (by positivity)]
  exact hbound
