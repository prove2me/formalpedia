-- Prove2me | solution 1 for FairPricingPerturbation.welfare_sensitivity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:32.785547+00:00
-- url     : https://prove2.me/submissions/e5ca7a0e-714d-4c9e-8301-049e66942a34

import Mathlib
import Theorems.Thm_FairPricingPerturbation_feasible_curve

namespace CohenPriceFairness.LocalWelfare.Sol_core_sensitivity

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

theorem c2_lin (f : ℝ → ℝ) (c x : ℝ) (hf : HasDerivAt f c x) (u : ℝ → ℝ)
    (hu : Tendsto u (𝓝[>] 0) (𝓝 x)) (hO : (fun α => u α - x) =O[𝓝[>] 0] (fun α => α)) :
    (fun α => f (u α) - f x - c * (u α - x)) =o[𝓝[>] 0] (fun α => α) := by
  have h1 := (hf.isLittleO.comp_tendsto hu).trans_isBigO hO
  refine h1.congr_left ?_
  intro α
  simp [Function.comp, smul_eq_mul, mul_comm]

theorem c2_sq_o : (fun α : ℝ => α ^ 2) =o[𝓝[>] 0] (fun α => α) :=
  (isLittleO_pow_id (by norm_num)).mono nhdsWithin_le_nhds

theorem c2_ev_small (C δ : ℝ) (hδ : 0 < δ) : ∀ᶠ α in 𝓝[>] (0:ℝ), C * α ^ 2 < δ := by
  have : Tendsto (fun α : ℝ => C * α ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun α : ℝ => C * α ^ 2) (𝓝 0) (𝓝 (C * 0 ^ 2)) :=
      (continuous_const.mul (continuous_pow 2)).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  exact this.eventually_lt_const hδ

theorem c2_exists_of_ev (p : ℝ → Prop) (h : ∀ᶠ α in 𝓝[>] (0:ℝ), p α) :
    ∃ ε > 0, ∀ α ∈ Set.Ioc (0:ℝ) ε, p α := by
  rcases (mem_nhdsGT_iff_exists_Ioc_subset).1 h with ⟨u, hu, hsub⟩
  exact ⟨u, hu, fun α hα => hsub hα⟩

theorem c2_lower_i (Ri : ℝ → ℝ) (bi ri vi τ α ρ qi : ℝ) (hr : ri < 0) (hτ : 0 < τ) (hα : 0 < α)
    (hρ : ∀ y, |y| < ρ → |Ri (bi + y) - Ri bi - ri / 2 * y ^ 2| ≤ τ * y ^ 2)
    (hq : |qi - bi - α * vi| ≤ τ * α) (hαρ : α * (|vi| + τ) < ρ) :
    Ri bi + (ri / 2 - τ) * (|vi| + τ) ^ 2 * α ^ 2 ≤ Ri qi := by
  set y := qi - bi with hy
  have hyb : |y| ≤ α * (|vi| + τ) := by
    have h1 : |y| ≤ |y - α * vi| + |α * vi| := by
      have := abs_add_le (y - α * vi) (α * vi)
      simpa using this
    rw [abs_mul, abs_of_pos hα] at h1
    nlinarith
  have hy2 : y ^ 2 ≤ (α * (|vi| + τ)) ^ 2 := by
    have := abs_le.mp hyb
    exact sq_le_sq' this.1 this.2
  have h3 := hρ y (lt_of_le_of_lt hyb hαρ)
  have hq' : bi + y = qi := by rw [hy]; ring
  rw [hq'] at h3
  have h4 := (abs_le.mp h3).1
  have h5 : (ri / 2 - τ) * (α * (|vi| + τ)) ^ 2 ≤ (ri / 2 - τ) * y ^ 2 :=
    mul_le_mul_of_nonpos_left hy2 (by linarith)
  nlinarith

theorem c2_rho (R : ℝ → ℝ) (b r : ℝ)
    (hRt : (fun h => R (b + h) - R b - r / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2))
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ ρ > 0, ∀ y, |y| < ρ → |R (b + y) - R b - r / 2 * y ^ 2| ≤ τ * y ^ 2 := by
  have h := hRt.def hτ
  rcases Metric.eventually_nhds_iff.1 h with ⟨ρ, hρ, hh⟩
  refine ⟨ρ, hρ, fun y hy => ?_⟩
  have := hh (y := y) (by simpa [Real.dist_eq] using hy)
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg y)] using this

theorem c2_lower (R M : Fin 2 → ℝ → ℝ) (b r mm v : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hcontM : ∃ η > 0, ∀ i, ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => R i (b i + h) - R i (b i) - r i / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (M i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hv : mm 0 * v 0 - mm 1 * v 1 = -(M 0 (b 0) - M 1 (b 1))) (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ α in 𝓝[>] (0:ℝ), ∃ q : Fin 2 → ℝ,
      ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
      R 0 (b 0) + R 1 (b 1) + (r 0 / 2 * v 0 ^ 2 + r 1 / 2 * v 1 ^ 2 - κ) * α ^ 2 ≤
        R 0 (q 0) + R 1 (q 1) := by
  set g : ℝ → ℝ := fun τ => (r 0 / 2 - τ) * (|v 0| + τ) ^ 2 + (r 1 / 2 - τ) * (|v 1| + τ) ^ 2
    with hg
  have hgc : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := by
    have : Continuous g := by rw [hg]; fun_prop
    exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hg0 : g 0 = r 0 / 2 * v 0 ^ 2 + r 1 / 2 * v 1 ^ 2 := by
    simp [hg, sq_abs]
  have hev : ∀ᶠ τ in 𝓝[>] (0:ℝ), r 0 / 2 * v 0 ^ 2 + r 1 / 2 * v 1 ^ 2 - κ < g τ ∧ 0 < τ := by
    refine Filter.Eventually.and ?_ self_mem_nhdsWithin
    rw [← hg0]
    exact hgc.eventually_const_lt (by linarith)
  obtain ⟨τ, hτg, hτ⟩ := hev.exists
  obtain ⟨ρ0, hρ0, hρ0'⟩ := c2_rho (R 0) (b 0) (r 0) (hRt 0) τ hτ
  obtain ⟨ρ1, hρ1, hρ1'⟩ := c2_rho (R 1) (b 1) (r 1) (hRt 1) τ hτ
  obtain ⟨ε1, hε1, hcurve⟩ := FairPricingPerturbation.feasible_curve M b mm v hb hcontM hMd hmm hv τ hτ
  have hsm : ∀ (c ρ : ℝ), 0 < ρ → ∀ᶠ α in 𝓝[>] (0:ℝ), α * c < ρ := by
    intro c ρ hρ
    have : Tendsto (fun α : ℝ => α * c) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun α : ℝ => α * c) (𝓝 0) (𝓝 (0 * c)) :=
        (continuous_id.mul continuous_const).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    exact this.eventually_lt_const hρ
  filter_upwards [Ioc_mem_nhdsGT hε1, hsm (|v 0| + τ) ρ0 hρ0, hsm (|v 1| + τ) ρ1 hρ1]
    with α hα h0 h1
  obtain ⟨q, hq0, hq1, hq2⟩ := hcurve α hα
  refine ⟨q, ⟨hq0, hq1⟩, ?_⟩
  have e0 := c2_lower_i (R 0) (b 0) (r 0) (v 0) τ α ρ0 (q 0) (hr 0) hτ hα.1 hρ0' (hq2 0) h0
  have e1 := c2_lower_i (R 1) (b 1) (r 1) (v 1) τ α ρ1 (q 1) (hr 1) hτ hα.1 hρ1' (hq2 1) h1
  have : (r 0 / 2 * v 0 ^ 2 + r 1 / 2 * v 1 ^ 2 - κ) * α ^ 2 ≤ g τ * α ^ 2 :=
    mul_le_mul_of_nonneg_right hτg.le (sq_nonneg α)
  simp only [hg] at this
  nlinarith

theorem c2_each (R : Fin 2 → ℝ → ℝ) (b : Fin 2 → ℝ)
    (hopt : ∀ i, ∀ p, 0 ≤ p → R i p ≤ R i (b i)) (q : Fin 2 → ℝ) (hq : ∀ i, 0 ≤ q i)
    (δ : ℝ) (h : R 0 (b 0) + R 1 (b 1) - δ ≤ R 0 (q 0) + R 1 (q 1)) :
    ∀ i, R i (b i) - δ ≤ R i (q i) := by
  have h0 := hopt 0 (q 0) (hq 0)
  have h1 := hopt 1 (q 1) (hq 1)
  intro i; fin_cases i <;> simp <;> linarith

theorem c2_exist (R M : Fin 2 → ℝ → ℝ) (b : Fin 2 → ℝ) (C : ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → R i p ≤ R i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → R i (b i) - δ ≤ R i p → |p - b i| < ε)
    (hcont : ∃ η > 0, ∀ i, ContinuousOn (R i) (Set.Icc (b i - η) (b i + η)) ∧
      ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hq : ∀ᶠ α in 𝓝[>] (0:ℝ), ∃ q : Fin 2 → ℝ,
      ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
      R 0 (b 0) + R 1 (b 1) + C * α ^ 2 ≤ R 0 (q 0) + R 1 (q 1)) :
    ∃ ε > 0, ∀ α ∈ Set.Icc (0 : ℝ) ε, ∃ p : Fin 2 → ℝ,
      ((∀ i, 0 ≤ p i) ∧ |M 0 (p 0) - M 1 (p 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
      ∀ q : Fin 2 → ℝ,
        ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
        R 0 (q 0) + R 1 (q 1) ≤ R 0 (p 0) + R 1 (p 1) := by
  obtain ⟨η, hη, hc⟩ := hcont
  set ε0 := min η (min (b 0) (b 1)) / 2 with hε0d
  have hm1 : min η (min (b 0) (b 1)) ≤ η := min_le_left _ _
  have hm2 : min η (min (b 0) (b 1)) ≤ b 0 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hm3 : min η (min (b 0) (b 1)) ≤ b 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hmpos : 0 < min η (min (b 0) (b 1)) := lt_min hη (lt_min (hb 0) (hb 1))
  have hε0 : 0 < ε0 := by rw [hε0d]; linarith
  have hε0η : ε0 < η := by rw [hε0d]; linarith
  have hε0b : ∀ i, ε0 < b i := by
    intro i; fin_cases i
    · simp; rw [hε0d]; linarith
    · simp; rw [hε0d]; linarith
  obtain ⟨δ0, hδ0, hl⟩ := hloc ε0 hε0
  obtain ⟨ε, hε, hall⟩ := c2_exists_of_ev _ (hq.and (c2_ev_small (-C) δ0 hδ0))
  refine ⟨ε, hε, fun α hα => ?_⟩
  rcases eq_or_lt_of_le hα.1 with h0 | hpos
  · subst h0
    refine ⟨b, ⟨fun i => (hb i).le, by simp⟩, fun q hq => ?_⟩
    have := hopt 0 (q 0) (hq.1 0)
    have := hopt 1 (q 1) (hq.1 1)
    linarith
  obtain ⟨⟨q, hqf, hqT⟩, hsmall⟩ := hall α ⟨hpos, hα.2⟩
  set B : Set (Fin 2 → ℝ) := Set.univ.pi (fun i => Set.Icc (b i - ε0) (b i + ε0)) with hB
  have inbox : ∀ q' : Fin 2 → ℝ, (∀ i, 0 ≤ q' i) →
      R 0 (b 0) + R 1 (b 1) - δ0 ≤ R 0 (q' 0) + R 1 (q' 1) → q' ∈ B := by
    intro q' hq' hT
    have he := c2_each R b hopt q' hq' δ0 hT
    intro i _
    have := abs_lt.mp (hl i (q' i) (hq' i) (he i))
    constructor <;> linarith [this.1, this.2]
  set g : (Fin 2 → ℝ) → ℝ := fun p => |M 0 (p 0) - M 1 (p 1)| with hg
  set K : Set (Fin 2 → ℝ) := B ∩ g ⁻¹' Set.Iic ((1 - α) * |M 0 (b 0) - M 1 (b 1)|) with hK
  have hBc : IsCompact B := isCompact_univ_pi (fun i => isCompact_Icc)
  have hmaps : ∀ i, Set.MapsTo (fun p : Fin 2 → ℝ => p i) B (Set.Icc (b i - η) (b i + η)) := by
    intro i p hp
    have := hp i (Set.mem_univ _)
    constructor <;> linarith [this.1, this.2]
  have hMc : ∀ i, ContinuousOn (fun p : Fin 2 → ℝ => M i (p i)) B := fun i =>
    (hc i).2.comp (continuous_apply i).continuousOn (hmaps i)
  have hRc : ∀ i, ContinuousOn (fun p : Fin 2 → ℝ => R i (p i)) B := fun i =>
    (hc i).1.comp (continuous_apply i).continuousOn (hmaps i)
  have hgc : ContinuousOn g B := ((hMc 0).sub (hMc 1)).abs
  have hKc : IsCompact K :=
    hBc.of_isClosed_subset (hgc.preimage_isClosed_of_isClosed hBc.isClosed isClosed_Iic)
      Set.inter_subset_left
  have hqB : q ∈ B := inbox q hqf.1 (by nlinarith)
  have hqK : q ∈ K := ⟨hqB, hqf.2⟩
  have hTc : ContinuousOn (fun p : Fin 2 → ℝ => R 0 (p 0) + R 1 (p 1)) K :=
    ((hRc 0).add (hRc 1)).mono Set.inter_subset_left
  obtain ⟨p, hpK, hpmax⟩ := hKc.exists_isMaxOn ⟨q, hqK⟩ hTc
  have hpB := hpK.1
  refine ⟨p, ⟨fun i => ?_, hpK.2⟩, fun q' hq' => ?_⟩
  · have := hpB i (Set.mem_univ _)
    linarith [this.1, hε0b i]
  by_cases h : R 0 (b 0) + R 1 (b 1) - δ0 ≤ R 0 (q' 0) + R 1 (q' 1)
  · exact hpmax ⟨inbox q' hq'.1 h, hq'.2⟩
  · have := hpmax hqK
    have h' := lt_of_not_ge h
    change R 0 (q 0) + R 1 (q 1) ≤ R 0 (p 0) + R 1 (p 1) at this
    linarith

theorem c2_core (R M S : Fin 2 → ℝ → ℝ) (w b r mm σ v : Fin 2 → ℝ) (μ : ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → R i p ≤ R i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → R i (b i) - δ ≤ R i p → |p - b i| < ε)
    (hcontM : ∃ η > 0, ∀ i, ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => R i (b i + h) - R i (b i) - r i / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (M i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hSd : ∀ i, HasDerivAt (S i) (σ i) (b i))
    (hv0 : r 0 * v 0 = μ * mm 0) (hv1 : r 1 * v 1 = -(μ * mm 1))
    (hvl : mm 0 * v 0 - mm 1 * v 1 = -(M 0 (b 0) - M 1 (b 1)))
    (hμΔ : 0 ≤ μ * (M 0 (b 0) - M 1 (b 1)))
    (P : ℝ → Fin 2 → ℝ)
    (hP : ∃ ε > 0, ∀ α ∈ Set.Ioc (0 : ℝ) ε,
        ((∀ i, 0 ≤ P α i) ∧
          |M 0 (P α 0) - M 1 (P α 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
        ∀ q : Fin 2 → ℝ,
          ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
          R 0 (q 0) + R 1 (q 1) ≤ R 0 (P α 0) + R 1 (P α 1)) :
    Tendsto (fun α =>
          ((R 0 (P α 0) + R 1 (P α 1) + w 0 * S 0 (P α 0) + w 1 * S 1 (P α 1)) -
            (R 0 (b 0) + R 1 (b 1) + w 0 * S 0 (b 0) + w 1 * S 1 (b 1))) / α)
        (𝓝[>] 0) (𝓝 (w 0 * σ 0 * v 0 + w 1 * σ 1 * v 1)) := by
  obtain ⟨εP, hεP, hPall⟩ := hP
  have hPev : ∀ᶠ α in 𝓝[>] (0:ℝ), (((∀ i, 0 ≤ P α i) ∧
          |M 0 (P α 0) - M 1 (P α 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
        ∀ q : Fin 2 → ℝ,
          ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
          R 0 (q 0) + R 1 (q 1) ≤ R 0 (P α 0) + R 1 (P α 1)) ∧ 0 < α := by
    filter_upwards [Ioc_mem_nhdsGT hεP] with α hα using ⟨hPall α hα, hα.1⟩
  set Qs := r 0 / 2 * v 0 ^ 2 + r 1 / 2 * v 1 ^ 2 with hQs
  set T0 := R 0 (b 0) + R 1 (b 1) with hT0
  have hQs0 : Qs ≤ 0 := by
    have := hr 0; have := hr 1
    rw [hQs]; nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  -- Step A: lower bound
  have hA : ∀ κ > 0, ∀ᶠ α in 𝓝[>] (0:ℝ),
      T0 + (Qs - κ) * α ^ 2 ≤ R 0 (P α 0) + R 1 (P α 1) := by
    intro κ hκ
    filter_upwards [c2_lower R M b r mm v hb hcontM hr hRt hMd hmm hvl κ hκ, hPev]
      with α hq hP
    obtain ⟨q, hqf, hqT⟩ := hq
    exact le_trans hqT (hP.1.2 q hqf)
  -- Step B: localisation
  have hPt : ∀ i, Tendsto (fun α => P α i) (𝓝[>] 0) (𝓝 (b i)) := by
    intro i
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hl⟩ := hloc ε hε
    filter_upwards [hA 1 one_pos, c2_ev_small (-(Qs - 1)) δ hδ, hPev] with α h1 h2 h3
    have he := c2_each R b hopt (P α) h3.1.1.1 δ (by nlinarith)
    rw [Real.dist_eq]
    exact hl i (P α i) (h3.1.1.1 i) (he i)
  have hdt : ∀ i, Tendsto (fun α => P α i - b i) (𝓝[>] 0) (𝓝 0) := by
    intro i
    simpa using (hPt i).sub_const (b i)
  -- Step C: Taylor of R along P
  have hRo : ∀ i, (fun α => R i (P α i) - R i (b i) - r i / 2 * (P α i - b i) ^ 2) =o[𝓝[>] 0]
      (fun α => (P α i - b i) ^ 2) := by
    intro i
    refine ((hRt i).comp_tendsto (hdt i)).congr_left ?_
    intro α
    simp [Function.comp]
  have hRb : ∀ i, ∀ κ > 0, ∀ᶠ α in 𝓝[>] (0:ℝ),
      |R i (P α i) - R i (b i) - r i / 2 * (P α i - b i) ^ 2| ≤ κ * (P α i - b i) ^ 2 := by
    intro i κ hκ
    filter_upwards [(hRo i).def hκ] with α h
    simpa [Real.norm_eq_abs] using h
  -- Step D: d = O(α)
  set C := 4 * (1 - Qs) / (-r 0) + 4 * (1 - Qs) / (-r 1) with hCdef
  have hr0 := hr 0
  have hr1 := hr 1
  have hC0 : 0 ≤ 4 * (1 - Qs) / (-r 0) := div_nonneg (by linarith) (by linarith)
  have hC1 : 0 ≤ 4 * (1 - Qs) / (-r 1) := div_nonneg (by linarith) (by linarith)
  have hC : 0 ≤ C := by rw [hCdef]; linarith
  have hD : ∀ᶠ α in 𝓝[>] (0:ℝ), ∀ i, (P α i - b i) ^ 2 ≤ C * α ^ 2 := by
    filter_upwards [hA 1 one_pos, hRb 0 (-r 0 / 4) (by linarith), hRb 1 (-r 1 / 4) (by linarith)]
      with α h1 h2 h3
    have a2 := (abs_le.mp h2).2
    have a3 := (abs_le.mp h3).2
    have n0 : 0 ≤ (-r 0) * (P α 0 - b 0) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have n1 : 0 ≤ (-r 1) * (P α 1 - b 1) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have nα : 0 ≤ α ^ 2 := sq_nonneg α
    have k0 : (-r 0) * (P α 0 - b 0) ^ 2 ≤ 4 * (1 - Qs) * α ^ 2 := by linarith
    have k1 : (-r 1) * (P α 1 - b 1) ^ 2 ≤ 4 * (1 - Qs) * α ^ 2 := by linarith
    have l0 : (P α 0 - b 0) ^ 2 ≤ 4 * (1 - Qs) / (-r 0) * α ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; linarith
    have l1 : (P α 1 - b 1) ^ 2 ≤ 4 * (1 - Qs) / (-r 1) * α ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; linarith
    have m0 : 0 ≤ 4 * (1 - Qs) / (-r 0) * α ^ 2 := mul_nonneg hC0 nα
    have m1 : 0 ≤ 4 * (1 - Qs) / (-r 1) * α ^ 2 := mul_nonneg hC1 nα
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]; rw [hCdef]; linarith
    · simp only [Fin.mk_one, Fin.isValue]; rw [hCdef]; linarith
  have hO : ∀ i, (fun α => P α i - b i) =O[𝓝[>] 0] (fun α => α) := by
    intro i
    refine IsBigO.of_bound (Real.sqrt C) ?_
    filter_upwards [hD] with α h
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, Real.sq_sqrt hC, sq_abs]
    exact h i
  -- Step E: linearisations
  have hMo : ∀ i, (fun α => M i (P α i) - M i (b i) - mm i * (P α i - b i)) =o[𝓝[>] 0]
      (fun α => α) := fun i => c2_lin (M i) (mm i) (b i) (hMd i) (fun α => P α i) (hPt i) (hO i)
  have hSo : ∀ i, (fun α => S i (P α i) - S i (b i) - σ i * (P α i - b i)) =o[𝓝[>] 0]
      (fun α => α) := fun i => c2_lin (S i) (σ i) (b i) (hSd i) (fun α => P α i) (hPt i) (hO i)
  have hMb : ∀ i, ∀ κ > 0, ∀ᶠ α in 𝓝[>] (0:ℝ),
      |M i (P α i) - M i (b i) - mm i * (P α i - b i)| ≤ κ * α := by
    intro i κ hκ
    filter_upwards [(hMo i).def hκ, hPev] with α h h'
    simpa [Real.norm_eq_abs, abs_of_pos h'.2] using h
  -- Step F: blow-up converges to v
  have hY : ∀ ε > 0, ∀ᶠ α in 𝓝[>] (0:ℝ),
      -r 0 / 2 * (P α 0 - b 0 - α * v 0) ^ 2 + -r 1 / 2 * (P α 1 - b 1 - α * v 1) ^ 2
        ≤ ε * α ^ 2 := by
    intro ε hε
    set L := 1 + 2 * C + 2 * |μ| with hLdef
    have hL : 0 < L := by rw [hLdef]; positivity
    set κ := ε / L with hκdef
    have hκ : 0 < κ := div_pos hε hL
    have hκL : κ * L = ε := div_mul_cancel₀ ε (ne_of_gt hL)
    filter_upwards [hA κ hκ, hRb 0 κ hκ, hRb 1 κ hκ, hD, hMb 0 κ hκ, hMb 1 κ hκ, hPev]
      with α hA' hR0 hR1 hD' hM0 hM1 hP'
    have hα := hP'.2
    have hfeas := hP'.1.1.2
    have r0a := abs_le.mp hR0
    have r1a := abs_le.mp hR1
    have q1 : -r 0 / 2 * (P α 0 - b 0) ^ 2 + -r 1 / 2 * (P α 1 - b 1) ^ 2 ≤
        (κ - Qs) * α ^ 2 + κ * ((P α 0 - b 0) ^ 2 + (P α 1 - b 1) ^ 2) := by
      linarith [r0a.1, r0a.2, r1a.1, r1a.2]
    have q2 : κ * ((P α 0 - b 0) ^ 2 + (P α 1 - b 1) ^ 2) ≤ κ * (2 * C * α ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hκ.le
      linarith [hD' 0, hD' 1]
    have c1 : μ * (M 0 (P α 0) - M 1 (P α 1)) ≤ (1 - α) * (μ * (M 0 (b 0) - M 1 (b 1))) := by
      calc μ * (M 0 (P α 0) - M 1 (P α 1)) ≤ |μ * (M 0 (P α 0) - M 1 (P α 1))| := le_abs_self _
        _ = |μ| * |M 0 (P α 0) - M 1 (P α 1)| := abs_mul _ _
        _ ≤ |μ| * ((1 - α) * |M 0 (b 0) - M 1 (b 1)|) :=
            mul_le_mul_of_nonneg_left hfeas (abs_nonneg _)
        _ = (1 - α) * |μ * (M 0 (b 0) - M 1 (b 1))| := by rw [abs_mul]; ring
        _ = (1 - α) * (μ * (M 0 (b 0) - M 1 (b 1))) := by rw [abs_of_nonneg hμΔ]
    set e0 := M 0 (P α 0) - M 0 (b 0) - mm 0 * (P α 0 - b 0) with he0
    set e1 := M 1 (P α 1) - M 1 (b 1) - mm 1 * (P α 1 - b 1) with he1
    have c2 : -(μ * (e0 - e1)) ≤ |μ| * (2 * κ * α) := by
      calc -(μ * (e0 - e1)) ≤ |μ * (e0 - e1)| := neg_le_abs _
        _ = |μ| * |e0 - e1| := abs_mul _ _
        _ ≤ |μ| * (|e0| + |e1|) := mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
        _ ≤ |μ| * (2 * κ * α) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have c3 : μ * (mm 0 * (P α 0 - b 0) - mm 1 * (P α 1 - b 1) + α * (M 0 (b 0) - M 1 (b 1)))
        ≤ |μ| * (2 * κ * α) := by
      have eq : μ * (mm 0 * (P α 0 - b 0) - mm 1 * (P α 1 - b 1) + α * (M 0 (b 0) - M 1 (b 1)))
          = μ * (M 0 (P α 0) - M 1 (P α 1)) - (1 - α) * (μ * (M 0 (b 0) - M 1 (b 1)))
            - μ * (e0 - e1) := by rw [he0, he1]; ring
      rw [eq]; linarith
    have c4 := mul_le_mul_of_nonneg_left c3 hα.le
    have iden : -r 0 / 2 * (P α 0 - b 0 - α * v 0) ^ 2 + -r 1 / 2 * (P α 1 - b 1 - α * v 1) ^ 2
        = -r 0 / 2 * (P α 0 - b 0) ^ 2 + -r 1 / 2 * (P α 1 - b 1) ^ 2 + α ^ 2 * Qs
          + α * (μ * (mm 0 * (P α 0 - b 0) - mm 1 * (P α 1 - b 1) + α * (M 0 (b 0) - M 1 (b 1))))
          := by
      rw [hQs]
      linear_combination (α * (P α 0 - b 0) - α ^ 2 * v 0) * hv0
        + (α * (P α 1 - b 1) - α ^ 2 * v 1) * hv1 - α ^ 2 * μ * hvl
    have fin : κ * L * α ^ 2 = ε * α ^ 2 := by rw [hκL]
    rw [iden]
    rw [hLdef] at fin
    linarith [q1, q2, c4, fin]
  have hconv : ∀ i, Tendsto (fun α => (P α i - b i) / α) (𝓝[>] 0) (𝓝 (v i)) := by
    intro i
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hri : 0 < -r i / 2 := by linarith [hr i]
    filter_upwards [hY ((-r i / 2) * (ε ^ 2 / 2)) (by positivity), hPev] with α h hP'
    have hα := hP'.2
    have hi : -r i / 2 * (P α i - b i - α * v i) ^ 2 ≤ (-r i / 2) * (ε ^ 2 / 2) * α ^ 2 := by
      have n0 : 0 ≤ -r 0 / 2 * (P α 0 - b 0 - α * v 0) ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg _)
      have n1 : 0 ≤ -r 1 / 2 * (P α 1 - b 1 - α * v 1) ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg _)
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue] at h ⊢; linarith
      · simp only [Fin.mk_one, Fin.isValue] at h ⊢; linarith
    have hx : (P α i - b i - α * v i) ^ 2 < (ε * α) ^ 2 := by
      have : (P α i - b i - α * v i) ^ 2 ≤ (ε ^ 2 / 2) * α ^ 2 := by
        rw [mul_assoc] at hi
        exact le_of_mul_le_mul_left hi hri
      have hpos : 0 < ε ^ 2 * α ^ 2 := by positivity
      rw [mul_pow]
      linarith
    have hab := abs_lt_of_sq_lt_sq hx (by positivity)
    rw [Real.dist_eq]
    have : (P α i - b i) / α - v i = (P α i - b i - α * v i) / α := by
      field_simp
    rw [this, abs_div, abs_of_pos hα, div_lt_iff₀ hα]
    linarith
  -- Step G: assemble
  have hTo : (fun α => R 0 (P α 0) + R 1 (P α 1) - T0) =o[𝓝[>] 0] (fun α => α) := by
    refine IsBigO.trans_isLittleO ?_ c2_sq_o
    refine IsBigO.of_bound (1 - Qs) ?_
    filter_upwards [hA 1 one_pos, hPev] with α h1 h2
    have u0 := hopt 0 (P α 0) (h2.1.1.1 0)
    have u1 := hopt 1 (P α 1) (h2.1.1.1 1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg α), abs_le]
    constructor <;> nlinarith
  have hS : ∀ i, Tendsto (fun α => (S i (P α i) - S i (b i)) / α) (𝓝[>] 0) (𝓝 (σ i * v i)) := by
    intro i
    have h1 := ((hconv i).const_mul (σ i)).add (hSo i).tendsto_div_nhds_zero
    rw [add_zero] at h1
    refine h1.congr (fun α => ?_)
    ring
  have hall := (hTo.tendsto_div_nhds_zero.add ((hS 0).const_mul (w 0))).add
    ((hS 1).const_mul (w 1))
  have hlim : (0 : ℝ) + w 0 * (σ 0 * v 0) + w 1 * (σ 1 * v 1) = w 0 * σ 0 * v 0 + w 1 * σ 1 * v 1 := by
    ring
  rw [hlim] at hall
  refine hall.congr (fun α => ?_)
  simp only [hT0]
  ring

end CohenPriceFairness.LocalWelfare.Sol_core_sensitivity

open CohenPriceFairness.LocalWelfare CohenPriceFairness.LocalWelfare.Sol_core_sensitivity
open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

theorem solution
    (R M S : Fin 2 → ℝ → ℝ) (w b r mm σ : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → R i p ≤ R i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → R i (b i) - δ ≤ R i p → |p - b i| < ε)
    (hcont : ∃ η > 0, ∀ i, ContinuousOn (R i) (Set.Icc (b i - η) (b i + η)) ∧
      ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => R i (b i + h) - R i (b i) - r i / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (M i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hSd : ∀ i, HasDerivAt (S i) (σ i) (b i))
    (hgap : M 0 (b 0) ≠ M 1 (b 1)) :
    (∃ ε > 0, ∀ α ∈ Set.Icc (0 : ℝ) ε, ∃ p : Fin 2 → ℝ,
      ((∀ i, 0 ≤ p i) ∧ |M 0 (p 0) - M 1 (p 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
      ∀ q : Fin 2 → ℝ,
        ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
        R 0 (q 0) + R 1 (q 1) ≤ R 0 (p 0) + R 1 (p 1)) ∧
    ∀ P : ℝ → Fin 2 → ℝ,
      (∃ ε > 0, ∀ α ∈ Set.Ioc (0 : ℝ) ε,
        ((∀ i, 0 ≤ P α i) ∧
          |M 0 (P α 0) - M 1 (P α 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) ∧
        ∀ q : Fin 2 → ℝ,
          ((∀ i, 0 ≤ q i) ∧ |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)|) →
          R 0 (q 0) + R 1 (q 1) ≤ R 0 (P α 0) + R 1 (P α 1)) →
      Tendsto (fun α =>
          ((R 0 (P α 0) + R 1 (P α 1) + w 0 * S 0 (P α 0) + w 1 * S 1 (P α 1)) -
            (R 0 (b 0) + R 1 (b 1) + w 0 * S 0 (b 0) + w 1 * S 1 (b 1))) / α)
        (𝓝[>] 0)
        (𝓝 (w 0 * σ 0 * ((-(M 0 (b 0) - M 1 (b 1)) / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
            w 1 * σ 1 * (-((-(M 0 (b 0) - M 1 (b 1)) / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)))) := by
  have hcontM : ∃ η > 0, ∀ i, ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)) := by
    obtain ⟨η, hη, h⟩ := hcont
    exact ⟨η, hη, fun i => (h i).2⟩
  have hr0 := hr 0
  have hr1 := hr 1
  have hK : mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 < 0 := by
    have a0 : mm 0 ^ 2 / r 0 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hr0.le
    have a1 : mm 1 ^ 2 / r 1 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hr1.le
    rcases hmm with h | h
    · have : mm 0 ^ 2 / r 0 < 0 := div_neg_of_pos_of_neg (by positivity) hr0
      linarith
    · have : mm 1 ^ 2 / r 1 < 0 := div_neg_of_pos_of_neg (by positivity) hr1
      linarith
  set Δ := M 0 (b 0) - M 1 (b 1) with hΔ
  set K := mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 with hKdef
  set μ := -Δ / K with hμ
  have hK0 : K ≠ 0 := ne_of_lt hK
  have hr0' : r 0 ≠ 0 := ne_of_lt hr0
  have hr1' : r 1 ≠ 0 := ne_of_lt hr1
  have hμK : μ * K = -Δ := by rw [hμ, div_mul_cancel₀ _ hK0]
  have hμΔ : 0 ≤ μ * Δ := by
    have : μ * Δ = Δ ^ 2 / (-K) := by rw [hμ]; field_simp
    rw [this]; exact div_nonneg (sq_nonneg _) (by linarith)
  set v : Fin 2 → ℝ := ![μ * mm 0 / r 0, -(μ * mm 1 / r 1)] with hvdef
  have hv0 : r 0 * v 0 = μ * mm 0 := by
    show r 0 * (μ * mm 0 / r 0) = μ * mm 0
    field_simp
  have hv1 : r 1 * v 1 = -(μ * mm 1) := by
    show r 1 * -(μ * mm 1 / r 1) = -(μ * mm 1)
    field_simp
  have hvl : mm 0 * v 0 - mm 1 * v 1 = -Δ := by
    rw [← hμK]
    show mm 0 * (μ * mm 0 / r 0) - mm 1 * -(μ * mm 1 / r 1) = μ * K
    rw [hKdef]
    ring
  refine ⟨c2_exist R M b _ hb hopt hloc hcont
    (c2_lower R M b r mm v hb hcontM hr hRt hMd hmm hvl 1 one_pos), fun P hP => ?_⟩
  have := c2_core R M S w b r mm σ v μ hb hopt hloc hcontM hr hRt hMd hmm hSd hv0 hv1 hvl hμΔ P hP
  exact this

