-- Prove2me | solution 1 for EquilibriumExperiment.Gradient.eq_A7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T13:28:07.043099+00:00
-- url     : https://prove2.me/submissions/20001002-5c34-4ae4-9784-d963757e35d1

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model
import Theorems.Thm_EquilibriumExperiment_Gradient_eq_A7_Zbar
import Theorems.Thm_EquilibriumExperiment_Gradient_eq_A7_DeltaHat
import Theorems.Thm_EquilibriumExperiment_Gradient_lemma_2

open MeasureTheory ProbabilityTheory Filter Topology

namespace EqExpA7Aux


/-- Chebyshev: `L²` convergence to a constant implies convergence in probability, along a
sequence of probability spaces. -/
lemma inProb_of_eLpNorm {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (X : ∀ n, Ω n → ℝ) (c : ℝ) (hX : ∀ n, AEStronglyMeasurable (X n) (P n))
    (h : Tendsto (fun n => eLpNorm (fun x => X n x - c) 2 (P n)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P n {x | ε < |X n x - c|}) atTop (𝓝 0) := by
  have hc : (ENNReal.ofReal ε) ^ (2 : ℝ) ≠ 0 := by
    have : ENNReal.ofReal ε ≠ 0 := by simpa using hε
    exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr this) ENNReal.ofReal_ne_top).ne'
  have hc' : (ENNReal.ofReal ε) ^ (2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hbound : ∀ n, P n {x | ε < |X n x - c|} ≤
      eLpNorm (fun x => X n x - c) 2 (P n) ^ (2 : ℝ) / (ENNReal.ofReal ε) ^ (2 : ℝ) := by
    intro n
    have hm : AEStronglyMeasurable (fun x => X n x - c) (P n) :=
      (hX n).sub aestronglyMeasurable_const
    have key := mul_meas_ge_le_pow_eLpNorm' (P n) (p := 2) (by norm_num) (by norm_num) hm
      (ENNReal.ofReal ε)
    simp only [ENNReal.toReal_ofNat] at key
    rw [ENNReal.le_div_iff_mul_le (Or.inl hc) (Or.inl hc'), mul_comm]
    refine le_trans ?_ key
    gcongr
    rw [Real.enorm_eq_ofReal_abs]
    exact fun hy => ENNReal.ofReal_le_ofReal (le_of_lt hy)
  have hlim : Tendsto (fun n => eLpNorm (fun x => X n x - c) 2 (P n) ^ (2 : ℝ) /
      (ENNReal.ofReal ε) ^ (2 : ℝ)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => eLpNorm (fun x => X n x - c) 2 (P n) ^ (2 : ℝ)) atTop
        (𝓝 ((0 : ENNReal) ^ (2 : ℝ))) :=
      ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    have := ENNReal.Tendsto.div_const h2 (Or.inr hc)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => bot_le) hbound

/-- Continuous mapping (Slutsky) for convergence in probability to constants, three variables. -/
lemma inProb_comp3 {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (X Y Z : ∀ n, Ω n → ℝ) (a b c : ℝ) (G : ℝ × ℝ × ℝ → ℝ) (hG : ContinuousAt G (a, b, c))
    (hX : ∀ ε, 0 < ε → Tendsto (fun n => P n {x | ε < |X n x - a|}) atTop (𝓝 0))
    (hY : ∀ ε, 0 < ε → Tendsto (fun n => P n {x | ε < |Y n x - b|}) atTop (𝓝 0))
    (hZ : ∀ ε, 0 < ε → Tendsto (fun n => P n {x | ε < |Z n x - c|}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P n {x | ε < |G (X n x, Y n x, Z n x) - G (a, b, c)|}) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hGδ⟩ := Metric.continuousAt_iff.mp hG ε hε
  have hδ2 : 0 < δ / 2 := by linarith
  have hsub : ∀ n, {x | ε < |G (X n x, Y n x, Z n x) - G (a, b, c)|} ⊆
      ({x | δ / 2 < |X n x - a|} ∪ {x | δ / 2 < |Y n x - b|}) ∪ {x | δ / 2 < |Z n x - c|} := by
    intro n x hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    have hd : dist (X n x, Y n x, Z n x) (a, b, c) < δ := by
      rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
      apply max_lt (by linarith) (max_lt (by linarith) (by linarith))
    have := hGδ hd
    rw [Real.dist_eq] at this
    simp only [Set.mem_ofPred_eq] at hx
    linarith
  have hsum : Tendsto (fun n => (P n {x | δ / 2 < |X n x - a|} + P n {x | δ / 2 < |Y n x - b|})
      + P n {x | δ / 2 < |Z n x - c|}) atTop (𝓝 0) := by
    have := ((hX _ hδ2).add (hY _ hδ2)).add (hZ _ hδ2)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun n => bot_le) (fun n => ?_)
  refine le_trans (measure_mono (hsub n)) ?_
  refine le_trans (measure_union_le _ _) ?_
  gcongr
  exact measure_union_le _ _


lemma accPt_Ici {x : ℝ} (hx : 0 ≤ x) : AccPt x (𝓟 (Set.Ici 0)) := by
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨x + ε / 2, ⟨hball ?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]; linarith
  · simp only [Set.mem_Ici]; linarith
  · intro h; linarith

end EqExpA7Aux

open EqExpA7Aux EquilibriumExperiment.Gradient

theorem solution {B : Type} [MeasurableSpace B] (M : EquilibriumExperiment.Gradient.Market B)
    (hM : M.Standing)
    {p : ℝ} (hp : 0 < p) (hpos : 0 < ∫ b, M.f b (p * M.omegaSup) ∂M.β)
    {ζ α : ℝ} (hζ : 0 < ζ) (hα : 0 < α) (hα' : α < 1 / 2) :
    Tendsto (fun n : ℕ => eLpNorm (fun x : Outcome B n => Dbar n x - M.d) 2
      (M.sample n (perturbLaw p (ζ * (n : ℝ) ^ (-α))))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => eLpNorm (fun x : Outcome B n =>
        M.Zbar n p (ζ * (n : ℝ) ^ (-α)) x - M.muLim p) 2
      (M.sample n (perturbLaw p (ζ * (n : ℝ) ^ (-α))))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => eLpNorm (fun x : Outcome B n =>
        M.DeltaHat n p (ζ * (n : ℝ) ^ (-α)) x - M.DeltaLim p) 2
      (M.sample n (perturbLaw p (ζ * (n : ℝ) ^ (-α))))) atTop (𝓝 0) ∧
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => M.sample n (perturbLaw p (ζ * (n : ℝ) ^ (-α)))
        {x | ε < |M.UpsHat n p (ζ * (n : ℝ) ^ (-α)) x - M.muLimDeriv p|}) atTop (𝓝 0) := by
  have hM' := hM
  obtain ⟨hd, hF, -, h31, -, hβ, hω, -, -, -, -, -, -, -, hfmono, hfderiv, -, hfmeas, -, -, -,
    -⟩ := hM'
  have hωs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M.ω (Set.Ioi 0) := hω.2.1
  set ζn : ℕ → ℝ := fun n => ζ * (n : ℝ) ^ (-α) with hζn
  -- the probability measures
  haveI hU : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Measure.restrict_apply MeasurableSet.univ, Real.volume_Icc]⟩
  haveI := hβ
  have hπprob : ∀ ζ' : ℝ, IsProbabilityMeasure (perturbLaw p ζ') := by
    intro ζ'
    constructor
    simp only [perturbLaw, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two, one_div, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
  -- (A.7), first part: `D̄ → d_a` in `L²`, from (3.1)
  have hDL2 : Tendsto (fun n : ℕ => eLpNorm (fun x : Outcome B n => Dbar n x - M.d) 2
      (M.sample n (perturbLaw p (ζn n)))) atTop (𝓝 0) := by
    have heq : ∀ n : ℕ, eLpNorm (fun x : Outcome B n => Dbar n x - M.d) 2
        (M.sample n (perturbLaw p (ζn n))) =
        (∫⁻ D, ENNReal.ofReal ((D / n - M.d) ^ 2) ∂(M.F n)) ^ (1 / (2 : ℝ)) := by
      intro n
      haveI := hπprob (ζn n)
      haveI := (hF n).1
      have hmp : MeasurePreserving (Prod.fst : Outcome B n → ℝ)
          (M.sample n (perturbLaw p (ζn n))) (M.F n) := measurePreserving_fst
      have hcomp : (fun x : Outcome B n => Dbar n x - M.d) = (fun D : ℝ => D / n - M.d) ∘
          Prod.fst := rfl
      rw [hcomp, eLpNorm_comp_measurePreserving (by fun_prop) hmp,
        eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      congr 1
      · refine lintegral_congr fun D => ?_
        rw [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofNat,
          ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
        congr 1
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    simp_rw [heq]
    have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp h31
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  have hZL2 := eq_A7_Zbar M hM hp hpos hζ hα hα'
  have hΔL2 := eq_A7_DeltaHat M hM hp hpos hζ hα hα'
  refine ⟨hDL2, hZL2, hΔL2, ?_⟩
  intro ε hε
  -- `μ_a(p) > 0` (Lemma 2)
  have hex : ∃ μ ∈ Set.Ioc (0 : ℝ) 1, μ = ∫ b, M.f b (p * M.ω (M.d / μ)) ∂M.β := by
    obtain ⟨μ, ⟨h1, h2⟩, -⟩ := ((lemma_2 M hM).1 p hp hpos).1
    exact ⟨μ, h1, h2⟩
  have hμpos : 0 < M.muLim p := by
    unfold Market.muLim
    rw [dif_pos hex]
    exact hex.choose_spec.1.1
  set μ := M.muLim p with hμdef
  set Δ := M.DeltaLim p with hΔdef
  set w := M.d / μ with hwdef
  have hw0 : 0 < w := div_pos hd hμpos
  -- measurability of `D̄`, `Z̄`, `Δ̂`
  have hZimeas : ∀ n (i : Fin n), Measurable (fun x : Outcome B n =>
      M.Z n (perturbLaw p (ζn n)) x i) := by
    intro n i
    unfold Market.Z
    apply Measurable.ite _ measurable_const measurable_const
    apply measurableSet_le
    · exact measurable_snd.comp (measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd))
    · have hpair : Measurable (fun x : Outcome B n =>
          ((x.2 i).1, (x.2 i).2.1 * M.q n (M.muN n (perturbLaw p (ζn n))))) := by
        have hi : Measurable (fun x : Outcome B n => x.2 i) :=
          (measurable_pi_apply i).comp measurable_snd
        exact (measurable_fst.comp hi).prodMk
          ((measurable_fst.comp (measurable_snd.comp hi)).mul_const _)
      exact hfmeas.comp hpair
  have hZbmeas : ∀ n, Measurable (fun x : Outcome B n => M.Zbar n p (ζn n) x) := by
    intro n
    unfold Market.Zbar
    exact (Finset.measurable_sum _ fun i _ => hZimeas n i).const_mul _
  have hepsmeas : ∀ n (i : Fin n), Measurable (fun x : Outcome B n => eps n p (ζn n) x i) := by
    intro n i
    unfold eps
    have hi : Measurable (fun x : Outcome B n => x.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    exact ((measurable_fst.comp (measurable_snd.comp hi)).sub_const _).div_const _
  have hepsbmeas : ∀ n, Measurable (fun x : Outcome B n => epsBar n p (ζn n) x) := by
    intro n
    unfold epsBar
    exact (Finset.measurable_sum _ fun i _ => hepsmeas n i).const_mul _
  have hΔmeas : ∀ n, Measurable (fun x : Outcome B n => M.DeltaHat n p (ζn n) x) := by
    intro n
    unfold Market.DeltaHat
    refine Measurable.div (Measurable.const_mul ?_ _) ?_
    · exact Finset.measurable_sum _ fun i _ =>
        ((hZimeas n i).sub (hZbmeas n)).mul ((hepsmeas n i).sub (hepsbmeas n))
    · exact Finset.measurable_sum _ fun i _ => ((hepsmeas n i).sub (hepsbmeas n)).pow_const 2
  have hΔp := inProb_of_eLpNorm (fun n => M.sample n (perturbLaw p (ζn n)))
    (fun n x => M.DeltaHat n p (ζn n) x) Δ (fun n => (hΔmeas n).aestronglyMeasurable) hΔL2
  have hDp := inProb_of_eLpNorm (fun n => M.sample n (perturbLaw p (ζn n)))
    (fun n x => Dbar n x) M.d (fun n => (measurable_fst.div_const _).aestronglyMeasurable) hDL2
  have hZp := inProb_of_eLpNorm (fun n => M.sample n (perturbLaw p (ζn n)))
    (fun n x => M.Zbar n p (ζn n) x) μ (fun n => (hZbmeas n).aestronglyMeasurable) hZL2
  -- the two cases `ω(w) > 0` and `ω(w) = 0`
  have hωw := hω.1 w hw0.le
  rcases eq_or_lt_of_le hωw.1 with hω0 | hωpos
  · -- `ω(w) = 0`: then `ω ≡ 0` on `[0, ∞)`, `Υ̂ = Δ̂` a.s. and `μ'_a(p) = Δ_a(p) = 0`
    have hzero : ∀ x, 0 ≤ x → M.ω x = 0 := by
      intro x hx
      rcases le_or_gt x w with hxw | hxw
      · have := hω.2.2.2.1 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hw0.le) hxw
        linarith [(hω.1 x hx).1]
      · have hx0 : 0 < x := lt_trans hw0 hxw
        have hc := hω.2.2.1.2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx)
          (show (0 : ℝ) ≤ 1 - w / x by rw [sub_nonneg, div_le_one hx0]; exact hxw.le)
          (show (0 : ℝ) ≤ w / x from div_nonneg hw0.le hx0.le) (show 1 - w / x + w / x = 1 by ring)
        simp only [smul_eq_mul, mul_zero, zero_add] at hc
        rw [div_mul_cancel₀ _ hx0.ne', ← hω0] at hc
        have h0 := (hω.1 0 le_rfl).1
        have h1 := (hω.1 x hx).1
        have h2 : 0 ≤ (1 - w / x) * M.ω 0 :=
          mul_nonneg (by rw [sub_nonneg, div_le_one hx0]; exact hxw.le) h0
        have h3 : w / x * M.ω x ≤ 0 := by linarith
        have h4 : 0 < w / x := div_pos hw0 hx0
        nlinarith
    have hΔ0 : Δ = 0 := by
      rw [hΔdef, Market.DeltaLim, ← hμdef, ← hwdef, ← hω0, zero_mul]
    have hμ'0 : M.muLimDeriv p = 0 := by
      rw [Market.muLimDeriv, ← hΔdef, hΔ0, zero_div]
    have hsub : ∀ n, {x : Outcome B n | ε < |M.UpsHat n p (ζn n) x - M.muLimDeriv p|} ⊆
        {x | ε < |M.DeltaHat n p (ζn n) x - Δ|} ∪ (Set.Iio 0 ×ˢ Set.univ) := by
      intro n x hx
      by_cases hx0 : x.1 < 0
      · exact Or.inr ⟨hx0, Set.mem_univ _⟩
      · left
        push Not at hx0
        have hZ0 : 0 ≤ M.Zbar n p (ζn n) x := by
          unfold Market.Zbar
          apply mul_nonneg (by positivity)
          apply Finset.sum_nonneg
          intro i _
          unfold Market.Z
          split_ifs <;> norm_num
        have hD0 : 0 ≤ Dbar n x := div_nonneg hx0 (Nat.cast_nonneg _)
        have hωz : M.ω (Dbar n x / M.Zbar n p (ζn n) x) = 0 := hzero _ (div_nonneg hD0 hZ0)
        have hU : M.UpsHat n p (ζn n) x = M.DeltaHat n p (ζn n) x := by
          unfold Market.UpsHat
          rw [hωz, mul_zero, div_zero, add_zero, div_one]
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [hU, hμ'0, ← hΔ0] at hx
        exact hx
    have hnull : ∀ n, M.sample n (perturbLaw p (ζn n)) (Set.Iio 0 ×ˢ Set.univ) = 0 := by
      intro n
      unfold Market.sample
      rw [Measure.prod_prod, (hF n).2, zero_mul]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hΔp ε hε)
      (fun n => bot_le) (fun n => ?_)
    refine le_trans (measure_mono (hsub n)) (le_trans (measure_union_le _ _) ?_)
    rw [hnull n, add_zero]
  · -- `ω(w) > 0`: continuous mapping
    let G : ℝ × ℝ × ℝ → ℝ := fun v =>
      v.1 / (1 + p * v.2.1 * v.1 * deriv M.ω (v.2.1 / v.2.2) /
        (v.2.2 ^ 2 * M.ω (v.2.1 / v.2.2)))
    have hopen : Set.Ioi (0 : ℝ) ∈ 𝓝 w := Ioi_mem_nhds hw0
    have hcω : ContinuousAt M.ω w := (hωs.continuousOn).continuousAt hopen
    have hcω' : ContinuousAt (deriv M.ω) w :=
      (hωs.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).continuousAt hopen
    -- signs: `Δ_a(p) ≥ 0`, `ω'(w) ≥ 0`
    have hω'0 : 0 ≤ deriv M.ω w := by
      have hdiff : DifferentiableAt ℝ M.ω w :=
        (hωs.differentiableOn (by simp)).differentiableAt hopen
      exact (hdiff.hasDerivAt.hasDerivWithinAt (s := Set.Ici 0)).nonneg_of_monotoneOn
        (accPt_Ici hw0.le) hω.2.2.2.1
    have hΔ0 : 0 ≤ Δ := by
      rw [hΔdef, Market.DeltaLim]
      apply mul_nonneg hωw.1
      apply integral_nonneg
      intro b
      have hx : 0 ≤ p * M.ω (M.d / M.muLim p) := mul_nonneg hp.le hωw.1
      exact (hfderiv b _ hx).1.nonneg_of_monotoneOn (accPt_Ici hx) (hfmono b)
    have hden : 0 < μ ^ 2 * M.ω w := by positivity
    have hfrac0 : 0 ≤ p * M.d * Δ * deriv M.ω w / (μ ^ 2 * M.ω w) := by positivity
    have hG : ContinuousAt G (Δ, M.d, μ) := by
      have hwc : ContinuousAt (fun v : ℝ × ℝ × ℝ => v.2.1 / v.2.2) (Δ, M.d, μ) :=
        (continuous_snd.fst.continuousAt).div (continuous_snd.snd.continuousAt) hμpos.ne'
      have h2 : ContinuousAt (fun v : ℝ × ℝ × ℝ => M.ω (v.2.1 / v.2.2)) (Δ, M.d, μ) :=
        ContinuousAt.comp (g := M.ω) hcω hwc
      have h4 : ContinuousAt (fun v : ℝ × ℝ × ℝ => deriv M.ω (v.2.1 / v.2.2)) (Δ, M.d, μ) :=
        ContinuousAt.comp (g := deriv M.ω) hcω' hwc
      have hnum : ContinuousAt (fun v : ℝ × ℝ × ℝ => p * v.2.1 * v.1 *
          deriv M.ω (v.2.1 / v.2.2)) (Δ, M.d, μ) :=
        ((continuousAt_const.mul continuous_snd.fst.continuousAt).mul
          continuous_fst.continuousAt).mul h4
      have hdn : ContinuousAt (fun v : ℝ × ℝ × ℝ => v.2.2 ^ 2 * M.ω (v.2.1 / v.2.2))
          (Δ, M.d, μ) := (continuous_snd.snd.continuousAt.pow 2).mul h2
      have hq : ContinuousAt (fun v : ℝ × ℝ × ℝ => p * v.2.1 * v.1 *
          deriv M.ω (v.2.1 / v.2.2) / (v.2.2 ^ 2 * M.ω (v.2.1 / v.2.2))) (Δ, M.d, μ) :=
        hnum.div hdn hden.ne'
      have hout : ContinuousAt (fun v : ℝ × ℝ × ℝ => 1 + p * v.2.1 * v.1 *
          deriv M.ω (v.2.1 / v.2.2) / (v.2.2 ^ 2 * M.ω (v.2.1 / v.2.2))) (Δ, M.d, μ) :=
        continuousAt_const.add hq
      have hne : (1 : ℝ) + p * M.d * Δ * deriv M.ω (M.d / μ) / (μ ^ 2 * M.ω (M.d / μ)) ≠ 0 := by
        rw [← hwdef]; linarith
      exact continuous_fst.continuousAt.div hout hne
    have main := inProb_comp3 (fun n => M.sample n (perturbLaw p (ζn n)))
      (fun n x => M.DeltaHat n p (ζn n) x) (fun n x => Dbar n x)
      (fun n x => M.Zbar n p (ζn n) x) Δ M.d μ G hG hΔp hDp hZp ε hε
    exact main
