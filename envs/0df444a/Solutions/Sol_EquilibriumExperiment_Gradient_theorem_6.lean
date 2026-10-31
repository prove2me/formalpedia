-- Prove2me | solution 1 for EquilibriumExperiment.Gradient.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T13:00:34.811134+00:00
-- url     : https://prove2.me/submissions/aadd2df7-0f6e-4ee7-95df-cd405b860fca

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model
import Theorems.Thm_EquilibriumExperiment_Gradient_eq_A7
import Theorems.Thm_EquilibriumExperiment_Gradient_proposition_12
import Theorems.Thm_EquilibriumExperiment_Gradient_lemma_2

open MeasureTheory ProbabilityTheory Filter Topology

namespace EqExpThm6Aux

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

end EqExpThm6Aux

open EqExpThm6Aux EquilibriumExperiment.Gradient

theorem solution {B : Type} [MeasurableSpace B] (M : EquilibriumExperiment.Gradient.Market B)
    (hM : M.Standing)
    {p : ℝ} (hp : 0 < p) (hpos : 0 < ∫ b, M.f b (p * M.omegaSup) ∂M.β)
    {ζ α : ℝ} (hζ : 0 < ζ) (hα : 0 < α) (hα' : α < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => M.sample n (EquilibriumExperiment.Gradient.perturbLaw p
        (ζ * (n : ℝ) ^ (-α)))
        {x | ε < |M.GammaHat n p (ζ * (n : ℝ) ^ (-α)) x - deriv M.u p|}) atTop (𝓝 0) := by
  have hM' := hM
  obtain ⟨hd, -, -, -, -, -, hω, -, -, -, -, -, -, -, -, -, -, hfmeas, -, -, hr, -⟩ := hM'
  have hωs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M.ω (Set.Ioi 0) := hω.2.1
  -- existence of `μ_a(p)` (Lemma 2) gives `μ_a(p) ∈ (0, 1]`
  have hex : ∃ μ ∈ Set.Ioc (0 : ℝ) 1, μ = ∫ b, M.f b (p * M.ω (M.d / μ)) ∂M.β := by
    obtain ⟨μ, ⟨h1, h2⟩, -⟩ := ((lemma_2 M hM).1 p hp hpos).1
    exact ⟨μ, h1, h2⟩
  have hμpos : 0 < M.muLim p := by
    unfold Market.muLim
    rw [dif_pos hex]
    exact hex.choose_spec.1.1
  set μ := M.muLim p with hμdef
  set μ' := M.muLimDeriv p with hμ'def
  -- the gradient formula (Proposition 12)
  have hderiv := (proposition_12 M hM hp hpos).deriv
  -- the consistency results (A.7)
  obtain ⟨hD, hZ, -, hU⟩ := eq_A7 M hM hp hpos hζ hα hα'
  set ζn : ℕ → ℝ := fun n => ζ * (n : ℝ) ^ (-α) with hζn
  -- the continuous map
  let G : ℝ × ℝ × ℝ → ℝ := fun v =>
    v.1 * (M.r (v.2.1 / v.2.2) - p * M.ω (v.2.1 / v.2.2) -
        (deriv M.r (v.2.1 / v.2.2) - p * deriv M.ω (v.2.1 / v.2.2)) * (v.2.1 / v.2.2)) -
      M.ω (v.2.1 / v.2.2) * v.2.2
  have hw0 : 0 < M.d / μ := div_pos hd hμpos
  have hopen : Set.Ioi (0 : ℝ) ∈ 𝓝 (M.d / μ) := Ioi_mem_nhds hw0
  have hcr : ContinuousAt M.r (M.d / μ) := (hr.continuousOn).continuousAt hopen
  have hcω : ContinuousAt M.ω (M.d / μ) := (hωs.continuousOn).continuousAt hopen
  have hcr' : ContinuousAt (deriv M.r) (M.d / μ) :=
    (hr.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).continuousAt hopen
  have hcω' : ContinuousAt (deriv M.ω) (M.d / μ) :=
    (hωs.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).continuousAt hopen
  have hG : ContinuousAt G (μ', M.d, μ) := by
    have hw : ContinuousAt (fun v : ℝ × ℝ × ℝ => v.2.1 / v.2.2) (μ', M.d, μ) :=
      (continuous_snd.fst.continuousAt).div (continuous_snd.snd.continuousAt) hμpos.ne'
    have h1 : ContinuousAt (fun v : ℝ × ℝ × ℝ => M.r (v.2.1 / v.2.2)) (μ', M.d, μ) :=
      ContinuousAt.comp (g := M.r) hcr hw
    have h2 : ContinuousAt (fun v : ℝ × ℝ × ℝ => M.ω (v.2.1 / v.2.2)) (μ', M.d, μ) :=
      ContinuousAt.comp (g := M.ω) hcω hw
    have h3 : ContinuousAt (fun v : ℝ × ℝ × ℝ => deriv M.r (v.2.1 / v.2.2)) (μ', M.d, μ) :=
      ContinuousAt.comp (g := deriv M.r) hcr' hw
    have h4 : ContinuousAt (fun v : ℝ × ℝ × ℝ => deriv M.ω (v.2.1 / v.2.2)) (μ', M.d, μ) :=
      ContinuousAt.comp (g := deriv M.ω) hcω' hw
    exact (continuous_fst.continuousAt.mul
      ((h1.sub (continuousAt_const.mul h2)).sub
        ((h3.sub (continuousAt_const.mul h4)).mul hw))).sub
      (h2.mul continuous_snd.snd.continuousAt)
  -- measurability of `D̄` and `Z̄`
  have hDmeas : ∀ n, AEStronglyMeasurable (fun x : Outcome B n => Dbar n x)
      (M.sample n (perturbLaw p (ζn n))) := by
    intro n
    exact (measurable_fst.div_const _).aestronglyMeasurable
  have hZmeas : ∀ n, AEStronglyMeasurable (fun x : Outcome B n => M.Zbar n p (ζn n) x)
      (M.sample n (perturbLaw p (ζn n))) := by
    intro n
    apply Measurable.aestronglyMeasurable
    unfold Market.Zbar Market.Z
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
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
  have hDp := inProb_of_eLpNorm (fun n => M.sample n (perturbLaw p (ζn n)))
    (fun n x => Dbar n x) M.d hDmeas hD
  have hZp := inProb_of_eLpNorm (fun n => M.sample n (perturbLaw p (ζn n)))
    (fun n x => M.Zbar n p (ζn n) x) μ hZmeas hZ
  have main := inProb_comp3 (fun n => M.sample n (perturbLaw p (ζn n)))
    (fun n x => M.UpsHat n p (ζn n) x) (fun n x => Dbar n x) (fun n x => M.Zbar n p (ζn n) x)
    μ' M.d μ G hG hU hDp hZp ε hε
  have hGval : G (μ', M.d, μ) = deriv M.u p := by
    rw [hderiv]
  rw [hGval] at main
  exact main
