-- Prove2me | solution 1 for EulerMascheroni.loglog_integral_asymp
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T12:26:07.403657+00:00
-- url     : https://prove2.me/submissions/71bdecc1-0424-4be8-bf0b-f9811c68021a

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Mertens.GammaIntegral =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# The γ-integral and the loglog-integral asymptotic (MERTENS arc, node MERT-3b)

Two facts feeding the identification `M = γ − B` on the `ζ`-side.

* `integral_exp_neg_log` (3b-α): `∫₀^∞ e^{-v} log v dv = -γ`, the Euler–Mascheroni
  constant.  Route: mathlib already differentiates the complex `Γ`-integral under the
  integral sign (`Complex.hasDerivAt_GammaIntegral`), so the parametric-integral /
  dominated-convergence work is done upstream.  We transfer that derivative to the real
  axis and equate with the landed `Real.hasDerivAt_Gamma_one (-γ)`.

* `loglog_integral_asymp` (3b-β): `(s-1)·∫₂^∞ loglog t · t^{-s} dt + log(s-1) → -γ`
  as `s → 1⁺` — the shape consumed by MERT-3c.
-/

open Set MeasureTheory Filter Topology

namespace Salt.Mertens

/-- **3b-α, the γ-integral.**  `∫₀^∞ e^{-v} · log v dv = -γ`, where `γ` is the
Euler–Mascheroni constant.

The parametric differentiation is entirely upstream: `Complex.hasDerivAt_GammaIntegral`
gives `HasDerivAt Γ_ℂ (∫ t^{s-1}·log t·e^{-t}) s` for `0 < re s`.  Evaluating at `s = 1`,
transferring to the real axis, and equating with `Real.hasDerivAt_Gamma_one` by derivative
uniqueness pins the integral to `-γ`. -/
theorem integral_exp_neg_log :
    ∫ v in Set.Ioi (0:ℝ), Real.exp (-v) * Real.log v = -Real.eulerMascheroniConstant := by
  -- The Γ-integral is differentiable at every `s` with `0 < re s`; specialize to `s = 1`.
  have hd : IsOpen {s : ℂ | 0 < s.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have h1 : HasDerivAt Complex.GammaIntegral
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 : ℂ) - 1) * (Real.log t * Real.exp (-t))) 1 :=
    Complex.hasDerivAt_GammaIntegral (by simp)
  -- On `re s > 0`, `Γ = Γ_integral`, so `Γ` has the same derivative at `1`.
  have heq : Complex.Gamma =ᶠ[𝓝 (1 : ℂ)] Complex.GammaIntegral := by
    filter_upwards [hd.mem_nhds (show 0 < (1 : ℂ).re by simp)] with a ha
    exact Complex.Gamma_eq_integral ha
  have h2 : HasDerivAt Complex.Gamma
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 : ℂ) - 1) * (Real.log t * Real.exp (-t))) 1 :=
    h1.congr_of_eventuallyEq heq
  -- Restrict to the real axis: `y ↦ Γ_ℂ y` is `y ↦ ↑(Γ_ℝ y)`.
  have h3 := HasDerivAt.comp_ofReal (z := (1 : ℝ)) h2
  have hfun : (fun y : ℝ => Complex.Gamma (y : ℂ)) = (fun y : ℝ => (Real.Gamma y : ℂ)) :=
    funext fun y => Complex.Gamma_ofReal y
  rw [hfun] at h3
  -- The landed real derivative: `Γ_ℝ' 1 = -γ`.
  have h4 : HasDerivAt (fun y : ℝ => (Real.Gamma y : ℂ))
      ((-Real.eulerMascheroniConstant : ℝ) : ℂ) 1 :=
    Real.hasDerivAt_Gamma_one.ofReal_comp
  -- Derivative uniqueness pins the (complex) integral value.
  have huniq := h3.unique h4
  -- Simplify the complex integrand at `s = 1` back to the real integral.
  have hval : ((∫ v in Ioi (0:ℝ), Real.exp (-v) * Real.log v : ℝ) : ℂ)
       = ((-Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    rw [← huniq, ← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [sub_self, Complex.cpow_zero, one_mul]
    push_cast
    ring
  exact_mod_cast hval

/-! ## 3b-β infrastructure: bounds and integrability -/

section Asymptotic

open Real

/-- For `y ≥ log 2`, `|log y| ≤ y`.  (Fails for small `y`, but `log 2 ≈ 0.693` is safely
above the crossover.)  Used to dominate both the `loglog·t^{-s}` and `log·e^{-εu}` integrands. -/
private theorem abs_log_le_self {y : ℝ} (hy : Real.log 2 ≤ y) : |Real.log y| ≤ y := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hypos : 0 < y := lt_of_lt_of_le h2 hy
  by_cases h1 : 1 ≤ y
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    linarith [Real.log_le_sub_one_of_pos hypos]
  · replace h1 := not_le.mp h1
    rw [abs_of_nonpos (Real.log_nonpos hypos.le h1.le)]
    have hll2 : -Real.log 2 ≤ Real.log (Real.log 2) := by
      have h12 : Real.log (2⁻¹ : ℝ) ≤ Real.log (Real.log 2) :=
        Real.log_le_log (by norm_num) (by nlinarith [Real.log_two_gt_d9])
      rwa [Real.log_inv] at h12
    have hmono : Real.log (Real.log 2) ≤ Real.log y := Real.log_le_log h2 hy
    linarith

/-- `fun t => log (log t)` is continuous on `[2,∞)` (there `log t ≥ log 2 > 0`). -/
private theorem continuousOn_loglog :
    ContinuousOn (fun t => Real.log (Real.log t)) (Ici (2:ℝ)) := by
  have hmaps : MapsTo Real.log (Ici (2:ℝ)) ({0}ᶜ) := fun x hx => by
    simp only [mem_Ici] at hx
    exact Set.mem_compl_singleton_iff.mpr (ne_of_gt (Real.log_pos (by linarith)))
  have hsub : (Ici (2:ℝ)) ⊆ ({0}ᶜ) := fun x hx => by
    simp only [mem_Ici] at hx
    exact Set.mem_compl_singleton_iff.mpr (by linarith)
  exact Real.continuousOn_log.comp (Real.continuousOn_log.mono hsub) hmaps

/-- Integrability of the `ζ`-side integrand `loglog t · t^{-s}` on `[2,∞)` for `s > 1`.
Domination: `|loglog t| ≤ log t ≤ t^{ε/2}/(ε/2)`, so the integrand is `≤ (2/ε)·t^{-1-ε/2}`,
a `rpow` with exponent `< -1`. -/
private theorem integrableOn_loglog_rpow {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t => Real.log (Real.log t) * t ^ (-s)) (Ici 2) := by
  set ε := s - 1 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  -- Dominating function `(2/ε)·t^{-1-ε/2}`, integrable on `[2,∞)`.
  have hg : IntegrableOn (fun t : ℝ => (2 / ε) * t ^ (-1 - ε / 2)) (Ici 2) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul _
  refine hg.mono' ?_ ?_
  · -- measurability of the integrand on `[2,∞)`
    refine (continuousOn_loglog.mul ?_).aestronglyMeasurable measurableSet_Ici
    exact continuousOn_id.rpow_const fun x hx => Or.inl (by simp only [mem_Ici] at hx; positivity)
  · -- domination
    refine (ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    simp only [mem_Ici] at ht
    have htpos : (0:ℝ) < t := by linarith
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg htpos.le _)]
    have hlog2 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
    have h1 : |Real.log (Real.log t)| ≤ Real.log t := abs_log_le_self hlog2
    have h2 : Real.log t ≤ t ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div htpos.le (by positivity)
    have hpow : t ^ (ε / 2) * t ^ (-s) = t ^ (-1 - ε / 2) := by
      rw [← Real.rpow_add htpos]; congr 1; rw [hε]; ring
    calc |Real.log (Real.log t)| * t ^ (-s)
        ≤ (t ^ (ε / 2) / (ε / 2)) * t ^ (-s) :=
          mul_le_mul_of_nonneg_right (le_trans h1 h2) (Real.rpow_nonneg htpos.le _)
      _ = (2 / ε) * t ^ (-1 - ε / 2) := by
          rw [div_mul_eq_mul_div, hpow, div_eq_mul_inv, inv_div,
            mul_comm (t ^ (-1 - ε / 2)) (2 / ε)]

/-- Integrability of `log u · e^{-εu}` on `[c,∞)` for `c ≥ log 2` and `ε > 0`.
Domination: `|log u| ≤ u ≤ (2/ε)·e^{εu/2}`, so the integrand is `≤ (2/ε)·e^{-εu/2}`. -/
private theorem integrableOn_log_exp {ε c : ℝ} (hεpos : 0 < ε) (hc : Real.log 2 ≤ c) :
    IntegrableOn (fun u => Real.log u * Real.exp (-ε * u)) (Ici c) := by
  have hεne : ε ≠ 0 := ne_of_gt hεpos
  have hg : IntegrableOn (fun u : ℝ => (2 / ε) * Real.exp (-ε / 2 * u)) (Ici c) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (integrableOn_exp_mul_Ioi (by linarith) c).const_mul _
  refine hg.mono' ?_ ?_
  · refine (ContinuousOn.mul ?_ ?_).aestronglyMeasurable measurableSet_Ici
    · apply Real.continuousOn_log.mono
      intro x hx; simp only [mem_Ici] at hx
      have : (0:ℝ) < x := lt_of_lt_of_le (Real.log_pos (by norm_num)) (le_trans hc hx)
      exact Set.mem_compl_singleton_iff.mpr (ne_of_gt this)
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  · refine (ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    simp only [mem_Ici] at hu
    have hupos : 0 < u := lt_of_lt_of_le (Real.log_pos (by norm_num)) (le_trans hc hu)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    have h1 : |Real.log u| ≤ u := abs_log_le_self (le_trans hc hu)
    have h2 : u ≤ (2 / ε) * Real.exp (ε / 2 * u) := by
      have hx : ε / 2 * u ≤ Real.exp (ε / 2 * u) :=
        le_trans (by linarith) (Real.add_one_le_exp (ε / 2 * u))
      have key := mul_le_mul_of_nonneg_left hx (by positivity : (0:ℝ) ≤ 2 / ε)
      rwa [show (2 / ε) * (ε / 2 * u) = u by field_simp] at key
    have hexp : Real.exp (ε / 2 * u) * Real.exp (-ε * u) = Real.exp (-ε / 2 * u) := by
      rw [← Real.exp_add]; congr 1; ring
    calc |Real.log u| * Real.exp (-ε * u)
        ≤ ((2 / ε) * Real.exp (ε / 2 * u)) * Real.exp (-ε * u) :=
          mul_le_mul_of_nonneg_right (le_trans h1 h2) (Real.exp_nonneg _)
      _ = (2 / ε) * (Real.exp (ε / 2 * u) * Real.exp (-ε * u)) := by ring
      _ = (2 / ε) * Real.exp (-ε / 2 * u) := by rw [hexp]

/-- **The substitution identity.**  With `ε = s - 1`, the change of variables `t = e^u`
(here run as `u = log t` via `integral_comp_mul_deriv_Ioi`) turns the `ζ`-side integral into
`∫_{log 2}^∞ log u · e^{-εu} du`. -/
private theorem sub_identity {s : ℝ} (hs : 1 < s) :
    (∫ t in Ioi 2, Real.log (Real.log t) * t ^ (-s))
      = ∫ u in Ioi (Real.log 2), Real.log u * Real.exp (-(s - 1) * u) := by
  set ε := s - 1 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set g : ℝ → ℝ := fun u => Real.log u * Real.exp (-ε * u) with hg_def
  -- Hypotheses for `integral_comp_mul_deriv_Ioi` with `f = log`, `a = 2`, `f' = ·⁻¹`.
  have hf : ContinuousOn Real.log (Ici (2:ℝ)) :=
    Real.continuousOn_log.mono fun x hx =>
      Set.mem_compl_singleton_iff.mpr (ne_of_gt (by simp only [mem_Ici] at hx; linarith))
  have hff' : ∀ x ∈ Ioi (2:ℝ), HasDerivWithinAt Real.log x⁻¹ (Ioi x) x := fun x hx => by
    simp only [mem_Ioi] at hx
    exact (Real.hasDerivAt_log (ne_of_gt (by linarith))).hasDerivWithinAt
  have himg_Ioi : Real.log '' Ioi (2:ℝ) ⊆ Ioi (Real.log 2) := by
    rintro _ ⟨x, hx, rfl⟩; simp only [mem_Ioi] at hx ⊢
    exact Real.log_lt_log (by norm_num) hx
  have himg_Ici : Real.log '' Ici (2:ℝ) ⊆ Ici (Real.log 2) := by
    rintro _ ⟨x, hx, rfl⟩; simp only [mem_Ici] at hx ⊢
    exact Real.log_le_log (by norm_num) hx
  have hg_cont : ContinuousOn g (Real.log '' Ioi (2:ℝ)) := by
    refine ContinuousOn.mono (ContinuousOn.mul ?_ ?_) himg_Ioi
    · exact Real.continuousOn_log.mono fun y hy =>
        Set.mem_compl_singleton_iff.mpr (ne_of_gt (by
          simp only [mem_Ioi] at hy; exact lt_trans (Real.log_pos (by norm_num)) hy))
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hg1 : IntegrableOn g (Real.log '' Ici (2:ℝ)) :=
    (integrableOn_log_exp hεpos (le_refl _)).mono_set himg_Ici
  -- Pointwise identity `loglog x · x^{-s} = (g∘log) x · x⁻¹` for `x > 0`.
  have hpt : ∀ x : ℝ, 0 < x →
      Real.log (Real.log x) * x ^ (-s) = (g ∘ Real.log) x * x⁻¹ := by
    intro x hxpos
    simp only [hg_def, Function.comp_apply]
    rw [mul_assoc]; congr 1
    rw [mul_comm (-ε) (Real.log x), ← Real.rpow_def_of_pos hxpos, ← Real.rpow_neg_one x,
      ← Real.rpow_add hxpos]
    congr 1; rw [hε]; ring
  have hg2 : IntegrableOn (fun x => (g ∘ Real.log) x * x⁻¹) (Ici (2:ℝ)) := by
    refine (integrableOn_loglog_rpow hs).congr_fun ?_ measurableSet_Ici
    intro x hx; simp only [mem_Ici] at hx
    exact hpt x (by linarith)
  have key := integral_comp_mul_deriv_Ioi (f' := fun x => x⁻¹)
    hf Real.tendsto_log_atTop hff' hg_cont hg1 hg2
  calc (∫ t in Ioi 2, Real.log (Real.log t) * t ^ (-s))
      = ∫ x in Ioi 2, (g ∘ Real.log) x * x⁻¹ :=
        setIntegral_congr_fun measurableSet_Ioi
          (fun x hx => hpt x (by simp only [mem_Ioi] at hx; linarith))
    _ = ∫ u in Ioi (Real.log 2), g u := key

/-- `log v · e^{-v}` is integrable on `(0,∞)`.  Near `0`, `log` is interval-integrable and
`e^{-v}` is bounded; at `∞`, the exponential dominates (via `integrableOn_log_exp` at `ε = 1`). -/
private theorem integrableOn_logexp_Ioi_zero :
    IntegrableOn (fun v => Real.log v * Real.exp (-v)) (Ioi (0:ℝ)) := by
  have h01 : IntegrableOn (fun v => Real.log v * Real.exp (-v)) (Ioc 0 1) := by
    have hii : IntervalIntegrable (fun v => Real.log v * Real.exp (-v)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'.mul_continuousOn
        (Real.continuous_exp.comp continuous_neg).continuousOn
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hii
  have h1 : IntegrableOn (fun v => Real.log v * Real.exp (-v)) (Ioi 1) := by
    have hle : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
    refine ((integrableOn_log_exp (show (0:ℝ) < 1 by norm_num) hle).mono_set
      Ioi_subset_Ici_self).congr_fun ?_ measurableSet_Ioi
    intro v _; simp only [neg_one_mul]
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0:ℝ) ≤ 1 by norm_num)]
  exact h01.union h1

/-- **The algebraic identity** feeding the limit.  With `ε = s - 1 > 0`, combining the
substitution identity, the linear rescaling `v = εu`, and `∫_{Ioi a} e^{-v} = e^{-a}`. -/
private theorem phi_eq {s : ℝ} (hs : 1 < s) :
    (s - 1) * (∫ t in Ioi 2, Real.log (Real.log t) * t ^ (-s)) + Real.log (s - 1)
      = (∫ v in Ioi ((s - 1) * Real.log 2), Real.log v * Real.exp (-v))
        + Real.log (s - 1) * (1 - Real.exp (-((s - 1) * Real.log 2))) := by
  rw [sub_identity hs]
  set ε := s - 1 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set G : ℝ → ℝ := fun v => (Real.log v - Real.log ε) * Real.exp (-v) with hG_def
  -- Rewrite the integrand as `G (ε·u)`, then apply the linear change of variables.
  have hcongr : (∫ u in Ioi (Real.log 2), Real.log u * Real.exp (-ε * u))
      = ∫ u in Ioi (Real.log 2), G (ε * u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu; simp only [mem_Ioi] at hu
    have hupos : 0 < u := lt_trans hlog2pos hu
    simp only [hG_def, Real.log_mul (ne_of_gt hεpos) (ne_of_gt hupos), neg_mul]
    ring
  have hlinsub : (∫ u in Ioi (Real.log 2), Real.log u * Real.exp (-ε * u))
      = ε⁻¹ • ∫ v in Ioi (ε * Real.log 2), G v := by
    rw [hcongr]; exact integral_comp_mul_left_Ioi G (Real.log 2) hεpos
  -- Split `∫ G` into the `log v·e^{-v}` and `e^{-v}` pieces.
  have hεlog2pos : 0 < ε * Real.log 2 := mul_pos hεpos hlog2pos
  have hint_logexp : IntegrableOn (fun v => Real.log v * Real.exp (-v))
      (Ioi (ε * Real.log 2)) :=
    integrableOn_logexp_Ioi_zero.mono_set (Ioi_subset_Ioi hεlog2pos.le)
  have hint_exp : IntegrableOn (fun v => Real.log ε * Real.exp (-v))
      (Ioi (ε * Real.log 2)) := (integrableOn_exp_neg_Ioi _).const_mul _
  have hGsplit : (∫ v in Ioi (ε * Real.log 2), G v)
      = (∫ v in Ioi (ε * Real.log 2), Real.log v * Real.exp (-v))
        - Real.log ε * Real.exp (-(ε * Real.log 2)) := by
    have hEq : ∀ v, G v = Real.log v * Real.exp (-v) - Real.log ε * Real.exp (-v) := by
      intro v; simp only [hG_def]; ring
    simp only [hEq]
    rw [integral_sub hint_logexp hint_exp, integral_const_mul, integral_exp_neg_Ioi]
  rw [hlinsub, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hεpos), one_mul, hGsplit]
  ring

/-- **Right-continuity of the tail integral at `0`.**  `∫_{Ioi a} log v·e^{-v} → -γ` as
`a → 0⁺`, since the missing mass `∫_{Ioc 0 a}` vanishes (absolute continuity of the integral)
and `∫_{Ioi 0} log v·e^{-v} = -γ` by 3b-α. -/
private theorem tendsto_J :
    Tendsto (fun a : ℝ => ∫ v in Ioi a, Real.log v * Real.exp (-v)) (𝓝[>] 0)
      (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hf0 := integrableOn_logexp_Ioi_zero
  have hJ0 : (∫ v in Ioi (0:ℝ), Real.log v * Real.exp (-v)) = -Real.eulerMascheroniConstant := by
    rw [← integral_exp_neg_log]
    exact setIntegral_congr_fun measurableSet_Ioi (fun v _ => mul_comm _ _)
  have hsplit : ∀ a : ℝ, 0 < a → (∫ v in Ioi a, Real.log v * Real.exp (-v))
      = (∫ v in Ioi (0:ℝ), Real.log v * Real.exp (-v))
        - ∫ v in Ioc 0 a, Real.log v * Real.exp (-v) := by
    intro a ha
    have key : (∫ v in Ioi (0:ℝ), Real.log v * Real.exp (-v))
        = (∫ v in Ioc 0 a, Real.log v * Real.exp (-v))
          + ∫ v in Ioi a, Real.log v * Real.exp (-v) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi ha.le]
      exact setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hf0.mono_set Set.Ioc_subset_Ioi_self) (hf0.mono_set (Ioi_subset_Ioi ha.le))
    linarith
  have hmeas : Tendsto (fun a : ℝ => (volume.restrict (Ioi (0:ℝ))) (Ioc (0:ℝ) a))
      (𝓝[>] 0) (𝓝 0) := by
    have heqm : (fun a : ℝ => (volume.restrict (Ioi (0:ℝ))) (Ioc (0:ℝ) a))
        =ᶠ[𝓝[>] (0:ℝ)] (fun a : ℝ => ENNReal.ofReal a) := by
      filter_upwards [self_mem_nhdsWithin] with a ha
      simp only [mem_Ioi] at ha
      rw [Measure.restrict_apply measurableSet_Ioc,
        Set.inter_eq_left.mpr Set.Ioc_subset_Ioi_self, Real.volume_Ioc, sub_zero]
    rw [tendsto_congr' heqm, ← ENNReal.ofReal_zero]
    exact (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have htend0 : Tendsto (fun a : ℝ => ∫ v in Ioc 0 a, Real.log v * Real.exp (-v))
      (𝓝[>] 0) (𝓝 0) := by
    refine (hf0.tendsto_setIntegral_nhds_zero (l := 𝓝[>] (0:ℝ))
      (s := fun a => Ioc 0 a) hmeas).congr (fun a => ?_)
    rw [Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self]
  have heq : (fun a : ℝ => ∫ v in Ioi a, Real.log v * Real.exp (-v))
      =ᶠ[𝓝[>] 0] (fun a => (∫ v in Ioi (0:ℝ), Real.log v * Real.exp (-v))
        - ∫ v in Ioc 0 a, Real.log v * Real.exp (-v)) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact hsplit a ha
  rw [tendsto_congr' heq, hJ0]
  simpa using (tendsto_const_nhds (x := -Real.eulerMascheroniConstant)).sub htend0

/-- **3b-β, the loglog-integral asymptotic.**  `(s-1)·∫₂^∞ loglog t·t^{-s} dt + log(s-1) → -γ`
as `s → 1⁺` — the shape MERT-3c consumes. -/
theorem loglog_integral_asymp :
    Filter.Tendsto
      (fun s : ℝ => (s - 1) * (∫ t in Set.Ioi (2:ℝ), Real.log (Real.log t) * t ^ (-s))
        + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (-Real.eulerMascheroniConstant)) := by
  have hΦ : (fun s : ℝ => (s - 1) * (∫ t in Ioi 2, Real.log (Real.log t) * t ^ (-s))
        + Real.log (s - 1))
      =ᶠ[𝓝[>] 1] (fun s : ℝ => (∫ v in Ioi ((s - 1) * Real.log 2), Real.log v * Real.exp (-v))
        + Real.log (s - 1) * (1 - Real.exp (-((s - 1) * Real.log 2)))) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact phi_eq hs
  rw [tendsto_congr' hΦ]
  -- Limit 1: the tail integral → -γ, via `tendsto_J` composed with `s ↦ (s-1)·log 2`.
  have hsub1' : Tendsto (fun s : ℝ => (s - 1) * Real.log 2) (𝓝[>] (1:ℝ)) (𝓝[>] (0:ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun s : ℝ => (s - 1) * Real.log 2) (𝓝 1) (𝓝 ((1 - 1) * Real.log 2)) :=
        ((continuous_id.sub continuous_const).mul continuous_const).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [mem_Ioi] at hs ⊢
      exact mul_pos (by linarith) (Real.log_pos (by norm_num))
  have hlim1 : Tendsto (fun s : ℝ => ∫ v in Ioi ((s - 1) * Real.log 2), Real.log v * Real.exp (-v))
      (𝓝[>] 1) (𝓝 (-Real.eulerMascheroniConstant)) := tendsto_J.comp hsub1'
  -- Limit 2: `log(s-1)·(1 - e^{-(s-1)log 2}) → 0` by squeeze (the `x log x → 0` limit kills it).
  have hlim2 : Tendsto (fun s : ℝ => Real.log (s - 1) * (1 - Real.exp (-((s - 1) * Real.log 2))))
      (𝓝[>] (1:ℝ)) (𝓝 0) := by
    have hxlogx : Tendsto (fun x : ℝ => Real.log x * x) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa [Real.rpow_one] using
        tendsto_log_mul_rpow_nhdsGT_zero (r := 1) (by norm_num)
    have hsub1 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1:ℝ)) (𝓝[>] (0:ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1)) :=
          (continuous_id.sub continuous_const).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [mem_Ioi] at hs ⊢; linarith
    have hg0 : Tendsto (fun s : ℝ => Real.log (s - 1) * (s - 1) * Real.log 2)
        (𝓝[>] (1:ℝ)) (𝓝 0) := by
      simpa using (hxlogx.comp hsub1).mul_const (Real.log 2)
    have hev : ∀ᶠ s in 𝓝[>] (1:ℝ), 1 < s ∧ s < 2 := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (show (1:ℝ) < 2 by norm_num)).filter_mono nhdsWithin_le_nhds]
        with s hs hs2
      exact ⟨hs, hs2⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg0 tendsto_const_nhds ?_ ?_
    · filter_upwards [hev] with s hs
      obtain ⟨hs1, hs2⟩ := hs
      have hx : 0 < s - 1 := by linarith
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hexp : 1 - Real.exp (-((s - 1) * Real.log 2)) ≤ (s - 1) * Real.log 2 := by
        linarith [Real.add_one_le_exp (-((s - 1) * Real.log 2))]
      have hlogneg : Real.log (s - 1) ≤ 0 := Real.log_nonpos hx.le (by linarith)
      calc Real.log (s - 1) * (s - 1) * Real.log 2
          = Real.log (s - 1) * ((s - 1) * Real.log 2) := by ring
        _ ≤ Real.log (s - 1) * (1 - Real.exp (-((s - 1) * Real.log 2))) :=
            mul_le_mul_of_nonpos_left hexp hlogneg
    · filter_upwards [hev] with s hs
      obtain ⟨hs1, hs2⟩ := hs
      have hx : 0 < s - 1 := by linarith
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hxpos : 0 < (s - 1) * Real.log 2 := mul_pos hx hlog2pos
      have hlogneg : Real.log (s - 1) ≤ 0 := Real.log_nonpos hx.le (by linarith)
      have h1exp : 0 ≤ 1 - Real.exp (-((s - 1) * Real.log 2)) := by
        have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hxpos.le)
        linarith
      exact mul_nonpos_iff.mpr (Or.inr ⟨hlogneg, h1exp⟩)
  simpa using hlim1.add hlim2

end Asymptotic

end Salt.Mertens

end




theorem solution :
    Filter.Tendsto
      (fun s : ℝ => (s - 1) * (∫ t in Set.Ioi (2:ℝ), Real.log (Real.log t) * t ^ (-s))
        + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (-Real.eulerMascheroniConstant)) :=
  Salt.Mertens.loglog_integral_asymp

