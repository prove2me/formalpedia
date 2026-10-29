-- Prove2me | solution 1 for FiniteEnergyPlane.tendstoUniformly_of_tendsto_intervalIntegral_sq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-28T21:32:57.483983+00:00
-- url     : https://prove2.me/submissions/e35b60b2-573b-4d07-8d2a-58555b43cb9b

import Mathlib

open MeasureTheory Filter Topology
open MeasureTheory Filter Topology Set

namespace FiniteEnergyPlane

/-- Periodic `C¹` loops whose derivatives are bounded in `L²(0,1)` and which converge in
`L²(0,1)` to a continuous periodic loop converge to it uniformly on `ℝ`. -/
theorem tendstoUniformly_of_tendsto_intervalIntegral_sq_of_forall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f f' : ℕ → ℝ → E) (hf : ∀ k t, HasDerivAt (f k) (f' k t) t)
    (hf' : ∀ k, Continuous (f' k)) (hper : ∀ k, Function.Periodic (f k) 1)
    (e : ℝ → E) (he : Continuous e) (hep : Function.Periodic e 1)
    (M : ℝ) (hM : ∀ k, ∫ t in (0:ℝ)..1, ‖f' k t‖ ^ 2 ≤ M)
    (hL2 : Tendsto (fun k => ∫ t in (0:ℝ)..1, ‖f k t - e t‖ ^ 2) atTop (𝓝 0)) :
    TendstoUniformly f e atTop := by
  have hfc : ∀ k, Continuous (f k) := fun k =>
    continuous_iff_continuousAt.2 fun t => (hf k t).continuousAt
  -- periodicity of the derivatives
  have hf'per : ∀ k, Function.Periodic (f' k) 1 := by
    intro k t
    have h1 : HasDerivAt (fun x => f k (x + 1)) (f' k (t + 1)) t :=
      (hf k (t + 1)).comp_add_const t 1
    have h2 : (fun x => f k (x + 1)) = f k := funext fun x => hper k x
    rw [h2] at h1
    exact h1.unique (hf k t)
  -- integrals over unit windows
  have hwin : ∀ (g : ℝ → ℝ), Continuous g → Function.Periodic g 1 → (∀ x, 0 ≤ g x) →
      ∀ t a b, t ≤ a → a ≤ b → b ≤ t + 1 →
        ∫ x in a..b, g x ≤ ∫ x in (0:ℝ)..1, g x := by
    intro g hg hgp hg0 t a b hta hab hbt
    have h1 : ∫ x in a..b, g x ≤ ∫ x in t..t + 1, g x :=
      intervalIntegral.integral_mono_interval hta hab hbt
        (Eventually.of_forall fun x => hg0 x) (hg.intervalIntegrable _ _)
    have h2 := hgp.intervalIntegral_add_eq t 0
    rw [zero_add] at h2
    linarith
  -- uniform continuity of `e`
  have hue : ∀ ε > 0, ∃ δ > 0, δ ≤ 1 ∧ ∀ t x, |x - t| ≤ δ → ‖e x - e t‖ < ε := by
    intro ε hε
    have hU : UniformContinuousOn e (Icc (-2 : ℝ) 3) :=
      isCompact_Icc.uniformContinuousOn_of_continuous he.continuousOn
    obtain ⟨δ, hδ, hδU⟩ := Metric.uniformContinuousOn_iff.1 hU ε hε
    refine ⟨min (δ / 2) 1, by positivity, min_le_right _ _, fun t x hx => ?_⟩
    set m : ℤ := ⌊t⌋
    have hm1 : (m : ℝ) ≤ t := Int.floor_le t
    have hm2 : t < m + 1 := Int.lt_floor_add_one t
    have hx1 : |x - t| ≤ 1 := hx.trans (min_le_right _ _)
    have hx2 : |x - t| ≤ δ / 2 := hx.trans (min_le_left _ _)
    rw [abs_le] at hx1
    have ex : e x = e (x - m * 1) := (hep.sub_int_mul_eq m).symm
    have et : e t = e (t - m * 1) := (hep.sub_int_mul_eq m).symm
    rw [ex, et, ← dist_eq_norm]
    refine hδU _ ⟨by linarith, by linarith⟩ _ ⟨by linarith, by linarith⟩ ?_
    rw [Real.dist_eq]
    have : x - m * 1 - (t - m * 1) = x - t := by ring
    rw [this]
    linarith
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  -- choose the scales
  set M' := max M 0
  have hM' : ∀ k, ∫ t in (0:ℝ)..1, ‖f' k t‖ ^ 2 ≤ M' := fun k => (hM k).trans (le_max_left _ _)
  set lam : ℝ := 3 * M' / ε + 1
  have hlam : 0 < lam := by positivity
  obtain ⟨δ, hδ, hδ1, hδe⟩ := hue (ε / 3) (by positivity)
  set h : ℝ := min δ (ε / (3 * lam))
  have hh : 0 < h := by positivity
  have hh1 : h ≤ 1 := (min_le_left _ _).trans hδ1
  have hhδ : h ≤ δ := min_le_left _ _
  have hhl : lam * h ≤ ε / 3 := by
    have : h ≤ ε / (3 * lam) := min_le_right _ _
    calc lam * h ≤ lam * (ε / (3 * lam)) := mul_le_mul_of_nonneg_left this hlam.le
      _ = ε / 3 := by field_simp
  -- the increment bound
  have hinc : ∀ k t x, t ≤ x → x ≤ t + h → ‖f k x - f k t‖ ≤ ε / 3 := by
    intro k t x htx hxt
    have hint : IntervalIntegrable (f' k) volume t x := (hf' k).intervalIntegrable _ _
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hf k y) hint
    rw [← hftc]
    refine (intervalIntegral.norm_integral_le_integral_norm htx).trans ?_
    have hpt : ∀ y, ‖f' k y‖ ≤ ‖f' k y‖ ^ 2 / (2 * lam) + lam / 2 := by
      intro y
      rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (‖f' k y‖ - lam), norm_nonneg (f' k y)]
    have hc2 : Continuous fun y => ‖f' k y‖ ^ 2 := ((hf' k).norm).pow 2
    have h1 : ∫ y in t..x, ‖f' k y‖ ≤ ∫ y in t..x, (‖f' k y‖ ^ 2 / (2 * lam) + lam / 2) :=
      intervalIntegral.integral_mono_on htx ((hf' k).norm.intervalIntegrable _ _)
        ((hc2.div_const _).add continuous_const |>.intervalIntegrable _ _) fun y _ => hpt y
    have h2 : ∫ y in t..x, (‖f' k y‖ ^ 2 / (2 * lam) + lam / 2) =
        (∫ y in t..x, ‖f' k y‖ ^ 2) / (2 * lam) + (x - t) * (lam / 2) := by
      rw [intervalIntegral.integral_add ((hc2.div_const _).intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_div, intervalIntegral.integral_const,
        smul_eq_mul]
    have h3 : ∫ y in t..x, ‖f' k y‖ ^ 2 ≤ M' :=
      (hwin _ hc2 (fun y => by simp only [hf'per k y]) (fun y => by positivity) t t x le_rfl htx
        (by linarith)).trans (hM' k)
    have h4 : M' / (2 * lam) ≤ ε / 6 := by
      rw [div_le_iff₀ (by positivity)]
      have hl : ε / 6 * (2 * lam) = M' + ε / 3 := by
        simp only [lam]; field_simp; ring
      rw [hl]; linarith
    have h5 : (x - t) * (lam / 2) ≤ ε / 6 := by nlinarith
    have h6 : (∫ y in t..x, ‖f' k y‖ ^ 2) / (2 * lam) ≤ M' / (2 * lam) :=
      div_le_div_of_nonneg_right h3 (by positivity)
    linarith
  -- the L² smallness
  have hev : ∀ᶠ k in atTop, ∫ t in (0:ℝ)..1, ‖f k t - e t‖ ^ 2 < h * (ε / 3) ^ 2 :=
    (tendsto_order.1 hL2).2 _ (by positivity)
  filter_upwards [hev] with k hk
  intro t
  set g : ℝ → ℝ := fun x => ‖f k x - e x‖ ^ 2
  have hgc : Continuous g := (((hfc k).sub he).norm).pow 2
  have hgp : Function.Periodic g 1 := fun x => by simp only [g, hper k x, hep x]
  -- a good point in `[t, t + h]`
  obtain ⟨x, hx, hgx⟩ : ∃ x ∈ Icc t (t + h), g x ≤ (ε / 3) ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∫ _ in t..t + h, (ε / 3) ^ 2 < ∫ x in t..t + h, g x :=
      intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by linarith)
        continuousOn_const hgc.continuousOn (fun x hx => (hcon x (Ioc_subset_Icc_self hx)).le)
        ⟨t, ⟨le_rfl, by linarith⟩, hcon t ⟨le_rfl, by linarith⟩⟩
    have hle := hwin g hgc hgp (fun x => by positivity) t t (t + h) le_rfl (by linarith)
      (by linarith)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hlt
    have : t + h - t = h := by ring
    rw [this] at hlt
    have : h * (ε / 3) ^ 2 < ∫ x in (0:ℝ)..1, ‖f k x - e x‖ ^ 2 := hlt.trans_le hle
    linarith
  have hgx' : ‖f k x - e x‖ ≤ ε / 3 := by
    have := Real.sqrt_le_sqrt hgx
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at this
  have h1 := hinc k t x hx.1 hx.2
  have h2 : ‖e x - e t‖ < ε / 3 := hδe t x (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
  rw [dist_eq_norm]
  calc ‖e t - f k t‖ ≤ ‖e t - e x‖ + ‖e x - f k t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖e t - e x‖ + (‖e x - f k x‖ + ‖f k x - f k t‖) := by
        gcongr; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by
        linarith [norm_sub_rev (e t) (e x), norm_sub_rev (e x) (f k x), norm_sub_rev (f k x) (f k t)]

/-- Eventually `1`-periodic `C¹` loops `f k` whose derivatives are eventually bounded in
`L²(0, 1)` and which converge in `L²(0, 1)` to a continuous `1`-periodic loop `e` converge to `e`
uniformly on `ℝ`. -/
theorem tendstoUniformly_of_tendsto_intervalIntegral_sq_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f f' : ℕ → ℝ → E) (hf : ∀ᶠ k in atTop, ∀ t, HasDerivAt (f k) (f' k t) t)
    (hf' : ∀ᶠ k in atTop, Continuous (f' k)) (hper : ∀ᶠ k in atTop, Function.Periodic (f k) 1)
    (e : ℝ → E) (he : Continuous e) (hep : Function.Periodic e 1)
    (M : ℝ) (hM : ∀ᶠ k in atTop, ∫ t in (0:ℝ)..1, ‖f' k t‖ ^ 2 ≤ M)
    (hL2 : Tendsto (fun k => ∫ t in (0:ℝ)..1, ‖f k t - e t‖ ^ 2) atTop (𝓝 0)) :
    TendstoUniformly f e atTop := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (((hf.and hf').and hper).and hM)
  have hg := tendstoUniformly_of_tendsto_intervalIntegral_sq_of_forall
    (fun k => f (k + N)) (fun k => f' (k + N)) (fun k => (hN (k + N) (by omega)).1.1.1)
    (fun k => (hN (k + N) (by omega)).1.1.2) (fun k => (hN (k + N) (by omega)).1.2) e he hep M
    (fun k => (hN (k + N) (by omega)).2) (hL2.comp (tendsto_add_atTop_nat N))
  rw [Metric.tendstoUniformly_iff] at hg ⊢
  intro ε hε
  filter_upwards [(tendsto_sub_atTop_nat N).eventually (hg ε hε), eventually_ge_atTop N]
    with k hk hkN
  simpa [Nat.sub_add_cancel hkN] using hk

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f f' : ℕ → ℝ → E) (hf : ∀ᶠ k in atTop, ∀ t, HasDerivAt (f k) (f' k t) t)
    (hf' : ∀ᶠ k in atTop, Continuous (f' k)) (hper : ∀ᶠ k in atTop, Function.Periodic (f k) 1)
    (e : ℝ → E) (he : Continuous e) (hep : Function.Periodic e 1)
    (M : ℝ) (hM : ∀ᶠ k in atTop, ∫ t in (0:ℝ)..1, ‖f' k t‖ ^ 2 ≤ M)
    (hL2 : Tendsto (fun k => ∫ t in (0:ℝ)..1, ‖f k t - e t‖ ^ 2) atTop (𝓝 0)) :
    TendstoUniformly f e atTop :=
  FiniteEnergyPlane.tendstoUniformly_of_tendsto_intervalIntegral_sq_aux f f' hf hf' hper e he hep M hM hL2
