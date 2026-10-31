-- Prove2me | solution 1 for FiniteEnergyPlane.exists_tendsto_of_dbar_expDecay
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T11:04:56.406476+00:00
-- url     : https://prove2.me/submissions/63ea7644-0ab3-49a0-a4ea-6979df5784ff

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib

open scoped Topology ContDiff
open Set Filter MeasureTheory

/-! Convergence of `f + i g` on a half-cylinder from an exponentially small Cauchy–Riemann defect
(child M of `exists_tendsto_cylEnd_of_isNondegenerate`). Slice calculus adapted from `HCL_base`. -/


namespace FiniteEnergyPlane.HWZM

/-- `∂ₛu`. -/
noncomputable def pS (u : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ := fderiv ℝ u x (1, 0)
/-- `∂ₜu`. -/
noncomputable def pT (u : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ := fderiv ℝ u x (0, 1)

lemma isOpen_U (s₀ : ℝ) : IsOpen (Ioi s₀ ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ

lemma cont_slice {w : ℝ × ℝ → ℝ} {s₀ s : ℝ} (hw : ContinuousOn w (Ioi s₀ ×ˢ univ))
    (hs : s₀ < s) : Continuous fun t => w (s, t) :=
  hw.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hs, trivial⟩

section C1
variable {u : ℝ × ℝ → ℝ} {s₀ : ℝ} (hu : ContDiffOn ℝ 1 u (Ioi s₀ ×ˢ univ))
include hu

lemma diffAt {x : ℝ × ℝ} (hx : x ∈ Ioi s₀ ×ˢ (univ : Set ℝ)) : DifferentiableAt ℝ u x :=
  (hu.contDiffAt ((isOpen_U s₀).mem_nhds hx)).differentiableAt (by simp)

lemma cont_pS : ContinuousOn (pS u) (Ioi s₀ ×ˢ univ) :=
  (hu.continuousOn_fderiv_of_isOpen (isOpen_U s₀) le_rfl).clm_apply continuousOn_const

lemma cont_pT : ContinuousOn (pT u) (Ioi s₀ ×ˢ univ) :=
  (hu.continuousOn_fderiv_of_isOpen (isOpen_U s₀) le_rfl).clm_apply continuousOn_const

lemma hasDerivAt_s {s t : ℝ} (hs : s₀ < s) :
    HasDerivAt (fun σ => u (σ, t)) (pS u (s, t)) s :=
  (diffAt hu (x := (s, t)) ⟨hs, trivial⟩).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))

lemma hasDerivAt_t {s t : ℝ} (hs : s₀ < s) :
    HasDerivAt (fun τ => u (s, τ)) (pT u (s, t)) t :=
  (diffAt hu (x := (s, t)) ⟨hs, trivial⟩).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))

/-- the `t`-derivative of a periodic slice integrates to zero -/
lemma integral_pT_eq_zero (hp : ∀ s > s₀, ∀ t : ℝ, u (s, t + 1) = u (s, t)) {s : ℝ}
    (hs : s₀ < s) : ∫ t in (0:ℝ)..1, pT u (s, t) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_t hu hs)
    ((cont_slice (cont_pT hu) hs).intervalIntegrable _ _)]
  have := hp s hs 0
  simp only [zero_add] at this
  rw [this, sub_self]

/-- a periodic slice stays within `η` of its mean when `|∂ₜu| ≤ η` -/
lemma abs_sub_mean_le (hp : ∀ s > s₀, ∀ t : ℝ, u (s, t + 1) = u (s, t)) {s η : ℝ}
    (hs : s₀ < s) (hη : ∀ t : ℝ, |pT u (s, t)| ≤ η) (t : ℝ) :
    |u (s, t) - ∫ x in (0:ℝ)..1, u (s, x)| ≤ η := by
  have hper : Function.Periodic (fun x => u (s, x)) 1 := fun x => hp s hs x
  obtain ⟨y, hy, hyt⟩ := hper.exists_mem_Ico₀ one_pos t
  rw [show u (s, t) = u (s, y) from hyt]
  have hc := cont_slice hu.continuousOn hs
  have e : u (s, y) - ∫ x in (0:ℝ)..1, u (s, x) = ∫ x in (0:ℝ)..1, (u (s, y) - u (s, x)) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable _ _)]
    simp
  rw [e]
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη 0)
  have hpt : ∀ x ∈ Icc (0:ℝ) 1, |u (s, y) - u (s, x)| ≤ η := by
    intro x hx
    have := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun τ => u (s, τ)) (f' := fun τ => pT u (s, τ))
      (fun τ _ => (hasDerivAt_t hu hs).hasDerivWithinAt) (fun τ _ => hη τ) (mem_univ x)
      (mem_univ y)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
    have hyx : |y - x| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hy.1, hy.2, hx.1, hx.2]
    exact this.trans (by nlinarith)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1) (C := η)
    (f := fun x => u (s, y) - u (s, x)) (fun x hx => by
      rw [uIoc_of_le zero_le_one] at hx
      rw [Real.norm_eq_abs]; exact hpt x (Ioc_subset_Icc_self hx))
  simpa using this

end C1

/-- differentiation under the integral sign on `(s₀, ∞) × ℝ` -/
lemma param_deriv (F F' : ℝ × ℝ → ℝ) {s₀ : ℝ} (hF : ContinuousOn F (Ioi s₀ ×ˢ univ))
    (hF' : ContinuousOn F' (Ioi s₀ ×ˢ univ))
    (hd : ∀ σ t, s₀ < σ → HasDerivAt (fun σ => F (σ, t)) (F' (σ, t)) σ) {s : ℝ} (hs : s₀ < s) :
    HasDerivAt (fun σ => ∫ t in (0:ℝ)..1, F (σ, t)) (∫ t in (0:ℝ)..1, F' (s, t)) s := by
  set r := (s - s₀) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hK : IsCompact (Metric.closedBall s r ×ˢ Icc (0:ℝ) 1) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hKΩ : Metric.closedBall s r ×ˢ Icc (0:ℝ) 1 ⊆ Ioi s₀ ×ˢ univ := by
    rintro ⟨a, b⟩ ⟨ha, -⟩
    refine ⟨?_, trivial⟩
    rw [Metric.mem_closedBall, Real.dist_eq] at ha
    show s₀ < a
    have := neg_abs_le (a - s)
    linarith
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hF'.mono hKΩ)
  have hball : Metric.ball s r ⊆ Ioi s₀ := by
    intro a ha
    rw [Metric.mem_ball, Real.dist_eq] at ha
    show s₀ < a
    have := neg_abs_le (a - s)
    linarith
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := 1) (F := fun σ t => F (σ, t)) (F' := fun σ t => F' (σ, t)) (x₀ := s)
    (bound := fun _ => M) (Metric.ball_mem_nhds s hr0)
    ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact this.2
  · filter_upwards [Ioi_mem_nhds hs] with σ hσ
    exact (cont_slice hF hσ).aestronglyMeasurable
  · exact (cont_slice hF hs).intervalIntegrable _ _
  · exact (cont_slice hF' hs).aestronglyMeasurable
  · refine Eventually.of_forall fun t ht σ hσ => hM (σ, t) ⟨Metric.ball_subset_closedBall hσ, ?_⟩
    rw [uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  · exact Eventually.of_forall fun t _ σ hσ => hd σ t (hball hσ)

/-- a function whose derivative is bounded by `C e^{-δs}` converges -/
lemma exists_tendsto_of_abs_deriv_le {m m' : ℝ → ℝ} {s₀ C δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ s > s₀, HasDerivAt m (m' s) s)
    (hb : ∀ s > s₀, |m' s| ≤ C * Real.exp (-(δ * s))) :
    ∃ d : ℝ, Tendsto m atTop (𝓝 d) := by
  set K := C / δ with hK
  set e : ℝ → ℝ := fun s => K * Real.exp (-(δ * s)) with he
  have hde : ∀ s, HasDerivAt e (-(C * Real.exp (-(δ * s)))) s := by
    intro s
    have h1 : HasDerivAt (fun s => -(δ * s)) (-(δ * 1)) s :=
      ((hasDerivAt_id s).const_mul δ).neg
    have hδ' : δ ≠ 0 := hδ.ne'
    refine ((h1.exp).const_mul K).congr_deriv ?_
    simp only [hK]
    field_simp
  set D : Set ℝ := Ioi s₀ with hD
  have hDi : interior D = D := isOpen_Ioi.interior_eq
  -- `χ = m - e` is monotone, `ψ = m + e` is antitone
  have hχ : MonotoneOn (fun s => m s - e s) D := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi s₀)
      (fun s hs => ((hd s hs).sub (hde s)).continuousAt.continuousWithinAt) ?_ ?_
      (f' := fun s => m' s - -(C * Real.exp (-(δ * s))))
    · intro s hs; rw [hDi] at hs; exact ((hd s hs).sub (hde s)).hasDerivWithinAt
    · intro s hs; rw [hDi] at hs
      have := (abs_le.1 (hb s hs)).1; linarith
  have hψ : AntitoneOn (fun s => m s + e s) D := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi s₀)
      (fun s hs => ((hd s hs).add (hde s)).continuousAt.continuousWithinAt) ?_ ?_
      (f' := fun s => m' s + -(C * Real.exp (-(δ * s))))
    · intro s hs; rw [hDi] at hs; exact ((hd s hs).add (hde s)).hasDerivWithinAt
    · intro s hs; rw [hDi] at hs
      have := (abs_le.1 (hb s hs)).2; linarith
  set a := s₀ + 1 with ha
  have haD : a ∈ D := show s₀ < s₀ + 1 by linarith
  set χ' : ℝ → ℝ := fun s => m (max s a) - e (max s a) with hχ'
  have hmax : ∀ s, max s a ∈ D := fun s => show s₀ < max s a from
    lt_of_lt_of_le (show s₀ < a by linarith) (le_max_right _ _)
  have hmono : Monotone χ' := fun x y hxy =>
    hχ (hmax x) (hmax y) (max_le_max hxy le_rfl)
  have hbdd : BddAbove (range χ') := by
    refine ⟨m a + e a, ?_⟩
    rintro _ ⟨x, rfl⟩
    have h1 : e (max x a) ≥ 0 ∨ e (max x a) < 0 := le_or_gt 0 _
    have hψa := hψ haD (hmax x) (le_max_right x a)
    have hepos : 0 ≤ e (max x a) := by
      have hC : 0 ≤ C := by
        have := (abs_nonneg _).trans (hb a haD)
        exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
      exact mul_nonneg (div_nonneg hC hδ.le) (Real.exp_pos _).le
    simp only [hχ']
    linarith
  have hlim := tendsto_atTop_ciSup hmono hbdd
  have he0 : Tendsto e atTop (𝓝 0) := by
    have : Tendsto (fun s => -(δ * s)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hδ)
    simpa [he] using (Real.tendsto_exp_atBot.comp this).const_mul K
  refine ⟨⨆ i, χ' i, ?_⟩
  have hsum := hlim.add he0
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop a] with s hs
  simp only [hχ', max_eq_left hs]
  ring

theorem exists_tendsto_of_dbar_expDecay_aux (f g : ℝ × ℝ → ℝ) (s₀ : ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.Ioi s₀ ×ˢ Set.univ))
    (hg : ContDiffOn ℝ 1 g (Set.Ioi s₀ ×ˢ Set.univ))
    (hper : ∀ s > s₀, ∀ t : ℝ, f (s, t + 1) = f (s, t) ∧ g (s, t + 1) = g (s, t))
    (ht : ∀ η > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      |fderiv ℝ f (s, t) (0, 1)| ≤ η ∧ |fderiv ℝ g (s, t) (0, 1)| ≤ η)
    (δ C : ℝ) (hδ : 0 < δ)
    (hdbar : ∀ s > s₀, ∀ t : ℝ,
      |fderiv ℝ f (s, t) (1, 0) - fderiv ℝ g (s, t) (0, 1)| +
        |fderiv ℝ f (s, t) (0, 1) + fderiv ℝ g (s, t) (1, 0)| ≤ C * Real.exp (-(δ * s))) :
    ∃ d c : ℝ, TendstoZeroUnif (fun p : ℝ × ℝ => f p - d) ∧
      TendstoZeroUnif (fun p : ℝ × ℝ => g p - c) := by
  have hpf : ∀ s > s₀, ∀ t : ℝ, f (s, t + 1) = f (s, t) := fun s hs t => (hper s hs t).1
  have hpg : ∀ s > s₀, ∀ t : ℝ, g (s, t + 1) = g (s, t) := fun s hs t => (hper s hs t).2
  -- the slice means converge
  have hmean : ∀ (u v : ℝ × ℝ → ℝ) (κ : ℝ), ContDiffOn ℝ 1 u (Ioi s₀ ×ˢ univ) →
      ContDiffOn ℝ 1 v (Ioi s₀ ×ˢ univ) → (∀ s > s₀, ∀ t : ℝ, v (s, t + 1) = v (s, t)) →
      (∀ s > s₀, ∀ t : ℝ, |pS u (s, t) + κ * pT v (s, t)| ≤ C * Real.exp (-(δ * s))) →
      ∃ d : ℝ, Tendsto (fun s => ∫ t in (0:ℝ)..1, u (s, t)) atTop (𝓝 d) := by
    intro u v κ hu hv hpv hb
    refine exists_tendsto_of_abs_deriv_le (s₀ := s₀) (C := C) hδ
      (m' := fun s => ∫ t in (0:ℝ)..1, pS u (s, t))
      (fun s hs => param_deriv u (pS u) hu.continuousOn (cont_pS hu)
        (fun σ t hσ => hasDerivAt_s hu hσ) hs) ?_
    intro s hs
    show |∫ t in (0:ℝ)..1, pS u (s, t)| ≤ _
    have hval : ∫ t in (0:ℝ)..1, pS u (s, t) =
        ∫ t in (0:ℝ)..1, (pS u (s, t) + κ * pT v (s, t)) := by
      rw [intervalIntegral.integral_add ((cont_slice (cont_pS hu) hs).intervalIntegrable _ _)
        (((cont_slice (cont_pT hv) hs).intervalIntegrable _ _).const_mul κ),
        intervalIntegral.integral_const_mul, integral_pT_eq_zero hv hpv hs, mul_zero, add_zero]
    rw [hval]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (C := C * Real.exp (-(δ * s))) (f := fun t => pS u (s, t) + κ * pT v (s, t))
      (fun t _ => by rw [Real.norm_eq_abs]; exact hb s hs t)
    simpa using this
  obtain ⟨d, hd⟩ := hmean f g (-1) hf hg hpg (fun s hs t => by
    have := hdbar s hs t
    have h0 := abs_nonneg (fderiv ℝ f (s, t) (0, 1) + fderiv ℝ g (s, t) (1, 0))
    simp only [pS, pT]
    rw [show fderiv ℝ f (s, t) (1, 0) + -1 * fderiv ℝ g (s, t) (0, 1) =
      fderiv ℝ f (s, t) (1, 0) - fderiv ℝ g (s, t) (0, 1) by ring]
    linarith)
  obtain ⟨c, hc⟩ := hmean g f 1 hg hf hpf (fun s hs t => by
    have := hdbar s hs t
    have h0 := abs_nonneg (fderiv ℝ f (s, t) (1, 0) - fderiv ℝ g (s, t) (0, 1))
    simp only [pS, pT]
    rw [show fderiv ℝ g (s, t) (1, 0) + 1 * fderiv ℝ f (s, t) (0, 1) =
      fderiv ℝ f (s, t) (0, 1) + fderiv ℝ g (s, t) (1, 0) by ring]
    linarith)
  -- each slice stays close to its mean
  have hconv : ∀ (u : ℝ × ℝ → ℝ) (d : ℝ), ContDiffOn ℝ 1 u (Ioi s₀ ×ˢ univ) →
      (∀ s > s₀, ∀ t : ℝ, u (s, t + 1) = u (s, t)) →
      (∀ η > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, |pT u (s, t)| ≤ η) →
      Tendsto (fun s => ∫ t in (0:ℝ)..1, u (s, t)) atTop (𝓝 d) →
      TendstoZeroUnif (fun p : ℝ × ℝ => u p - d) := by
    intro u d hu hpu htu hdu η hη
    obtain ⟨s₁, hs₁⟩ := htu (η / 2) (by linarith)
    obtain ⟨s₂, hs₂⟩ := (Metric.tendsto_atTop.1 hdu) (η / 2) (by linarith)
    refine ⟨max (max s₁ s₂) (s₀ + 1), fun s hs t => ?_⟩
    have h1 : s₁ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
    have h2 : s₂ ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
    have h0 : s₀ < s := lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) hs)
    have e1 := abs_sub_mean_le hu hpu h0 (fun t => hs₁ s h1 t) t
    have e2 := hs₂ s h2
    rw [Real.dist_eq] at e2
    rw [Real.norm_eq_abs]
    calc |u (s, t) - d| = |(u (s, t) - ∫ x in (0:ℝ)..1, u (s, x)) +
          ((∫ x in (0:ℝ)..1, u (s, x)) - d)| := by ring_nf
      _ ≤ |u (s, t) - ∫ x in (0:ℝ)..1, u (s, x)| + |(∫ x in (0:ℝ)..1, u (s, x)) - d| :=
          abs_add_le _ _
      _ ≤ η := by linarith
  refine ⟨d, c, hconv f d hf hpf (fun η hη => ?_) hd, hconv g c hg hpg (fun η hη => ?_) hc⟩
  · obtain ⟨s₁, hs₁⟩ := ht η hη; exact ⟨s₁, fun s hs t => (hs₁ s hs t).1⟩
  · obtain ⟨s₁, hs₁⟩ := ht η hη; exact ⟨s₁, fun s hs t => (hs₁ s hs t).2⟩

end FiniteEnergyPlane.HWZM

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (f g : ℝ × ℝ → ℝ) (s₀ : ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.Ioi s₀ ×ˢ Set.univ))
    (hg : ContDiffOn ℝ 1 g (Set.Ioi s₀ ×ˢ Set.univ))
    (hper : ∀ s > s₀, ∀ t : ℝ, f (s, t + 1) = f (s, t) ∧ g (s, t + 1) = g (s, t))
    (ht : ∀ η > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      |fderiv ℝ f (s, t) (0, 1)| ≤ η ∧ |fderiv ℝ g (s, t) (0, 1)| ≤ η)
    (δ C : ℝ) (hδ : 0 < δ)
    (hdbar : ∀ s > s₀, ∀ t : ℝ,
      |fderiv ℝ f (s, t) (1, 0) - fderiv ℝ g (s, t) (0, 1)| +
        |fderiv ℝ f (s, t) (0, 1) + fderiv ℝ g (s, t) (1, 0)| ≤ C * Real.exp (-(δ * s))) :
    ∃ d c : ℝ, TendstoZeroUnif (fun p : ℝ × ℝ => f p - d) ∧
      TendstoZeroUnif (fun p : ℝ × ℝ => g p - c) :=
  HWZM.exists_tendsto_of_dbar_expDecay_aux f g s₀ hf hg hper ht δ C hδ hdbar
