-- Prove2me | solution 1 for ContinuityEqWiki.integral_form_iff_differential_form
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:21:51.904458+00:00
-- url     : https://prove2.me/submissions/64412a61-f210-4d0e-ac59-66d9a8d844c1

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

open ContinuityEqWiki

namespace LUHelpIF

open MeasureTheory

theorem timeDeriv_eq (Φ : ℝ × Space → ℝ) (t : ℝ) (x : Space)
    (h : DifferentiableAt ℝ Φ (t, x)) :
    deriv (fun s => Φ (s, x)) t = fderiv ℝ Φ (t, x) ((1 : ℝ), (0 : Space)) := by
  have h1 : HasDerivAt (Φ ∘ fun s => (s, x)) (fderiv ℝ Φ (t, x) ((1 : ℝ), (0 : Space))) t :=
    h.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  exact h1.deriv

theorem div_eq (F : Space → Space) (hF : ContDiff ℝ 1 F) (x : Space) :
    div F x = ∑ i, fderiv ℝ F x (Pi.single i 1) i := by
  unfold div
  apply Finset.sum_congr rfl
  intro i _
  unfold partialDeriv
  have h := (hF.differentiable one_ne_zero x).hasFDerivAt
  have h2 : HasFDerivAt ((fun v : Space => v i) ∘ F)
      ((ContinuousLinearMap.proj i).comp (fderiv ℝ F x)) x :=
    (hasFDerivAt_apply i (F x)).comp x h
  rw [show (fun y => F y i) = (fun v : Space => v i) ∘ F from rfl, h2.fderiv]
  rfl

theorem div_cont (F : Space → Space) (hF : ContDiff ℝ 1 F) : Continuous (div F) := by
  have : div F = fun x => ∑ i, fderiv ℝ F x (Pi.single i 1) i := funext (div_eq F hF)
  rw [this]
  have hcont : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  apply continuous_finset_sum
  intro i _
  exact (continuous_apply i).comp (hcont.clm_apply continuous_const)

theorem flux_eq (F : Space → Space) (hF : ContDiff ℝ 1 F) (a b : Space) (hab : a ≤ b) :
    boxFlux F a b = ∫ x in Set.Icc a b, div F x := by
  rw [funext (div_eq F hF)]
  unfold boxFlux
  have hcont : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  refine (MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable a b hab F (fderiv ℝ F) ∅
    Set.countable_empty hF.continuous.continuousOn ?_ ?_).symm
  · intro x _
    exact (hF.differentiable one_ne_zero x).hasFDerivAt
  · apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply Continuous.continuousOn
    apply continuous_finset_sum
    intro i _
    exact (continuous_apply i).comp (hcont.clm_apply continuous_const)

theorem amount_deriv (ρ : ℝ → Space → ℝ) (hρ : ContDiff ℝ 1 (Function.uncurry ρ))
    (a b : Space) (t : ℝ) :
    deriv (amountInBox ρ a b) t = ∫ x in Set.Icc a b, timeDeriv ρ t x := by
  have hd : Differentiable ℝ (Function.uncurry ρ) := hρ.differentiable one_ne_zero
  set G : ℝ × Space → ℝ := fun q => fderiv ℝ (Function.uncurry ρ) q ((1 : ℝ), (0 : Space))
  have hG : Continuous G := (hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hTD : ∀ s y, timeDeriv ρ s y = G (s, y) := fun s y =>
    timeDeriv_eq (Function.uncurry ρ) s y (hd _)
  have hK : IsCompact (Set.Icc (t - 1) (t + 1) ×ˢ Set.Icc a b) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  have hρs : ∀ s, Continuous (ρ s) := fun s =>
    hρ.continuous.comp (continuous_const.prodMk continuous_id)
  have hGs : ∀ s, Continuous (fun y => G (s, y)) := fun s =>
    hG.comp (continuous_const.prodMk continuous_id)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Icc a b)) (F := fun s y => ρ s y)
    (F' := fun s y => timeDeriv ρ s y) (x₀ := t) (bound := fun _ => M)
    (s := Metric.ball t 1) (Metric.ball_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun s => (hρs s).aestronglyMeasurable)
    ((hρs t).continuousOn.integrableOn_compact isCompact_Icc)
    (by simp_rw [hTD]; exact (hGs t).aestronglyMeasurable)
    (by
      refine (ae_restrict_of_forall_mem measurableSet_Icc ?_)
      intro y hy s hs
      rw [hTD]
      apply hM
      refine ⟨?_, hy⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
      constructor <;> linarith)
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall fun y s _ =>
      (((hd _).comp s ((differentiableAt_id).prodMk (differentiableAt_const y))) :
        DifferentiableAt ℝ (fun r => ρ r y) s).hasDerivAt)
  exact key.2.deriv

theorem pos_box (f : Space → ℝ) (hf : Continuous f) (x : Space) (hx : 0 < f x) :
    ∃ a b : Space, (∀ i, a i < b i) ∧ 0 < ∫ y in Set.Icc a b, f y := by
  have hev : ∀ᶠ y in nhds x, f x / 2 < f y :=
    hf.continuousAt.eventually (lt_mem_nhds (by linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨fun i => x i - ε / 2, fun i => x i + ε / 2, fun i => by linarith, ?_⟩
  have hsub : ∀ y ∈ Set.Icc (fun i => x i - ε / 2) (fun i => x i + ε / 2), f x / 2 ≤ f y := by
    intro y hy
    apply le_of_lt
    apply hball
    rw [dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq, abs_lt]
    have h1 := hy.1 i
    have h2 := hy.2 i
    simp only at h1 h2
    constructor <;> linarith
  have hvol : 0 < volume.real (Set.Icc (fun i => x i - ε / 2) (fun i => x i + ε / 2)) := by
    rw [measureReal_def, Real.volume_Icc_pi]
    apply ENNReal.toReal_pos
    · rw [Finset.prod_ne_zero_iff]
      intro i _
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith
    · exact ENNReal.prod_ne_top (fun i _ => ENNReal.ofReal_ne_top)
  have hmono : ∫ y in Set.Icc (fun i => x i - ε / 2) (fun i => x i + ε / 2), f x / 2 ≤
      ∫ y in Set.Icc (fun i => x i - ε / 2) (fun i => x i + ε / 2), f y := by
    apply setIntegral_mono_on
    · exact continuous_const.continuousOn.integrableOn_compact isCompact_Icc
    · exact hf.continuousOn.integrableOn_compact isCompact_Icc
    · exact measurableSet_Icc
    · exact hsub
  rw [setIntegral_const, smul_eq_mul] at hmono
  have : 0 < volume.real (Set.Icc (fun i => x i - ε / 2) (fun i => x i + ε / 2)) * (f x / 2) :=
    mul_pos hvol (by linarith)
  linarith

theorem zero_of_box (f : Space → ℝ) (hf : Continuous f)
    (h : ∀ a b : Space, (∀ i, a i < b i) → ∫ y in Set.Icc a b, f y = 0) (x : Space) :
    f x = 0 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨a, b, hab, hpos⟩ := pos_box (fun y => -f y) hf.neg x (by linarith)
    rw [integral_neg, h a b hab] at hpos
    simp at hpos
  · obtain ⟨a, b, hab, hpos⟩ := pos_box f hf x hgt
    rw [h a b hab] at hpos
    exact lt_irrefl _ hpos

end LUHelpIF

open LUHelpIF MeasureTheory in
theorem solution
    (ρ : ℝ → Space → ℝ) (j : ℝ → Space → Space) (σ : ℝ → Space → ℝ)
    (hρ : ContDiff ℝ 1 (Function.uncurry ρ)) (hj : ContDiff ℝ 1 (Function.uncurry j))
    (hσ : Continuous (Function.uncurry σ)) :
    IntegralForm ρ j σ ↔ DifferentialForm ρ j σ := by
  have hjt : ∀ t, ContDiff ℝ 1 (j t) := fun t =>
    hj.comp (contDiff_const.prodMk contDiff_id)
  have hσt : ∀ t, Continuous (σ t) := fun t =>
    hσ.comp (continuous_const.prodMk continuous_id)
  have hd : Differentiable ℝ (Function.uncurry ρ) := hρ.differentiable one_ne_zero
  have hTDc : ∀ t, Continuous (fun y => timeDeriv ρ t y) := by
    intro t
    have : (fun y => timeDeriv ρ t y) =
        fun y => fderiv ℝ (Function.uncurry ρ) (t, y) ((1 : ℝ), (0 : Space)) :=
      funext fun y => timeDeriv_eq (Function.uncurry ρ) t y (hd _)
    rw [this]
    exact ((hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
      (continuous_const.prodMk continuous_id)
  have hint : ∀ (f : Space → ℝ), Continuous f → ∀ a b : Space,
      IntegrableOn f (Set.Icc a b) := fun f hf a b =>
    hf.continuousOn.integrableOn_compact isCompact_Icc
  -- integral identity on boxes
  have hbox : ∀ a b : Space, (∀ i, a i < b i) → ∀ t,
      deriv (amountInBox ρ a b) t + boxFlux (j t) a b - generationInBox σ a b t =
        ∫ y in Set.Icc a b, (timeDeriv ρ t y + div (j t) y - σ t y) := by
    intro a b hab t
    rw [amount_deriv ρ hρ, flux_eq (j t) (hjt t) a b (fun i => (hab i).le)]
    unfold generationInBox
    rw [integral_sub, integral_add]
    · exact hint _ (hTDc t) a b
    · exact hint _ (div_cont _ (hjt t)) a b
    · exact (hint _ (hTDc t) a b).add (hint _ (div_cont _ (hjt t)) a b)
    · exact hint _ (hσt t) a b
  constructor
  · intro hI t x
    have hc : Continuous (fun y => timeDeriv ρ t y + div (j t) y - σ t y) :=
      ((hTDc t).add (div_cont _ (hjt t))).sub (hσt t)
    have := zero_of_box _ hc (fun a b hab => by rw [← hbox a b hab t, hI a b hab t, sub_self]) x
    linarith
  · intro hD a b hab t
    have h := hbox a b hab t
    have h0 : ∫ y in Set.Icc a b, (timeDeriv ρ t y + div (j t) y - σ t y) = 0 := by
      have : (fun y => timeDeriv ρ t y + div (j t) y - σ t y) = fun _ => 0 := by
        funext y; rw [hD t y]; ring
      rw [this, integral_zero]
    linarith
