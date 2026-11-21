-- Prove2me | solution 1 for FiniteEnergyPlane.exists_halfCyl_solution_of_complexGraph
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T15:37:56.567866+00:00
-- url     : https://prove2.me/submissions/2d0ea97b-3066-41b9-b9e7-336f00afdf24

import Definitions.Def_FiniteEnergyPlane_Tube
import Theorems.Thm_FiniteEnergyPlane_GraphEnd_halfCyl_equation_of_graph
import Theorems.Thm_FiniteEnergyPlane_GraphEnd_isExpAsymptoticTo_Sf



/-! B3E sketch: assembly over the published children P and A. -/

namespace FiniteEnergyPlane.B3ES

open FiniteEnergyPlane.GraphEnd
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Real

noncomputable section

lemma cylInf_log_arg {z : ℂ} (hz : z ≠ 0) :
    cylInf (Real.log ‖z‖ / (2 * π)) (Complex.arg z / (2 * π)) = z := by
  unfold cylInf ccwLoop
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hπ, Real.exp_log (norm_pos_iff.2 hz), mul_div_cancel₀ _ hπ]
  exact Complex.norm_mul_exp_arg_mul_I z

/-- A continuous map into `ball 0 ρ` decaying along the end is bounded by some `r₁ < ρ`. -/
lemma exists_norm_le_of_expDecay (f : ℂ → ℂ) (hf : Continuous f) (ρ : ℝ)
    (hfρ : ∀ x, f x ∈ ball (0 : ℂ) ρ) (δ : ℝ) (hδ : δ < 0)
    (has : ExpDecayCInfty (fun p : ℝ × ℝ => f (cylInf p.1 p.2)) (-δ)) :
    ∃ r₁ : ℝ, 0 ≤ r₁ ∧ r₁ < ρ ∧ ∀ x, ‖f x‖ ≤ r₁ := by
  have hρ : 0 < ρ := by
    have := hfρ 0; rw [mem_ball_zero_iff] at this; exact (norm_nonneg _).trans_lt this
  obtain ⟨C, s₁, hC⟩ := has.2 0
  have ht : Tendsto (fun s : ℝ => C * Real.exp (δ * s)) atTop (𝓝 0) := by
    have : Tendsto (fun s : ℝ => Real.exp (δ * s)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hδ)
    simpa using this.const_mul C
  obtain ⟨s₂, hs₂⟩ := eventually_atTop.1 ((ht.eventually (gt_mem_nhds (half_pos hρ))).and
    (eventually_ge_atTop s₁))
  set R := Real.exp (2 * π * s₂)
  obtain ⟨z₀, -, hz₀⟩ := (isCompact_closedBall (0 : ℂ) R).exists_isMaxOn
    (nonempty_closedBall.2 (Real.exp_pos _).le) (hf.norm.continuousOn)
  refine ⟨max (ρ / 2) ‖f z₀‖, le_max_of_le_left (by positivity),
    max_lt (half_lt_self hρ) (mem_ball_zero_iff.1 (hfρ z₀)), fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ R
  · exact le_max_of_le_right (hz₀ (mem_closedBall_zero_iff.2 hx))
  · push_neg at hx
    have hx0 : x ≠ 0 := by
      intro h; rw [h, norm_zero] at hx; exact absurd hx (not_lt.2 (Real.exp_pos _).le)
    have hs : s₂ < Real.log ‖x‖ / (2 * π) := by
      rw [lt_div_iff₀ (by positivity), mul_comm, ← Real.lt_log_iff_exp_lt (norm_pos_iff.2 hx0)]
        at *
      exact hx
    have hb := hC _ ((hs₂ _ hs.le).2) (Complex.arg x / (2 * π))
    rw [norm_iteratedFDeriv_zero] at hb
    simp only [cylInf_log_arg hx0] at hb
    refine le_max_of_le_left (hb.trans ?_)
    have := (hs₂ _ hs.le).1
    rw [neg_mul, neg_neg] at *
    exact this.le

theorem exists_halfCyl_solution (ρ b : ℝ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ : ℝ) (hδ : δ < 0)
    (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgρ : ∀ x, g x ∈ ball (0 : ℂ) ρ)
    (hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1)
    (hgas : ExpDecayCInfty (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) (-δ))
    (ψ v : ℂ → ℂ) (κ : ℂ) (b' : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hv : ContDiff ℝ ∞ v) (hvρ : ∀ z, v z ∈ ball (0 : ℂ) ρ)
    (hhol : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z))
    (hκ : κ ≠ 0) (hb' : 0 < b')
    (hψas : ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b')
    (hvas : ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ)) :
    ∃ (P : ℂ → ℂ →L[ℝ] ℂ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat 1)
      (w : ℝ × ℝ → CauchyRiemannIndex.Vec 1) (d C : ℝ),
      (∀ z, Function.Injective (P z)) ∧
      ContDiff ℝ ∞ (fun z => P z (v z - g (ψ z))) ∧
      (∀ z₀ : ℂ, ∃ r > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ r,
        ‖fderiv ℝ (fun y => P y (v y - g (ψ y))) z 1 +
            Complex.I * fderiv ℝ (fun y => P y (v y - g (ψ y))) z Complex.I‖ ≤
          M * ‖P z (v z - g (ψ z))‖) ∧
      (∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) ∧
      (∀ s t : ℝ, S (s, t + 1) = S (s, t)) ∧
      0 < d ∧ IsExpAsymptoticTo S (fun t => Sinf (t + Complex.arg κ / (2 * π))) d ∧
      IsHalfCylSolution S w ∧
      (∀ s > 0, ∀ t : ℝ, vecToC (w (s, t)) =
        P (cylInf s t) (v (cylInf s t) - g (ψ (cylInf s t)))) ∧
      ∀ s > 0, ∀ t : ℝ, ‖w (s, t)‖ ≤ C * Real.exp (δ * s) := by
  obtain ⟨rg, hrg0, hrgρ, hrg⟩ := exists_norm_le_of_expDecay g hg.continuous ρ hgρ δ hδ hgas
  obtain ⟨rv, hrv0, hrvρ, hrv⟩ := exists_norm_le_of_expDecay v hv.continuous ρ hvρ δ hδ hvas
  set r₁ := max rg rv with hr₁
  have hr₁ρ : r₁ < ρ := max_lt hrgρ hrvρ
  have hr₁0 : 0 ≤ r₁ := le_max_of_le_left hrg0
  have hgr : ∀ x, ‖g x‖ ≤ r₁ := fun x => (hrg x).trans (le_max_left _ _)
  have hvr : ∀ z, ‖v z‖ ≤ r₁ := fun z => (hrv z).trans (le_max_right _ _)
  let β : ContDiffBump (0 : ℂ) :=
    ⟨r₁ + (ρ - r₁) / 3, r₁ + 2 * (ρ - r₁) / 3, by linarith, by linarith⟩
  have hβIn : r₁ < β.rIn := by show r₁ < r₁ + (ρ - r₁) / 3; linarith
  have hβOut : β.rOut ≤ ρ := by show r₁ + 2 * (ρ - r₁) / 3 ≤ ρ; linarith
  obtain ⟨hinj, hζ, hloc, hS, hper, hsol, hvec⟩ :=
    halfCyl_equation_of_graph ρ r₁ Jbar hT.1 hT.2.1 β hβIn.le hβOut hr₁ρ g ψ v hg hψ hv hgr hvr
      hgJ hhol
  obtain ⟨hasy, C, hC⟩ := isExpAsymptoticTo_Sf ρ b hb Jbar Jinf Sinf hT δ hδ β r₁ hr₁ρ hβIn
    hβOut g hg hgr hgJ hgas ψ v κ b' hψ hv hvr hκ hb' hψas hvas
  have hm : 0 < min (min b b') (-δ) := lt_min (lt_min hb hb') (by linarith)
  exact ⟨Pf Jbar β g ψ, Sf Jbar β g ψ v, wf Jbar β g ψ v, min (min b b') (-δ) / 2, C,
    hinj, hζ, hloc, hS, hper, half_pos hm, hasy _ (half_pos hm) (half_lt_self hm), hsol,
    fun s _ t => hvec s t, hC⟩

end

end FiniteEnergyPlane.B3ES

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (ρ b : ℝ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ : ℝ) (hδ : δ < 0)
    (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgρ : ∀ x, g x ∈ ball (0 : ℂ) ρ)
    (hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1)
    (hgas : ExpDecayCInfty (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) (-δ))
    (ψ v : ℂ → ℂ) (κ : ℂ) (b' : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hv : ContDiff ℝ ∞ v) (hvρ : ∀ z, v z ∈ ball (0 : ℂ) ρ)
    (hhol : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z))
    (hκ : κ ≠ 0) (hb' : 0 < b')
    (hψas : ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b')
    (hvas : ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ)) :
    ∃ (P : ℂ → ℂ →L[ℝ] ℂ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat 1)
      (w : ℝ × ℝ → CauchyRiemannIndex.Vec 1) (d C : ℝ),
      (∀ z, Function.Injective (P z)) ∧
      ContDiff ℝ ∞ (fun z => P z (v z - g (ψ z))) ∧
      (∀ z₀ : ℂ, ∃ r > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ r,
        ‖fderiv ℝ (fun y => P y (v y - g (ψ y))) z 1 +
            Complex.I * fderiv ℝ (fun y => P y (v y - g (ψ y))) z Complex.I‖ ≤
          M * ‖P z (v z - g (ψ z))‖) ∧
      (∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) ∧
      (∀ s t : ℝ, S (s, t + 1) = S (s, t)) ∧
      0 < d ∧ IsExpAsymptoticTo S (fun t => Sinf (t + Complex.arg κ / (2 * π))) d ∧
      IsHalfCylSolution S w ∧
      (∀ s > 0, ∀ t : ℝ, vecToC (w (s, t)) = P (cylInf s t) (v (cylInf s t) - g (ψ (cylInf s t)))) ∧
      ∀ s > 0, ∀ t : ℝ, ‖w (s, t)‖ ≤ C * Real.exp (δ * s) :=
  FiniteEnergyPlane.B3ES.exists_halfCyl_solution ρ b hb Jbar Jinf Sinf hT δ hδ g hg hgρ hgJ hgas ψ v κ b' hψ hv hvρ hhol hκ hb' hψas hvas
