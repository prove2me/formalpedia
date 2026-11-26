-- Prove2me | solution 1 for FiniteEnergyPlane.ofReal_loopAction_le_diskArea
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T20:45:55.358092+00:00
-- url     : https://prove2.me/submissions/dda115d8-2c05-4783-8aa6-9741720db176
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FiniteEnergyPlane_SpanningDisk
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_aCoord_neg_and_boundary_pos_of_isDiskCurve
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_of_apply_eq_of_injective_fderiv
import Theorems.Thm_FiniteEnergyPlane_ofReal_integral_liouville_le_diskArea

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

namespace FiniteEnergyPlane

theorem old_proj_of_mem {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (x : V n) (hx : H x = 1) : proj H x = x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hH.2.2 0 hx
    simp at this
  obtain ⟨r, ⟨hr0, hr1⟩, hru⟩ := hH.2.1 x hx0
  have e1 : ∃ r : ℝ, 0 < r ∧ H (r • x) = 1 := ⟨r, hr0, hr1⟩
  have h1 : scaleToS H x = 1 := by
    unfold scaleToS
    rw [dif_pos e1]
    have := hru _ (Classical.choose_spec e1)
    have h1' := hru 1 ⟨one_pos, by rw [one_smul]; exact hx⟩
    rw [this, h1']
  simp [proj, h1]

theorem old_ccwLoop_contDiff : ContDiff ℝ ∞ (ccwLoop 1) := by
  unfold ccwLoop
  have : ContDiff ℝ ∞ (fun t : ℝ => ((2 * π * t : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
  exact contDiff_const.mul ((this.mul contDiff_const).cexp)

theorem old_norm_ccwLoop (t : ℝ) : ‖ccwLoop 1 t‖ = 1 := by
  simp only [ccwLoop]
  rw [Complex.ofReal_one, one_mul, Complex.norm_exp_ofReal_mul_I]

theorem ofReal_loopAction_le_diskArea_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (e : ℂ → V 1) (z₀ : ℂ) (he : IsSpecialSpanningDisk H P e z₀)
    (Γ : Finset ℂ) (u : ℂ → V 1) (hu : IsDiskCurve H J e z₀ (closedBall 0 1) Γ u)
    (hΓ : ∀ z ∈ Γ, Tendsto (fun w => aCoord H (u w)) (𝓝[≠] z) atBot) :
    ENNReal.ofReal (loopAction H u (ccwLoop 1)) ≤ diskArea e := by
  obtain ⟨⟨ρ, hemb, hz₀, hzero, -⟩, -, hS, hL, -, -⟩ := id he
  obtain ⟨hesm, hρ, hmaps, -, hfinj⟩ := id hemb
  obtain ⟨hΓ₁, hsm, -, -, -, c, hcbd, hw⟩ := id hu
  have hpos := (aCoord_neg_and_boundary_pos_of_isDiskCurve H hH J hJ e ρ hemb z₀
    (closedBall 0 1) (closedBall_subset_ball hρ) Γ u hu hΓ).2.1
  -- the boundary loop
  set w : ℝ → V 1 := fun t => u (ccwLoop 1 t) with hwdef
  have hwsm : ContDiff ℝ ∞ w := by
    refine hsm.comp_contDiff old_ccwLoop_contDiff fun t => ⟨?_, ?_⟩
    · simp [old_norm_ccwLoop]
    · intro hm
      have := hΓ₁ hm
      simp [old_norm_ccwLoop] at this
  have hcρ : ∀ t, c t ∈ ball (0 : ℂ) ρ := fun t =>
    mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 (hcbd t).1) hρ)
  have hcont : Continuous c := by
    have : Continuous fun t => (c t - z₀) + z₀ := hw.1.add continuous_const
    simpa using this
  have hweq : w = fun t => e (c t) := funext fun t => (hcbd t).2
  -- smoothness of `c`
  have hc1 : ContDiff ℝ 1 c := by
    have := contDiffOn_of_apply_eq_of_injective_fderiv (E := V 1) (l := 1) le_rfl isOpen_univ
      (F := fun p : ℝ × ℂ => e p.2) (g := w) (ρ := c)
      ((hesm.of_le (by exact_mod_cast le_top)).comp contDiff_snd).contDiffOn
      (hwsm.of_le (by exact_mod_cast le_top)).contDiffOn hcont.continuousOn
      (fun t _ => (hcbd t).2.symm) (fun t _ => hfinj _ (hcρ t))
    exact contDiffOn_univ.1 this
  have hderiv : ∀ t, deriv w t = fderiv ℝ e (c t) (deriv c t) := by
    intro t
    rw [hweq]
    have h1 : HasDerivAt c (deriv c t) t :=
      ((hc1.differentiable one_ne_zero) t).hasDerivAt
    have h2 : HasFDerivAt e (fderiv ℝ e (c t)) (c t) :=
      ((hesm.differentiable (by simp)) (c t)).hasFDerivAt
    exact (h2.comp_hasDerivAt t h1).deriv
  -- the action of the boundary loop
  have hloop : loopInS H u (ccwLoop 1) = w := by
    funext t
    simp only [loopInS, hwdef]
    rw [(hcbd t).2]
    exact old_proj_of_mem H hH _ (hmaps (hcρ t))
  have hact : loopAction H u (ccwLoop 1) =
      ∫ t in (0 : ℝ)..1, liouville (e (c t)) (fderiv ℝ e (c t) (deriv c t)) := by
    unfold loopAction
    rw [hloop]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hwdef, (hcbd t).2] at *
    rw [← hderiv t]
  have htr : ∀ t, liouville (e (c t)) (fderiv ℝ e (c t) (deriv c t)) ≠ 0 := by
    intro t
    have := hpos t
    rw [← hderiv t]
    simp only [hwdef] at this ⊢
    rw [(hcbd t).2] at this
    exact this.ne'
  rw [hact]
  exact ofReal_integral_liouville_le_diskArea e hesm z₀ hz₀
    ((hzero z₀ (ball_subset_ball hρ.le hz₀)).2 rfl) hL hS c hc1 (fun t => (hcbd t).1) hw htr

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (e : ℂ → V 1) (z₀ : ℂ) (he : IsSpecialSpanningDisk H P e z₀)
    (Γ : Finset ℂ) (u : ℂ → V 1) (hu : IsDiskCurve H J e z₀ (closedBall 0 1) Γ u)
    (hΓ : ∀ z ∈ Γ, Tendsto (fun w => aCoord H (u w)) (𝓝[≠] z) atBot) :
    ENNReal.ofReal (loopAction H u (ccwLoop 1)) ≤ diskArea e :=
  ofReal_loopAction_le_diskArea_aux H hH J hJ P e z₀ he Γ u hu hΓ
