-- Prove2me | solution 1 for FiniteEnergyPlane.czIndexOfPath_eq_alphaMinus_add_alphaPlus
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T16:26:52.639318+00:00
-- url     : https://prove2.me/submissions/a1c5525c-24fe-4ed6-a16b-5c990c99f366

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_exists_loopAlpha_czIndexOfPath_eq
import Theorems.Thm_FiniteEnergyPlane_hasEigenWind_iff_of_shift
import Theorems.Thm_FiniteEnergyPlane_hasEigenWind_iff_hasLoopEigenWind
import Theorems.Thm_FiniteEnergyPlane_czIndexOfPath_linearizedXiPath_eq
import Theorems.Thm_FiniteEnergyPlane_isNondegenerate_bridge
import Theorems.Thm_FiniteEnergyPlane_periodicOrbit_bridge
import Theorems.Thm_FiniteEnergyPlane_exists_unitaryXiFrame_hasXiLoopWind_iff
import Theorems.Thm_FiniteEnergyPlane_asympOp_frame_bridge
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Mathlib.Analysis.Calculus.Deriv.Shift



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem h310_main (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let toV : HryniewiczCriterion.R4 → V 1 := fun x k => x (Fin.cast (by norm_num) k)
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J →
    ∀ (P : HryniewiczCriterion.PeriodicOrbit H₀) (Q : ReebOrbit H),
      Set.range Q.x = Set.range (fun τ => toV (P.x τ)) →
      Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ) →
      Q.IsNondegenerate →
      ∃ a b : ℤ, IsAlphaMinus J Q a ∧ IsAlphaPlus J Q b ∧ (b = a ∨ b = a + 1) ∧
        ∀ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
          HryniewiczCriterion.IsLinearizedFlow H₀ P.x Y →
          HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath H₀ P Y) =
            a + b := by
  intro toV H J hJ P Q hrange hT hnd
  have hH : IsStrictlyStarShapedLevel H := (periodicOrbit_bridge H₀).1.2 hH₀
  -- start `Q` at the point `x(0)` of `P`
  obtain ⟨c, hc⟩ : ∃ c, Q.x c = toV (P.x 0) := by
    have : toV (P.x 0) ∈ Set.range Q.x := hrange ▸ ⟨0, rfl⟩
    exact this
  let Q' : ReebOrbit H :=
    { x := fun τ => Q.x (τ + c)
      T := Q.T
      T_pos := Q.T_pos
      mem := fun τ => Q.mem (τ + c)
      hasDerivAt := fun τ => HasDerivAt.comp_add_const τ c (Q.hasDerivAt (τ + c))
      periodic := fun τ => by
        show Q.x (τ + Q.T + c) = Q.x (τ + c)
        rw [add_right_comm]; exact Q.periodic (τ + c) }
  have hrange' : Set.range Q'.x = Set.range Q.x := by
    ext y
    constructor
    · rintro ⟨τ, rfl⟩; exact ⟨τ + c, rfl⟩
    · rintro ⟨τ, rfl⟩; exact ⟨τ - c, by simp [Q']⟩
  have hT' : Q'.T = Q.T := rfl
  have hshift : ∀ μ k, HasEigenWind J Q μ k ↔ HasEigenWind J Q' μ k :=
    hasEigenWind_iff_of_shift J Q Q' c hT' (fun τ => rfl)
  have hnd' : Q'.IsNondegenerate :=
    (isNondegenerate_bridge H₀ hH₀ P Q' (hrange'.trans hrange) (hT'.trans hT)).2
      ((isNondegenerate_bridge H₀ hH₀ P Q hrange hT).1 hnd)
  -- a unitary frame along `Q'` homotopic to the global frame, and `A_{Q'}` in that frame
  obtain ⟨Z, hZ, hwind⟩ := exists_unitaryXiFrame_hasXiLoopWind_iff H hH J hJ Q'
  obtain ⟨Sinf, hS, hS', hA, hndiff⟩ := (asympOp_frame_bridge H hH J hJ Q').2 Z hZ
  obtain ⟨Ψ, hΨ, -⟩ := CauchyRiemannIndex.fundamentalSolution_existsUnique 1 Sinf hS.1
  obtain ⟨a, b, ⟨⟨μa, hμa, ha⟩, ha'⟩, ⟨⟨μb, hμb, hb⟩, hb'⟩, hab, hcz⟩ :=
    exists_loopAlpha_czIndexOfPath_eq Sinf hS hS' (hndiff.1 hnd')
  have htr : ∀ μ k, HasEigenWind J Q μ k ↔ HasLoopEigenWind Sinf μ k := fun μ k =>
    (hshift μ k).trans (hasEigenWind_iff_hasLoopEigenWind J Q' Z hZ hwind Sinf hS hS' hA μ k)
  refine ⟨a, b, ⟨⟨μa, hμa, (htr μa a).2 ha⟩, fun μ hμ k hk => ha' μ hμ k ((htr μ k).1 hk)⟩,
    ⟨⟨μb, hμb, (htr μb b).2 hb⟩, fun μ hμ k hk => hb' μ hμ k ((htr μ k).1 hk)⟩, hab,
    fun Y hY => ?_⟩
  rw [czIndexOfPath_linearizedXiPath_eq H₀ hH₀ J P Q' (hrange'.trans hrange) (hT'.trans hT)
    (by show Q.x (0 + c) = _; rw [zero_add]; exact hc)
    hnd' Z hZ hwind Sinf hS hS' hA Ψ hΨ Y hY]
  exact hcz Ψ hΨ

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let toV : HryniewiczCriterion.R4 → V 1 := fun x k => x (Fin.cast (by norm_num) k)
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J →
    ∀ (P : HryniewiczCriterion.PeriodicOrbit H₀) (Q : ReebOrbit H),
      Set.range Q.x = Set.range (fun τ => toV (P.x τ)) →
      Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ) →
      Q.IsNondegenerate →
      ∃ a b : ℤ, IsAlphaMinus J Q a ∧ IsAlphaPlus J Q b ∧ (b = a ∨ b = a + 1) ∧
        ∀ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
          HryniewiczCriterion.IsLinearizedFlow H₀ P.x Y →
          HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath H₀ P Y) =
            a + b :=
  h310_main H₀ hH₀
