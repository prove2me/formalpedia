-- Prove2me | solution 1 for FiniteEnergyPlane.ReebOrbit.apply_eq_apply_add_of_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:23:23.956041+00:00
-- url     : https://prove2.me/submissions/3418c912-ee8d-4f5d-9a05-87690ec50d90

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitz_near_compact

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

namespace S177RB
open FiniteEnergyPlane

variable {n : ℕ}

lemma j0_cd {G : V n → V n} (hG : ContDiff ℝ 1 G) : ContDiff ℝ 1 (fun x => j0 (G x)) := by
  refine contDiff_pi.2 fun k => ?_
  simp only [j0]
  split_ifs
  · exact ((contDiff_apply ℝ ℝ _).comp hG).neg
  · exact (contDiff_apply ℝ ℝ _).comp hG

lemma hamVF_cd {H : V n → ℝ} (hH : ContDiff ℝ ∞ H) : ContDiff ℝ 1 (hamVF H) := by
  have hf : ContDiff ℝ 1 (fderiv ℝ H) := hH.fderiv_right (WithTop.coe_le_coe.2 le_top)
  have hg : ContDiff ℝ 1 (grad H) :=
    contDiff_pi.2 fun k => hf.clm_apply contDiff_const
  exact j0_cd hg

lemma liou_cd {F G : V n → V n} (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (fun x => liouville (F x) (G x)) := by
  simp only [liouville, omega0, dot]
  refine ContDiff.div_const ?_ _
  refine ContDiff.sum fun k _ => ?_
  exact ((contDiff_apply ℝ ℝ k).comp (j0_cd hF)).mul ((contDiff_apply ℝ ℝ k).comp hG)

end S177RB

open FiniteEnergyPlane in
theorem solution {n : ℕ} {H : V n → ℝ}
    (hH : IsStrictlyStarShapedLevel H) (P Q : ReebOrbit H) {τ₁ τ₂ : ℝ} (h : Q.x τ₁ = P.x τ₂) :
    ∀ τ, Q.x τ = P.x (τ + (τ₂ - τ₁)) := by
  set φ : V n → ℝ := fun x => liouville x (hamVF H x)
  have hφ : ContDiff ℝ 1 φ := S177RB.liou_cd contDiff_id (S177RB.hamVF_cd hH.1)
  set O : Set (V n) := {x | φ x ≠ 0}
  have hO : IsOpen O := isOpen_ne_fun hφ.continuous continuous_const
  have hR : ContDiffOn ℝ 1 (reeb H) O := by
    intro x hx
    exact ((hφ.contDiffAt.inv hx).smul (S177RB.hamVF_cd hH.1).contDiffAt).contDiffWithinAt
  have hcP : Continuous P.x := continuous_iff_continuousAt.2 fun τ => (P.hasDerivAt τ).continuousAt
  have hcQ : Continuous Q.x := continuous_iff_continuousAt.2 fun τ => (Q.hasDerivAt τ).continuousAt
  set K : Set (V n) := Set.range P.x ∪ Set.range Q.x
  have hK : IsCompact K :=
    (Function.Periodic.compact_of_continuous P.periodic P.T_pos.ne' hcP).union
      (Function.Periodic.compact_of_continuous Q.periodic Q.T_pos.ne' hcQ)
  have hKS : K ⊆ energySurface H := by
    rintro _ (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
    · exact P.mem τ
    · exact Q.mem τ
  have hKO : K ⊆ O := fun x hx => (reeb_spec H hH x (hKS hx)).1.ne'
  obtain ⟨δ, hδ, D, hD, hball⟩ := exists_lipschitz_near_compact hO hR hK hKO
  set L : ℝ := max D (2 * D / δ)
  have hL : 0 ≤ L := le_max_of_le_left hD
  have hlip : LipschitzOnWith (Real.toNNReal L) (reeb H) K := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
    rw [Real.coe_toNNReal _ hL, dist_eq_norm, dist_eq_norm]
    obtain ⟨-, hb⟩ := hball y hy
    by_cases hc : ‖y - y'‖ ≤ δ
    · have h1 : y' ∈ closedBall y δ := by rw [mem_closedBall, dist_eq_norm, norm_sub_rev]; exact hc
      have := (hb y (mem_closedBall_self hδ.le)).2 y' h1
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · push Not at hc
      obtain ⟨-, hb'⟩ := hball y' hy'
      have b1 := (hb y (mem_closedBall_self hδ.le)).1
      have b2 := (hb' y' (mem_closedBall_self hδ.le)).1
      have : ‖reeb H y - reeb H y'‖ ≤ 2 * D := (norm_sub_le _ _).trans (by linarith)
      refine this.trans ?_
      calc 2 * D = 2 * D / δ * δ := by field_simp
        _ ≤ L * ‖y - y'‖ := mul_le_mul (le_max_right _ _) hc.le hδ.le hL
  have key := ODE_solution_unique_univ (v := fun _ => reeb H) (s := fun _ => K)
    (f := Q.x) (g := fun τ => P.x (τ + (τ₂ - τ₁))) (t₀ := τ₁) (fun _ => hlip)
    (fun t => ⟨Q.hasDerivAt t, Or.inr ⟨t, rfl⟩⟩)
    (fun t => ⟨by
        have := (P.hasDerivAt (t + (τ₂ - τ₁))).scomp t ((hasDerivAt_id t).add_const (τ₂ - τ₁))
        simpa [Function.comp_def] using this, Or.inl ⟨_, rfl⟩⟩)
    (by rw [h]; congr 1; ring)
  intro τ
  exact congrFun key τ
