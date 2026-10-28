-- Prove2me | solution 2 for FiniteEnergyPlane.ReebOrbit.apply_eq_apply_add_of_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-25T23:45:29.976826+00:00
-- url     : https://prove2.me/submissions/952b6c05-a667-4646-b725-d235e6585021

import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Connected.Clopen
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Definitions.Def_FiniteEnergyPlane_Setting

open FiniteEnergyPlane MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} {H : V n → ℝ}
    (hH : IsStrictlyStarShapedLevel H) (P Q : ReebOrbit H) {τ₁ τ₂ : ℝ} (h : Q.x τ₁ = P.x τ₂) :
    ∀ τ, Q.x τ = P.x (τ + (τ₂ - τ₁)) := by
  -- the Reeb field is `C¹` near `S`
  have hH2 : ContDiff ℝ 2 H := hH.1.of_le (WithTop.coe_le_coe.2 le_top)
  have hj0 : ContDiff ℝ 1 (j0 : V n → V n) := by
    refine contDiff_pi.2 fun k => ?_
    unfold j0
    by_cases hk : (k : ℕ) % 2 = 0
    · simp only [hk, dif_pos]; exact (contDiff_apply ℝ ℝ _).neg
    · simp only [hk, dif_neg, not_false_eq_true]; exact contDiff_apply ℝ ℝ _
  have hgrad : ContDiff ℝ 1 (grad H) :=
    contDiff_pi.2 fun k => (hH2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hX : ContDiff ℝ 1 (hamVF H) := hj0.comp hgrad
  have hlv : ContDiff ℝ 1 fun x => liouville x (hamVF H x) := by
    show ContDiff ℝ 1 fun x => (∑ k, j0 x k * hamVF H x k) / 2
    refine ContDiff.div_const (ContDiff.sum fun k _ => ?_) _
    exact ((contDiff_pi.1 hj0) k).mul ((contDiff_pi.1 hX) k)
  have hR : ∀ p ∈ energySurface H, ContDiffAt ℝ 1 (reeb H) p := fun p hp =>
    (hlv.contDiffAt.inv (reeb_spec H hH p hp).1.ne').smul hX.contDiffAt
  -- the coincidence set is clopen
  set d := τ₂ - τ₁
  set A : Set ℝ := {τ | Q.x τ = P.x (τ + d)}
  have hQc : Continuous Q.x := continuous_iff_continuousAt.2 fun τ => (Q.hasDerivAt τ).continuousAt
  have hPc : Continuous P.x := continuous_iff_continuousAt.2 fun τ => (P.hasDerivAt τ).continuousAt
  have hg : ∀ τ, HasDerivAt (fun τ => P.x (τ + d)) (reeb H (P.x (τ + d))) τ :=
    fun τ => (P.hasDerivAt (τ + d)).comp_add_const τ d
  have hclosed : IsClosed A := isClosed_eq hQc (hPc.comp (continuous_add_const d))
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    obtain ⟨K, U, hU, hK⟩ := (hR _ (Q.mem τ)).exists_lipschitzOnWith
    have hQU : ∀ᶠ s in 𝓝 τ, Q.x s ∈ U := hQc.continuousAt.eventually_mem hU
    have hPU : ∀ᶠ s in 𝓝 τ, P.x (s + d) ∈ U :=
      (hPc.comp (continuous_add_const d)).continuousAt.eventually_mem (by
        show U ∈ 𝓝 (P.x (τ + d)); rw [← show Q.x τ = P.x (τ + d) from hτ]; exact hU)
    have := ODE_solution_unique_of_eventually (v := fun _ => reeb H) (s := fun _ => U) (K := K)
      (Eventually.of_forall fun _ => hK)
      (hQU.mono fun s hs => ⟨Q.hasDerivAt s, hs⟩) (hPU.mono fun s hs => ⟨hg s, hs⟩) hτ
    exact this
  have h₁ : τ₁ ∈ A := by
    show Q.x τ₁ = P.x (τ₁ + d)
    rw [h]; congr 1; ring
  have hA : A = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨τ₁, h₁⟩
  exact fun τ => (show τ ∈ A from hA ▸ Set.mem_univ τ)
