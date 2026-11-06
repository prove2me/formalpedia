-- Prove2me | solution 1 for BianchiIX.exists_ode_local_contDiff_succ
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:11:22.708176+00:00
-- url     : https://prove2.me/submissions/b076197b-afe7-4a2c-bfce-9779d1820946

import Theorems.Thm_BianchiIX_contDiffOn_ode_family_with_derivative
import Theorems.Thm_BianchiIX_exists_ode_local_contDiff_one
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial


namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal ContDiff
universe u


/-- The tangent lift raises the regularity of a local solution family by one order. -/
theorem solution (n : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {f : E → E}, ContDiff ℝ ∞ f → ∀ (x₀ : E) (t₀ : ℝ),
      ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E × ℝ → E,
        ContDiffOn ℝ (n + 1) α (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
        ∀ x ∈ ball x₀ r, α (x, t₀) = x ∧
          ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt (fun u => α (x, u)) (f (α (x, t))) t := by
  induction n with
  | zero =>
    intro E _ _ _ f hf x₀ t₀
    simpa using exists_ode_local_contDiff_one (hf.of_le (by decide)) x₀ t₀
  | succ n ih =>
    intro E _ _ _ f hf x₀ t₀
    let idE := ContinuousLinearMap.id ℝ E
    let T : E × (E →L[ℝ] E) → E × (E →L[ℝ] E) :=
      fun z => (f z.1, (fderiv ℝ f z.1).comp z.2)
    have hT : ContDiff ℝ ∞ T :=
      (hf.comp contDiff_fst).prodMk
        ((hf.fderiv_right (by simp)).comp contDiff_fst |>.clm_comp contDiff_snd)
    obtain ⟨r, hr, ε, hε, Φ, hcΦ, hΦ⟩ := ih hT (x₀, idE) t₀
    let α : E × ℝ → E := fun z => (Φ ((z.1, idE), z.2)).1
    let J : E × ℝ → E →L[ℝ] E := fun z => (Φ ((z.1, idE), z.2)).2
    let U := ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)
    let K := closedBall x₀ (r / 2) ×ˢ Icc (t₀ - ε / 2) (t₀ + ε / 2)
    let V := ball x₀ (r / 2) ×ˢ Ioo (t₀ - ε / 2) (t₀ + ε / 2)
    have hxpair {x : E} (hx : x ∈ ball x₀ r) : (x, idE) ∈ ball (x₀, idE) r := by
      simpa only [mem_ball, dist_prod_same_right] using hx
    have hcomp : ContDiffOn ℝ (n + 1) (fun z : E × ℝ => Φ ((z.1, idE), z.2)) U :=
      hcΦ.comp (by fun_prop) (fun _ hz => ⟨hxpair hz.1, hz.2⟩)
    have hcα : ContDiffOn ℝ (n + 1) α U := contDiff_fst.comp_contDiffOn hcomp
    have hcJ : ContDiffOn ℝ (n + 1) J U := contDiff_snd.comp_contDiffOn hcomp
    have hKU : K ⊆ U := by
      intro z hz
      refine ⟨?_, ?_⟩
      · exact lt_of_le_of_lt hz.1 (by linarith : r / 2 < r)
      · constructor <;> linarith [hz.2.1, hz.2.2]
    have hVK : V ⊆ K := fun _ hz => ⟨ball_subset_closedBall hz.1, Ioo_subset_Icc_self hz.2⟩
    have hVU : V ⊆ U := hVK.trans hKU
    have hα0 {x : E} (hx : x ∈ ball x₀ r) : α (x, t₀) = x :=
      congrArg Prod.fst (hΦ (x, idE) (hxpair hx)).1
    have hJ0 {x : E} (hx : x ∈ ball x₀ r) : J (x, t₀) = idE :=
      congrArg Prod.snd (hΦ (x, idE) (hxpair hx)).1
    have hode {x : E} (hx : x ∈ ball x₀ r) {t : ℝ} (ht : t ∈ Ioo (t₀ - ε) (t₀ + ε)) :
        HasDerivAt (fun u => α (x, u)) (f (α (x, t))) t ∧
          HasDerivAt (fun u => J (x, u)) ((fderiv ℝ f (α (x, t))).comp (J (x, t))) t := by
      have H := (hΦ (x, idE) (hxpair hx)).2 t ht
      exact ⟨(ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t H,
        (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t H⟩
    have horder : (1 : WithTop ℕ∞) ≤ n + 1 := by
      exact le_add_left le_rfl
    obtain ⟨L, hL⟩ := (hcα.mono hKU).exists_lipschitzOnWith
      (ne_of_gt (lt_of_lt_of_le (by norm_num) horder))
      ((convex_closedBall x₀ (r / 2)).prod (convex_Icc _ _))
      ((isCompact_closedBall x₀ (r / 2)).prod isCompact_Icc)
    have hxsmall {x : E} (hx : x ∈ ball x₀ (r / 2)) : x ∈ ball x₀ r :=
      ball_subset_ball (by linarith : r / 2 ≤ r) hx
    have hsmall {x : E} {t : ℝ} (hx : x ∈ ball x₀ (r / 2))
        (ht : t ∈ Ioo (t₀ - ε / 2) (t₀ + ε / 2)) : (x, t) ∈ U := hVU ⟨hx, ht⟩
    have H := contDiffOn_ode_family_with_derivative (hf.of_le (by decide)) (half_pos hε)
      (hcα.continuousOn.mono hKU) (hcJ.continuousOn.mono hVU)
      (fun _ hx => hα0 (hxsmall hx)) (fun _ hx => hJ0 (hxsmall hx))
      (fun _ hx _ ht => (hode (hsmall hx ht).1 (hsmall hx ht).2).1)
      (fun _ hx _ ht => (hode (hsmall hx ht).1 (hsmall hx ht).2).2)
      (L := L) (fun t ht => LipschitzOnWith.of_dist_le_mul (fun x hx y hy => by
        simpa only [dist_prod_same_right] using
          hL.dist_le_mul (x, t) (hVK ⟨hx, ht⟩) (y, t) (hVK ⟨hy, ht⟩)))
    let D : E × ℝ → (E × ℝ →L[ℝ] E) := fun z =>
      (J z).coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight (f (α z)))
    have hcD : ContDiffOn ℝ (n + 1) D V := by
      have hcV := (ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ)).contDiff.comp_contDiffOn
        ((hf.of_le (by exact_mod_cast (le_top : (n : ℕ∞) + 1 ≤ ⊤))).comp_contDiffOn (hcα.mono hVU))
      exact ((hcJ.mono hVU).clm_comp (contDiffOn_const (c := ContinuousLinearMap.fst ℝ E ℝ))).add
        (hcV.clm_comp (contDiffOn_const (c := ContinuousLinearMap.snd ℝ E ℝ)))
    refine ⟨r / 2, half_pos hr, ε / 2, half_pos hε, α, ?_, fun x hx =>
      ⟨hα0 (hxsmall hx), fun t ht => (hode (hsmall hx ht).1 (hsmall hx ht).2).1⟩⟩
    rw [show ((n.succ : ℕ) : WithTop ℕ∞) + 1 = (n + 1) + 1 by simp,
      contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (isOpen_ball.prod isOpen_Ioo).uniqueDiffOn]
    exact ⟨by simp, D, hcD, fun z hz => (H.2 z hz).hasFDerivAt.hasFDerivWithinAt⟩
