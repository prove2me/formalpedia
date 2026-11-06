-- Prove2me | solution 1 for BianchiIX.exists_ode_local_contDiff_one
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:10:22.660594+00:00
-- url     : https://prove2.me/submissions/f7717225-284a-4d25-8990-b2548c14588f

import Theorems.Thm_BianchiIX_contDiffOn_ode_family_with_derivative
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

section
noncomputable section
open BianchiIX
open Set Filter Metric Asymptotics
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem BianchiIX.contDiffOn_ode_family {f : E → E} (hf : ContDiff ℝ 2 f)
    {x₀ : E} {t₀ r ε : ℝ} (hε : 0 < ε)
    {α : E × ℝ → E} {J : E × ℝ → E →L[ℝ] E} {L : ℝ≥0}
    (hcα : ContinuousOn α (closedBall x₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε)))
    (hcJ : ContinuousOn J (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)))
    (hα0 : ∀ x ∈ ball x₀ r, α (x, t₀) = x)
    (hJ0 : ∀ x ∈ ball x₀ r, J (x, t₀) = ContinuousLinearMap.id ℝ E)
    (hα : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun u => α (x, u)) (f (α (x, t))) t)
    (hJ : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun u => J (x, u)) ((fderiv ℝ f (α (x, t))).comp (J (x, t))) t)
    (hLip : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      LipschitzOnWith L (fun x => α (x, t)) (ball x₀ r)) :
    ContDiffOn ℝ 1 α (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) :=
  (contDiffOn_ode_family_with_derivative hf hε hcα hcJ hα0 hJ0 hα hJ hLip).1

end
end

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter Metric Asymptotics
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]


/-- Apply Picard-Lindelof once to the state and its linear variation together. -/
theorem solution {f : E → E} (hf : ContDiff ℝ 2 f) (x₀ : E) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E × ℝ → E,
      ContDiffOn ℝ 1 α (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ x ∈ ball x₀ r, α (x, t₀) = x ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt (fun u => α (x, u)) (f (α (x, t))) t := by
  let idE := ContinuousLinearMap.id ℝ E
  let T : E × (E →L[ℝ] E) → E × (E →L[ℝ] E) :=
    fun z => (f z.1, (fderiv ℝ f z.1).comp z.2)
  have hT : ContDiff ℝ 1 T :=
    ((hf.of_le (by norm_num)).comp contDiff_fst).prodMk
      (((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).comp contDiff_fst).clm_comp contDiff_snd)
  obtain ⟨ε, hε, a, r, L, K, hr, hPL⟩ := IsPicardLindelof.of_contDiffAt_one
    (hT.contDiffAt (x := (x₀, idE)))
  obtain ⟨Φ, hΦ, L', hLip⟩ :=
    (hPL t₀).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  have hcΦ : ContinuousOn (fun z => Φ z.1 z.2)
      (closedBall (x₀, idE) r ×ˢ Icc (t₀ - ε) (t₀ + ε)) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ L'
      (fun x hx => HasDerivWithinAt.continuousOn (hΦ x hx).2) hLip
  have hxpair (x : E) (hx : x ∈ closedBall x₀ r) : (x, idE) ∈ closedBall (x₀, idE) r := by
    simpa only [mem_closedBall, dist_prod_same_right] using hx
  let α : E × ℝ → E := fun z => (Φ (z.1, idE) z.2).1
  let J : E × ℝ → E →L[ℝ] E := fun z => (Φ (z.1, idE) z.2).2
  have hc : ContinuousOn (fun z : E × ℝ => Φ (z.1, idE) z.2)
      (closedBall x₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε)) :=
    hcΦ.comp (by fun_prop : ContinuousOn (fun z : E × ℝ => ((z.1, idE), z.2))
      (closedBall x₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε))) (fun z hz => ⟨hxpair z.1 hz.1, hz.2⟩)
  have hode (x : E) (hx : x ∈ ball x₀ r) (t : ℝ) (ht : t ∈ Ioo (t₀ - ε) (t₀ + ε)) :
      HasDerivAt (fun u => α (x, u)) (f (α (x, t))) t ∧
      HasDerivAt (fun u => J (x, u)) ((fderiv ℝ f (α (x, t))).comp (J (x, t))) t := by
    have H := ((hΦ (x, idE) (hxpair x (ball_subset_closedBall hx))).2 t
      (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    exact ⟨(ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t H,
      (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t H⟩
  have hα0 (x : E) (hx : x ∈ ball x₀ r) : α (x, t₀) = x :=
    congrArg Prod.fst (hΦ (x, idE) (hxpair x (ball_subset_closedBall hx))).1
  have hJ0 (x : E) (hx : x ∈ ball x₀ r) : J (x, t₀) = idE :=
    congrArg Prod.snd (hΦ (x, idE) (hxpair x (ball_subset_closedBall hx))).1
  refine ⟨r, hr, ε, hε, α, ?_, fun x hx => ⟨hα0 x hx, fun t ht => (hode x hx t ht).1⟩⟩
  apply contDiffOn_ode_family hf hε (continuous_fst.comp_continuousOn hc)
    ((continuous_snd.comp_continuousOn hc).mono
      (fun _ hz => ⟨ball_subset_closedBall hz.1, Ioo_subset_Icc_self hz.2⟩)) hα0 hJ0
    (fun x hx t ht => (hode x hx t ht).1) (fun x hx t ht => (hode x hx t ht).2)
    (L := L')
  intro t ht
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  calc
    _ ≤ dist (Φ (x, idE) t) (Φ (y, idE) t) := le_max_left _ _
    _ ≤ L' * dist (x, idE) (y, idE) :=
      (hLip t (Ioo_subset_Icc_self ht)).dist_le_mul _ (hxpair x (ball_subset_closedBall hx))
        _ (hxpair y (ball_subset_closedBall hy))
    _ = _ := by rw [dist_prod_same_right]
