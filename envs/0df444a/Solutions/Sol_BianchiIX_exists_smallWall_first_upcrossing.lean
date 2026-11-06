-- Prove2me | solution 1 for BianchiIX.exists_smallWall_first_upcrossing
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:08:12.776202+00:00
-- url     : https://prove2.me/submissions/3b8c41db-e9d0-4e59-9b04-59beefcc1f03

import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_GeometricExceptionData
import Theorems.Thm_BianchiIX_exists_smallWall_growth_gap
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_wall_formula
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_first_level_hit {f : ℝ → ℝ} {a b h : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (ha : f a < h) (hb : h ≤ f b) :
    ∃ T ∈ Ioc a b, f T = h ∧ ∀ u ∈ Ico a T, f u < h := by
  let S : Set ℝ := Icc a b ∩ f ⁻¹' {h}
  have hclosed : IsClosed S := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed (fun _ hx => hx.1)
  obtain ⟨v, hv, heq⟩ := intermediate_value_Icc hab hf ⟨ha.le, hb⟩
  obtain ⟨T, hT, hleast⟩ := hcompact.exists_isLeast ⟨v, hv, heq⟩
  have hTa : a < T := lt_of_le_of_ne hT.1.1 (by
    intro heq
    have hh : f T = h := hT.2
    rw [← heq] at hh
    exact ha.ne hh)
  refine ⟨T, ⟨hTa, hT.1.2⟩, hT.2, ?_⟩
  intro u hu
  by_contra! hh
  obtain ⟨v, hv, hvh⟩ := intermediate_value_Icc hu.1
    (hf.mono (Icc_subset_Icc le_rfl (hu.2.le.trans hT.1.2))) ⟨ha.le, hh⟩
  have hTv := hleast (show v ∈ S from ⟨⟨hv.1, hv.2.trans (hu.2.le.trans hT.1.2)⟩, hvh⟩)
  exact (not_le_of_gt hu.2) (hTv.trans hv.2)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.continuous_wallRate (i : Fin 3) : Continuous (wallRate i) := by
  change Continuous (fun x => wallRate i x)
  fin_cases i <;> dsimp [wallRate, rateOne, rateTwo, rateThree, shearSq] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.hasDerivAt_wallValue {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t) (i : Fin 3) :
    HasDerivAt (fun u => wallValue i (α u)) (wallRate i (α t) * wallValue i (α t)) t := by
  have H := hasDerivAt_pi.mp hα (i.addNat 2)
  fin_cases i <;> exact H

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.normalized_wall_pos {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (i : Fin 3) (hpos : 0 < wallValue i (α t₀)) :
    0 < wallValue i (α t) := by
  rw [normalized_wall_formula hI hopen hα ht₀ ht i]
  exact mul_pos hpos (Real.exp_pos _)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.le_exp_of_linear_deriv_le {I : Set ℝ} (hI : Convex ℝ I)
    {f f' : ℝ → ℝ} {c s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hbound : ∀ u ∈ I, f' u ≤ c * f u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (c * (t - s)) := by
  exact le_exp_of_clock_deriv_le hI hf (fun u _ => hasDerivAt_id u)
    (fun u hu => by simpa only [mul_one] using hbound u hu) hs ht hst

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.wall_growth_index_constant {α : ℝ → NormalizedState} {s t c : ℝ}
    (hst : s ≤ t) (hc : 0 < c) (hα : ContinuousOn α (Icc s t))
    (H : ∀ u ∈ Icc s t, ∃ i : Fin 3, c ≤ wallRate i (α u) ∧
      ∀ j : Fin 3, j ≠ i → wallRate j (α u) ≤ -c) :
    ∃ i : Fin 3, ∀ u ∈ Icc s t, c ≤ wallRate i (α u) ∧
      ∀ j : Fin 3, j ≠ i → wallRate j (α u) ≤ -c := by
  obtain ⟨i, hi, _⟩ := H s ⟨le_rfl, hst⟩
  have hnonzero (u : ℝ) (hu : u ∈ Icc s t) : wallRate i (α u) ≠ 0 := by
    obtain ⟨j, hj, hj'⟩ := H u hu
    by_cases heq : i = j
    · subst j
      exact (hc.trans_le hj).ne'
    · exact (lt_of_le_of_lt (hj' i heq) (neg_neg_of_pos hc)).ne
  refine ⟨i, ?_⟩
  intro u hu
  have hpos : 0 < wallRate i (α u) := by
    by_contra! hneg
    have hcont := (continuous_wallRate i).comp_continuousOn
      (hα.mono (Icc_subset_Icc le_rfl hu.2))
    obtain ⟨v, hv, heq⟩ := intermediate_value_Icc' hu.1 hcont
      (show (0 : ℝ) ∈ Icc (wallRate i (α u)) (wallRate i (α s)) from ⟨hneg, hc.le.trans hi⟩)
    exact hnonzero v ⟨hv.1, hv.2.trans hu.2⟩ heq
  obtain ⟨j, hj, hj'⟩ := H u hu
  have heq : i = j := by
    by_contra hne
    have hbad := hj' i hne
    linarith only [hbad, hpos, hc]
  simpa only [heq] using And.intro hj hj'

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalized_growth_gap_motion {x : NormalizedState} {T c : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x) (hT : 0 ≤ T) (hcpos : 0 < c)
    (H : ∀ u ∈ Icc 0 T, ∃ i : Fin 3, c ≤ wallRate i (normalizedMaxCurve x 0 u) ∧
      ∀ j : Fin 3, j ≠ i → wallRate j (normalizedMaxCurve x 0 u) ≤ -c) :
    ∃ i : Fin 3,
      (∀ u ∈ Icc 0 T, c ≤ wallRate i (normalizedMaxCurve x 0 u) ∧
        ∀ j : Fin 3, j ≠ i → wallRate j (normalizedMaxCurve x 0 u) ≤ -c) ∧
      StrictMonoOn (fun u => wallValue i (normalizedMaxCurve x 0 u)) (Icc 0 T) ∧
      (∀ j : Fin 3, j ≠ i → StrictAntiOn (fun u => wallValue j (normalizedMaxCurve x 0 u)) (Icc 0 T)) ∧
      wallValue i x * Real.exp (c * T) ≤ wallValue i (normalizedMaxCurve x 0 T) := by
  let α := normalizedMaxCurve x 0
  have hflow (u : ℝ) (hu : u ∈ Icc 0 T) : HasDerivAt α (normalizedField (α u)) u :=
    (normalizedMaxCurve_forward_of_constraint hc hu.1).1
  have hpos (u : ℝ) (hu : u ∈ Icc 0 T) (i : Fin 3) : 0 < wallValue i (α u) := by
    have hstart : 0 < wallValue i x := by fin_cases i <;> first | exact hp.1 | exact hp.2.1 | exact hp.2.2
    exact normalized_wall_pos (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
      (fun v hv => hasDerivAt_normalizedMaxCurve hv) (initial_mem_normalizedMaxDomain x 0)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hu.1) i
      (by simpa only [normalizedMaxCurve_initial] using hstart)
  obtain ⟨i, Hi⟩ := wall_growth_index_constant hT hcpos (HasDerivAt.continuousOn hflow) H
  have hd (j : Fin 3) (u : ℝ) (hu : u ∈ Icc 0 T) := hasDerivAt_wallValue (hflow u hu) j
  refine ⟨i, Hi, ?_, ?_, ?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Icc 0 T) (HasDerivAt.continuousOn (hd i))
    intro u hu
    rw [(hd i u (interior_subset hu)).deriv]
    exact mul_pos (hcpos.trans_le (Hi u (interior_subset hu)).1) (hpos u (interior_subset hu) i)
  · intro j hj
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 T) (HasDerivAt.continuousOn (hd j))
    intro u hu
    rw [(hd j u (interior_subset hu)).deriv]
    exact mul_neg_of_neg_of_pos
      ((Hi u (interior_subset hu)).2 j hj |>.trans_lt (neg_neg_of_pos hcpos))
      (hpos u (interior_subset hu) j)
  · have hh := le_exp_of_linear_deriv_le (convex_Icc 0 T)
      (fun u hu => (hd i u hu).neg) (c := c) (fun u hu => by
        have hb := mul_le_mul_of_nonneg_right (Hi u hu).1 (hpos u hu i).le
        change -(wallRate i (α u) * wallValue i (α u)) ≤ c * (-wallValue i (α u))
        nlinarith only [hb]) ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
    simpa only [Pi.neg_apply, α, normalizedMaxCurve_initial, sub_zero, neg_mul, neg_le_neg_iff] using hh

end
end

private theorem BianchiIX.wallValue_le_wallMaximum (x : NormalizedState) (i : Fin 3) :
    wallValue i x ≤ normalizedWallMaximum x := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)


/-- Every Taub-avoiding positive orbit starting below a small wall height has a first upward wall hit. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ ν₀ > (0 : ℝ), ν₀ ≤ 1 / 4 ∧ ∃ c > (0 : ℝ), c ≤ 1 ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ x : NormalizedState,
        stateConstraint x = 1 → positiveWalls x → (∀ i : Fin 3, wallValue i x < ν) →
        normalizedTaubAvoidance ε x → ∃ T > (0 : ℝ), ∃ i : Fin 3,
          IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
            ∃ j : Fin 3, wallValue j (normalizedMaxCurve x 0 t) = ν} T ∧
          (∀ u ∈ Ico 0 T, ∀ j : Fin 3, wallValue j (normalizedMaxCurve x 0 u) < ν) ∧
          (∀ u ∈ Icc 0 T, c ≤ wallRate i (normalizedMaxCurve x 0 u) ∧
            ∀ j : Fin 3, j ≠ i → wallRate j (normalizedMaxCurve x 0 u) ≤ -c) ∧
          wallValue i (normalizedMaxCurve x 0 T) = ν ∧
          (∀ j : Fin 3, j ≠ i → wallValue j (normalizedMaxCurve x 0 T) < ν) ∧
          HasDerivAt (fun u => wallValue i (normalizedMaxCurve x 0 u))
            (wallRate i (normalizedMaxCurve x 0 T) * ν) T ∧
          0 < c * ν ∧ c * ν ≤ wallRate i (normalizedMaxCurve x 0 T) * ν := by
  obtain ⟨ν₀, hν₀, hν₀max, c, hc, hcmax, HG⟩ := exists_smallWall_growth_gap hε
  refine ⟨ν₀, hν₀, hν₀max, c, hc, hcmax, ?_⟩
  intro ν hν hνcap x hx hp hsmall ha
  let α := normalizedMaxCurve x 0
  let f := fun t => normalizedWallMaximum (α t)
  have hdom (u : ℝ) (hu : 0 ≤ u) : u ∈ normalizedMaxDomain x 0 :=
    normalizedMaxDomain_contains_Ici_of_constraint hx 0 hu
  have hflow (u : ℝ) (hu : 0 ≤ u) : HasDerivAt α (normalizedField (α u)) u :=
    (normalizedMaxCurve_forward_of_constraint hx hu).1
  have hpos (u : ℝ) (hu : 0 ≤ u) (i : Fin 3) : 0 < wallValue i (α u) := by
    have hstart : 0 < wallValue i x := by fin_cases i <;> first | exact hp.1 | exact hp.2.1 | exact hp.2.2
    exact normalized_wall_pos (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
      (fun v hv => hasDerivAt_normalizedMaxCurve hv) (initial_mem_normalizedMaxDomain x 0)
      (hdom u hu) i (by simpa only [normalizedMaxCurve_initial] using hstart)
  have hgap (u : ℝ) (hu : 0 ≤ u) (hfu : f u ≤ ν) :
      ∃ i : Fin 3, c ≤ wallRate i (α u) ∧ ∀ j : Fin 3, j ≠ i → wallRate j (α u) ≤ -c :=
    HG (α u) (normalizedMaxCurve_forward_of_constraint hx hu).2.1
      (fun i => ⟨(hpos u hu i).le, ((wallValue_le_wallMaximum (α u) i).trans hfu).trans hνcap⟩)
      (ha u hu (hdom u hu))
  have hf (H : ℝ) : ContinuousOn f (Icc 0 H) := by
    have hα : ContinuousOn α (Icc 0 H) := fun u hu => (hflow u hu.1).continuousAt.continuousWithinAt
    exact (show Continuous normalizedWallMaximum by unfold normalizedWallMaximum; fun_prop).comp_continuousOn hα
  have hf0 : f 0 < ν := by
    change max (α 0 2) (max (α 0 3) (α 0 4)) < ν
    simp only [α, normalizedMaxCurve_initial]
    exact max_lt (hsmall 0) (max_lt (hsmall 1) (hsmall 2))
  have hexit : ∃ H ≥ (0 : ℝ), ν ≤ f H := by
    by_contra! hnone
    let m := min (x 2) (min (x 3) (x 4))
    have hm : 0 < m := lt_min hp.1 (lt_min hp.2.1 hp.2.2)
    have hmi (i : Fin 3) : m ≤ wallValue i x := by
      fin_cases i
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans (min_le_right _ _)
    let H := ν / (c * m)
    have hH : 0 < H := div_pos hν (mul_pos hc hm)
    obtain ⟨i, _, _, _, hgrow⟩ := normalized_growth_gap_motion hx hp hH.le hc
      (fun u hu => hgap u hu.1 (hnone u hu.1).le)
    have hl := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (c * H)) hm.le
    have heq : m * (c * H + 1) = ν + m := by
      dsimp [H]
      field_simp [hc.ne', hm.ne']
    rw [heq] at hl
    have hh := (hl.trans (mul_le_mul_of_nonneg_right (hmi i) (Real.exp_pos _).le)).trans hgrow
    have hu : wallValue i (α H) < ν := (wallValue_le_wallMaximum (α H) i).trans_lt (hnone H hH.le)
    linarith only [hh, hu, hm]
  obtain ⟨H, hH, hreach⟩ := hexit
  obtain ⟨T, hT, hhit, hprefix⟩ := exists_first_level_hit hH (hf H) hf0 hreach
  have hwhole (u : ℝ) (hu : u ∈ Icc 0 T) : f u ≤ ν := by
    rcases lt_or_eq_of_le hu.2 with hh | rfl
    · exact (hprefix u ⟨hu.1, hh⟩).le
    · exact hhit.le
  obtain ⟨i, Hi, _, Hanti, _⟩ := normalized_growth_gap_motion hx hp hT.1.le hc
    (fun u hu => hgap u hu.1 (hwhole u hu))
  have hother (j : Fin 3) (hj : j ≠ i) : wallValue j (α T) < ν := by
    have hh := Hanti j hj ⟨le_rfl, hT.1.le⟩ ⟨hT.1.le, le_rfl⟩ hT.1
    exact hh.trans (by simpa only [normalizedMaxCurve_initial] using hsmall j)
  have hactive : wallValue i (α T) = ν := by
    have hle := (wallValue_le_wallMaximum (α T) i).trans_eq hhit
    apply le_antisymm hle
    by_contra! hh
    have hall (j : Fin 3) : wallValue j (α T) < ν := by
      by_cases hj : j = i
      · simpa only [hj] using hh
      · exact hother j hj
    have hfT : f T < ν := max_lt (hall 0) (max_lt (hall 1) (hall 2))
    exact (ne_of_lt hfT) hhit
  have hpre (u : ℝ) (hu : u ∈ Ico 0 T) (j : Fin 3) : wallValue j (α u) < ν :=
    (wallValue_le_wallMaximum (α u) j).trans_lt (hprefix u hu)
  have hleast : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
      ∃ j : Fin 3, wallValue j (α t) = ν} T := by
    refine ⟨⟨hT.1, hdom T hT.1.le, i, hactive⟩, ?_⟩
    intro u hu
    by_contra! hh
    obtain ⟨j, hj⟩ := hu.2.2
    exact (hpre u ⟨hu.1.le, hh⟩ j).ne hj
  have hd := hasDerivAt_wallValue (hflow T hT.1.le) i
  rw [hactive] at hd
  exact ⟨T, hT.1, i, hleast, hpre, Hi, hactive, hother, hd,
    mul_pos hc hν, mul_le_mul_of_nonneg_right (Hi T ⟨hT.1.le, le_rfl⟩).1 hν.le⟩
