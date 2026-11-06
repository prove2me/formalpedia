-- Prove2me | solution 1 for BianchiIX.exists_restartFastProjectiveEntry_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:46:42.482454+00:00
-- url     : https://prove2.me/submissions/c3e4b207-a279-4a52-ab48-efd806abcef4

import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_SectionRestartData
import Theorems.Thm_BianchiIX_exists_restartRadialCurve_control
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Pi

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restart_cutoff_budget (C C₀ q : ℝ) :
    ∀ᶠ ρ : ℝ in 𝓝[>] 0, (0 < ρ ∧ ρ ≤ 1) ∧ 2 * C₀ * ρ ≤ 1 / 16 ∧
      C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8 := by
  have HI : Tendsto (fun ρ : ℝ => ρ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HL : Tendsto (fun ρ : ℝ => ρ * Real.log ρ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have HB : Tendsto (fun ρ : ℝ => 2 * C₀ * ρ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using HI.const_mul (2 * C₀)
  have HT : Tendsto (fun ρ : ℝ => C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ))) (𝓝[>] 0) (𝓝 0) := by
    convert! HL.const_mul (-C * C₀ * q) using 1
    · ext ρ
      rw [one_div, Real.log_inv]
      ring
    · simp
  filter_upwards [show ∀ᶠ ρ : ℝ in 𝓝[>] 0, 0 < ρ from self_mem_nhdsWithin,
    HI.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    HB.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    HT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))] with ρ hρ hρ1 hb ht
  exact ⟨⟨hρ, hρ1.le⟩, hb.le, ht.le⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.curvature_abs_le_sum_sq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    |curvature a b c| ≤ (a + b + c) ^ 2 := by
  rw [abs_le]
  constructor
  · unfold curvature
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  · unfold curvature
    nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompact_box_bounds {x : RestartState} (hx : ‖x‖ ≤ 1 / 16) :
    |curvature (x 0) (x 2) (x 3)| ≤ 9 / 256 ∧
      246 / 256 ≤ restartRadicand x ∧ restartRadicand x ≤ 265 / 256 ∧
      15 / 16 ≤ restartCompactRoot x ∧ restartCompactRoot x ≤ 17 / 16 ∧
      -4 < restartCompactField x 0 ∧ restartCompactField x 0 < -2 := by
  have hc (i : Fin 4) : |x i| ≤ 1 / 16 := (norm_le_pi_norm x i).trans hx
  have hs (i : Fin 4) : (x i) ^ 2 ≤ 1 / 256 := by
    obtain ⟨hl, hu⟩ := abs_le.mp (hc i)
    nlinarith only [hl, hu]
  have hm (i j : Fin 4) : |x i * x j| ≤ 1 / 256 := by
    rw [abs_mul]
    calc
      _ ≤ (1 / 16 : ℝ) * (1 / 16) := mul_le_mul (hc i) (hc j) (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hQ : |curvature (x 0) (x 2) (x 3)| ≤ 9 / 256 := by
    obtain ⟨h02l, h02u⟩ := abs_le.mp (hm 0 2)
    obtain ⟨h23l, h23u⟩ := abs_le.mp (hm 2 3)
    obtain ⟨h30l, h30u⟩ := abs_le.mp (hm 3 0)
    apply abs_le.mpr
    dsimp only [curvature]
    constructor
    · nlinarith only [sq_nonneg (x 0), sq_nonneg (x 2), sq_nonneg (x 3), h02u, h23u, h30u]
    · nlinarith only [hs 0, hs 2, hs 3, h02l, h23l, h30l]
  have hRl : 246 / 256 ≤ restartRadicand x := by
    dsimp only [restartRadicand]
    linarith only [hs 1, (abs_le.mp hQ).2]
  have hRu : restartRadicand x ≤ 265 / 256 := by
    dsimp only [restartRadicand]
    linarith only [sq_nonneg (x 1), (abs_le.mp hQ).1]
  have hr0 : 0 ≤ restartCompactRoot x := Real.sqrt_nonneg _
  have hr2 : restartCompactRoot x ^ 2 = restartRadicand x := Real.sq_sqrt (by linarith only [hRl])
  have hrl : 15 / 16 ≤ restartCompactRoot x := by nlinarith only [hr0, hr2, hRl]
  have hru : restartCompactRoot x ≤ 17 / 16 := by nlinarith only [hr0, hr2, hRu]
  refine ⟨hQ, hRl, hRu, hrl, hru, ?_, ?_⟩
  · change -4 < curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x
    linarith only [(abs_le.mp hQ).1, hru]
  · change curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x < -2
    linarith only [(abs_le.mp hQ).2, hrl]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionChart_constraint {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 ≤ restartSectionRadicand h Z) : stateConstraint (restartSectionChart h Z) = 1 := by
  have H := Real.sq_sqrt hZ
  dsimp [stateConstraint, constraint, shearSq, restartSectionChart]
  rw [neg_sq, H]
  unfold restartSectionRadicand
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartCenterProjection_section (h : ℝ) (Z : RestartCenterState) :
    restartCenterProjection (restartSectionChart h Z) = Z := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartPhysicalCoordinates_norm_le {x : NormalizedState} {R : ℝ} (hR : 0 ≤ R)
    (hn : |x 2| ≤ R) (hZ : ‖restartCenterProjection x‖ ≤ R) :
    ‖restartPhysicalCoordinates x‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  fin_cases i
  · exact hn
  · exact (norm_le_pi_norm (restartCenterProjection x) 0).trans hZ
  · exact (norm_le_pi_norm (restartCenterProjection x) 1).trans hZ
  · exact (norm_le_pi_norm (restartCenterProjection x) 2).trans hZ

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionRadicand_pos_of_small {h : ℝ} {Z : RestartCenterState}
    (hh : |h| ≤ 1 / 16) (hZ : ‖Z‖ ≤ 1 / 16) : 0 < restartSectionRadicand h Z := by
  have hw := restartPhysicalCoordinates_norm_le (x := restartSectionChart h Z) (by norm_num : (0 : ℝ) ≤ 1 / 16)
    hh (by rwa [restartCenterProjection_section])
  have H := (restartCompact_box_bounds hw).2.1
  change 246 / 256 ≤ restartSectionRadicand h Z at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartSectionChart {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 < restartSectionRadicand h Z) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (restartSectionChart h) Z := by
  have hr : ContDiff ℝ k (restartSectionRadicand h) := by
    unfold restartSectionRadicand curvature
    fun_prop
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact (hr.contDiffAt.sqrt hZ.ne').neg
  · exact contDiffAt_apply ℝ ℝ (0 : Fin 3) Z
  · exact contDiffAt_const
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 3) Z
  · exact contDiffAt_apply ℝ ℝ (2 : Fin 3) Z

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionHeight_of_constraint {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    restartProjectionHeight (x 2, ![x 1, x 3, x 4]) = 1 + x 0 := by
  have hd : restartProjectionDefect (x 2, ![x 1, x 3, x 4]) = 1 - (x 0) ^ 2 := by
    change (x 1) ^ 2 + curvature (x 2) (x 3) (x 4) = _
    dsimp only [stateConstraint, constraint, shearSq] at hc
    linarith only [hc]
  have hden : 1 - x 0 ≠ 0 := by linarith only [hp]
  rw [restartProjectionHeight, hd, show 1 - (1 - (x 0) ^ 2) = (x 0) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_neg hp]
  change (1 - x 0 ^ 2) / (1 - x 0) = 1 + x 0
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.curvature_lower_of_active_dominance {n a b : ℝ} (ha : 0 < a)
    (hn : 0 ≤ n ∧ n ≤ a / 16) (hb : 0 ≤ b ∧ b ≤ a / 16) :
    3 / 4 * a ^ 2 ≤ curvature n a b := by
  have Hnb := mul_le_mul hn.2 hb.2 hb.1 (by positivity : 0 ≤ a / 16)
  have Hgap : 7 * a / 8 ≤ a - n - b := by linarith only [hn.2, hb.2]
  have Hsq := mul_self_le_mul_self (by positivity : 0 ≤ 7 * a / 8) Hgap
  unfold curvature
  nlinarith only [Hnb, Hsq]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartProjectionDefect {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t : ℝ} (H : HasDerivAt p v t) :
    HasDerivAt (fun x => restartProjectionDefect (p x))
      (restartProjectionDefectTangent (p t) v) t := by
  have Hn : HasDerivAt (fun x => (p x).1) v.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H
  have Hc (i : Fin 3) : HasDerivAt (fun x => (p x).2 i) (v.2 i) t := by
    let P : RestartCenterState →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact P.hasFDerivAt.comp_hasDerivAt t
      ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H)
  have HD := ((Hc 0).pow 2).add
    ((((Hn.pow 2).add ((Hc 1).pow 2)).add ((Hc 2).pow 2)).const_mul 2)
  have HD' := HD.sub (((Hn.add (Hc 1)).add (Hc 2)).pow 2)
  convert! HD' using 1
  · funext x
    dsimp [restartProjectionDefect, curvature]
    ring
  · dsimp [restartProjectionDefectTangent]
    ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionDefectTangent_bound {p v : RestartRadialState} {R D : ℝ}
    (hp : ‖p‖ ≤ R) (hv : ‖v‖ ≤ D) :
    |restartProjectionDefectTangent p v| ≤ 32 * R * D := by
  have hR : 0 ≤ R := (norm_nonneg p).trans hp
  have hD : 0 ≤ D := (norm_nonneg v).trans hv
  have pn : |p.1| ≤ R := (norm_fst_le p).trans hp
  have pc (i : Fin 3) : |p.2 i| ≤ R := (norm_le_pi_norm p.2 i).trans ((norm_snd_le p).trans hp)
  have vn : |v.1| ≤ D := (norm_fst_le v).trans hv
  have vc (i : Fin 3) : |v.2 i| ≤ D := (norm_le_pi_norm v.2 i).trans ((norm_snd_le v).trans hv)
  have ps : |p.1 + p.2 1 + p.2 2| ≤ 3 * R :=
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith only [pn, pc 1, pc 2])
  have vs : |v.1 + v.2 1 + v.2 2| ≤ 3 * D :=
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith only [vn, vc 1, vc 2])
  have Hsum : |p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2| ≤ 3 * R * D := by
    calc
      _ ≤ |p.1 * v.1| + |p.2 1 * v.2 1| + |p.2 2 * v.2 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ R * D + R * D + R * D := by
        simp only [abs_mul]
        gcongr
        · exact pc 1
        · exact vc 1
        · exact pc 2
        · exact vc 2
      _ = _ := by ring
  unfold restartProjectionDefectTangent
  calc
    _ ≤ |2 * p.2 0 * v.2 0| + |4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)| +
        |2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| := by
      have HT : |2 * p.2 0 * v.2 0 + 4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2) -
          2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| ≤
          |2 * p.2 0 * v.2 0 + 4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)| +
          |2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| := by
        simpa using (abs_sub_le (2 * p.2 0 * v.2 0 + 4 *
          (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)) 0
          (2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)))
      exact HT.trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * R * D + 4 * (3 * R * D) + 2 * (3 * R) * (3 * D) := by
      norm_num only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      gcongr
      · exact pc 0
      · exact vc 0
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionDefect_bounds {p : RestartRadialState} {r R : ℝ}
    (hr : 0 < r) (hp : ‖p‖ ≤ R) (ha : r / 2 ≤ p.2 1)
    (hn : 0 ≤ p.1 ∧ p.1 ≤ p.2 1 / 16) (hb : 0 ≤ p.2 2 ∧ p.2 2 ≤ p.2 1 / 16) :
    3 * r ^ 2 / 16 ≤ restartProjectionDefect p ∧ restartProjectionDefect p ≤ 10 * R ^ 2 := by
  have ha0 : 0 < p.2 1 := by linarith only [ha, hr]
  have hR : 0 ≤ R := (norm_nonneg p).trans hp
  have pn : |p.1| ≤ R := (norm_fst_le p).trans hp
  have pc (i : Fin 3) : |p.2 i| ≤ R := (norm_le_pi_norm p.2 i).trans ((norm_snd_le p).trans hp)
  constructor
  · have H := curvature_lower_of_active_dominance ha0 hn hb
    have Ha := pow_le_pow_left₀ (by positivity : 0 ≤ r / 2) ha 2
    dsimp only [restartProjectionDefect]
    nlinarith only [H, Ha, sq_nonneg (p.2 0)]
  · have H := (le_abs_self _).trans (curvature_abs_le_sum_sq hn.1 ha0.le hb.1)
    have Hs : (p.2 0) ^ 2 ≤ R ^ 2 := by nlinarith only [sq_abs (p.2 0), pow_le_pow_left₀ (abs_nonneg (p.2 0)) (pc 0) 2]
    have Hsum : p.1 + p.2 1 + p.2 2 ≤ 3 * R := by
      linarith only [(le_abs_self _).trans pn, (le_abs_self _).trans (pc 1), (le_abs_self _).trans (pc 2)]
    have Hsq := pow_le_pow_left₀ (add_nonneg (add_nonneg hn.1 ha0.le) hb.1) Hsum 2
    dsimp only [restartProjectionDefect]
    nlinarith only [H, Hs, Hsq]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionHeight_eq_sqrt {p : RestartRadialState}
    (hd : restartProjectionDefect p ≤ 1) :
    restartProjectionHeight p = 1 - Real.sqrt (1 - restartProjectionDefect p) := by
  have Hsq := Real.sq_sqrt (by linarith only [hd] : 0 ≤ 1 - restartProjectionDefect p)
  apply (div_eq_iff (by positivity : 1 + Real.sqrt (1 - restartProjectionDefect p) ≠ 0)).mpr
  nlinarith only [Hsq]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionHeight_bounds {p : RestartRadialState} {r R : ℝ}
    (hr : 0 < r) (hp : ‖p‖ ≤ R) (hR : R ≤ 1 / 16) (ha : r / 2 ≤ p.2 1)
    (hn : 0 ≤ p.1 ∧ p.1 ≤ p.2 1 / 16) (hb : 0 ≤ p.2 2 ∧ p.2 2 ≤ p.2 1 / 16) :
    (0 ≤ restartProjectionDefect p ∧ restartProjectionDefect p ≤ 1 / 2) ∧
      r ^ 2 / 16 ≤ restartProjectionHeight p ∧ restartProjectionHeight p ≤ 10 * R ^ 2 := by
  obtain ⟨Hlo, Hhi⟩ := restartProjectionDefect_bounds hr hp ha hn hb
  have hd0 : 0 ≤ restartProjectionDefect p := le_trans (by positivity) Hlo
  have hd1 : restartProjectionDefect p ≤ 1 / 2 := by
    have HR := (norm_nonneg p).trans hp
    nlinarith only [Hhi, hR, HR]
  have hsqrt := Real.sqrt_nonneg (1 - restartProjectionDefect p)
  have hsqrt1 : Real.sqrt (1 - restartProjectionDefect p) ≤ 1 := by
    rw [Real.sqrt_le_one]
    linarith only [hd0]
  have hden : 0 < 1 + Real.sqrt (1 - restartProjectionDefect p) := by positivity
  refine ⟨⟨hd0, hd1⟩, ?_, ?_⟩
  · apply (le_div_iff₀ hden).mpr
    have H := mul_le_mul_of_nonneg_left hsqrt1 (sq_nonneg r)
    nlinarith only [Hlo, H, sq_nonneg r]
  · apply (div_le_iff₀ hden).mpr
    nlinarith only [Hhi, mul_nonneg (sq_nonneg R) hsqrt]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartProjectionHeight {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t : ℝ} (H : HasDerivAt p v t)
    (hd : restartProjectionDefect (p t) < 1) :
    HasDerivAt (fun x => restartProjectionHeight (p x))
      (restartProjectionDefectTangent (p t) v / (2 * Real.sqrt (1 - restartProjectionDefect (p t)))) t := by
  have HD := hasDerivAt_restartProjectionDefect H
  have HS := ((HD.const_sub 1).sqrt (by linarith only [hd] : 1 - restartProjectionDefect (p t) ≠ 0)).const_sub 1
  have Heq : (fun x => restartProjectionHeight (p x)) =ᶠ[𝓝 t]
      fun x => 1 - Real.sqrt (1 - restartProjectionDefect (p x)) := by
    filter_upwards [HD.continuousAt.eventually (isOpen_Iio.mem_nhds hd)] with x hx
    exact restartProjectionHeight_eq_sqrt hx.le
  convert! HS.congr_of_eventuallyEq Heq using 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionHeight_derivative_bound {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t R D : ℝ} (H : HasDerivAt p v t)
    (hd : restartProjectionDefect (p t) ≤ 1 / 2) (hp : ‖p t‖ ≤ R) (hv : ‖v‖ ≤ D) :
    DifferentiableAt ℝ (fun x => restartProjectionHeight (p x)) t ∧
      |deriv (fun x => restartProjectionHeight (p x)) t| ≤ 32 * R * D := by
  have HD := hasDerivAt_restartProjectionHeight H (by linarith only [hd])
  refine ⟨HD.differentiableAt, ?_⟩
  rw [HD.deriv, abs_div, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt (1 - restartProjectionDefect (p t)))]
  have hsqrt : 1 / 2 ≤ Real.sqrt (1 - restartProjectionDefect (p t)) := by
    have Hsq := Real.sq_sqrt (by linarith only [hd] : 0 ≤ 1 - restartProjectionDefect (p t))
    nlinarith only [Hsq, Real.sqrt_nonneg (1 - restartProjectionDefect (p t)), hd]
  exact (div_le_self (abs_nonneg _) (by linarith only [hsqrt])).trans
    (restartProjectionDefectTangent_bound hp hv)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_restartRadialCurve (θ ζ ρ : ℝ) :
    HasDerivAt (restartRadialCurve θ ζ) (restartRadialDirection θ) ρ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [restartRadialCurve, restartRadialDirection] using (hasDerivAt_id ρ).const_mul θ
  · convert! hasDerivAt_id ρ using 1
  · simpa [restartRadialCurve, restartRadialDirection] using hasDerivAt_const ρ ζ

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartRadialCurve_annulus {r ρ θ ζ L : ℝ} (hr : 0 < r)
    (hρ : ρ ∈ Icc r (2 * r)) (hL : 0 ≤ L) (hθ : |θ| ≤ L)
    (hζ : 0 ≤ ζ ∧ ζ ≤ r / 9) :
    ‖restartRadialCurve θ ζ ρ‖ ≤ (2 * (L + 1)) * r ∧
      r / 2 ≤ restartRadialNorm (restartRadialCurve θ ζ ρ) := by
  have hρ0 : 0 < ρ := hr.trans_le hρ.1
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (2 * (L + 1)) * r)).mpr
    intro i
    fin_cases i
    · change |θ * ρ| ≤ _
      rw [abs_mul, abs_of_pos hρ0]
      have H := mul_le_mul hθ hρ.2 hρ0.le hL
      nlinarith only [H, hr]
    · change |ρ| ≤ _
      rw [abs_of_pos hρ0]
      nlinarith only [hρ.2, mul_nonneg hL hr.le]
    · change |ζ| ≤ _
      rw [abs_of_nonneg hζ.1]
      nlinarith only [hζ.2, hr, mul_nonneg hL hr.le]
  · have hdiff : 0 ≤ ρ - ζ := by linarith only [hρ.1, hζ.2, hr]
    have H := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg (θ * ρ)) :
      (ρ - ζ) ^ 2 ≤ (θ * ρ) ^ 2 + (ρ - ζ) ^ 2)
    rw [Real.sqrt_sq hdiff] at H
    change r / 2 ≤ Real.sqrt ((θ * ρ) ^ 2 + (ρ - ζ) ^ 2)
    linarith only [H, hρ.1, hζ.2, hr]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartFastEntry_control :
    ∃ C ≥ (32 : ℝ), ∀ h ∈ Ioc (0 : ℝ) (1 / (4 * C)),
      ∀ L : ℝ, 0 ≤ L → ∀ q : ℝ, 2 < q → ∃ rstar : ℝ, 0 < rstar ∧
        ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) →
          ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let Z := restartRadialCurve θ ζ ρ
            let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
            let p := restartSectionRadialState h T Z
            let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
            r ≤ 1 ∧ 8 * (L + 1) * r ≤ 1 / 16 ∧ 0 ≤ T ∧
            0 < restartSectionRadicand h Z ∧ T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧
            stateConstraint x = 1 ∧ x 0 ≤ -(15 / 16) ∧
            HasDerivAt (fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)) v ρ ∧
            0 < p.1 ∧ p.1 ≤ h * r ^ q ∧ ‖p‖ ≤ 8 * (L + 1) * r ∧ r / 2 ≤ p.2 1 ∧
            (0 ≤ p.2 2 ∧ p.2 2 ≤ 2 * ζ) ∧ p.1 ≤ p.2 1 / 16 ∧ p.2 2 ≤ p.2 1 / 16 ∧
            ‖v‖ ≤ 2 * (L + 1) ∧ |v.1| ≤ 2 * (L + 1) * p.1 / r ∧
            |v.2 2| ≤ 8 * C * (L + 1) * p.2 2 / r := by
  obtain ⟨C, hC, HC⟩ := exists_restartRadialCurve_control
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨C, hC, ?_⟩
  intro h hh L hL q hq
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hh.2
    linarith only [H]
  have hhsmall : h ≤ 1 / 16 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.1.le]
  let M := 8 * (L + 1)
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hL]
  have Hevent : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ((0 < r ∧ r ≤ 1) ∧ M * r ≤ 1 / 16 ∧ C * (M * r) * (q / 2 * Real.log (1 / r)) ≤ 1 / 8) ∧
      r * (q / 2 * Real.log (1 / r)) ≤ 1 := by
    filter_upwards [eventually_restart_cutoff_budget C (4 * (L + 1)) q,
      eventually_restart_cutoff_budget 1 1 q] with r H₁ H₂
    have heq : 2 * (4 * (L + 1)) * r = M * r := by dsimp only [M]; ring
    rw [heq] at H₁
    exact ⟨H₁, by nlinarith only [H₂.2.2]⟩
  obtain ⟨r₀, hr₀, Hr₀⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp Hevent
  refine ⟨min r₀ (1 / 64), lt_min hr₀ (by norm_num), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have Hr := Hr₀ ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have hrsmall : r ≤ 1 / 64 := hr.2.trans (min_le_right _ _)
  have hζsmall : 0 ≤ ζ ∧ ζ ≤ r / 9 := ⟨hζ.1, hζ.2.trans (by nlinarith only [hrsmall, hr.1])⟩
  let T := q / 2 * Real.log (1 / r)
  let Z := restartRadialCurve θ ζ ρ
  let p := restartSectionRadialState h T Z
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
  have hT : 0 ≤ T := mul_nonneg (by linarith only [hq] : 0 ≤ q / 2)
    (Real.log_nonneg ((le_div_iff₀ hr.1).mpr (by linarith only [Hr.1.1.2])))
  obtain ⟨Hcurve, hneg, hnpos, hnexp, hcenter, hactive, hweak, hcv, hnv, hwv⟩ :=
    HC h r T L hh.1 hCh Hr.1.1 hL Hr.1.2.1 hT Hr.1.2.2 Hr.2 θ ζ ρ hθ hζsmall hρ
  change 0 < p.1 at hnpos
  change p.1 ≤ h * Real.exp (-2 * T) at hnexp
  change ‖p.2‖ ≤ M * r at hcenter
  change r / 2 ≤ p.2 1 at hactive
  change 0 ≤ p.2 2 ∧ p.2 2 ≤ 2 * ζ at hweak
  change ∀ i : Fin 3, |v.2 i| ≤ 2 * (L + 1) at hcv
  change |v.1| ≤ 2 * (L + 1) * p.1 / r at hnv
  have he : Real.exp (-2 * T) = r ^ q := by
    rw [Real.rpow_def_of_pos hr.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  rw [he] at hnexp
  have hpower : r ^ q ≤ r ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 Hr.1.1.2 hq.le
  have hnsmall : p.1 ≤ r ^ 2 := hnexp.trans
    ((mul_le_mul_of_nonneg_left hpower hh.1.le).trans
      (mul_le_of_le_one_left (sq_nonneg r) (by linarith only [hhsmall])))
  have hnr : p.1 ≤ r := hnsmall.trans (by nlinarith only [hr.1, Hr.1.1.2])
  have hp : ‖p‖ ≤ M * r := by
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, abs_of_pos hnpos]
    exact ⟨hnr.trans (by nlinarith only [mul_le_mul_of_nonneg_right hM hr.1.le]), hcenter⟩
  have hv : ‖v‖ ≤ 2 * (L + 1) := by
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs]
    refine ⟨hnv.trans ?_, (pi_norm_le_iff_of_nonneg (by positivity)).mpr hcv⟩
    apply (div_le_iff₀ hr.1).mpr
    exact mul_le_mul_of_nonneg_left hnr (by positivity)
  have hZ := (restartRadialCurve_annulus hr.1 hρ hL hθ hζsmall).1
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rwa [abs_of_pos hh.1]) (by
      change ‖Z‖ ≤ 2 * (L + 1) * r at hZ
      have Hb : 8 * (L + 1) * r ≤ 1 / 16 := Hr.1.2.1
      linarith only [hZ, Hb])
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have hcon := (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hrad.le) hT).2.1
  refine ⟨Hr.1.1.2, Hr.1.2.1, hT, hrad, hdom, hcon, hneg, Hcurve, hnpos, hnexp, hp,
    hactive, hweak, ?_, ?_, hv, hnv, hwv⟩
  · nlinarith only [hnsmall, hactive, mul_le_mul_of_nonneg_right hrsmall hr.1.le]
  · have Hw := hweak.2.trans (mul_le_mul_of_nonneg_left hζ.2 (by norm_num))
    nlinarith only [Hw, hactive, mul_le_mul_of_nonneg_right hrsmall hr.1.le]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restartSectionProjectionHeight_eq {h T : ℝ} {Z : RestartCenterState}
    (hrad : 0 < restartSectionRadicand h Z) (hT : 0 ≤ T)
    (hneg : normalizedMaxCurve (restartSectionChart h Z) 0 T 0 < 0) :
    (fun W => restartProjectionHeight (restartSectionRadialState h T W)) =ᶠ[𝓝 Z]
      (fun W => 1 + normalizedMaxCurve (restartSectionChart h W) 0 T 0) := by
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have Hchart := (contDiffAt_restartSectionChart hrad 1).continuousAt
  have Hflow := (hasFDerivAt_normalizedMaxCurve_initial hdom).continuousAt.comp Hchart
  have Hcoord : ContinuousAt (fun W => normalizedMaxCurve (restartSectionChart h W) 0 T 0) Z :=
    (continuous_apply 0).continuousAt.comp Hflow
  have HR : ContinuousAt (restartSectionRadicand h) Z := by
    unfold restartSectionRadicand curvature
    fun_prop
  filter_upwards [HR.eventually (isOpen_Ioi.mem_nhds hrad),
    Hcoord.eventually (isOpen_Iio.mem_nhds hneg)] with W hW hN
  have HC := (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hW.le) hT).2.1
  exact restartProjectionHeight_of_constraint HC hN

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartFastProjectionHeight_bounds {h T θ ζ ρ r R D : ℝ} {v : RestartRadialState}
    (hrad : 0 < restartSectionRadicand h (restartRadialCurve θ ζ ρ)) (hT : 0 ≤ T)
    (hneg : normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 T 0 < 0)
    (H : HasDerivAt (fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)) v ρ)
    (hr : 0 < r) (hp : ‖restartSectionRadialState h T (restartRadialCurve θ ζ ρ)‖ ≤ R)
    (hR : R ≤ 1 / 16)
    (ha : r / 2 ≤ (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 1)
    (hn : 0 ≤ (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).1 ∧
      (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).1 ≤
        (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 1 / 16)
    (hb : 0 ≤ (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 2 ∧
      (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 2 ≤
        (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 1 / 16)
    (hv : ‖v‖ ≤ D) :
    DifferentiableAt ℝ (restartFastProjectionHeight h T θ ζ) ρ ∧
      r ^ 2 / 16 ≤ restartFastProjectionHeight h T θ ζ ρ ∧
      restartFastProjectionHeight h T θ ζ ρ ≤ 10 * R ^ 2 ∧
      |deriv (restartFastProjectionHeight h T θ ζ) ρ| ≤ 32 * R * D := by
  obtain ⟨Hd, Hlo, Hhi⟩ := restartProjectionHeight_bounds hr hp hR ha hn hb
  have Hgerm := (eventually_restartSectionProjectionHeight_eq hrad hT hneg).comp_tendsto
    (hasDerivAt_restartRadialCurve θ ζ ρ).continuousAt
  change (fun y => restartProjectionHeight (restartSectionRadialState h T (restartRadialCurve θ ζ y))) =ᶠ[𝓝 ρ]
    restartFastProjectionHeight h T θ ζ at Hgerm
  have HD := restartProjectionHeight_derivative_bound H Hd.2 hp hv
  have Hactual := HD.1.hasDerivAt.congr_of_eventuallyEq Hgerm.symm
  rw [Hgerm.eq_of_nhds] at Hlo Hhi
  exact ⟨Hactual.differentiableAt, Hlo, Hhi, by rw [Hactual.deriv]; exact HD.2⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_toProjectiveState {x : NormalizedState} (hA : 1 + x 0 ≠ 0) :
    coreAngle (toProjectiveState x 0) (toProjectiveState x 2) =
      Real.arsinh (((1 + x 0) / Real.sqrt 3 - x 1) / x 3) := by
  change Real.arsinh ((1 - Real.sqrt 3 * x 1 / (1 + x 0)) /
    (Real.sqrt 3 * x 3 / (1 + x 0))) = _
  congr 1
  have hsqrt : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  by_cases ha : x 3 = 0
  · simp [ha]
  · field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectiveEntry_bounds {x : NormalizedState} {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hsmall : M * r ≤ 1 / 16)
    (hAlo : r ^ 2 / 16 ≤ 1 + x 0) (hAhi : 1 + x 0 ≤ 10 * (M * r) ^ 2)
    (hs : |x 1| ≤ M * r) (ha : r / 2 ≤ x 3 ∧ x 3 ≤ M * r)
    (hn : 0 ≤ x 2) (hb : 0 ≤ x 4) :
    1 / (20 * M ^ 2 * r) ≤ toProjectiveState x 2 ∧
      toProjectiveState x 2 ≤ 32 * M / r ∧
      (0 ≤ toProjectiveState x 1 ∧ toProjectiveState x 1 ≤ 32 * x 2 / r ^ 2) ∧
      (0 ≤ toProjectiveState x 3 ∧ toProjectiveState x 3 ≤ 32 * x 4 / r ^ 2) ∧
      |coreAngle (toProjectiveState x 0) (toProjectiveState x 2)| ≤ Real.arsinh (4 * M) := by
  have hA : 0 < 1 + x 0 := lt_of_lt_of_le (by positivity) hAlo
  have ha0 : 0 < x 3 := by linarith only [hr, ha.1]
  have hM0 : 0 < M := by nlinarith only [ha.1, ha.2, hr]
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith only [hsqrtSq, hsqrt]
  have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith only [hsqrtSq, hsqrt]
  have Hcoord (u : ℝ) (hu : 0 ≤ u) :
      0 ≤ Real.sqrt 3 * u / (1 + x 0) ∧ Real.sqrt 3 * u / (1 + x 0) ≤ 32 * u / r ^ 2 := by
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 2 * u / (r ^ 2 / 16) :=
        div_le_div₀ (mul_nonneg (by norm_num) hu) (mul_le_mul_of_nonneg_right hsqrt2 hu) (by positivity) hAlo
      _ = _ := by ring
  refine ⟨?_, ?_, Hcoord (x 2) hn, Hcoord (x 4) hb, ?_⟩
  · change _ ≤ Real.sqrt 3 * x 3 / (1 + x 0)
    calc
      _ = (r / 2) / (10 * (M * r) ^ 2) := by field_simp; ring
      _ ≤ Real.sqrt 3 * x 3 / (1 + x 0) :=
        div_le_div₀ (by positivity) (by nlinarith only [ha.1, mul_le_mul_of_nonneg_right hsqrt1 ha0.le]) hA hAhi
  · exact (Hcoord (x 3) ha0.le).2.trans (by
      apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
      have heq : 32 * M / r * r ^ 2 = 32 * (M * r) := by field_simp
      rw [heq]
      linarith only [ha.2])
  · rw [coreAngle_toProjectiveState (ne_of_gt hA)]
    have HAr : 1 + x 0 ≤ M * r := by
      have H := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hM hr.le)
      nlinarith only [hAhi, H, mul_nonneg hM hr.le]
    have HAs : (1 + x 0) / Real.sqrt 3 ≤ M * r :=
      (div_le_self hA.le hsqrt1).trans HAr
    have Hnum : |(1 + x 0) / Real.sqrt 3 - x 1| ≤ 2 * M * r := by
      have H := abs_sub_le ((1 + x 0) / Real.sqrt 3) 0 (x 1)
      simp only [sub_zero, zero_sub, abs_neg, abs_of_pos (div_pos hA hsqrt)] at H
      linarith only [H, HAs, hs]
    have Harg : |((1 + x 0) / Real.sqrt 3 - x 1) / x 3| ≤ 4 * M := by
      rw [abs_div, abs_of_pos ha0]
      apply (div_le_iff₀ ha0).mpr
      nlinarith only [Hnum, mul_le_mul_of_nonneg_left ha.1 hM]
    apply abs_le.mpr
    constructor
    · rw [← Real.arsinh_neg]
      exact Real.arsinh_le_arsinh.mpr (abs_le.mp Harg).1
    · exact Real.arsinh_le_arsinh.mpr (abs_le.mp Harg).2

end
end

private theorem BianchiIX.differentiableAt_restartFastProjectiveEntry {h T θ ζ ρ : ℝ} {v : RestartRadialState}
    (H : HasDerivAt (fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)) v ρ)
    (HA : DifferentiableAt ℝ (restartFastProjectionHeight h T θ ζ) ρ)
    (hA : restartFastProjectionHeight h T θ ζ ρ ≠ 0) :
    DifferentiableAt ℝ (restartFastProjectiveEntry h T θ ζ) ρ := by
  have Hn : DifferentiableAt ℝ (fun y => (restartSectionRadialState h T (restartRadialCurve θ ζ y)).1) ρ :=
    ((ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt ρ H).differentiableAt
  have Hc (i : Fin 3) : DifferentiableAt ℝ
      (fun y => (restartSectionRadialState h T (restartRadialCurve θ ζ y)).2 i) ρ := by
    let P : RestartCenterState →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact (P.hasFDerivAt.comp_hasDerivAt ρ
      ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt ρ H)).differentiableAt
  apply differentiableAt_pi.mpr
  intro i
  fin_cases i
  · exact ((Hc 0).const_mul (Real.sqrt 3)).div HA hA
  · exact (Hn.const_mul (Real.sqrt 3)).div HA hA
  · exact ((Hc 1).const_mul (Real.sqrt 3)).div HA hA
  · exact ((Hc 2).const_mul (Real.sqrt 3)).div HA hA

private theorem BianchiIX.differentiableAt_restartFastCoreAngle {h T θ ζ ρ : ℝ}
    (H : DifferentiableAt ℝ (restartFastProjectiveEntry h T θ ζ) ρ)
    (hv : restartFastProjectiveEntry h T θ ζ ρ 2 ≠ 0) :
    DifferentiableAt ℝ (restartFastCoreAngle h T θ ζ) ρ :=
  (((differentiableAt_pi.mp H 0).const_sub 1).div (differentiableAt_pi.mp H 2) hv).arsinh

/-- Every projective entry value is obtained from the exact flow; the height also has its ordinary radial derivative bound. -/
theorem solution :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q : ℝ, 2 < q → ∃ rstar : ℝ, 0 < rstar ∧
        ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) →
          ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let M := 8 * (L + 1)
            let y := restartFastProjectiveEntry h T θ ζ ρ
            T ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            DifferentiableAt ℝ (restartFastProjectiveEntry h T θ ζ) ρ ∧
            DifferentiableAt ℝ (restartFastCoreAngle h T θ ζ) ρ ∧
            DifferentiableAt ℝ (restartFastProjectionHeight h T θ ζ) ρ ∧
            r ^ 2 / 16 ≤ restartFastProjectionHeight h T θ ζ ρ ∧
            restartFastProjectionHeight h T θ ζ ρ ≤ 10 * (M * r) ^ 2 ∧
            |deriv (restartFastProjectionHeight h T θ ζ) ρ| ≤ 64 * M * (L + 1) * r ∧
            2 ≤ y 2 ∧ 1 / (20 * M ^ 2 * r) ≤ y 2 ∧ y 2 ≤ 32 * M / r ∧
            (0 < y 1 ∧ y 1 ≤ 32 * h * r ^ (q - 2)) ∧
            (0 ≤ y 3 ∧ y 3 ≤ 64 * ζ / r ^ 2) ∧
            (0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 2048 * M * ζ / r ^ 3) ∧
            |restartFastCoreAngle h T θ ζ ρ| ≤ Real.arsinh (4 * M) := by
  obtain ⟨C, hC, HC⟩ := exists_restartFastEntry_control
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨1 / (4 * C), by positivity, ?_⟩
  intro h hh L hL q hq
  obtain ⟨r₀, hr₀, HR⟩ := HC h hh L hL q hq
  let M := 8 * (L + 1)
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨min r₀ (1 / (40 * M ^ 2)), lt_min hr₀ (by positivity), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  let T := q / 2 * Real.log (1 / r)
  let Z := restartRadialCurve θ ζ ρ
  let p := restartSectionRadialState h T Z
  let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
  let y := restartFastProjectiveEntry h T θ ζ ρ
  obtain ⟨_, hsmall, hT, hrad, hdom, _, hneg, Hcurve, hnpos, hnexp, hp, ha, hb, hnsmall, hbsmall, hv, _, _⟩ :=
    HR r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  obtain ⟨HAD, HAlo, HAhi, HAder⟩ := restartFastProjectionHeight_bounds hrad hT
    (by linarith only [hneg]) Hcurve hr.1 hp hsmall ha ⟨hnpos.le, hnsmall⟩ ⟨hb.1, hbsmall⟩ hv
  have hA : 0 < restartFastProjectionHeight h T θ ζ ρ := lt_of_lt_of_le (by positivity [hr.1]) HAlo
  have HYD := differentiableAt_restartFastProjectiveEntry Hcurve HAD (ne_of_gt hA)
  have Hs : |x 1| ≤ M * r :=
    (norm_le_pi_norm p.2 0).trans ((norm_snd_le p).trans hp)
  have Hahi : x 3 ≤ M * r :=
    (le_abs_self _).trans ((norm_le_pi_norm p.2 1).trans ((norm_snd_le p).trans hp))
  obtain ⟨HVlo, HVhi, HU, HW, Hangle⟩ := restartProjectiveEntry_bounds hr.1 hM.le hsmall HAlo HAhi Hs ⟨ha, Hahi⟩ hnpos.le hb.1
  change 1 / (20 * M ^ 2 * r) ≤ y 2 at HVlo
  change y 2 ≤ 32 * M / r at HVhi
  change 0 ≤ y 1 ∧ y 1 ≤ 32 * x 2 / r ^ 2 at HU
  change 0 ≤ y 3 ∧ y 3 ≤ 32 * x 4 / r ^ 2 at HW
  have HVtwo : 2 ≤ y 2 := by
    apply le_trans _ HVlo
    apply (le_div_iff₀ (by positivity [hr.1] : 0 < 20 * M ^ 2 * r)).mpr
    have H := (le_div_iff₀ (by positivity : 0 < 40 * M ^ 2)).mp (hr.2.trans (min_le_right _ _))
    nlinarith only [H]
  have HUpos : 0 < y 1 := by
    exact div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hnpos) hA
  have HUhi : y 1 ≤ 32 * h * r ^ (q - 2) := by
    calc
      _ ≤ 32 * (h * r ^ q) / r ^ 2 := HU.2.trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnexp (by norm_num)) (sq_nonneg r))
      _ = _ := by rw [Real.rpow_sub hr.1, Real.rpow_two]; ring
  have HWhi : y 3 ≤ 64 * ζ / r ^ 2 := HW.2.trans (by
    apply div_le_div_of_nonneg_right _ (sq_nonneg r)
    have Hb : x 4 ≤ 2 * ζ := hb.2
    linarith only [Hb])
  have Hp : y 2 * y 3 ≤ 2048 * M * ζ / r ^ 3 := by
    calc
      _ ≤ (32 * M / r) * (64 * ζ / r ^ 2) := mul_le_mul HVhi HWhi HW.1 (by positivity [hr.1])
      _ = _ := by ring
  have HZD := differentiableAt_restartFastCoreAngle HYD (by change y 2 ≠ 0; linarith only [HVtwo])
  refine ⟨hdom, HYD, HZD, HAD, HAlo, HAhi, ?_, HVtwo, HVlo, HVhi, ⟨HUpos, HUhi⟩,
    ⟨HW.1, HWhi⟩, ⟨mul_nonneg (by linarith only [HVtwo]) HW.1, Hp⟩, Hangle⟩
  calc
    _ ≤ 32 * (M * r) * (2 * (L + 1)) := HAder
    _ = _ := by ring
