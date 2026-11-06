-- Prove2me | solution 1 for BianchiIX.exists_era_bounded_phase_estimates
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:40:19.836833+00:00
-- url     : https://prove2.me/submissions/b2c6ed3f-b56d-4ada-ad03-30c6196aa82a

import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_coreRadiusReturn_exit_chart
import Theorems.Thm_BianchiIX_exists_core_itinerary
import Theorems.Thm_BianchiIX_exists_terminalNatural_bounded_phase_estimates
import Theorems.Thm_BianchiIX_positive_cone_transport
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
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
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.positive_scalar_cone_transport (L : (Fin 3 → ℝ) →L[ℝ] ℝ)
    {w : Fin 3 → ℝ} {a : Fin 2 → ℝ} {B : ℝ} (hw0 : 0 < w 0)
    (hw : ∀ i : Fin 2, |w i.succ| ≤ a i * w 0)
    (H : ∀ z : Fin 3 → ℝ, z 0 = 1 → (∀ i : Fin 2, |z i.succ| ≤ a i) →
      0 < L z ∧ |Real.log (L z)| ≤ B) :
    0 < L w ∧ |Real.log (L w)| ≤ |Real.log (w 0)| + B := by
  let D : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi (fun _ => L)
  have HD : ∀ z : Fin 3 → ℝ, z 0 = 1 → (∀ i : Fin 2, |z i.succ| ≤ a i) →
      0 < D z 0 ∧ |Real.log (D z 0)| ≤ B ∧
        ∀ i : Fin 2, |D z i.succ| ≤ 1 * D z 0 := by
    intro z hz0 hz
    obtain ⟨hp, hl⟩ := H z hz0 hz
    exact ⟨hp, hl, fun _ => by change |L z| ≤ 1 * L z; rw [abs_of_pos hp, one_mul]⟩
  have HT := positive_cone_transport D hw0 hw HD
  exact ⟨HT.1, HT.2.1⟩

end
end


/-- The complete actual era has positive bounded phase and controlled ordinary phase distortion. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C ≥ (1 : ℝ),
      ∀ (m : ℕ) (β : ℝ) (X : CoreAngleState), 0 < β → β < 1 / 2 →
        (0 < X 1 ∧ X 1 ≤ ε / X 0) → (0 < X 2 ∧ X 2 ≤ ε / X 0) →
        X 1 + X 2 ≤ ε * (β / 2) ^ (2 * J) →
        ((m : ℝ) + 1 + β ≤ X 0 / 2 ∧ X 0 / 2 ≤ (m : ℝ) + 2 - β) →
        C * (X 1 + X 2) < β / 4 →
        let Z := eraCoreExit m X
        let P := eraBoundedPhase η J m
        let x := axisCycle (fromProjectiveState (coreTailEntry Z))
        let T := terminalNaturalTime η J Z
        ContDiffAt ℝ 1 (eraCoreExit m) X ∧ ContDiffAt ℝ 1 P X ∧
        ContDiffAt ℝ 1 (terminalNaturalTime η J ∘ eraCoreExit m) X ∧
        ContDiffAt ℝ 1 (terminalNaturalState η J ∘ eraCoreExit m) X ∧
        (β / 2 < P X ∧ P X < 1 - β / 2) ∧
        |P X - (X 0 / 2 - ((m : ℝ) + 1))| ≤ C * (X 1 + X 2) ∧
        Nat.floor (X 0 / 2) = m + 1 ∧ 2 < terminalNaturalPhase η J Z ∧
        (∀ j ≤ m, coreRadiusReturnValid ((coreReflectionState coreRadiusReturnTime)^[j] X)) ∧
        (∀ j < m,
          let Y := (coreReflectionState coreRadiusReturnTime)^[j] X
          4 < coreReturnState coreRadiusReturnTime Y 0 ∧ 0 < coreReflectionTime Y ∧
          coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y) = projectiveReflection
            (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y))) ∧
        (2 < Z 0 ∧ Z 0 < 4) ∧
        coreTailEntry Z = projectiveOriginalFlow
          (coreRadiusEntry ((coreReflectionState coreRadiusReturnTime)^[m] X)) 0
          (coreRadiusReturnTime ((coreReflectionState coreRadiusReturnTime)^[m] X)) ∧
        IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
          projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} T ∧
        toProjectiveState (normalizedMaxCurve x 0 T) = terminalNaturalState η J Z ∧
        terminalNaturalState η J Z 2 = 1 ∧
        0 < normalizedEventRate projectiveActiveWall x 0 T ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (X 1) → |v 2| ≤ Real.sqrt (X 2) →
          0 < fderiv ℝ P X v ∧ |Real.log (2 * fderiv ℝ P X v)| ≤ C * Real.sqrt (X 1 + X 2) := by
  obtain ⟨δ, hδ, hδmax, HT⟩ := exists_terminalNatural_bounded_phase_estimates
  obtain ⟨εk, hεk, hεkmax, K, hK, HK⟩ := exists_core_itinerary
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨A, hA, εt, hεt, HA⟩ := HT η hη hηδ J hJ
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  let ε := min εk εt
  let C := K + A + 1
  have hε : 0 < ε := lt_min hεk hεt
  have hC : 1 ≤ C := by dsimp [C]; linarith only [hK, hA]
  have hKC : K ≤ C := by dsimp [C]; linarith only [hA]
  have hAC : A ≤ C := by dsimp [C]; linarith only [hK]
  refine ⟨ε, hε, (min_le_left _ _).trans hεkmax, C, hC, ?_⟩
  intro m β X hβ hβmax hu hw hsmall hphase hmargin Z P x T
  let b₀ := X 1 + X 2
  have hb₀ : 0 ≤ b₀ := add_nonneg hu.1.le hw.1.le
  have hk0 : 0 < X 0 := by nlinarith only [hphase.1, hβ, Nat.cast_nonneg (α := ℝ) m]
  have hscale : ε / X 0 ≤ εk / X 0 := div_le_div_of_nonneg_right (min_le_left _ _) hk0.le
  have hcoreSmall : K * b₀ < β / 2 :=
    ((mul_le_mul_of_nonneg_right hKC hb₀).trans_lt hmargin).trans (by linarith only [hβ])
  obtain ⟨Hall, Hconnections, hRband, hcount, hαband⟩ := HK m β X hβ hβmax
    ⟨hu.1, hu.2.trans hscale⟩ ⟨hw.1, hw.2.trans hscale⟩ hphase hcoreSmall
  obtain ⟨_, Hvalid, _, HF, _, Hwalls, Hb, Herr, HD⟩ := Hall m le_rfl
  change ContDiffAt ℝ 1 (eraCoreExit m) X at HF
  change (∀ i : Fin 2, 0 < Z i.succ) at Hwalls
  change Z 1 + Z 2 ≤ b₀ at Hb
  let α := (Z 0 - 2) / 2
  let b := Z 1 + Z 2
  change 3 * β / 4 < α ∧ α < 1 - 3 * β / 4 at hαband
  change 2 + 3 * β / 2 < Z 0 ∧ Z 0 < 4 - 3 * β / 2 at hRband
  have huZ : 0 < Z 1 := Hwalls 0
  have hwZ : 0 < Z 2 := Hwalls 1
  have hb : 0 < b := add_pos (Hwalls 0) (Hwalls 1)
  have hα : 0 < α ∧ α ≤ 1 := by
    constructor <;> linarith only [hαband.1, hαband.2, hβ]
  have hβα : β / 2 ≤ α := by linarith only [hαband.1, hβ]
  have hsmallT : b ≤ εt * α ^ (2 * J) := by
    calc
      _ ≤ b₀ := Hb
      _ ≤ ε * (β / 2) ^ (2 * J) := hsmall
      _ ≤ εt * α ^ (2 * J) := by gcongr; exact min_le_right _ _
  have hZ : Z = ![2 + 2 * α, Z 1, Z 2] := by
    funext i
    fin_cases i
    · change Z 0 = 2 + 2 * α
      dsimp [α]
      ring
    · rfl
    · rfl
  have Hterminal := HA α b (Z 1) (Z 2) hα hb hsmallT
    (by rw [abs_of_pos huZ, abs_of_pos hwZ]) huZ hwZ
  dsimp only at Hterminal
  rw [← hZ] at Hterminal
  obtain ⟨HQ, Htime, Hstate, Hfirst, Hactual, Hactive, Htrans, Hvalue, Hdiff⟩ := Hterminal
  have Hreg : ContDiffAt ℝ 1 P X := (HQ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp X HF
  have Htreg := (Htime.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp X HF
  have Hsreg := (Hstate.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp X HF
  have hvalue₀ : |P X - α| ≤ A * b₀ := Hvalue.trans (mul_le_mul_of_nonneg_left Hb hA0.le)
  have hδQ := abs_lt.mp ((hvalue₀.trans (mul_le_mul_of_nonneg_right hAC hb₀)).trans_lt hmargin)
  have hwindow : β / 2 < P X ∧ P X < 1 - β / 2 := by
    constructor <;> linarith only [hδQ.1, hδQ.2, hαband.1, hαband.2]
  have hR : |Z 0 - (X 0 - 2 * m)| ≤ K * b₀ :=
    (le_add_of_nonneg_left (abs_nonneg _)).trans Herr
  have hαerror : |α - (X 0 / 2 - ((m : ℝ) + 1))| ≤ (K / 2) * b₀ := by
    rw [show α - (X 0 / 2 - ((m : ℝ) + 1)) = (Z 0 - (X 0 - 2 * m)) / 2 by dsimp [α]; ring,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (div_le_div_of_nonneg_right hR (by norm_num)).trans_eq (by ring)
  have hphaseError : |P X - (X 0 / 2 - ((m : ℝ) + 1))| ≤ C * b₀ := by
    calc
      _ ≤ |P X - α| + |α - (X 0 / 2 - ((m : ℝ) + 1))| := abs_sub_le _ _ _
      _ ≤ A * b₀ + (K / 2) * b₀ := add_le_add hvalue₀ hαerror
      _ = (A + K / 2) * b₀ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith only [hK]) hb₀
  have hPpos : 0 < P X := (half_pos hβ).trans hwindow.1
  have hphasePos : 0 < terminalNaturalPhase η J Z := by
    by_contra! hn
    exact (not_le_of_gt hPpos) (div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 2) hn)
  have hnext : 2 < terminalNaturalPhase η J Z := by
    have Hlt : 2 / terminalNaturalPhase η J Z < 1 := hwindow.2.trans (by linarith only [hβ])
    simpa only [one_mul] using (div_lt_iff₀ hphasePos).mp Hlt
  have hRterminal : 2 < Z 0 ∧ Z 0 < 4 := by
    constructor <;> linarith only [hRband.1, hRband.2, hβ]
  have hb₀ε : b₀ ≤ ε := hsmall.trans (mul_le_of_le_one_right hε.le
    (pow_le_one₀ (half_pos hβ).le (by linarith only [hβmax])))
  have hbquarter : b ≤ 1 / 4 := Hb.trans (hb₀ε.trans
    (((min_le_left εk εt).trans hεkmax).trans (by norm_num)))
  have hchart := coreRadiusReturn_exit_chart Hvalid hRterminal.1.le
    ⟨huZ.le, (le_add_of_nonneg_right hwZ.le).trans hbquarter⟩
    ⟨hwZ.le, (le_add_of_nonneg_left huZ.le).trans hbquarter⟩
  have Hconnections' (j : ℕ) (hj : j < m) := Hconnections j hj
  have hgeometry : ∀ j < m,
      let Y := (coreReflectionState coreRadiusReturnTime)^[j] X
      4 < coreReturnState coreRadiusReturnTime Y 0 ∧ 0 < coreReflectionTime Y ∧
      coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y) = projectiveReflection
        (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y)) := by
    intro j hj Y
    obtain ⟨hR, ht, hactual⟩ := Hconnections' j hj
    dsimp only at hactual
    rw [Function.iterate_succ_apply'] at hactual
    exact ⟨by linarith only [hR, hβ], ht, hactual⟩
  refine ⟨HF, Hreg, Htreg, Hsreg, hwindow, hphaseError, hcount, hnext,
    fun j hj => (Hall j hj).2.1, hgeometry, hRterminal, hchart, Hfirst, Hactual, Hactive, Htrans, ?_⟩
  intro v hv0 hv1 hv2
  let w := fderiv ℝ (eraCoreExit m) X v
  obtain ⟨hw0, hwlog, hwcone⟩ := HD v hv0 hv1 hv2
  have Htransport := positive_scalar_cone_transport
    ((2 : ℝ) • fderiv ℝ (terminalNaturalBoundedPhase η J) Z) hw0 hwcone (by
      intro z hz0 hz
      obtain ⟨hp, _, hl⟩ := Hdiff z hz0 (hz 0) (hz 1)
      exact ⟨by change (0 : ℝ) < 2 * fderiv ℝ (terminalNaturalBoundedPhase η J) Z z; linarith only [hp], hl⟩)
  have hchain : fderiv ℝ P X v = fderiv ℝ (terminalNaturalBoundedPhase η J) Z w := by
    change fderiv ℝ (terminalNaturalBoundedPhase η J ∘ eraCoreExit m) X v = _
    rw [fderiv_comp X (HQ.differentiableAt (by norm_num)) (HF.differentiableAt (by norm_num)),
      ContinuousLinearMap.comp_apply]
  change 0 < 2 * fderiv ℝ (terminalNaturalBoundedPhase η J) Z w ∧
    |Real.log (2 * fderiv ℝ (terminalNaturalBoundedPhase η J) Z w)| ≤ |Real.log (w 0)| + A * Real.sqrt b at Htransport
  rw [hchain]
  refine ⟨by linarith only [Htransport.1], Htransport.2.trans ?_⟩
  calc
    _ ≤ K * Real.sqrt b₀ + A * Real.sqrt b₀ :=
      add_le_add hwlog (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt Hb) hA0.le)
    _ = (K + A) * Real.sqrt b₀ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.sqrt_nonneg _)
