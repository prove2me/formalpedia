-- Prove2me | solution 1 for BianchiIX.exists_normalized_exit_prefix_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T18:03:30.595341+00:00
-- url     : https://prove2.me/submissions/90bca951-8343-4b2d-9f09-886eb55caf5f

import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_exists_Ioo_covering_Icc
import Theorems.Thm_BianchiIX_exists_exitTail_scale_bounds
import Theorems.Thm_BianchiIX_exists_scaled_exitLog_reparametrization
import Theorems.Thm_BianchiIX_hasDerivAt_toExitTailState
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.Real.Lemmas

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_Ioo_covering_of_eventually {s t : ℝ} {P : ℝ → Prop} (hst : s ≤ t)
    (hP : ∀ u ∈ Icc s t, ∀ᶠ v in 𝓝 u, P v) :
    ∃ l r : ℝ, l < s ∧ t < r ∧ ∀ u ∈ Ioo l r, P u := by
  obtain ⟨l, r, hls, htr, hsub⟩ := exists_Ioo_covering_Icc hst isOpen_interior
    (fun u hu => mem_interior_iff_mem_nhds.mpr (hP u hu))
  exact ⟨l, r, hls, htr, fun u hu => interior_subset (hsub hu)⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exp_neg_exitTailLength {η α : ℝ} (hη : 0 < η) (hα : 0 < α) (J : ℕ) :
    Real.exp (-exitTailLength η α J) = η * α ^ J := by
  simp only [exitTailLength, one_div, Real.log_inv]
  rw [show -(-Real.log η + (J : ℝ) * -Real.log α) = Real.log η + J * Real.log α by ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_log hη, Real.exp_log hα]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_of_coreRadius {m v : ℝ} (hm : m < 1) :
    exitTailGap (coreRadius m v) v = 1 - m := by
  unfold exitTailGap
  rw [coreRadius_sq]
  dsimp only [coreEnergy]
  rw [add_sub_cancel_right, Real.sqrt_sq_eq_abs, abs_of_neg (by linarith only [hm] : m - 1 < 0)]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_compact {R v : ℝ} (hR : 7 / 4 ≤ R) (hv : 0 ≤ v ∧ v ≤ 1) :
    1 ≤ exitTailGap R v ∧ exitTailGap R v ≤ R := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith only [hv.1, hv.2]
  refine ⟨?_, ?_⟩
  · exact (Real.le_sqrt (by norm_num) (by nlinarith only [hR, hv2])).mpr
      (by nlinarith only [hR, hv2])
  · exact (Real.sqrt_le_left hR0).mpr (by nlinarith only [sq_nonneg v])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTail_coupling_bound {u v w : ℝ} (hv : 0 ≤ v) :
    |coupling u v w| ≤ |u| * v + (|u| + |w|) ^ 2 := by
  have H : |v + w - u| ≤ v + |w| + |u| := by
    exact (abs_sub _ _).trans (add_le_add ((abs_add_le v w).trans_eq (by rw [abs_of_nonneg hv])) le_rfl)
  rw [coupling, abs_mul]
  have H' := mul_le_mul_of_nonneg_left H (abs_nonneg u)
  nlinarith only [H', mul_nonneg (abs_nonneg u) (abs_nonneg w), sq_nonneg |w|]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailSpeed_compact {R u v w : ℝ} (hR : 7 / 4 ≤ R)
    (hu : |u| ≤ 1 / 100) (hv : 0 ≤ v ∧ v ≤ 1) (hw : |w| ≤ 1 / 100) :
    1 / 2 ≤ exitTailSpeed R u v w := by
  have ht := (exitTailGap_compact hR hv).1
  have hc := exitTail_coupling_bound (u := u) (w := w) hv.1
  have huv : |u| * v ≤ 1 / 100 := by
    nlinarith only [mul_le_mul_of_nonneg_left hv.2 (abs_nonneg u), hu]
  have hb : (|u| + |w|) ^ 2 ≤ (1 / 50 : ℝ) ^ 2 := by
    nlinarith only [hu, hw, abs_nonneg u, abs_nonneg w]
  have H := neg_abs_le (coupling u v w)
  dsimp only [exitTailSpeed]
  linarith only [ht, hc, huv, hb, H]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiff_exitClockRate (n : WithTop ℕ∞) : ContDiff ℝ n exitClockRate := by
  unfold exitClockRate coupling
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_normalized_exitLog_reparametrization {x : NormalizedState} {t₀ s : ℝ}
    {I : Set ℝ} (hI : Convex ℝ I) (ho : IsOpen I) (hs : s ∈ I)
    (hdom : I ⊆ normalizedMaxDomain x t₀) (hc : stateConstraint x = 1)
    (hA : ∀ t ∈ I, 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (hv : ∀ t ∈ I, 0 < toProjectiveState (normalizedMaxCurve x t₀ t) 2)
    (hD : ∀ t ∈ I, 0 < exitClockRate (toProjectiveState (normalizedMaxCurve x t₀ t))) :
    let β := fun t => toProjectiveState (normalizedMaxCurve x t₀ t)
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = I ∧
      (∀ t ∈ I, e t = Real.log (β s 2) - Real.log (β t 2)) ∧
      Convex ℝ e.target ∧ 0 ∈ e.target ∧ e.symm 0 = s ∧ StrictMonoOn e I ∧
      (∀ z ∈ e.target,
        HasDerivAt e.symm (1 / ((1 + normalizedMaxCurve x t₀ (e.symm z) 0) *
          exitClockRate (β (e.symm z)))) z ∧
        β (e.symm z) 2 = β s 2 * Real.exp (-z) ∧
        HasDerivAt (fun u => β (e.symm u)) (exitLogField (β (e.symm z))) z) := by
  apply exists_scaled_exitLog_reparametrization
    (a := fun t => 1 + normalizedMaxCurve x t₀ t 0) hI ho hs ?_ hA ?_ hv hD
  · intro t ht
    exact (continuousAt_const.add (hasDerivAt_pi.mp
      (hasDerivAt_normalizedMaxCurve (hdom ht)) 0).continuousAt).continuousWithinAt
  · intro t ht
    exact hasDerivAt_toProjectiveState_normalized (hasDerivAt_normalizedMaxCurve (hdom ht))
      (ne_of_gt (hA t ht)) ((normalizedMaxCurve_constraint (hdom ht)).trans hc)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitClockRate_tail {y : ProjectiveState} (hm : y 0 < 1) :
    exitClockRate y = exitTailSpeed (coreRadius (y 0) (y 2)) (y 1) (y 2) (y 3) := by
  dsimp only [exitClockRate, exitTailSpeed]
  rw [exitTailGap_of_coreRadius hm]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitClockRate_compact {y : ProjectiveState} (hm : y 0 < 1)
    (hR : 7 / 4 ≤ coreRadius (y 0) (y 2))
    (hu : |y 1| ≤ 1 / 100) (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : |y 3| ≤ 1 / 100) :
    1 / 2 ≤ exitClockRate y := by
  rw [exitClockRate_tail hm]
  exact exitTailSpeed_compact hR hu hv hw

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitPhysicalRegion_clock {h : ℝ} {y : ProjectiveState} (hh : 0 < h)
    (hy : exitPhysicalRegion h y) : 1 / 2 ≤ exitClockRate y :=
  exitClockRate_compact (lt_of_le_of_lt hy.1 (by norm_num)) hy.2.1.1 hy.2.2.1
    ⟨(hh.trans_le hy.2.2.2.1.1).le, hy.2.2.2.1.2⟩ hy.2.2.2.2

end
end

private theorem BianchiIX.exists_normalized_exit_regular_interval {x : NormalizedState} {t₀ s t : ℝ}
    (hst : s ≤ t) (hdom : Icc s t ⊆ normalizedMaxDomain x t₀)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0)
    (hv : ∀ u ∈ Icc s t, 0 < toProjectiveState (normalizedMaxCurve x t₀ u) 2)
    (hM : ∀ u ∈ Icc s t, toProjectiveState (normalizedMaxCurve x t₀ u) 0 < 1)
    (hD : ∀ u ∈ Icc s t, 0 < exitClockRate (toProjectiveState (normalizedMaxCurve x t₀ u))) :
    ∃ l r : ℝ, l < s ∧ t < r ∧ ∀ u ∈ Ioo l r,
      u ∈ normalizedMaxDomain x t₀ ∧ 0 < 1 + normalizedMaxCurve x t₀ u 0 ∧
      0 < toProjectiveState (normalizedMaxCurve x t₀ u) 2 ∧
      toProjectiveState (normalizedMaxCurve x t₀ u) 0 < 1 ∧
      0 < exitClockRate (toProjectiveState (normalizedMaxCurve x t₀ u)) := by
  apply exists_Ioo_covering_of_eventually hst
  intro u hu
  have hα := (hasDerivAt_normalizedMaxCurve (hdom hu)).continuousAt
  have hAc : ContinuousAt (fun v => 1 + normalizedMaxCurve x t₀ v 0) u :=
    continuousAt_const.add ((continuous_apply 0).continuousAt.comp hα)
  have hβ : ContinuousAt (fun v => toProjectiveState (normalizedMaxCurve x t₀ v)) u :=
    (contDiffAt_toProjectiveState 1 (ne_of_gt (hA u hu))).continuousAt.comp hα
  have hvc := (continuous_apply (2 : Fin 4)).continuousAt.comp hβ
  have hmc := (continuous_apply (0 : Fin 4)).continuousAt.comp hβ
  have hDc := (contDiff_exitClockRate 1).continuous.continuousAt.comp hβ
  have hmem : ∀ᶠ v in 𝓝 u, v ∈ normalizedMaxDomain x t₀ :=
    (isOpen_normalizedMaxDomain x t₀).mem_nhds (hdom hu)
  exact hmem.and ((hAc.eventually (isOpen_Ioi.mem_nhds (hA u hu))).and
    ((hvc.eventually (isOpen_Ioi.mem_nhds (hv u hu))).and
      ((hmc.eventually (isOpen_Iio.mem_nhds (hM u hu))).and
        (hDc.eventually (isOpen_Ioi.mem_nhds (hD u hu))))))


/-- Uniform signed tail estimates applied to actual normalized-flow prefixes. -/
theorem solution {η : ℝ} (hη : 0 < η ∧ η ≤ 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ A ≥ (2 : ℝ), ∃ ε > (0 : ℝ), ∀ (x : NormalizedState) (t₀ s t α b : ℝ),
      stateConstraint x = 1 → t₀ ≤ s → s ≤ t → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ J →
      (∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) →
      let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
      (∀ u ∈ Icc s t, exitPhysicalRegion (η * α ^ J) (β u)) → β s 2 = 1 →
      coreRadius (β s 0) (β s 2) = 2 + 2 * α → |β s 1| + |β s 3| ≤ b →
      |β t 1| + |β t 3| ≤ A * b / 2 ∧
      |coreRadius (β t 0) (β t 2) - coreRadius (β s 0) (β s 2)| ≤ 40 * A * b ∧
      2 + α < coreRadius (β t 0) (β t 2) ∧ |β t 1| ≤ β t 2 / 2 := by
  obtain ⟨A, hA, ε, hε, HP⟩ := exists_exitTail_scale_bounds hη hJ
  refine ⟨A, hA, ε, hε, ?_⟩
  intro x t₀ s t α b hc hs hst hα hb hsmall hAflow β hregion hV hR hw
  have hh : 0 < η * α ^ J := mul_pos hη.1 (pow_pos hα.1 J)
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have htm : t ∈ Icc s t := ⟨hst, le_rfl⟩
  have hdom : Icc s t ⊆ normalizedMaxDomain x t₀ := fun u hu =>
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1)
  have hv (u : ℝ) (hu : u ∈ Icc s t) : 0 < β u 2 := hh.trans_le (hregion u hu).2.2.2.1.1
  have hm (u : ℝ) (hu : u ∈ Icc s t) : β u 0 < 1 := lt_of_le_of_lt (hregion u hu).1 (by norm_num)
  have hd (u : ℝ) (hu : u ∈ Icc s t) : 0 < exitClockRate (β u) := by
    have H := exitPhysicalRegion_clock hh (hregion u hu)
    linarith only [H]
  obtain ⟨l, r, hls, htr, hregular⟩ := exists_normalized_exit_regular_interval hst hdom hAflow hv hm hd
  have hcover : Icc s t ⊆ Ioo l r := fun u hu => ⟨hls.trans_le hu.1, hu.2.trans_lt htr⟩
  have hsI := hcover hsm
  have htI := hcover htm
  obtain ⟨e, hsrc, heq, htarget, hzero, hinv0, hmono, hflow⟩ :=
    exists_normalized_exitLog_reparametrization (convex_Ioo l r) isOpen_Ioo hsI
      (fun u hu => (hregular u hu).1) hc (fun u hu => (hregular u hu).2.1)
      (fun u hu => (hregular u hu).2.2.1) (fun u hu => (hregular u hu).2.2.2.2)
  have htE : t ∈ e.source := by rwa [hsrc]
  have hes : e s = 0 := by rw [heq s hsI]; exact sub_self _
  have het : e t = -Real.log (β t 2) := by
    rw [heq t htI]
    change Real.log (β s 2) - Real.log (β t 2) = _
    rw [hV, Real.log_one, zero_sub]
  have hEt : 0 ≤ e t := by simpa only [hes] using hmono.monotoneOn hsI htI hst
  have hEL : e t ≤ exitTailLength η α J := by
    have H := Real.log_le_log hh (hregion t htm).2.2.2.1.1
    rw [← exp_neg_exitTailLength hη.1 hα.1 J, Real.log_exp] at H
    rw [het]
    linarith only [H]
  have hzt (z : ℝ) (hz : z ∈ Icc 0 (e t)) : z ∈ e.target :=
    htarget.ordConnected.out hzero (e.map_source htE) hz
  have hinv (z : ℝ) (hz : z ∈ Icc 0 (e t)) : e.symm z ∈ Icc s t := by
    have hzT := hzt z hz
    have hxI : e.symm z ∈ Ioo l r := by rw [← hsrc]; exact e.map_target hzT
    constructor
    · apply (hmono.le_iff_le hsI hxI).mp
      rw [hes, e.right_inv hzT]
      exact hz.1
    · apply (hmono.le_iff_le hxI htI).mp
      rw [e.right_inv hzT]
      exact hz.2
  let Y : ℝ → ExitTailState := fun z => toExitTailState (β (e.symm z))
  have hval (z : ℝ) (hz : z ∈ Icc 0 (e t)) : β (e.symm z) 2 = Real.exp (-z) := by
    have H := (hflow z (hzt z hz)).2.1
    change β (e.symm z) 2 = β s 2 * Real.exp (-z) at H
    simpa only [hV, one_mul] using H
  have hY (z : ℝ) (hz : z ∈ Icc 0 (e t)) : HasDerivAt Y (exitTailField (Real.exp (-z)) (Y z)) z := by
    have H := hasDerivAt_toExitTailState (hflow z (hzt z hz)).2.2
      (hv _ (hinv z hz)) (hm _ (hinv z hz))
    change HasDerivAt Y (exitTailField (β (e.symm z) 2) (Y z)) z at H
    rwa [hval z hz] at H
  have HY0 : Y 0 = toExitTailState (β s) := by dsimp only [Y]; rw [hinv0]
  have HYt : Y (e t) = toExitTailState (β t) := by dsimp only [Y]; rw [e.left_inv htE]
  have H := HP α b (e t) Y hα hb hsmall ⟨hEt, hEL⟩
    (by rw [HY0]; exact hR) (by rw [HY0]; exact hw) hY (e t) ⟨hEt, le_rfl⟩
  have Hvt : β t 2 = Real.exp (-(e t)) := by simpa only [e.left_inv htE] using hval (e t) ⟨hEt, le_rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have Hs := H.2.2.1
    rw [HYt] at Hs
    exact Hs
  · have Hr := H.2.2.2.1
    rw [HYt, HY0] at Hr
    exact Hr
  · have Hr := H.2.2.2.2.1
    rw [HYt] at Hr
    exact Hr
  · have Hu := H.2.2.2.2.2
    rw [HYt, ← Hvt] at Hu
    exact Hu
