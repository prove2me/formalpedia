-- Prove2me | solution 1 for BianchiIX.exists_coreReflection_prefix_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:36:40.651192+00:00
-- url     : https://prove2.me/submissions/688e805d-1aa9-4503-972e-ecd09a1ad07c

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_exists_coreReflection_step
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

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_iterate_along_orbit (f : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (Y : ℕ → Fin 3 → ℝ) (n : ℕ)
    (horbit : ∀ j < n, Y (j + 1) = f (Y j))
    (hreg : ∀ j < n, ContDiffAt ℝ 1 f (Y j)) :
    f^[n] (Y 0) = Y n ∧ ContDiffAt ℝ 1 (f^[n]) (Y 0) := by
  revert horbit hreg
  induction n with
  | zero => intro _ _; exact ⟨rfl, contDiffAt_id⟩
  | succ n ih =>
    intro horbit hreg
    obtain ⟨hy, hd⟩ := ih (fun j hj => horbit j (by omega)) (fun j hj => hreg j (by omega))
    have hfn : ContDiffAt ℝ 1 f (f^[n] (Y 0)) := by rw [hy]; exact hreg n (by omega)
    have hn : f^[n + 1] = f ∘ f^[n] := funext (Function.iterate_succ_apply' f n)
    rw [hn, Function.comp_apply, hy, ← horbit n (by omega)]
    exact ⟨rfl, hfn.comp _ hd⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.positive_cone_iterate (f : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (Y : ℕ → Fin 3 → ℝ) (a : ℕ → Fin 2 → ℝ) (L : ℕ → ℝ) (n : ℕ)
    (horbit : ∀ j < n, Y (j + 1) = f (Y j))
    (hreg : ∀ j < n, DifferentiableAt ℝ f (Y j))
    (H : ∀ j < n, ∀ z : Fin 3 → ℝ, z 0 = 1 → (∀ i : Fin 2, |z i.succ| ≤ a j i) →
      0 < fderiv ℝ f (Y j) z 0 ∧ |Real.log (fderiv ℝ f (Y j) z 0)| ≤ L j ∧
        ∀ i : Fin 2, |fderiv ℝ f (Y j) z i.succ| ≤ a (j + 1) i * fderiv ℝ f (Y j) z 0)
    {v : Fin 3 → ℝ} (hv0 : v 0 = 1) (hv : ∀ i : Fin 2, |v i.succ| ≤ a 0 i) :
    f^[n] (Y 0) = Y n ∧ DifferentiableAt ℝ (f^[n]) (Y 0) ∧
      let w := fderiv ℝ (f^[n]) (Y 0) v
      0 < w 0 ∧ |Real.log (w 0)| ≤ ∑ j ∈ Finset.range n, L j ∧
        ∀ i : Fin 2, |w i.succ| ≤ a n i * w 0 := by
  revert horbit hreg H
  induction n with
  | zero =>
    intro _ _ _
    simp only [Function.iterate_zero, fderiv_id, ContinuousLinearMap.id_apply,
      hv0, Real.log_one, abs_zero, Finset.range_zero, Finset.sum_empty, mul_one]
    exact ⟨rfl, differentiableAt_id, zero_lt_one, le_rfl, hv⟩
  | succ n ih =>
    intro horbit hreg H
    obtain ⟨hy, hd, hp, hl, hcone⟩ := ih
      (fun j hj => horbit j (by omega)) (fun j hj => hreg j (by omega))
      (fun j hj => H j (by omega))
    have hfn : DifferentiableAt ℝ f (f^[n] (Y 0)) := by rw [hy]; exact hreg n (by omega)
    have hn : f^[n + 1] = f ∘ f^[n] := funext (Function.iterate_succ_apply' f n)
    have hder : fderiv ℝ (f^[n + 1]) (Y 0) v =
        fderiv ℝ f (Y n) (fderiv ℝ (f^[n]) (Y 0) v) := by
      rw [hn, fderiv_comp _ hfn hd, ContinuousLinearMap.comp_apply, hy]
    have HT := positive_cone_transport (fderiv ℝ f (Y n)) hp hcone (H n (by omega))
    refine ⟨?_, ?_, ?_⟩
    · rw [hn, Function.comp_apply, hy, ← horbit n (by omega)]
    · rw [hn]
      exact hfn.comp _ hd
    · dsimp only
      rw [hder]
      refine ⟨HT.1, ?_, HT.2.2⟩
      rw [Finset.sum_range_succ]
      exact HT.2.1.trans (add_le_add hl le_rfl)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.affine_mul_exp_neg_le_one (x : ℝ) : (1 + x) * Real.exp (-x) ≤ 1 := by
  have H := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at H
  simpa only [add_comm] using H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.rpow_div_le_core_loss {a b k c p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hk : 2 ≤ k) (hc : 0 < c) (hp : 0 < p) (hdec : b ≤ Real.exp (-c / k) * a) :
    a ^ p / k ≤ (1 + p * c / 2) / (p * c) * (a ^ p - b ^ p) := by
  have hk0 : 0 < k := by linarith only [hk]
  have hpc : 0 < p * c := mul_pos hp hc
  have hz : 0 ≤ p * c / k := (div_pos hpc hk0).le
  have hpow : b ^ p ≤ Real.exp (-(p * c / k)) * a ^ p := by
    have H := Real.rpow_le_rpow hb hdec hp.le
    rw [Real.mul_rpow (Real.exp_pos _).le ha, ← Real.exp_mul] at H
    convert! H using 1
    congr 2
    ring
  have hab : b ^ p ≤ a ^ p := hpow.trans
    ((mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz))
      (Real.rpow_nonneg ha p)).trans_eq (one_mul _))
  have H := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 1 + p * c / k)
  have He := mul_le_mul_of_nonneg_right (affine_mul_exp_neg_le_one (p * c / k))
    (Real.rpow_nonneg ha p)
  have hpaid : (p * c / k) * a ^ p ≤ (1 + p * c / k) * (a ^ p - b ^ p) := by
    nlinarith only [H, He]
  have hzmax : p * c / k ≤ p * c / 2 :=
    div_le_div_of_nonneg_left hpc.le (by norm_num) hk
  have Hmax := mul_le_mul_of_nonneg_right (add_le_add_left hzmax 1) (sub_nonneg.mpr hab)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpc).mpr
  calc
    a ^ p / k * (p * c) = (p * c / k) * a ^ p := by ring
    _ ≤ (1 + p * c / k) * (a ^ p - b ^ p) := hpaid
    _ ≤ (1 + p * c / 2) * (a ^ p - b ^ p) := by simpa only [add_comm] using Hmax

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.sum_rpow_div_le_core_losses {a b k : ℕ → ℝ} {c p : ℝ}
    (hc : 0 < c) (hp : 0 < p) (n : ℕ)
    (ha : ∀ j ≤ n, 0 ≤ a j) (hk : ∀ j < n, 2 ≤ k j)
    (hdec : ∀ j < n, b j ≤ Real.exp (-c / k j) * a j)
    (hconn : ∀ j < n, a (j + 1) ≤ b j) :
    ∑ j ∈ Finset.range n, a j ^ p / k j ≤
      (1 + p * c / 2) / (p * c) * (a 0 ^ p - a n ^ p) := by
  let A := (1 + p * c / 2) / (p * c)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hstep (j : ℕ) (hj : j < n) : a j ^ p / k j ≤ A * (a j ^ p - a (j + 1) ^ p) := by
    have hnext : 0 ≤ a (j + 1) := ha _ (by omega)
    have H := rpow_div_le_core_loss (ha j hj.le) (hnext.trans (hconn j hj))
      (hk j hj) hc hp (hdec j hj)
    exact H.trans (mul_le_mul_of_nonneg_left
      (sub_le_sub_left (Real.rpow_le_rpow hnext (hconn j hj) hp.le) _) hA)
  have htel (m : ℕ) : ∑ j ∈ Finset.range m, (a j ^ p - a (j + 1) ^ p) = a 0 ^ p - a m ^ p := by
    induction m with
    | zero => simp
    | succ m hm => rw [Finset.sum_range_succ, hm]; ring
  calc
    _ ≤ ∑ j ∈ Finset.range n, A * (a j ^ p - a (j + 1) ^ p) :=
      Finset.sum_le_sum fun j hj => hstep j (Finset.mem_range.mp hj)
    _ = A * (a 0 ^ p - a n ^ p) := by rw [← Finset.mul_sum, htel]

end
end


/-- The actual finite core-reflection orbit pays for its phase and composite derivative errors by amplitude loss. -/
theorem solution :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), c ≤ 1 / 2 ∧
      ∀ (n : ℕ) (Y : ℕ → CoreAngleState),
        let F := coreReturnState coreRadiusReturnTime
        let G := coreReflectionState coreRadiusReturnTime
        let b := fun j => Y j 1 + Y j 2
        (0 < Y 0 1 ∧ Y 0 1 ≤ ε / Y 0 0) → (0 < Y 0 2 ∧ Y 0 2 ≤ ε / Y 0 0) →
        (∀ j < n, 2 ≤ Y j 0 ∧ 31 / 8 ≤ F (Y j) 0) →
        (∀ j < n, Y (j + 1) = G (Y j)) →
        (∀ j ≤ n, ∀ i : Fin 2, 0 < Y j i.succ) ∧
        (∀ p > (0 : ℝ), ∑ j ∈ Finset.range n, (b j) ^ p / Y j 0 ≤
          ((1 + p * c / 2) / (p * c)) * ((b 0) ^ p - (b n) ^ p)) ∧
        (∑ j ∈ Finset.range n, (|F (Y j) 0 - Y j 0| + |Y (j + 1) 0 - (F (Y j) 0 - 2)|)) ≤
          C * ((1 + c / 2) / c) * (b 0 - b n) ∧
        |Y n 0 - (Y 0 0 - 2 * n)| ≤ C * ((1 + c / 2) / c) * (b 0 - b n) ∧
        G^[n] (Y 0) = Y n ∧ (ContDiffAt ℝ 1 (G^[n]) (Y 0) ∧
          ∀ j < n, 0 < coreReflectionTime (Y j) ∧
            coreRadiusEntry (Y (j + 1)) = projectiveReflection
              (projectiveOriginalFlow (coreRadiusEntry (Y j)) 0 (coreReflectionTime (Y j)))) ∧
        (∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 0 1) → |v 2| ≤ Real.sqrt (Y 0 2) →
          let d := fderiv ℝ (G^[n]) (Y 0) v
          0 < d 0 ∧ |Real.log (d 0)| ≤
            C * ((1 + c / 4) / (c / 2)) * (Real.sqrt (b 0) - Real.sqrt (b n)) ∧
            ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (Y n i.succ) * d 0) ∧
        (2 ≤ Y n 0 →
          let Z := F (Y n)
          let B := Z 1 + Z 2
          let J := F ∘ G^[n]
          coreRadiusReturnValid (Y n) ∧ ContDiffAt ℝ 1 J (Y 0) ∧
          ContDiffAt ℝ 1 (coreRadiusReturnTime ∘ G^[n]) (Y 0) ∧
          (∀ i : Fin 2, 0 < Z i.succ) ∧ B ≤ b 0 ∧
          |Z 0 - (Y 0 0 - 2 * n)| ≤ C * ((1 + c / 2) / c) * (b 0 - B) ∧
          ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 0 1) → |v 2| ≤ Real.sqrt (Y 0 2) →
            let d := fderiv ℝ J (Y 0) v
            0 < d 0 ∧ |Real.log (d 0)| ≤
              C * ((1 + c / 4) / (c / 2)) * (Real.sqrt (b 0) - Real.sqrt B) ∧
              ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (Z i.succ) * d 0) := by
  obtain ⟨ε, hε, hεmax, C, hC, c, hc, hcmax, H⟩ := exists_coreReflection_step
  refine ⟨ε, hε, hεmax, C, hC, c, hc, hcmax, ?_⟩
  intro n Y F G b hu hw hphase horbit
  have hentry : ∀ j ≤ n, ∀ i : Fin 2,
      0 < Y j i.succ ∧ (2 ≤ Y j 0 → Y j i.succ ≤ ε / Y j 0) := by
    intro j
    induction j with
    | zero =>
      intro _ i
      fin_cases i
      · exact ⟨hu.1, fun _ => hu.2⟩
      · exact ⟨hw.1, fun _ => hw.2⟩
    | succ j ih =>
      intro hj i
      have hjn : j < n := by omega
      have hp := ih (by omega)
      obtain ⟨_, _, _, _, HS⟩ := H (Y j) (hphase j hjn).1
        ⟨(hp 0).1, (hp 0).2 (hphase j hjn).1⟩ ⟨(hp 1).1, (hp 1).2 (hphase j hjn).1⟩
      obtain ⟨_, _, _, _, _, _, _, hwall, hnext, _⟩ := HS (hphase j hjn).2
      rw [horbit j hjn]
      exact ⟨(hwall i).2.1, fun hk => hnext hk i⟩
  have HE (j : ℕ) (hj : j < n) := (H (Y j) (hphase j hj).1
    ⟨(hentry j hj.le 0).1, (hentry j hj.le 0).2 (hphase j hj).1⟩
    ⟨(hentry j hj.le 1).1, (hentry j hj.le 1).2 (hphase j hj).1⟩).2.2.2.2 (hphase j hj).2
  have hnonneg (j : ℕ) (hj : j ≤ n) : 0 ≤ b j :=
    add_nonneg (hentry j hj 0).1.le (hentry j hj 1).1.le
  have hdec (j : ℕ) (hj : j < n) : F (Y j) 1 + F (Y j) 2 ≤ Real.exp (-c / Y j 0) * b j := by
    obtain ⟨_, _, _, _, _, _, _, hwall, _, _⟩ := HE j hj
    simpa only [b, F, mul_add] using! add_le_add (hwall 0).2.2.2 (hwall 1).2.2.2
  have hconn (j : ℕ) (hj : j < n) : b (j + 1) ≤ F (Y j) 1 + F (Y j) 2 := by
    obtain ⟨_, _, _, _, _, _, _, hwall, _, _⟩ := HE j hj
    dsimp only [b]
    rw [horbit j hj]
    exact add_le_add (hwall 0).2.2.1 (hwall 1).2.2.1
  have hbudget (p : ℝ) (hp : 0 < p) := sum_rpow_div_le_core_losses
    (a := b) (b := fun j => F (Y j) 1 + F (Y j) 2) (k := fun j => Y j 0)
    hc hp n hnonneg (fun j hj => (hphase j hj).1) hdec hconn
  have hlinear : ∑ j ∈ Finset.range n, b j / Y j 0 ≤ ((1 + c / 2) / c) * (b 0 - b n) := by
    simpa only [Real.rpow_one, one_mul] using hbudget 1 zero_lt_one
  have hroot : ∑ j ∈ Finset.range n, Real.sqrt (b j) / Y j 0 ≤
      ((1 + c / 4) / (c / 2)) * (Real.sqrt (b 0) - Real.sqrt (b n)) := by
    have Hhalf := hbudget (1 / 2) (by norm_num)
    simpa only [← Real.sqrt_eq_rpow, show (1 / 2 : ℝ) * c = c / 2 by ring,
      show c / 2 / 2 = c / 4 by ring] using Hhalf
  have hsum : (∑ j ∈ Finset.range n, (|F (Y j) 0 - Y j 0| + |Y (j + 1) 0 - (F (Y j) 0 - 2)|)) ≤
      C * ((1 + c / 2) / c) * (b 0 - b n) := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, C * (b j / Y j 0) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn := Finset.mem_range.mp hj
        rw [horbit j hjn]
        exact (HE j hjn).2.2.2.2.1.trans_eq (by ring)
      _ = C * ∑ j ∈ Finset.range n, b j / Y j 0 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := (mul_le_mul_of_nonneg_left hlinear hC.le).trans_eq (by ring)
  have htel (m : ℕ) : ∑ j ∈ Finset.range m, (Y (j + 1) 0 - (Y j 0 - 2)) =
      Y m 0 - (Y 0 0 - 2 * m) := by
    induction m with
    | zero => simp
    | succ m hm => rw [Finset.sum_range_succ, hm, Nat.cast_add, Nat.cast_one]; ring
  have hphaseSum : |Y n 0 - (Y 0 0 - 2 * n)| ≤ C * ((1 + c / 2) / c) * (b 0 - b n) := by
    rw [← htel]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply LE.le.trans _ hsum
    apply Finset.sum_le_sum
    intro j _
    have heq : Y (j + 1) 0 - (Y j 0 - 2) =
        (F (Y j) 0 - Y j 0) + (Y (j + 1) 0 - (F (Y j) 0 - 2)) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hiter (v : CoreAngleState) (hv0 : v 0 = 1)
      (hv : ∀ i : Fin 2, |v i.succ| ≤ Real.sqrt (Y 0 i.succ)) :=
    positive_cone_iterate G Y (fun j i => Real.sqrt (Y j i.succ))
      (fun j => C * Real.sqrt (b j) / Y j 0) n horbit
      (fun j hj => (HE j hj).2.2.2.1.differentiableAt (by norm_num))
      (fun j hj z hz0 hz => by
        obtain ⟨_, _, _, _, _, _, _, _, _, HD⟩ := HE j hj
        simpa only [horbit j hj] using HD z hz0 (hz 0) (hz 1)) hv0 hv
  have hregular := contDiffAt_iterate_along_orbit G Y n horbit (fun j hj => (HE j hj).2.2.2.1)
  have hgeometry (j : ℕ) (hj : j < n) : 0 < coreReflectionTime (Y j) ∧
      coreRadiusEntry (Y (j + 1)) = projectiveReflection
        (projectiveOriginalFlow (coreRadiusEntry (Y j)) 0 (coreReflectionTime (Y j))) := by
    rw [horbit j hj]
    exact ⟨(HE j hj).1, (HE j hj).2.1⟩
  have hderiv (v : CoreAngleState) (hv0 : v 0 = 1) (hv1 : |v 1| ≤ Real.sqrt (Y 0 1))
      (hv2 : |v 2| ≤ Real.sqrt (Y 0 2)) :
      let d := fderiv ℝ (G^[n]) (Y 0) v
      0 < d 0 ∧ |Real.log (d 0)| ≤
        C * ((1 + c / 4) / (c / 2)) * (Real.sqrt (b 0) - Real.sqrt (b n)) ∧
        ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (Y n i.succ) * d 0 := by
    have hv (i : Fin 2) : |v i.succ| ≤ Real.sqrt (Y 0 i.succ) := by
      fin_cases i
      · exact hv1
      · exact hv2
    obtain ⟨_, _, hd0, hlog, hdcone⟩ := hiter v hv0 hv
    refine ⟨hd0, hlog.trans ?_, hdcone⟩
    calc
      _ = C * ∑ j ∈ Finset.range n, Real.sqrt (b j) / Y j 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hroot hC.le).trans_eq (by ring)
  refine ⟨fun j hj i => (hentry j hj i).1, hbudget, hsum, hphaseSum,
    hregular.1, ⟨hregular.2, hgeometry⟩, hderiv, ?_⟩
  intro hk Z B J
  obtain ⟨hvalid, hF, _, ⟨ht, hval, hwall, hdiff⟩, _⟩ := H (Y n) hk
    ⟨(hentry n le_rfl 0).1, (hentry n le_rfl 0).2 hk⟩
    ⟨(hentry n le_rfl 1).1, (hentry n le_rfl 1).2 hk⟩
  have hB : 0 ≤ B := add_nonneg (hwall 0).1.le (hwall 1).1.le
  have hlast : B ≤ Real.exp (-c / Y n 0) * b n := by
    simpa only [B, Z, F, b, mul_add] using! add_le_add (hwall 0).2 (hwall 1).2
  have hBnext : B ≤ b n := hlast.trans
    ((mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (by linarith only [hk])))
      (hnonneg n le_rfl)).trans_eq (one_mul _))
  have hbn : b n ≤ b 0 := by
    have hs : 0 ≤ ∑ j ∈ Finset.range n, b j / Y j 0 := Finset.sum_nonneg (by
      intro j hj
      have hjn := Finset.mem_range.mp hj
      exact div_nonneg (hnonneg j hjn.le) (by linarith only [(hphase j hjn).1]))
    have hA : 0 < (1 + c / 2) / c := by positivity
    nlinarith only [hs.trans hlinear, hA]
  have hfinal (p : ℝ) (hp : 0 < p) := rpow_div_le_core_loss (hnonneg n le_rfl) hB hk hc hp hlast
  have hlastLinear : b n / Y n 0 ≤ ((1 + c / 2) / c) * (b n - B) := by
    simpa only [Real.rpow_one, one_mul] using hfinal 1 zero_lt_one
  have hlastRoot : Real.sqrt (b n) / Y n 0 ≤
      ((1 + c / 4) / (c / 2)) * (Real.sqrt (b n) - Real.sqrt B) := by
    simpa only [← Real.sqrt_eq_rpow, show (1 / 2 : ℝ) * c = c / 2 by ring,
      show c / 2 / 2 = c / 4 by ring] using hfinal (1 / 2) (by norm_num)
  have hF' : ContDiffAt ℝ 1 F (G^[n] (Y 0)) := by rw [hregular.1]; exact hF
  have ht' : ContDiffAt ℝ 1 coreRadiusReturnTime (G^[n] (Y 0)) := by rw [hregular.1]; exact ht
  have hlastValue : |Z 0 - Y n 0| ≤ C * ((1 + c / 2) / c) * (b n - B) := by
    calc
      _ ≤ C * (b n / Y n 0) := hval.trans_eq (by ring)
      _ ≤ _ := (mul_le_mul_of_nonneg_left hlastLinear hC.le).trans_eq (by ring)
  refine ⟨hvalid, hF'.comp _ hregular.2, ht'.comp _ hregular.2,
    fun i => (hwall i).1, hBnext.trans hbn, ?_, ?_⟩
  · calc
      _ ≤ |Z 0 - Y n 0| + |Y n 0 - (Y 0 0 - 2 * n)| := abs_sub_le _ _ _
      _ ≤ C * ((1 + c / 2) / c) * (b n - B) +
          C * ((1 + c / 2) / c) * (b 0 - b n) := add_le_add hlastValue hphaseSum
      _ = _ := by ring
  · intro v hv0 hv1 hv2 d
    obtain ⟨hp, hl, hcone⟩ := hderiv v hv0 hv1 hv2
    have HT := positive_cone_transport (fderiv ℝ F (Y n)) hp hcone
      (fun z hz0 hz => hdiff z hz0 (hz 0) (hz 1))
    have hd : d = fderiv ℝ F (Y n) (fderiv ℝ (G^[n]) (Y 0) v) := by
      change fderiv ℝ (F ∘ G^[n]) (Y 0) v = _
      rw [fderiv_comp _ (hF'.differentiableAt (by norm_num))
        (hregular.2.differentiableAt (by norm_num)), ContinuousLinearMap.comp_apply, hregular.1]
    rw [hd]
    refine ⟨HT.1, HT.2.1.trans ?_, HT.2.2⟩
    have hpaid : C * Real.sqrt (b n) / Y n 0 ≤
        C * ((1 + c / 4) / (c / 2)) * (Real.sqrt (b n) - Real.sqrt B) := by
      calc
        _ = C * (Real.sqrt (b n) / Y n 0) := by ring
        _ ≤ _ := (mul_le_mul_of_nonneg_left hlastRoot hC.le).trans_eq (by ring)
    exact (add_le_add hl hpaid).trans_eq (by ring)
