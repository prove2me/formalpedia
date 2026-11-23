-- Prove2me | solution 1 for CalibeatBandit.Supplement.bernstein_abs_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T19:01:10.409817+00:00
-- url     : https://prove2.me/submissions/bce19175-1db5-4d88-b3fd-115c9b901957

import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Tactic
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_CalibeatBandit_rewardLoss
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_Supplement_robustPolicy
import Definitions.Def_CalibeatBandit_pseudoRewardLoss
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Definitions.Def_CalibeatBandit_etaStar
import Definitions.Def_CalibeatBandit_rT
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Mul
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_algState
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CalibeatBandit_HSRof
import Definitions.Def_CalibeatBandit_HRecOf
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Definitions.Def_CalibeatBandit_IsCalibeating
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_CalibeatBandit_Supplement_IsRobust

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

theorem integrable_of_abs_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hm : Measurable f) {B : ℝ}
    (hb : ∀ ω, |f ω| ≤ B) : Integrable f P :=
  (integrable_const B).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hb ω)

theorem integral_exp_sum_le_one {T : ℕ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (info preDraw : ℕ → MeasurableSpace Ω)
    (hinfo : ∀ a b, a ≤ b → b ≤ T → info a ≤ info b)
    (hinfo_le : ∀ n ≤ T, info n ≤ mΩ)
    (hpre : ∀ n < T, preDraw n ≤ mΩ)
    (hprev : ∀ n < T, info n ≤ preDraw n)
    (d : ℕ → Ω → ℝ) {B : ℝ}
    (hm : ∀ t < T, Measurable[info (t + 1)] (d t))
    (hb : ∀ t < T, ∀ ω, |d t ω| ≤ B)
    (hc : ∀ t < T, condExp (preDraw t) P (fun ω => Real.exp (d t ω)) ≤ᵐ[P] fun _ => 1) :
    ∫ ω, Real.exp (∑ t ∈ Finset.range T, d t ω) ∂P ≤ 1 := by
  let F (n : ℕ) (ω : Ω) := Real.exp (∑ t ∈ Finset.range n, d t ω)
  have hF (n : ℕ) (hn : n ≤ T) : Measurable[info n] (F n) := by
    refine Real.continuous_exp.measurable.comp (Finset.measurable_sum _ fun t ht => ?_)
    have hs := Nat.succ_le_of_lt (Finset.mem_range.mp ht)
    exact (hm t (lt_of_lt_of_le (Finset.mem_range.mp ht) hn)).mono
      (hinfo _ _ hs hn) le_rfl
  have hi (n : ℕ) (hn : n ≤ T) : Integrable (F n) P := by
    apply integrable_of_abs_bound ((hF n hn).mono (hinfo_le n hn) le_rfl)
    intro ω
    rw [show F n ω = Real.exp (∑ t ∈ Finset.range n, d t ω) from rfl,
      abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ∑ _ ∈ Finset.range n, B := Finset.sum_le_sum fun t ht =>
        (le_abs_self _).trans (hb t ((Finset.mem_range.mp ht).trans_le hn) ω)
      _ = (n : ℝ) * B := by simp
  have step (n : ℕ) (hn : n < T) : (∫ ω, F (n + 1) ω ∂P) ≤ ∫ ω, F n ω ∂P := by
    let G : Ω → ℝ := fun ω => Real.exp (d n ω)
    have hG : Integrable G P := by
      refine integrable_of_abs_bound (B := Real.exp B) (Real.continuous_exp.measurable.comp
        ((hm n hn).mono (hinfo_le _ (Nat.succ_le_of_lt hn)) le_rfl)) ?_
      intro ω
      change |Real.exp (d n ω)| ≤ Real.exp B
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hb n hn ω))
    have heq : F (n + 1) = F n * G := by
      funext ω
      simp [F, G, Finset.sum_range_succ, Real.exp_add]
    have hprod : Integrable (F n * G) P := heq ▸ hi (n + 1) (Nat.succ_le_of_lt hn)
    have hpull := condExp_mul_of_stronglyMeasurable_left
      ((hF n hn.le).mono (hprev n hn) le_rfl).stronglyMeasurable
      hprod hG
    rw [heq, ← integral_condExp (m := preDraw n) (hpre n hn)]
    apply integral_mono_ae integrable_condExp (hi n hn.le)
    filter_upwards [hpull, hc n hn] with ω hw hcω
    rw [hw]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) hcω
  have hbound (n : ℕ) (hn : n ≤ T) : (∫ ω, F n ω ∂P) ≤ 1 := by
    induction n with
    | zero => simp [F]
    | succ n ih =>
      have hh : n < T := Nat.lt_of_succ_le hn
      exact (step n hh).trans (ih hh.le)
  exact hbound T le_rfl

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit.Supplement

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

private theorem factorial_ge_geometric (n : ℕ) : 2 * 3 ^ n ≤ (n + 2).factorial := by
  induction n with
  | zero => decide
  | succ n ih =>
    change 2 * 3 ^ (n + 1) ≤ (n + 2 + 1).factorial
    rw [pow_succ, Nat.factorial_succ, ← mul_assoc]
    calc
      2 * 3 ^ n * 3 ≤ (n + 2).factorial * 3 := Nat.mul_le_mul_right _ ih
      _ ≤ (n + 2 + 1) * (n + 2).factorial := by
        rw [mul_comm ((n + 2).factorial)]
        exact Nat.mul_le_mul_right _ (by omega)

private theorem exp_le_bernstein {x a : ℝ} (hx : |x| ≤ a) (ha : a < 3) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - a / 3)) := by
  let f (n : ℕ) := x ^ n / (n.factorial : ℝ)
  have ha₀ : 0 ≤ a := (abs_nonneg x).trans hx
  have h₁ : HasSum f (Real.exp x) := by
    simpa [f, Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x
  have h₂ := hasSum_geometric_of_lt_one (show 0 ≤ a / 3 by positivity) (show a / 3 < 1 by linarith)
  have hsplit : Real.exp x = 1 + x + ∑' n, f (n + 2) := by
    rw [← h₁.tsum_eq, ← h₁.summable.sum_add_tsum_nat_add 2]
    simp [f, Finset.sum_range_succ]
  rw [hsplit]
  apply add_le_add_right
  have htail := (summable_nat_add_iff 2).2 h₁.summable
  calc
    (∑' n, f (n + 2)) ≤ ∑' n, (x ^ 2 / 2) * (a / 3) ^ n := by
      apply htail.tsum_le_tsum _ (h₂.mul_left (x ^ 2 / 2)).summable
      intro n
      have hf := (show (2 : ℝ) * (3 : ℝ) ^ n ≤ ((n + 2).factorial : ℝ) by
        exact_mod_cast factorial_ge_geometric n)
      have h0 : (0 : ℝ) < ((n + 2).factorial : ℝ) := by positivity
      have heq : (x ^ 2 / 2) * (a / 3) ^ n = (x ^ 2 * a ^ n) / (2 * 3 ^ n) := by
        rw [div_pow, div_mul_div_comm]
      rw [heq]
      exact (div_le_div_of_nonneg_right (show x ^ (n + 2) ≤ x ^ 2 * a ^ n by
        rw [pow_add, mul_comm]
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) hx _)) (sq_nonneg x)) h0.le).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hf)
    _ = x ^ 2 / (2 * (1 - a / 3)) := by
      rw [(h₂.mul_left (x ^ 2 / 2)).tsum_eq]
      have hn : 1 - a / 3 ≠ 0 := by linarith
      field_simp

private theorem condExp_bernstein_le_one {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : @Measurable Ω ℝ mΩ _ X) {b v η : ℝ}
    (hb : ∀ ω, |X ω| ≤ b) (hv : 0 ≤ v)
    (hη : 0 ≤ η) (hηb : η * b < 3)
    (hc : condExp m P X =ᵐ[P] 0)
    (hvX : condExp m P (fun ω => X ω ^ 2) ≤ᵐ[P] fun _ => v) :
    let α := η ^ 2 / (2 * (1 - η * b / 3))
    condExp m P (fun ω => Real.exp (η * X ω - α * v)) ≤ᵐ[P] fun _ => 1 := by
  intro α
  have hα : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg (sq_nonneg _) (by linarith)
  let k := Real.exp (-(α * v))
  let F : Ω → ℝ := fun ω => k * (1 + η * X ω + α * X ω ^ 2)
  have hi : Integrable X P := @integrable_of_abs_bound Ω mΩ P _ X hX b hb
  have hi2 : Integrable (fun ω => X ω ^ 2) P := by
    refine @integrable_of_abs_bound Ω mΩ P _ (fun ω => X ω ^ 2) (hX.pow_const (2 : ℕ)) (b ^ 2) ?_
    intro ω
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb ω) _
  have hA : Integrable (fun ω => 1 + η * X ω) P :=
    (integrable_const _).add (hi.const_mul η)
  have hB : Integrable (fun ω => α * X ω ^ 2) P := hi2.const_mul α
  have hF : Integrable F P := (hA.add hB).const_mul k
  have hE : Integrable (fun ω => Real.exp (η * X ω - α * v)) P := by
    have hf : @Measurable Ω ℝ mΩ _ (fun ω => Real.exp (η * X ω - α * v)) :=
      Real.continuous_exp.measurable.comp ((hX.const_mul η).sub measurable_const)
    refine @integrable_of_abs_bound Ω mΩ P _ _ hf (Real.exp (η * b)) fun ω => ?_
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_exp.mpr
    exact (sub_le_self _ (mul_nonneg hα hv)).trans
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb ω)) hη)
  have he (ω : Ω) : Real.exp (η * X ω - α * v) ≤ F ω := by
    rw [sub_eq_add_neg, Real.exp_add, mul_comm]
    have h := exp_le_bernstein (x := η * X ω) (a := η * b)
      (by rw [abs_mul, abs_of_nonneg hη]; exact mul_le_mul_of_nonneg_left (hb ω) hη) hηb
    have heq : (η * X ω) ^ 2 / (2 * (1 - η * b / 3)) = α * X ω ^ 2 := by
      dsimp [α]
      ring
    rw [heq] at h
    exact mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
  have hF' :
      condExp m P F =ᵐ[P] fun ω =>
        k * (1 + η * condExp m P X ω + α * condExp m P (fun ω => X ω ^ 2) ω) := by
    let U : Ω → ℝ := fun _ => 1
    let Y : Ω → ℝ := η • X
    let Z : Ω → ℝ := α • (fun ω => X ω ^ 2)
    have hiU : Integrable U P := integrable_const _
    have hiY : Integrable Y P := hi.smul η
    have hiZ : Integrable Z P := hi2.smul α
    have hU : condExp m P U = U := condExp_const hm (1 : ℝ)
    have hY : condExp m P Y =ᵐ[P] η • condExp m P X := condExp_smul ..
    have hZ : condExp m P Z =ᵐ[P] α • condExp m P (fun ω => X ω ^ 2) := condExp_smul ..
    have heq : F = k • (U + Y + Z) := rfl
    rw [heq]
    filter_upwards [condExp_smul (μ := P) k (U + Y + Z) m, condExp_add (hiU.add hiY) hiZ m,
      condExp_add hiU hiY m, hY, hZ] with ω h₁ h₂ h₃ h₄ h₅
    rw [h₁, Pi.smul_apply, h₂, Pi.add_apply, h₃, Pi.add_apply, hU, h₄, h₅]
    rfl
  filter_upwards [condExp_mono (m := m) hE hF (ae_of_all _ he), hF', hc, hvX] with ω h₁ h₂ h₃ h₄
  apply h₁.trans
  rw [h₂, h₃]
  change k * (1 + η * 0 + α * condExp m P (fun ω => X ω ^ 2) ω) ≤ 1
  calc
    _ ≤ k * (1 + α * v) := by
      rw [mul_zero, add_zero]
      gcongr
    _ ≤ k * Real.exp (α * v) :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _ |>.trans_eq' (add_comm _ _))
        (Real.exp_nonneg _)
    _ = 1 := by dsimp [k]; rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- Bernstein's upper tail for martingale differences with a uniform bound on
their absolute size and on their conditional second moments. -/
theorem bernstein_upper_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (info : ℕ → MeasurableSpace Ω) {s : ℕ} (hs : 0 < s)
    (hinfo : ∀ a n, a ≤ n → n ≤ s → info a ≤ info n)
    (hinfo_le : ∀ n ≤ s, info n ≤ mΩ)
    (d : ℕ → Ω → ℝ) {b v L : ℝ} (hb₀ : 0 ≤ b) (hv : 0 < v) (hL : 0 < L)
    (hm : ∀ t < s, Measurable[info (t + 1)] (d t))
    (hb : ∀ t < s, ∀ ω, |d t ω| ≤ b)
    (hc : ∀ t < s, condExp (info t) P (d t) =ᵐ[P] 0)
    (hvX : ∀ t < s, condExp (info t) P (fun ω => d t ω ^ 2) ≤ᵐ[P] fun _ => v) :
    P {ω | Real.sqrt (2 * s * v * L) + b * L / 3 < ∑ t ∈ Finset.range s, d t ω}
      ≤ ENNReal.ofReal (Real.exp (-L)) := by
  let V : ℝ := s * v
  let R : ℝ := Real.sqrt (2 * V * L)
  let c := b / 3
  let D := V + c * R
  let η := R / D
  let α := η ^ 2 / (2 * (1 - η * b / 3))
  let A := R + c * L
  have hV : 0 < V := by exact mul_pos (by exact_mod_cast hs) hv
  have hR : 0 < R := Real.sqrt_pos.2 (by positivity)
  have hc₀ : 0 ≤ c := by positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hη : 0 ≤ η := by positivity
  have hnorm : 1 - η * b / 3 = V / D := by
    dsimp [η]
    field_simp
    dsimp [D, c]
    ring
  have hηb : η * b < 3 := by nlinarith only [hnorm, (div_pos hV hD)]
  have hR2 : R ^ 2 = 2 * V * L := Real.sq_sqrt (by positivity)
  have hα : α = R ^ 2 / (2 * D * V) := by
    dsimp only [α]
    rw [hnorm]
    dsimp only [η]
    field_simp [ne_of_gt hD, ne_of_gt hV]
  have hexp : -η * A + s * (α * v) = -L := by
    rw [show (s : ℝ) * (α * v) = α * V by dsimp [V]; ring]
    calc
      _ = (-(R * A) + R ^ 2 / 2) / D := by
        rw [hα]
        dsimp only [η]
        field_simp [ne_of_gt hD, ne_of_gt hV]
      _ = -(L * D) / D := by
        congr 1
        dsimp only [A, D]
        rw [mul_add, ← pow_two, hR2]
        ring
      _ = -L := by rw [neg_div, mul_div_cancel_right₀ _ hD.ne']
  let S (ω : Ω) : ℝ := ∑ t ∈ Finset.range s, d t ω
  have hmS : Measurable S := by
    apply Finset.measurable_sum
    intro t ht'
    have ht : t < s := Finset.mem_range.mp ht'
    exact (hm t ht).mono (hinfo_le (t + 1) (by omega)) le_rfl
  have hS (ω : Ω) : |S ω| ≤ s * b := by
    calc
      _ ≤ ∑ t ∈ Finset.range s, |d t ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range s, b := Finset.sum_le_sum fun t ht => hb t (Finset.mem_range.mp ht) ω
      _ = _ := by simp
  have hi : Integrable (fun ω => Real.exp (η * S ω)) P := by
    apply integrable_of_abs_bound (B := Real.exp (η * (s * b)))
      (Real.continuous_exp.measurable.comp (hmS.const_mul _))
    intro ω
    change |Real.exp (η * S ω)| ≤ _
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hS ω)) hη)
  have hg (t : ℕ) (ht : t < s) : condExp (info t) P
      (fun ω => Real.exp (η * d t ω - α * v)) ≤ᵐ[P] fun _ => 1 :=
    @condExp_bernstein_le_one Ω mΩ P _ (info t) (hinfo_le t ht.le) _ ((hm t ht).mono (hinfo_le (t+1) (by omega)) le_rfl) b v η
      (hb t ht) hv.le hη hηb (hc t ht) (hvX t ht)
  have hbound := integral_exp_sum_le_one P info info hinfo hinfo_le
    (fun n hn => hinfo_le n hn.le) (fun _ _ => le_rfl)
    (fun t ω => η * d t ω - α * v) (B := η * b + |α * v|)
    (fun t ht => ((hm t ht).const_mul η).sub measurable_const)
    (fun t ht ω => (abs_sub _ _).trans (by
      rw [abs_mul, abs_of_nonneg hη]
      gcongr
      exact hb t ht ω)) hg
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, Real.exp_sub] at hbound
  rw [integral_div] at hbound
  have hmgf : mgf S P η ≤ Real.exp (s * (α * v)) := by
    unfold mgf
    rw [show (s : ℝ) * (α * v) = α * (s * v) by ring]
    simpa only [one_mul] using (div_le_iff₀ (Real.exp_pos _)).mp hbound
  have hre : P.real {ω | A < S ω} ≤ Real.exp (-L) := by
    calc
      _ ≤ P.real {ω | A ≤ S ω} :=
        measureReal_mono (μ := P) (s₁ := {ω | A < S ω}) (s₂ := {ω | A ≤ S ω}) (fun ω h => (show A < S ω from h).le) (measure_ne_top _ _)
      _ ≤ Real.exp (-η * A) * mgf S P η :=
        measure_ge_le_exp_mul_mgf A hη hi
      _ ≤ Real.exp (-η * A) * Real.exp (s * (α * v)) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, hexp]
  have hR' : R = Real.sqrt (2 * s * v * L) := by
    dsimp [R, V]
    congr 1
    ring
  have hA : A = Real.sqrt (2 * s * v * L) + b * L / 3 := by
    change R + c * L = _
    rw [hR']
    dsimp [c]
    ring
  rw [← hA, ← ENNReal.ofReal_toReal (measure_ne_top P {ω | A < S ω})]
  exact ENNReal.ofReal_le_ofReal hre

/-- The two-sided form of the same concentration bound. -/
theorem bernstein_abs_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (info : ℕ → MeasurableSpace Ω) {s : ℕ} (hs : 0 < s)
    (hinfo : ∀ a n, a ≤ n → n ≤ s → info a ≤ info n)
    (hinfo_le : ∀ n ≤ s, info n ≤ mΩ)
    (d : ℕ → Ω → ℝ) {b v L : ℝ} (hb₀ : 0 ≤ b) (hv : 0 < v) (hL : 0 < L)
    (hm : ∀ t < s, Measurable[info (t + 1)] (d t))
    (hb : ∀ t < s, ∀ ω, |d t ω| ≤ b)
    (hc : ∀ t < s, condExp (info t) P (d t) =ᵐ[P] 0)
    (hvX : ∀ t < s, condExp (info t) P (fun ω => d t ω ^ 2) ≤ᵐ[P] fun _ => v) :
    P {ω | Real.sqrt (2 * s * v * L) + b * L / 3 < |∑ t ∈ Finset.range s, d t ω|}
      ≤ 2 * ENNReal.ofReal (Real.exp (-L)) := by
  let A := Real.sqrt (2 * s * v * L) + b * L / 3
  let high : Set Ω := {ω | A < ∑ t ∈ Finset.range s, d t ω}
  let low : Set Ω := {ω | A < ∑ t ∈ Finset.range s, -d t ω}
  have hhi : P high ≤ ENNReal.ofReal (Real.exp (-L)) :=
    bernstein_upper_tail P info hs hinfo hinfo_le d hb₀ hv hL hm hb hc hvX
  have hlo : P low ≤ ENNReal.ofReal (Real.exp (-L)) :=
    bernstein_upper_tail P info hs hinfo hinfo_le (fun t ω => -d t ω) hb₀ hv hL
      (fun t ht => (hm t ht).neg) (fun t ht ω => by simpa using hb t ht ω)
      (fun t ht => (condExp_neg ..).trans (by simpa using (hc t ht).neg))
      (fun t ht => by simpa only [neg_sq] using hvX t ht)
  calc
    _ ≤ P (high ∪ low) := by
      apply measure_mono
      intro ω hω
      change A < |∑ t ∈ Finset.range s, d t ω| at hω
      rw [abs_eq_max_neg, lt_max_iff] at hω
      simpa [high, low, Finset.sum_neg_distrib] using hω
    _ ≤ P high + P low := measure_union_le _ _
    _ ≤ _ := by rw [two_mul]; exact add_le_add hhi hlo

end CalibeatBandit.Supplement

end

theorem solution : type_of% @CalibeatBandit.Supplement.bernstein_abs_tail := @CalibeatBandit.Supplement.bernstein_abs_tail
