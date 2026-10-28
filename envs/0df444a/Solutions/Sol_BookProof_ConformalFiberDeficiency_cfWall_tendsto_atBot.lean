-- Prove2me | solution 1 for BookProof.ConformalFiberDeficiency.cfWall_tendsto_atBot
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:25:45.957831+00:00
-- url     : https://prove2.me/submissions/c64bcff7-753b-441d-b1d4-ba2ba4134608

-- Generated from ChapterConformalFiberDeficiency.lean — theorem BookProof.ConformalFiberDeficiency.cfWall_tendsto_atBot
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWallDeficiencyObstruction
import Mathlib
import Definitions.Def_ChapterConformalFiberDeficiency
import Definitions.Def_ChapterBddBelowFiberSumEsa



open MeasureTheory Real Filter Topology
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction

noncomputable section
open BookProof.ConformalFiberDeficiency

theorem t_exp : Tendsto (fun y : ℝ => Real.exp (-(2 * y))) atBot atTop := by
  rw [show (fun y : ℝ => Real.exp (-(2 * y))) = fun y => Real.exp ((-2:ℝ) * y) by
    funext y; congr 1; ring]
  exact tendsto_exp_atTop.comp
    ((tendsto_const_mul_atTop_of_neg (by norm_num : (-2:ℝ) < 0)).2 tendsto_id)

theorem t_le (t : ℝ) : 1 / (2 * Real.cosh (t / 2) ^ 2) ≤ 2 * Real.exp (-t) := by
  have h1 : Real.exp (t / 2) / 2 ≤ Real.cosh (t / 2) := by
    rw [Real.cosh_eq]; have := (Real.exp_pos (-(t/2))).le; linarith
  have hp : 0 < Real.exp (t / 2) / 2 := by positivity
  have h2 : (Real.exp (t / 2) / 2) ^ 2 ≤ Real.cosh (t / 2) ^ 2 := pow_le_pow_left₀ hp.le h1 2
  have he : (Real.exp (t / 2)) ^ 2 = Real.exp t := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hc : 0 < Real.cosh (t / 2) := Real.cosh_pos _
  rw [div_le_iff₀ (by positivity)]
  have : 2 * Real.exp (-t) * Real.exp t = 2 := by rw [mul_assoc, ← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-t)]

theorem t_sech : Tendsto (fun y : ℝ => 1 / (2 * Real.cosh (y / 2) ^ 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => 2 * Real.exp (-y)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun y => ?_) (fun y => t_le y)
  positivity

theorem t_V : Tendsto cfV atTop (𝓝 (-(3 / 4))) := by
  have h1 : Tendsto (fun y : ℝ => (1 + Real.exp (-y)) ^ 2) atTop (𝓝 ((1 + 0) ^ 2)) :=
    ((tendsto_const_nhds.add Real.tendsto_exp_neg_atTop_nhds_zero).pow 2)
  have h := (tendsto_const_nhds (x := (1/4:ℝ))).sub t_sech |>.sub h1
  have e : (1 / 4 : ℝ) - 0 - (1 + 0) ^ 2 = -(3/4) := by norm_num
  rw [e] at h
  exact h.congr (fun y => by simp [cfV])

theorem t_Wtop : Tendsto cfWall atTop (𝓝 0) := by
  have h := (t_V.neg.div_const 24).sub_const (1/32 : ℝ)
  have e : -(-(3 / 4 : ℝ)) / 24 - 1 / 32 = 0 := by norm_num
  rw [e] at h
  exact h.congr (fun y => by simp [cfWall])

theorem t_Wbot : Tendsto cfWall atBot atTop := by
  refine tendsto_atTop_mono cfWall_ge_exp ?_
  have : Tendsto (fun y : ℝ => Real.exp (-y)) atBot atTop :=
    tendsto_exp_atTop.comp tendsto_neg_atBot_atTop
  exact this.atTop_div_const (by norm_num)

theorem t_pack :
    ∃ (U V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V),
      (∀ y, 0 ≤ U y) ∧ Tendsto U atBot atTop ∧ Tendsto U atTop (𝓝 0) ∧
        (∀ y, V y = -24 * (U y + 1 / 32)) ∧
        ¬ EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam V hV) :=
  ⟨cfWall, cfV, contDiff_cfV, cfWall_nonneg, t_Wbot, t_Wtop, cfV_eq_wall, cfV_not_essentiallySelfAdjoint⟩

theorem solution : Tendsto cfWall atBot atTop := by
  exact t_Wbot

