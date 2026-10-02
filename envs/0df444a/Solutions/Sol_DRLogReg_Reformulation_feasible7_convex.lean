-- Prove2me | solution 1 for DRLogReg.Reformulation.feasible7_convex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T08:17:21.29471+00:00
-- url     : https://prove2.me/submissions/01956d5a-69fd-4b34-a782-08b3c69aaffe

import Mathlib
import Definitions.Def_DRLogReg_Reformulation_Core
import Definitions.Def_DRLogReg_Reformulation_Program

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.Reformulation

theorem a27_softplus_convex :
    ConvexOn ℝ Set.univ (fun t : ℝ => Real.log (1 + Real.exp t)) := by
  have hpos : ∀ t : ℝ, 0 < 1 + Real.exp t := fun t => by positivity
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.log (1 + Real.exp t))
      (Real.exp t / (1 + Real.exp t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => 1 + Real.exp t) (Real.exp t) t := by
      simpa using (Real.hasDerivAt_exp t).const_add 1
    exact h1.log (hpos t).ne'
  apply Monotone.convexOn_univ_of_deriv
  · intro t; exact (hd t).differentiableAt
  · intro a b hab
    simp only [(hd a).deriv, (hd b).deriv]
    rw [div_le_div_iff₀ (hpos a) (hpos b)]
    have : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
    nlinarith

theorem a27_softplus_comb (u v a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Real.log (1 + Real.exp (a * u + b * v)) ≤
      a * Real.log (1 + Real.exp u) + b * Real.log (1 + Real.exp v) := by
  have := a27_softplus_convex.2 (Set.mem_univ u) (Set.mem_univ v) ha hb hab
  simpa [smul_eq_mul] using this

theorem a27_logloss_comb {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β γ : V →L[ℝ] ℝ) (x : V) (y : Bool) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    logloss (a • β + b • γ) x y ≤ a * logloss β x y + b * logloss γ x y := by
  unfold logloss
  have h := a27_softplus_comb (-(sgn y * β x)) (-(sgn y * γ x)) a b ha hb hab
  have e : -(sgn y * (a • β + b • γ) x) = a * -(sgn y * β x) + b * -(sgn y * γ x) := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [e]; exact h

end DRLogReg.Reformulation

open DRLogReg.Reformulation in
theorem solution
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) :
    Convex ℝ (feasible7 κ xhat yhat) := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    have h := a27_logloss_comb p.1 q.1 (xhat i) (yhat i) a b ha hb hab
    have h1 := mul_le_mul_of_nonneg_left (hp1 i) ha
    have h2 := mul_le_mul_of_nonneg_left (hq1 i) hb
    linarith
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    have h := a27_logloss_comb p.1 q.1 (xhat i) (!yhat i) a b ha hb hab
    have h1 := mul_le_mul_of_nonneg_left (hp2 i) ha
    have h2 := mul_le_mul_of_nonneg_left (hq2 i) hb
    nlinarith
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    calc ‖a • p.1 + b • q.1‖ ≤ ‖a • p.1‖ + ‖b • q.1‖ := norm_add_le _ _
      _ = a * ‖p.1‖ + b * ‖q.1‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * p.2.1 + b * q.2.1 := by
        have h1 := mul_le_mul_of_nonneg_left hp3 ha
        have h2 := mul_le_mul_of_nonneg_left hq3 hb
        linarith
