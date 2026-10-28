-- Prove2me | solution 1 for FiniteEnergyPlane.exists_tendsto_loopAction_cwLoop
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T17:16:54.549293+00:00
-- url     : https://prove2.me/submissions/a1897187-6b35-4abd-a809-371f7b738dee

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_integral_mul_integral_bilin_circleMap_eq
import Theorems.Thm_FiniteEnergyPlane_setIntegral_annulus_eq_integral_circleMap
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn

namespace FEPA3

open FiniteEnergyPlane
open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

variable {n : ℕ}

/-- The partner index `2i ↔ 2i+1`. -/
def pairIdx (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
  if h : (k : ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩

theorem pairIdx_involutive : Function.Involutive (pairIdx (n := n)) := by
  intro k
  by_cases h : (k : ℕ) % 2 = 0
  · have h' : ¬ ((k : ℕ) + 1) % 2 = 0 := by omega
    simp only [pairIdx, h, h', dite_true, dite_false]
    ext; simp
  · have h' : ((k : ℕ) - 1) % 2 = 0 := by omega
    simp only [pairIdx, h, h', dite_true, dite_false]
    ext; simp; omega

theorem j0_add (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; simp only [j0, Pi.add_apply]; split_ifs <;> ring

theorem j0_smul (c : ℝ) (u : V n) : j0 (c • u) = c • j0 u := by
  funext k; simp only [j0, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

/-- `j0` as a continuous linear map. -/
noncomputable def j0L : V n →L[ℝ] V n :=
  LinearMap.toContinuousLinearMap
    { toFun := j0, map_add' := j0_add, map_smul' := j0_smul }

@[simp] theorem j0L_apply (u : V n) : j0L u = j0 u := rfl

/-- `ω₀` as a continuous bilinear map. -/
noncomputable def omegaL : V n →L[ℝ] V n →L[ℝ] ℝ :=
  ∑ k, ((ContinuousLinearMap.proj k).comp j0L).smulRight
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (n + 1)) => ℝ) k)

theorem omegaL_apply (u v : V n) : omegaL u v = omega0 u v := by
  simp [omegaL, omega0, dot, ContinuousLinearMap.sum_apply]

theorem omega0_antisymm (u v : V n) : omega0 u v = -omega0 v u := by
  have e := Equiv.sum_comp (Function.Involutive.toPerm _ (pairIdx_involutive (n := n)))
    (fun k => j0 u k * v k)
  simp only [omega0, dot]
  rw [← e, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.Involutive.coe_toPerm, pairIdx, j0]
  by_cases h : (k : ℕ) % 2 = 0
  · have h' : ¬ ((k : ℕ) + 1) % 2 = 0 := by omega
    simp only [h, h', if_true, if_false, dite_true, dite_false]
    have : (⟨(k : ℕ) + 1 - 1, by have := k.2; omega⟩ : Fin (2 * (n + 1))) = k := by
      ext; simp
    rw [this]; ring
  · have h' : ((k : ℕ) - 1) % 2 = 0 := by omega
    simp only [h, h', if_true, if_false, dite_true, dite_false]
    have : (⟨(k : ℕ) - 1 + 1, by have := k.2; omega⟩ : Fin (2 * (n + 1))) = k := by
      ext; simp; omega
    rw [this]; ring

/-- The boundary term of a map `w` on the circle of radius `r`. -/
noncomputable def bdryTerm {n : ℕ} (w : ℂ → V n) (r : ℝ) : ℝ :=
  (1 / 2) * ∫ θ in (0 : ℝ)..2 * π,
    omegaL (w (circleMap 0 r θ)) (fderiv ℝ w (circleMap 0 r θ) (circleMap 0 r θ * Complex.I))

theorem continuousOn_dens {n : ℕ} (w : ℂ → V n) {U : Set ℂ} (hU : IsOpen U)
    (hw : ContDiffOn ℝ ∞ w U) :
    ContinuousOn (fun z => omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I)) U := by
  have hd : ContinuousOn (fderiv ℝ w) U := hw.continuousOn_fderiv_of_isOpen hU (by simp)
  simp_rw [← omegaL_apply]
  exact ((omegaL.continuous.comp_continuousOn (hd.clm_apply continuousOn_const)).clm_apply
    (hd.clm_apply continuousOn_const))

/-- Stokes on an annulus inside an open set. -/
theorem annulus_eq {n : ℕ} (w : ℂ → V n) {U : Set ℂ} (hU : IsOpen U) (hw : ContDiffOn ℝ ∞ w U)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hsub : ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → z ∈ U) :
    ∫ z in ball 0 b \ ball 0 a, omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) =
      bdryTerm w b - bdryTerm w a := by
  have hc : ContinuousOn (fun z => omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I))
      (closedBall 0 b \ ball 0 a) := by
    refine (continuousOn_dens w hU hw).mono ?_
    intro z hz
    refine hsub z ?_ ?_
    · simpa using hz.2
    · simpa using hz.1
  rw [setIntegral_annulus_eq_integral_circleMap ha hab hc]
  have hS := integral_mul_integral_bilin_circleMap_eq (omegaL (n := n))
    (fun x y => by rw [omegaL_apply, omegaL_apply, omega0_antisymm]) hU
    (hw.of_le (WithTop.coe_le_coe.2 le_top)) ha hab hsub 0
  simp only [sub_zero, omegaL_apply] at hS
  simp only [smul_eq_mul, bdryTerm, omegaL_apply]
  exact hS

/-- The action of the clockwise loop is minus the boundary term. -/
theorem loopAction_cw_eq {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) {U : Set ℂ} (hU : IsOpen U)
    (hw : ContDiffOn ℝ ∞ (fun z => proj H (u z)) U) (ρ : ℝ) (hρ : ∀ θ, circleMap 0 ρ θ ∈ U) :
    loopAction H u (cwLoop 0 ρ) = -bdryTerm (fun z => proj H (u z)) ρ := by
  set w := fun z => proj H (u z) with hwdef
  have hcm : ∀ t : ℝ, cwLoop 0 ρ t = circleMap 0 ρ (-(2 * π) * t) := by
    intro t; simp [cwLoop, circleMap]
  have hloop : loopInS H u (cwLoop 0 ρ) = fun t => w (circleMap 0 ρ (-(2 * π) * t)) := by
    funext t; simp [loopInS, hwdef, hcm]
  have hder : ∀ t : ℝ, deriv (loopInS H u (cwLoop 0 ρ)) t =
      (-(2 * π)) • fderiv ℝ w (circleMap 0 ρ (-(2 * π) * t))
        (circleMap 0 ρ (-(2 * π) * t) * Complex.I) := by
    intro t
    rw [hloop]
    have hh : HasDerivAt (fun t : ℝ => -(2 * π) * t) (-(2 * π)) t := by
      simpa using (hasDerivAt_id t).const_mul (-(2 * π))
    have h1 := (hasDerivAt_circleMap 0 ρ (-(2 * π) * t)).scomp t hh
    have h2 : HasFDerivAt w (fderiv ℝ w (circleMap 0 ρ (-(2 * π) * t))) (circleMap 0 ρ (-(2 * π) * t)) :=
      ((hw.contDiffAt (hU.mem_nhds (hρ _))).differentiableAt (by simp)).hasFDerivAt
    have := h2.comp_hasDerivAt t h1
    rw [show (fun t => w (circleMap 0 ρ (-(2 * π) * t))) =
      w ∘ (circleMap 0 ρ ∘ fun t => -(2 * π) * t) from rfl, this.deriv, ← map_smul]
  set f : ℝ → ℝ := fun θ => omegaL (w (circleMap 0 ρ θ))
      (fderiv ℝ w (circleMap 0 ρ θ) (circleMap 0 ρ θ * Complex.I)) with hfdef
  have hper : Function.Periodic f (2 * π) := by
    intro θ; simp only [hfdef, periodic_circleMap 0 ρ θ]
  unfold loopAction
  simp_rw [hder, hloop]
  simp only [liouville, map_smul, smul_eq_mul]
  have e : ∀ t : ℝ, omega0 (w (circleMap 0 ρ (-(2 * π) * t)))
      ((-(2 * π)) • fderiv ℝ w (circleMap 0 ρ (-(2 * π) * t))
        (circleMap 0 ρ (-(2 * π) * t) * Complex.I)) / 2 = (-π) * f (-(2 * π) * t) := by
    intro t
    simp only [hfdef, ← omegaL_apply, map_smul, smul_eq_mul]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left f (by have := Real.pi_pos; intro h; linarith : (-(2 * π) : ℝ) ≠ 0),
    mul_one, mul_zero, intervalIntegral.integral_symm]
  have hp := hper.intervalIntegral_add_eq (-(2 * π)) 0
  simp only [mul_zero, mul_one, neg_add_cancel, zero_add] at hp
  rw [hp, bdryTerm, smul_eq_mul]
  field_simp
  ring

theorem main {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) :
    ∃ Q : ℝ, Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 Q) := by
  set U : Set ℂ := ball 0 1 \ {0} with hUdef
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  obtain ⟨-, hprojs, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  set w : ℂ → V n := fun z => proj H (u z) with hwdef
  have hw : ContDiffOn ℝ ∞ w U := hprojs.comp hu.1 (fun z hz => hu.2.1 z hz)
  have hsub : ∀ a b : ℝ, 0 < a → b < 1 → ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → z ∈ U := by
    intro a b ha hb z h1 h2
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff]; linarith
    · intro hz; rw [Set.mem_singleton_iff] at hz; subst hz; simp at h1; linarith
  have hcirc : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ θ, circleMap 0 ρ θ ∈ U := by
    intro ρ h0 h1 θ
    refine hsub ρ ρ h0 h1 _ ?_ ?_ <;> rw [norm_circleMap_zero, abs_of_pos h0]
  set dens : ℂ → ℝ := fun z => omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) with hdensdef
  have eD := energyDensity_nonneg H hH J hJ U hU u hu
  have hnn : ∀ z ∈ U, 0 ≤ dens z := fun z hz => eD.2.1 z hz
  have hE : dlambdaEnergy H U u < ⊤ := eD.2.2.1.trans_lt hu.2.2.2
  have hdc : ContinuousOn dens U := continuousOn_dens w hU hw
  set q : ℝ → ℝ := fun ρ => loopAction H u (cwLoop 0 ρ) with hqdef
  have hq : ∀ ρ, 0 < ρ → ρ < 1 → q ρ = -bdryTerm w ρ := fun ρ h0 h1 =>
    loopAction_cw_eq H u hU hw ρ (hcirc ρ h0 h1)
  have hannU : ∀ a b : ℝ, 0 < a → b < 1 → ball 0 b \ ball 0 a ⊆ U := by
    intro a b ha hb z hz
    refine hsub a b ha hb z ?_ ?_
    · simpa using hz.2
    · have := hz.1; rw [mem_ball_zero_iff] at this; exact this.le
  have hann : ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
      q a - q b = ∫ z in ball 0 b \ ball 0 a, dens z := by
    intro a b ha hab hb
    rw [hq a ha (hab.trans_lt hb), hq b (ha.trans_le hab) hb,
      annulus_eq w hU hw ha hab (hsub a b ha hb)]
    ring
  have hmeas : ∀ a b : ℝ, MeasurableSet (ball (0 : ℂ) b \ ball 0 a) := fun a b =>
    measurableSet_ball.diff measurableSet_ball
  have hint_nn : ∀ a b : ℝ, 0 < a → b < 1 → 0 ≤ ∫ z in ball 0 b \ ball 0 a, dens z :=
    fun a b ha hb => setIntegral_nonneg (hmeas a b) (fun z hz => hnn z (hannU a b ha hb hz))
  have hint_le : ∀ a b : ℝ, 0 < a → b < 1 →
      ∫ z in ball 0 b \ ball 0 a, dens z ≤ (dlambdaEnergy H U u).toReal := by
    intro a b ha hb
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_restrict_of_forall_mem (hmeas a b) (fun z hz => hnn z (hannU a b ha hb hz)))
      ((hdc.mono (hannU a b ha hb)).aestronglyMeasurable (hmeas a b))]
    exact ENNReal.toReal_mono hE.ne (lintegral_mono_set (hannU a b ha hb))
  have hanti : AntitoneOn q (Set.Ioo 0 1) := by
    intro a ha b hb hab
    have := hann a b ha.1 hab hb.2
    have := hint_nn a b ha.1 hb.2
    linarith
  have hbdd : BddAbove (q '' Set.Ioo 0 1) := by
    refine ⟨q (1 / 2) + (dlambdaEnergy H U u).toReal, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    have hE0 : 0 ≤ (dlambdaEnergy H U u).toReal := ENNReal.toReal_nonneg
    rcases le_total a (1 / 2) with h | h
    · have := hann a (1 / 2) ha.1 h (by norm_num)
      have := hint_le a (1 / 2) ha.1 (by norm_num)
      linarith
    · have := hanti ⟨by norm_num, by norm_num⟩ ha h
      linarith
  exact ⟨_, AntitoneOn.tendsto_nhdsWithin_Ioo_right ⟨1 / 2, by norm_num, by norm_num⟩ hanti hbdd⟩

end FEPA3

open FiniteEnergyPlane
open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) :
    ∃ Q : ℝ, Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 Q) :=
  FEPA3.main H hH J hJ u hu
