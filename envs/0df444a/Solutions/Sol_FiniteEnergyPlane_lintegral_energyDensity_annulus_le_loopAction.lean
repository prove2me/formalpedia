-- Prove2me | solution 1 for FiniteEnergyPlane.lintegral_energyDensity_annulus_le_loopAction
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-26T21:06:33.410343+00:00
-- url     : https://prove2.me/submissions/ed15564c-4528-469b-a12e-466b774f244e

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_integral_mul_integral_bilin_circleMap_eq
import Theorems.Thm_FiniteEnergyPlane_setIntegral_annulus_eq_integral_circleMap
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg



/-! Stokes helpers on an annulus inside an open set: copied from fizzyinc3's accepted solution
f12a0a9a (namespace FEPA3, renamed ZCS). -/

namespace ZCS

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

end ZCS

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set ZCS
open scoped ContDiff ENNReal Real

/-- The cutoff `χ_A(s) = smoothTransition (s - A)`. -/
theorem zc_chi_contDiff (A : ℝ) : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (s - A)) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const)

theorem zc_admissible (A : ℝ) : Admissible (fun s : ℝ => Real.smoothTransition (s - A) ^ 2) := by
  refine ⟨(zc_chi_contDiff A).pow 2, ?_, fun s => ⟨by positivity, ?_⟩⟩
  · intro s t hst
    have h1 := Real.smoothTransition.monotone (sub_le_sub_right hst A)
    have h0 := Real.smoothTransition.nonneg (s - A)
    exact pow_le_pow_left₀ h0 h1 2
  · have h0 := Real.smoothTransition.nonneg (s - A)
    have h1 := Real.smoothTransition.le_one (s - A)
    nlinarith

/-- Pointwise identity: the energy density for `φ = χ²` is the `ω₀`-density of `χ(a) • w`. -/
theorem zc_density_eq {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (χ : ℝ → ℝ) (hχ : Differentiable ℝ χ)
    (z : ℂ) (ha : DifferentiableAt ℝ (fun z => aCoord H (u z)) z)
    (hw : DifferentiableAt ℝ (fun z => proj H (u z)) z) :
    omega0 (fderiv ℝ (fun z => χ (aCoord H (u z)) • proj H (u z)) z 1)
        (fderiv ℝ (fun z => χ (aCoord H (u z)) • proj H (u z)) z Complex.I) =
      energyDensity H (fun s => χ s ^ 2) u z := by
  have hca : HasFDerivAt (fun y => χ (aCoord H (u y)))
      (deriv χ (aCoord H (u z)) • fderiv ℝ (fun y => aCoord H (u y)) z) z :=
    (hχ (aCoord H (u z))).hasDerivAt.comp_hasFDerivAt z ha.hasFDerivAt
  have hW : HasFDerivAt (fun z => χ (aCoord H (u z)) • proj H (u z)) _ z :=
    hca.smul hw.hasFDerivAt
  rw [hW.fderiv]
  have hφ : deriv (fun s => χ s ^ 2) (aCoord H (u z)) =
      2 * χ (aCoord H (u z)) * deriv χ (aCoord H (u z)) := by
    have h2 : HasDerivAt (fun s => χ s ^ 2)
        ((2 : ℕ) * χ (aCoord H (u z)) ^ (2 - 1) * deriv χ (aCoord H (u z))) (aCoord H (u z)) :=
      (hχ (aCoord H (u z))).hasDerivAt.pow 2
    rw [h2.deriv]; push_cast; ring
  simp only [energyDensity, ds, dt, liouville]
  rw [hφ]
  set a : ℂ → ℝ := fun z => aCoord H (u z) with hadef
  set w : ℂ → V n := fun z => proj H (u z) with hwdef
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  simp only [← omegaL_apply, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  have h0 : omegaL (w z) (w z) = 0 := by
    rw [omegaL_apply]; have := omega0_antisymm (w z) (w z); linarith
  have hanti : ∀ v : V n, omegaL v (w z) = -omegaL (w z) v := by
    intro v; rw [omegaL_apply, omegaL_apply, omega0_antisymm]
  rw [h0]
  simp only [hwdef] at hanti ⊢
  rw [hanti]
  ring

/-- On a circle where `χ ∘ a` is `0` or `1` everywhere, the boundary term of `χ(a) • w` is `0`
or that of `w`. -/
theorem zc_bdryTerm_eq {n : ℕ} (W w : ℂ → V n) (ρ : ℝ)
    (hW : ∀ θ, DifferentiableAt ℝ W (circleMap 0 ρ θ))
    (hw : ∀ θ, DifferentiableAt ℝ w (circleMap 0 ρ θ))
    (heq : ∀ θ, W (circleMap 0 ρ θ) = w (circleMap 0 ρ θ)) :
    bdryTerm W ρ = bdryTerm w ρ := by
  unfold bdryTerm
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hfun : (fun θ => W (circleMap 0 ρ θ)) = fun θ => w (circleMap 0 ρ θ) := funext heq
  have h1 := (hW θ).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap 0 ρ θ)
  have h2 := (hw θ).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap 0 ρ θ)
  have h1' : HasDerivAt (fun θ => W (circleMap 0 ρ θ))
      (fderiv ℝ W (circleMap 0 ρ θ) (circleMap 0 ρ θ * Complex.I)) θ := h1
  have h2' : HasDerivAt (fun θ => w (circleMap 0 ρ θ))
      (fderiv ℝ w (circleMap 0 ρ θ) (circleMap 0 ρ θ * Complex.I)) θ := h2
  rw [hfun] at h1'
  simp only [heq θ, h1'.unique h2']

theorem zc_bdryTerm_zero {n : ℕ} (W : ℂ → V n) (ρ : ℝ) (h0 : ∀ θ, W (circleMap 0 ρ θ) = 0) :
    bdryTerm W ρ = 0 := by
  unfold bdryTerm
  simp [h0]

theorem lintegral_energyDensity_annulus_le_loopAction_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (A ρ₁ ρ₂ : ℝ) (h₂ : 0 < ρ₂)
    (h₂₁ : ρ₂ < ρ₁) (h₁ : ρ₁ < 1)
    (hc₁ : (∀ z : ℂ, ‖z‖ = ρ₁ → aCoord H (u z) ≤ A) ∨
      (∀ z : ℂ, ‖z‖ = ρ₁ → A + 1 ≤ aCoord H (u z)))
    (hc₂ : (∀ z : ℂ, ‖z‖ = ρ₂ → aCoord H (u z) ≤ A) ∨
      (∀ z : ℂ, ‖z‖ = ρ₂ → A + 1 ≤ aCoord H (u z))) :
    ∫⁻ z in ball 0 ρ₁ \ ball 0 ρ₂,
        ENNReal.ofReal (energyDensity H (fun s => Real.smoothTransition (s - A) ^ 2) u z) ≤
      ENNReal.ofReal (|loopAction H u (cwLoop 0 ρ₁)| + |loopAction H u (cwLoop 0 ρ₂)|) := by
  set U : Set ℂ := ball 0 1 \ {0} with hUdef
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  obtain ⟨-, hprojs, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  set χ : ℝ → ℝ := fun s => Real.smoothTransition (s - A) with hχdef
  set φ : ℝ → ℝ := fun s => Real.smoothTransition (s - A) ^ 2 with hφdef
  set a : ℂ → ℝ := fun z => aCoord H (u z) with hadef
  set w : ℂ → V n := fun z => proj H (u z) with hwdef
  set W : ℂ → V n := fun z => χ (a z) • w z with hWdef
  have hw : ContDiffOn ℝ ∞ w U := hprojs.comp hu.1 (fun z hz => hu.2.1 z hz)
  have ha : ContDiffOn ℝ ∞ a U := haCs.comp hu.1 (fun z hz => hu.2.1 z hz)
  have hχ : ContDiff ℝ ∞ χ := zc_chi_contDiff A
  have hW : ContDiffOn ℝ ∞ W U := (hχ.comp_contDiffOn ha).smul hw
  have hdiff : ∀ {f : ℂ → V n}, ContDiffOn ℝ ∞ f U → ∀ z ∈ U, DifferentiableAt ℝ f z :=
    fun hf z hz => (hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hdiffa : ∀ z ∈ U, DifferentiableAt ℝ a z :=
    fun z hz => (ha.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  -- the density identity on `U`
  have hden : ∀ z ∈ U, omega0 (fderiv ℝ W z 1) (fderiv ℝ W z Complex.I) =
      energyDensity H φ u z := fun z hz =>
    zc_density_eq H u χ (hχ.differentiable (by simp)) z (hdiffa z hz) (hdiff hw z hz)
  have hmemU : ∀ z : ℂ, ρ₂ ≤ ‖z‖ → ‖z‖ ≤ ρ₁ → z ∈ U := by
    intro z hz1 hz2
    refine ⟨by rw [mem_ball_zero_iff]; linarith, ?_⟩
    intro h; rw [mem_singleton_iff] at h; rw [h, norm_zero] at hz1; linarith
  have hS := annulus_eq W hU hW h₂ h₂₁.le hmemU
  have hann : ball (0 : ℂ) ρ₁ \ ball 0 ρ₂ ⊆ U := by
    intro z hz
    refine hmemU z ?_ ?_
    · simpa using hz.2
    · exact (mem_ball_zero_iff.1 hz.1).le
  have hS' : ∫ z in ball 0 ρ₁ \ ball 0 ρ₂, energyDensity H φ u z =
      bdryTerm W ρ₁ - bdryTerm W ρ₂ := by
    rw [← hS]
    refine setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball) fun z hz => ?_
    exact (hden z (hann hz)).symm
  -- boundary terms
  have hcircU : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ θ, circleMap 0 ρ θ ∈ U := by
    intro ρ h0 h1 θ
    have hn : ‖circleMap 0 ρ θ‖ = ρ := by rw [norm_circleMap_zero, abs_of_pos h0]
    refine ⟨by rw [mem_ball_zero_iff, hn]; exact h1, ?_⟩
    intro h; rw [mem_singleton_iff] at h; rw [h, norm_zero] at hn; linarith
  have hbd : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ((∀ z : ℂ, ‖z‖ = ρ → a z ≤ A) ∨
      (∀ z : ℂ, ‖z‖ = ρ → A + 1 ≤ a z)) →
      |bdryTerm W ρ| ≤ |loopAction H u (cwLoop 0 ρ)| := by
    intro ρ h0 h1 hc
    have hn : ∀ θ, ‖circleMap 0 ρ θ‖ = ρ := fun θ => by
      rw [norm_circleMap_zero, abs_of_pos h0]
    rcases hc with hc | hc
    · rw [zc_bdryTerm_zero W ρ fun θ => ?_, abs_zero]
      · exact abs_nonneg _
      · simp only [hWdef, hχdef]
        rw [Real.smoothTransition.zero_of_nonpos (by linarith [hc _ (hn θ)]), zero_smul]
    · rw [zc_bdryTerm_eq W w ρ (fun θ => hdiff hW _ (hcircU ρ h0 h1 θ))
        (fun θ => hdiff hw _ (hcircU ρ h0 h1 θ)) fun θ => ?_,
        loopAction_cw_eq H u hU hw ρ (hcircU ρ h0 h1), abs_neg]
      simp only [hWdef, hχdef]
      rw [Real.smoothTransition.one_of_one_le (by linarith [hc _ (hn θ)]), one_smul]
  have hb₁ := hbd ρ₁ (h₂.trans h₂₁) h₁ hc₁
  have hb₂ := hbd ρ₂ h₂ (h₂₁.trans h₁) hc₂
  -- nonnegativity and integrability
  have hnn : ∀ z ∈ U, 0 ≤ energyDensity H φ u z :=
    (energyDensity_nonneg H hH J hJ U hU u hu).1 φ (zc_admissible A)
  have hcont : ContinuousOn (fun z => energyDensity H φ u z) (closedBall 0 ρ₁ \ ball 0 ρ₂) := by
    refine ((continuousOn_dens W hU hW).mono ?_).congr ?_
    · intro z hz; exact hmemU z (by simpa using hz.2) (by simpa using hz.1)
    · intro z hz; exact (hden z (hmemU z (by simpa using hz.2) (by simpa using hz.1))).symm
  have hcpt : IsCompact (closedBall (0 : ℂ) ρ₁ \ ball 0 ρ₂) :=
    (isCompact_closedBall 0 ρ₁).diff isOpen_ball
  have hint : IntegrableOn (fun z => energyDensity H φ u z) (ball 0 ρ₁ \ ball 0 ρ₂) :=
    (hcont.integrableOn_compact hcpt).mono_set (diff_subset_diff_left ball_subset_closedBall)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' (measurableSet_ball.diff measurableSet_ball)).2
      (Eventually.of_forall fun z hz => hnn z (hann hz)))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hS']
  have := abs_sub (bdryTerm W ρ₁) (bdryTerm W ρ₂)
  have := le_abs_self (bdryTerm W ρ₁ - bdryTerm W ρ₂)
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (A ρ₁ ρ₂ : ℝ) (h₂ : 0 < ρ₂)
    (h₂₁ : ρ₂ < ρ₁) (h₁ : ρ₁ < 1)
    (hc₁ : (∀ z : ℂ, ‖z‖ = ρ₁ → aCoord H (u z) ≤ A) ∨
      (∀ z : ℂ, ‖z‖ = ρ₁ → A + 1 ≤ aCoord H (u z)))
    (hc₂ : (∀ z : ℂ, ‖z‖ = ρ₂ → aCoord H (u z) ≤ A) ∨
      (∀ z : ℂ, ‖z‖ = ρ₂ → A + 1 ≤ aCoord H (u z))) :
    ∫⁻ z in ball 0 ρ₁ \ ball 0 ρ₂,
        ENNReal.ofReal (energyDensity H (fun s => Real.smoothTransition (s - A) ^ 2) u z) ≤
      ENNReal.ofReal (|loopAction H u (cwLoop 0 ρ₁)| + |loopAction H u (cwLoop 0 ρ₂)|) :=
  FiniteEnergyPlane.lintegral_energyDensity_annulus_le_loopAction_aux H hH J hJ u hu A ρ₁ ρ₂ h₂ h₂₁ h₁ hc₁ hc₂
