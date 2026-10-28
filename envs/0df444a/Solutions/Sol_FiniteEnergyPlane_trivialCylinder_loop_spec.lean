-- Prove2me | solution 1 for FiniteEnergyPlane.trivialCylinder_loop_spec
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-25T22:10:08.3318+00:00
-- url     : https://prove2.me/submissions/0725c95e-a745-40f2-879e-dbb5414bf7d8

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Real



namespace FiniteEnergyPlane

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

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Radial scaling in the symplectization: `proj` is invariant and `a` shifts by `log c / 2`. -/
theorem proj_aCoord_smul_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (c : ℝ) (hc : 0 < c) (y : V n) (hy : y ≠ 0) :
    proj H (c • y) = proj H y ∧ aCoord H (c • y) = aCoord H y + Real.log c / 2 := by
  obtain ⟨r, ⟨hr0, hr1⟩, hru⟩ := hH.2.1 y hy
  have e1 : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := ⟨r, hr0, hr1⟩
  have e2 : ∃ r : ℝ, 0 < r ∧ H (r • (c • y)) = 1 :=
    ⟨r / c, div_pos hr0 hc, by rw [smul_smul, div_mul_cancel₀ _ hc.ne']; exact hr1⟩
  have h1 : scaleToS H y = r := by
    unfold scaleToS
    rw [dif_pos e1]
    exact hru _ (Classical.choose_spec e1)
  have h2 : scaleToS H (c • y) = r / c := by
    unfold scaleToS
    rw [dif_pos e2]
    have hs2 := Classical.choose_spec e2
    have := hru (Classical.choose e2 * c) ⟨mul_pos hs2.1 hc, by rw [← smul_smul]; exact hs2.2⟩
    rw [← this, mul_div_cancel_right₀ _ hc.ne']
  refine ⟨?_, ?_⟩
  · unfold proj
    rw [h1, h2, smul_smul, div_mul_cancel₀ _ hc.ne']
  · unfold aCoord
    rw [h1, h2, Real.log_div hr0.ne' hc.ne']
    ring

/-- Uniform convergence on `[0, 1]` of `1`-periodic functions is uniform convergence on `ℝ`. -/
theorem tendstoUniformly_of_periodic_aux {F : Type*} [NormedAddCommGroup F] (f : ℕ → ℝ → F)
    (g : ℝ → F) (hf : ∀ k, Function.Periodic (f k) 1) (hg : Function.Periodic g 1)
    (h : TendstoUniformlyOn f g atTop (Set.Icc 0 1)) : TendstoUniformly f g atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 h ε hε] with k hk t
  have ht : Int.fract t ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have e1 : f k t = f k (Int.fract t) := by
    rw [Int.fract, ← (hf k).sub_int_mul_eq ⌊t⌋, mul_one]
  have e2 : g t = g (Int.fract t) := by
    rw [Int.fract, ← hg.sub_int_mul_eq ⌊t⌋, mul_one]
  rw [e1, e2]
  exact hk _ ht

/-- Iterated derivatives of a `1`-periodic function are `1`-periodic. -/
theorem periodic_iteratedDeriv_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (hf : Function.Periodic f 1) (m : ℕ) :
    Function.Periodic (iteratedDeriv m f) 1 := by
  intro t
  have h := congrFun (iteratedDeriv_comp_add_const (n := m) (f := f) (s := (1 : ℝ))) t
  rw [← h]
  congr 1
  funext x
  exact hf x

/-- Pointwise convergence from `C^∞_loc` convergence. -/
theorem tendsto_of_tendstoCInftyLocOn_aux {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : ℕ → X → Y) (g : X → Y) (U : Set X)
    (h : JHolomorphic.TendstoCInftyLocOn f g U) (x : X) (hx : x ∈ U) :
    Tendsto (fun k => f k x) atTop (𝓝 (g x)) := by
  have h0 := (h {x} (Set.singleton_subset_iff.2 hx) isCompact_singleton 0).tendsto_at
    (Set.mem_singleton x)
  have hc := ((continuousMultilinearCurryFin0 ℝ X Y).continuous.tendsto _).comp h0
  simpa [iteratedFDeriv_zero_eq_comp, Function.comp_def] using hc

/-- Uniform convergence of iterated derivatives of curves from `C^∞_loc` convergence on `ℝ`. -/
theorem tendstoUniformlyOn_iteratedDeriv_aux {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : ℕ → ℝ → Y) (g : ℝ → Y) (h : JHolomorphic.TendstoCInftyLocOn f g Set.univ) (m : ℕ)
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun k => iteratedDeriv m (f k)) (iteratedDeriv m g) atTop K := by
  have h0 := h K (Set.subset_univ _) hK m
  have hc := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => ℝ) Y
    (fun _ => 1)).uniformContinuous.comp_tendstoUniformlyOn h0
  have e : ∀ F : ℝ → Y, iteratedDeriv m F = fun x => iteratedFDeriv ℝ m F x (fun _ => 1) :=
    fun F => funext fun x => iteratedDeriv_eq_iteratedFDeriv
  simp only [e]
  exact hc

/-- Loop actions converge under `C¹` convergence of the loops on `[0, 1]`. -/
theorem tendsto_loopAction_aux {n : ℕ} (F : ℕ → ℝ → V n) (F₀ : ℝ → V n) (hF0c : Continuous F₀)
    (hF1c : Continuous (deriv F₀)) (hFc : ∀ k, Continuous (F k) ∧ Continuous (deriv (F k)))
    (h0 : TendstoUniformlyOn F F₀ atTop (Set.Icc 0 1))
    (h1 : TendstoUniformlyOn (fun k => deriv (F k)) (deriv F₀) atTop (Set.Icc 0 1)) :
    Tendsto (fun k => ∫ t in (0 : ℝ)..1, liouville (F k t) (deriv (F k) t)) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, liouville (F₀ t) (deriv F₀ t))) := by
  have hl : ∀ x v : V n, liouville x v = omegaL x v / 2 := fun x v => by
    rw [omegaL_apply]; rfl
  simp_rw [hl]
  set K := ‖(omegaL : V n →L[ℝ] V n →L[ℝ] ℝ)‖ with hK
  obtain ⟨A, hA⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hF0c.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hF1c.continuousOn
  have ev0 := Metric.tendstoUniformlyOn_iff.1 h0 1 one_pos
  have ev1 := Metric.tendstoUniformlyOn_iff.1 h1 1 one_pos
  have hsub : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc 0 1 := by
    rw [Set.uIoc_of_le zero_le_one]; exact Set.Ioc_subset_Icc_self
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => K * (A + 1) * (B + 1) / 2) ?_ ?_ intervalIntegrable_const ?_
  · refine Eventually.of_forall fun k => ?_
    exact ((omegaL.continuous₂.comp₂ (hFc k).1 (hFc k).2).div_const 2).aestronglyMeasurable
  · filter_upwards [ev0, ev1] with k hk0 hk1
    refine Eventually.of_forall fun t ht => ?_
    have htI := hsub ht
    have hx : ‖F k t‖ ≤ A + 1 := by
      have := hk0 t htI
      rw [dist_eq_norm] at this
      have h2 := norm_sub_norm_le (F k t) (F₀ t)
      rw [norm_sub_rev] at this
      linarith [hA t htI]
    have hv : ‖deriv (F k) t‖ ≤ B + 1 := by
      have := hk1 t htI
      rw [dist_eq_norm] at this
      have h2 := norm_sub_norm_le (deriv (F k) t) (deriv F₀ t)
      rw [norm_sub_rev] at this
      linarith [hB t htI]
    rw [norm_div, Real.norm_two]
    have hKn : 0 ≤ K := norm_nonneg (omegaL (n := n))
    have := (ContinuousLinearMap.le_opNorm₂ (omegaL (n := n)) (F k t) (deriv (F k) t))
    have hA1 : 0 ≤ A + 1 := by linarith [(norm_nonneg _).trans (hA 0 ⟨le_rfl, zero_le_one⟩)]
    have : K * ‖F k t‖ * ‖deriv (F k) t‖ ≤ K * (A + 1) * (B + 1) := by
      gcongr
    linarith
  · refine Eventually.of_forall fun t ht => ?_
    have htI := hsub ht
    have ha := h0.tendsto_at htI
    have hb := h1.tendsto_at htI
    exact ((omegaL.continuous₂.tendsto _).comp (ha.prodMk_nhds hb)).div_const 2

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Points of `S` are fixed by `proj` and have `a = 0`. -/
theorem proj_aCoord_of_mem_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (x : V n) (hx : H x = 1) : x ≠ 0 ∧ proj H x = x ∧ aCoord H x = 0 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hH.2.2 0 hx
    simp at this
  obtain ⟨r, ⟨hr0, hr1⟩, hru⟩ := hH.2.1 x hx0
  have e1 : ∃ r : ℝ, 0 < r ∧ H (r • x) = 1 := ⟨r, hr0, hr1⟩
  have h1 : scaleToS H x = 1 := by
    unfold scaleToS
    rw [dif_pos e1]
    have := hru _ (Classical.choose_spec e1)
    have h1' := hru 1 ⟨one_pos, by rw [one_smul]; exact hx⟩
    rw [this, h1']
  refine ⟨hx0, ?_, ?_⟩
  · unfold proj; rw [h1, one_smul]
  · unfold aCoord; rw [h1, Real.log_one]; simp

/-- Coordinates, loops and action of a reparametrized trivial cylinder. -/
theorem trivialCylinder_loop_spec_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (k : ℤ) (c : ℂ) (hc : c ≠ 0) :
    (∀ z : ℂ, z ≠ 0 → trivialCylinder P (c * z ^ k) ≠ 0 ∧
      aCoord H (trivialCylinder P (c * z ^ k)) = P.T / (2 * π) * Real.log ‖c * z ^ k‖) ∧
    ∃ c' : ℝ, (∀ t : ℝ, loopInS H (fun z => trivialCylinder P (c * z ^ k)) (ccwLoop 1) t =
        P.x (k * P.T * t + c')) ∧
      loopAction H (fun z => trivialCylinder P (c * z ^ k)) (ccwLoop 1) = k * P.T := by
  have hxS : ∀ τ, H (P.x τ) = 1 := P.mem
  have hper : Function.Periodic P.x P.T := fun τ => P.periodic τ
  -- value of the trivial cylinder at `w ≠ 0`
  have hval : ∀ w : ℂ, w ≠ 0 → trivialCylinder P w ≠ 0 ∧
      proj H (trivialCylinder P w) = P.x (P.T * Complex.arg w / (2 * π)) ∧
      aCoord H (trivialCylinder P w) = P.T / (2 * π) * Real.log ‖w‖ := by
    intro w hw
    have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
    have hr : 0 < ‖w‖ ^ (P.T / π) := Real.rpow_pos_of_pos hwn _
    obtain ⟨hx0, hpx, hax⟩ := proj_aCoord_of_mem_aux H hH _ (hxS (P.T * Complex.arg w / (2 * π)))
    obtain ⟨hp, ha⟩ := proj_aCoord_smul_aux H hH _ hr _ hx0
    refine ⟨smul_ne_zero hr.ne' hx0, ?_, ?_⟩
    · unfold trivialCylinder; rw [hp, hpx]
    · unfold trivialCylinder
      rw [ha, hax, Real.log_rpow hwn]
      field_simp
      ring
  refine ⟨fun z hz => ?_, ?_⟩
  · have hw : c * z ^ k ≠ 0 := mul_ne_zero hc (zpow_ne_zero _ hz)
    exact ⟨(hval _ hw).1, (hval _ hw).2.2⟩
  -- the loop
  set c' : ℝ := P.T * Complex.arg c / (2 * π) with hc'
  have hloop : ∀ t : ℝ, loopInS H (fun z => trivialCylinder P (c * z ^ k)) (ccwLoop 1) t =
      P.x (k * P.T * t + c') := by
    intro t
    have hz : ccwLoop 1 t = Complex.exp (((2 * π * t : ℝ) : ℂ) * Complex.I) := by
      simp [ccwLoop]
    have hw : c * ccwLoop 1 t ^ k ≠ 0 := by
      rw [hz]; exact mul_ne_zero hc (zpow_ne_zero _ (Complex.exp_ne_zero _))
    simp only [loopInS]
    rw [(hval _ hw).2.1]
    -- the argument of `c e^{2π i k t}`
    set θ : ℝ := Complex.arg c + 2 * π * k * t with hθ
    have hcw : c * ccwLoop 1 t ^ k = (‖c‖ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [hz, ← Complex.exp_int_mul]
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I c]
      rw [mul_assoc, ← Complex.exp_add, hθ]
      congr 3
      push_cast
      ring
    have harg : Complex.arg (c * ccwLoop 1 t ^ k) =
        θ - (toIocDiv Real.two_pi_pos (-π) θ : ℝ) * (2 * π) := by
      rw [hcw, Complex.arg_real_mul _ (norm_pos_iff.2 hc), Complex.arg_exp_mul_I, toIocMod,
        zsmul_eq_mul]
    rw [harg]
    have e : P.T * (θ - (toIocDiv Real.two_pi_pos (-π) θ : ℝ) * (2 * π)) / (2 * π) =
        (k * P.T * t + c') - (toIocDiv Real.two_pi_pos (-π) θ : ℝ) * P.T := by
      rw [hθ, hc']
      field_simp
      ring
    rw [e, hper.sub_int_mul_eq]
  refine ⟨c', hloop, ?_⟩
  -- the action
  have hfun : loopInS H (fun z => trivialCylinder P (c * z ^ k)) (ccwLoop 1) =
      fun t => P.x (k * P.T * t + c') := funext hloop
  unfold loopAction
  rw [hfun]
  have hd : ∀ t : ℝ, deriv (fun t => P.x (k * P.T * t + c')) t =
      ((k : ℝ) * P.T) • reeb H (P.x (k * P.T * t + c')) := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (k : ℝ) * P.T * t + c') ((k : ℝ) * P.T) t := by
      simpa using ((hasDerivAt_id t).const_mul ((k : ℝ) * P.T)).add_const c'
    exact ((P.hasDerivAt _).scomp t h1).deriv
  simp_rw [hd]
  have hl : ∀ t : ℝ, liouville (P.x (k * P.T * t + c'))
      (((k : ℝ) * P.T) • reeb H (P.x (k * P.T * t + c'))) = (k : ℝ) * P.T := by
    intro t
    have hr := (reeb_spec H hH _ (hxS (k * P.T * t + c'))).2.1
    have hlin : ∀ (x v : V n) (a : ℝ), liouville x (a • v) = a * liouville x v := by
      intro x v a
      simp only [liouville, omega0, dot, Pi.smul_apply, smul_eq_mul]
      have e : ∑ i, j0 x i * (a * v i) = a * ∑ i, j0 x i * v i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [e]; ring
    rw [hlin, hr, mul_one]
  simp_rw [hl]
  simp

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (k : ℤ) (c : ℂ) (hc : c ≠ 0) :
    (∀ z : ℂ, z ≠ 0 → trivialCylinder P (c * z ^ k) ≠ 0 ∧
      aCoord H (trivialCylinder P (c * z ^ k)) = P.T / (2 * π) * Real.log ‖c * z ^ k‖) ∧
    ∃ c' : ℝ, (∀ t : ℝ, loopInS H (fun z => trivialCylinder P (c * z ^ k)) (ccwLoop 1) t =
        P.x (k * P.T * t + c')) ∧
      loopAction H (fun z => trivialCylinder P (c * z ^ k)) (ccwLoop 1) = k * P.T :=
  trivialCylinder_loop_spec_aux H hH P k c hc
