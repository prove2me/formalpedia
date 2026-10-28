-- Prove2me | solution 1 for FiniteEnergyPlane.exists_subseq_tendstoCInfty_cwLoop
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-26T22:05:33.607075+00:00
-- url     : https://prove2.me/submissions/b9d35649-35bc-4e7f-b165-a902ee062b36

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendsto_rescaled_punctured
import Theorems.Thm_FiniteEnergyPlane_tendstoCInftyLocOn_comp
import Theorems.Thm_FiniteEnergyPlane_trivialCylinder_loop_spec
import Theorems.Thm_FiniteEnergyPlane_eq_trivialCylinder_of_dlambdaEnergy_eq_zero
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn



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

/-- A constant sequence converges in `C^∞_loc`. -/
theorem pdd_tendstoCInftyLocOn_const {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (g : X → Y) (U : Set X) :
    JHolomorphic.TendstoCInftyLocOn (fun _ : ℕ => g) g U := fun K _ _ m =>
  Metric.tendstoUniformlyOn_iff.2 fun ε hε => Eventually.of_forall fun _ x _ => by simpa using hε

theorem pdd_cwLoop_eq (ρ t : ℝ) : cwLoop 0 ρ t = ccwLoop ρ (-t) := by
  simp only [cwLoop, ccwLoop, zero_add]
  congr 2
  push_cast
  ring

theorem pdd_cwLoop_scale (ρ t : ℝ) : cwLoop 0 ρ t = (ρ : ℂ) * cwLoop 0 1 t := by
  simp [cwLoop]

theorem pdd_cwLoop_periodic (ρ : ℝ) : Function.Periodic (cwLoop 0 ρ) 1 := by
  intro t
  rw [pdd_cwLoop_eq, pdd_cwLoop_eq, show -(t + 1) = -t + -1 by ring]
  simp only [ccwLoop]
  congr 1
  rw [show (((2 * π * (-t + -1) : ℝ)) : ℂ) * Complex.I =
      ((2 * π * -t : ℝ) : ℂ) * Complex.I + -(2 * π * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]

theorem pdd_contDiff_cwLoop : ContDiff ℝ ∞ (cwLoop 0 1) := by
  have h : cwLoop 0 1 = fun t : ℝ => Complex.exp (((-(2 * π) * t : ℝ) : ℂ) * Complex.I) := by
    funext t
    simp only [cwLoop, zero_add, Complex.ofReal_one, one_mul]
    congr 1
    push_cast
    ring
  rw [h]
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => (((-(2 * π) * t : ℝ)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
  exact Complex.contDiff_exp.comp (h1.mul contDiff_const)

theorem pdd_norm_cwLoop (t : ℝ) : ‖cwLoop 0 1 t‖ = 1 := by
  rw [pdd_cwLoop_eq]
  simp only [ccwLoop, Complex.ofReal_one, one_mul]
  rw [Complex.norm_exp_ofReal_mul_I]

/-- The action of the loop `t ↦ x(α t + c)` along a Reeb orbit is `α`. -/
theorem pdd_loopAction_orbit {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (α c : ℝ) :
    ∫ t in (0 : ℝ)..1, liouville (P.x (α * t + c)) (deriv (fun t => P.x (α * t + c)) t) = α := by
  have hd : ∀ t : ℝ, deriv (fun t => P.x (α * t + c)) t = α • reeb H (P.x (α * t + c)) := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => α * t + c) α t := by
      simpa using ((hasDerivAt_id t).const_mul α).add_const c
    exact ((P.hasDerivAt _).scomp t h1).deriv
  simp_rw [hd]
  have hl : ∀ t : ℝ, liouville (P.x (α * t + c)) (α • reeb H (P.x (α * t + c))) = α := by
    intro t
    have hr := (reeb_spec H hH _ (P.mem (α * t + c))).2.1
    have hlin : ∀ (x v : V n) (a : ℝ), liouville x (a • v) = a * liouville x v := by
      intro x v a
      simp only [liouville, omega0, dot, Pi.smul_apply, smul_eq_mul]
      have e : ∑ i, j0 x i * (a * v i) = a * ∑ i, j0 x i * v i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [e]; ring
    rw [hlin, hr, mul_one]
  simp_rw [hl]
  simp

/-- (d) Nonzero charge: along any `ρ_k → 0⁺` a subsequence of the loops converges in `C^∞` to
`t ↦ x(Q t + c)` for a periodic Reeb orbit `(x, |Q|)`. -/
theorem exists_subseq_tendstoCInfty_cwLoop_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C)
    (Q : ℝ) (hQ0 : Q ≠ 0) (hQ : Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 Q))
    (ρ : ℕ → ℝ) (hρ : ∀ k, 0 < ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : ReebOrbit H, P.T = |Q| ∧ ∃ c : ℝ,
      TendstoCInfty (fun k => loopInS H u (cwLoop 0 (ρ (φ k)))) (fun t => P.x (Q * t + c)) := by
  classical
  obtain ⟨-, hprojs, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  -- a tail with `ρ < 1/2`
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hρ0.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  set ρ' : ℕ → ℝ := fun k => ρ (k + N) with hρ'def
  have hρ'0 : ∀ k, 0 < ρ' k := fun k => hρ _
  have hρ'h : ∀ k, ρ' k < 1 / 2 := fun k => hN _ (Nat.le_add_left _ _)
  have hρ' : Tendsto ρ' atTop (𝓝 0) := hρ0.comp (tendsto_add_atTop_nat N)
  obtain ⟨φ, hφ, w, hw, hw0, hconv⟩ :=
    exists_subseq_tendsto_rescaled_punctured H hH J hJ u hu hG ρ' hρ'0 hρ'
  set c : ℕ → ℝ := fun j => Real.exp (-2 * aCoord H (u ((ρ' (φ j) : ℝ) : ℂ))) with hcdef
  have hcpos : ∀ j, 0 < c j := fun j => Real.exp_pos _
  set v : ℕ → ℂ → V n := fun j z => c j • u (((ρ' (φ j) : ℝ) : ℂ) * z) with hvdef
  change JHolomorphic.TendstoCInftyLocOn v w {z | z ≠ 0} at hconv
  -- the annulus around the unit circle
  set W : Set ℂ := {z | 1 / 2 < ‖z‖ ∧ ‖z‖ < 2} with hWdef
  have hWo : IsOpen W :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hW0 : W ⊆ {z | z ≠ 0} := fun z hz => norm_pos_iff.1 (lt_trans (by norm_num) hz.1)
  have hWU : ∀ j, ∀ z ∈ W, ((ρ' (φ j) : ℝ) : ℂ) * z ∈ ball (0 : ℂ) 1 \ {0} := by
    intro j z hz
    have hn : ‖((ρ' (φ j) : ℝ) : ℂ) * z‖ = ρ' (φ j) * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ'0 _).le]
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, hn]
      nlinarith [hρ'h (φ j), hρ'0 (φ j), hz.2, hz.1]
    · exact mul_ne_zero (by exact_mod_cast (hρ'0 _).ne') (hW0 hz)
  have hvsm : ∀ j, ContDiffOn ℝ ∞ (v j) W := fun j =>
    (hu.1.comp (contDiff_const.mul contDiff_id).contDiffOn fun z hz => hWU j z hz).const_smul (c j)
  have hv0 : ∀ j, ∀ z ∈ W, v j z ≠ 0 := fun j z hz =>
    smul_ne_zero (hcpos j).ne' (hu.2.1 _ (hWU j z hz))
  have hconvW : JHolomorphic.TendstoCInftyLocOn v w W := fun K hK hKc m =>
    hconv K (hK.trans hW0) hKc m
  have hwsm : ContDiffOn ℝ ∞ w W := hw.1.mono hW0
  have hwne : ∀ z ∈ W, w z ≠ 0 := fun z hz => hw.2.1 z (hW0 hz)
  -- the unit circle, clockwise
  set γ : ℝ → ℂ := cwLoop 0 1 with hγdef
  have hγ : ContDiff ℝ ∞ γ := pdd_contDiff_cwLoop
  have hγW : ∀ t, γ t ∈ W := fun t => by
    show 1 / 2 < ‖cwLoop 0 1 t‖ ∧ ‖cwLoop 0 1 t‖ < 2
    rw [pdd_norm_cwLoop]
    norm_num
  have hc1 := tendstoCInftyLocOn_comp (X := ℝ) (Y := ℂ) (Z := V n) isOpen_univ hWo
    (fun _ => γ) γ v w (fun _ => hγ.contDiffOn) hγ.contDiffOn hvsm hwsm
    (fun _ t _ => hγW t) (fun t _ => hγW t) (pdd_tendstoCInftyLocOn_const γ _) hconvW
  have hwγ : ContDiff ℝ ∞ (w ∘ γ) := hwsm.comp_contDiff hγ hγW
  have hc2 := tendstoCInftyLocOn_comp (X := ℝ) (Y := V n) (Z := V n) isOpen_univ
    (isOpen_ne : IsOpen {y : V n | y ≠ 0}) (fun j => v j ∘ γ) (w ∘ γ) (fun _ => proj H) (proj H)
    (fun j => ((hvsm j).comp_contDiff hγ hγW).contDiffOn) hwγ.contDiffOn (fun _ => hprojs) hprojs
    (fun j t _ => hv0 j _ (hγW t)) (fun t _ => hwne _ (hγW t)) hc1
    (pdd_tendstoCInftyLocOn_const _ _)
  -- the loops of `u` are the loops of the rescalings
  set F : ℕ → ℝ → V n := fun j => loopInS H u (cwLoop 0 (ρ' (φ j))) with hFdef
  set F₀ : ℝ → V n := loopInS H w γ with hF₀def
  have hFeq : ∀ j, F j = proj H ∘ (v j ∘ γ) := by
    intro j
    funext t
    simp only [hFdef, loopInS, Function.comp_apply, hvdef]
    rw [(proj_aCoord_smul_aux H hH (c j) (hcpos j) _ (hu.2.1 _ (hWU j _ (hγW t)))).1,
      pdd_cwLoop_scale]
  have hF₀eq : F₀ = proj H ∘ (w ∘ γ) := rfl
  have hunif : ∀ m, TendstoUniformlyOn (fun j => iteratedDeriv m (F j)) (iteratedDeriv m F₀)
      atTop (Set.Icc 0 1) := by
    intro m
    have h := tendstoUniformlyOn_iteratedDeriv_aux _ _ hc2 m _
      (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    simp only [← hFeq, ← hF₀eq] at h
    exact h
  have hFsm : ∀ j, ContDiff ℝ ∞ (F j) := fun j => by
    rw [hFeq]; exact hprojs.comp_contDiff ((hvsm j).comp_contDiff hγ hγW) (fun t => hv0 j _ (hγW t))
  have hF₀sm : ContDiff ℝ ∞ F₀ := hprojs.comp_contDiff hwγ (fun t => hwne _ (hγW t))
  -- the action of the limit loop is `Q`
  have hlimA := tendsto_loopAction_aux F F₀ hF₀sm.continuous (hF₀sm.continuous_deriv (by simp))
    (fun j => ⟨(hFsm j).continuous, (hFsm j).continuous_deriv (by simp)⟩)
    (by simpa using hunif 0) (by simpa [iteratedDeriv_one] using hunif 1)
  have hρw : Tendsto (fun j => ρ' (φ j)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hρ'.comp hφ.tendsto_atTop, Eventually.of_forall fun j => hρ'0 _⟩
  have hwact : loopAction H w γ = Q := tendsto_nhds_unique hlimA (hQ.comp hρw)
  -- `w` is nonconstant
  have hnc' : ∃ z₁ : ℂ, z₁ ≠ 0 ∧ ∃ z₂ : ℂ, z₂ ≠ 0 ∧ w z₁ ≠ w z₂ := by
    by_contra hcon
    push_neg at hcon
    have hγ0 : ∀ t, γ t ≠ 0 := fun t => hW0 (hγW t)
    have hconst : F₀ = fun _ => F₀ 0 := by
      funext t
      simp only [hF₀def, loopInS]
      rw [hcon _ (hγ0 t) _ (hγ0 0)]
    have h0 : loopAction H w γ = 0 := by
      unfold loopAction
      rw [← hF₀def, hconst]
      simp [liouville, omega0, dot]
    exact hQ0 (hwact.symm.trans h0)
  -- classification of the limit
  obtain ⟨P, k, -, c0, hc0, hwP⟩ :=
    eq_trivialCylinder_of_dlambdaEnergy_eq_zero H hH J hJ w hw hnc' hw0
  obtain ⟨-, c', hloop, -⟩ := trivialCylinder_loop_spec H hH P k c0 hc0
  have hF₀P : F₀ = fun t => P.x ((-(k * P.T)) * t + c') := by
    funext t
    simp only [hF₀def, loopInS]
    rw [hwP _ (hW0 (hγW t))]
    have := hloop (-t)
    simp only [loopInS] at this
    rw [hγdef, pdd_cwLoop_eq, this]
    congr 1
    ring
  have hQk : Q = -(k * P.T) := by
    rw [← hwact]
    unfold loopAction
    rw [← hF₀def, hF₀P]
    exact pdd_loopAction_orbit H hH P _ c'
  have hQabs : |Q| = ((|k| : ℤ) : ℝ) * P.T := by
    rw [hQk, abs_neg, abs_mul, abs_of_pos P.T_pos, Int.cast_abs]
  have hper : Function.Periodic P.x P.T := fun τ => P.periodic τ
  let P' : ReebOrbit H :=
    { x := P.x
      T := |Q|
      T_pos := abs_pos.2 hQ0
      mem := P.mem
      hasDerivAt := P.hasDerivAt
      periodic := fun τ => by rw [hQabs]; exact (hper.int_mul |k|) τ }
  refine ⟨fun j => φ j + N, fun a b hab => Nat.add_lt_add_right (hφ hab) N, P', rfl, c', ?_⟩
  have hF₀Q : F₀ = fun t => P'.x (Q * t + c') := by
    rw [hF₀P, hQk]
  intro m
  have hper' : ∀ j, Function.Periodic (F j) 1 := fun j t => by
    simp only [hFdef, loopInS]
    rw [pdd_cwLoop_periodic]
  have hper0 : Function.Periodic F₀ 1 := fun t => by
    simp only [hF₀def, loopInS, hγdef]
    rw [pdd_cwLoop_periodic]
  show TendstoUniformly (fun j => iteratedDeriv m (F j)) _ atTop
  rw [← hF₀Q]
  exact tendstoUniformly_of_periodic_aux _ _ (fun j => periodic_iteratedDeriv_aux _ (hper' j) m)
    (periodic_iteratedDeriv_aux _ hper0 m) (hunif m)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C)
    (Q : ℝ) (hQ0 : Q ≠ 0) (hQ : Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 Q))
    (ρ : ℕ → ℝ) (hρ : ∀ k, 0 < ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : ReebOrbit H, P.T = |Q| ∧ ∃ c : ℝ,
      TendstoCInfty (fun k => loopInS H u (cwLoop 0 (ρ (φ k)))) (fun t => P.x (Q * t + c)) :=
  FiniteEnergyPlane.exists_subseq_tendstoCInfty_cwLoop_aux H hH J hJ u hu hG Q hQ0 hQ ρ hρ hρ0
