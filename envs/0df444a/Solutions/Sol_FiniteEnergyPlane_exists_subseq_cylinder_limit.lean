-- Prove2me | solution 1 for FiniteEnergyPlane.exists_subseq_cylinder_limit
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-25T22:07:30.475679+00:00
-- url     : https://prove2.me/submissions/b7db2ab6-961a-445a-87ea-d93a58ae633f

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendsto_rescaled_plane
import Theorems.Thm_FiniteEnergyPlane_tendstoCInftyLocOn_comp
import Theorems.Thm_FiniteEnergyPlane_trivialCylinder_loop_spec
import Theorems.Thm_FiniteEnergyPlane_eq_trivialCylinder_of_dlambdaEnergy_eq_zero
import Theorems.Thm_FiniteEnergyPlane_loopAction_ccwLoop_eq_dlambdaEnergy
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_pos_of_plane
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg
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
theorem tendstoCInftyLocOn_const_aux {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (g : X → Y) (U : Set X) :
    JHolomorphic.TendstoCInftyLocOn (fun _ : ℕ => g) g U := fun K _ _ m =>
  Metric.tendstoUniformlyOn_iff.2 fun ε hε => Eventually.of_forall fun _ x _ => by simpa using hε

theorem ccwLoop_periodic_aux (R : ℝ) : Function.Periodic (ccwLoop R) 1 := by
  intro t
  simp only [ccwLoop]
  congr 1
  rw [show (((2 * π * (t + 1) : ℝ)) : ℂ) * Complex.I =
      ((2 * π * t : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem ccwLoop_ne_zero_aux (t : ℝ) : ccwLoop 1 t ≠ 0 := by
  simp [ccwLoop, Complex.exp_ne_zero]

theorem contDiff_ccwLoop_aux (R : ℝ) : ContDiff ℝ ∞ (ccwLoop R) := by
  unfold ccwLoop
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => ((2 * π * t : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
  exact contDiff_const.mul (Complex.contDiff_exp.comp (h1.mul contDiff_const))

/-- Limits of a finite-energy plane along circles going to infinity. -/
theorem exists_subseq_cylinder_limit_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂)
    (hG : ∃ C : ℝ, ∀ z : ℂ, ‖z‖ * gradNorm H u z ≤ C) (R : ℕ → ℝ)
    (hR : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : ReebOrbit H,
      P.T = (dlambdaEnergy H Set.univ u).toReal ∧ ∃ c : ℝ,
        TendstoCInfty (fun j => loopInS H u (ccwLoop (R (φ j)))) (fun t => P.x (P.T * t + c)) ∧
        ∀ L : ℝ, Tendsto (fun j => aCoord H (u ((Real.exp (2 * π * L) * R (φ j) : ℝ) : ℂ)) -
          aCoord H (u ((R (φ j) : ℝ) : ℂ))) atTop (𝓝 (P.T * L)) := by
  classical
  obtain ⟨-, hprojs, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  set D := dlambdaEnergy H Set.univ u with hDdef
  have hD0 : 0 < D := dlambdaEnergy_pos_of_plane H hH J hJ u hu hnc
  have hDE : D ≤ energy H Set.univ u :=
    (energyDensity_nonneg H hH J hJ Set.univ isOpen_univ u hu).2.2.1
  have hDtop : D ≠ ⊤ := ne_top_of_le_ne_top hu.2.2.2.ne hDE
  have hT : 0 < D.toReal := ENNReal.toReal_pos hD0.ne' hDtop
  -- actions of large circles
  have hact : Tendsto (fun R => loopAction H u (ccwLoop R)) atTop (𝓝 D.toReal) := by
    have hball : Tendsto (fun R : ℝ => dlambdaEnergy H (ball 0 R) u) atTop (𝓝 D) := by
      set μ := (volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal (dlambdaDensity H u z))
      have hμ : ∀ s : Set ℂ, MeasurableSet s → dlambdaEnergy H s u = μ s := fun s hs =>
        (withDensity_apply _ hs).symm
      have hU : (⋃ R : ℝ, ball (0 : ℂ) R) = Set.univ := by
        ext z
        simp only [Set.mem_iUnion, mem_ball_zero_iff, Set.mem_univ, iff_true]
        exact ⟨‖z‖ + 1, by linarith⟩
      have h := tendsto_measure_iUnion_atTop (μ := μ) (s := fun R : ℝ => ball (0 : ℂ) R)
        (fun a b hab => ball_subset_ball hab)
      rw [hU, ← hμ _ MeasurableSet.univ] at h
      exact h.congr fun R => (hμ _ measurableSet_ball).symm
    refine ((ENNReal.tendsto_toReal hDtop).comp hball).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact (loopAction_ccwLoop_eq_dlambdaEnergy H hH J hJ u hu R hR).symm
  -- pass to a tail where `R > 0`
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hR.eventually (eventually_gt_atTop (0 : ℝ)))
  set R' : ℕ → ℝ := fun k => R (k + N) with hR'def
  have hR'0 : ∀ k, 0 < R' k := fun k => hN _ (Nat.le_add_left _ _)
  have hR' : Tendsto R' atTop atTop := hR.comp (tendsto_add_atTop_nat N)
  obtain ⟨φ, hφ, w, hw, hw0, hconv⟩ :=
    exists_subseq_tendsto_rescaled_plane H hH J hJ u hu hG R' hR'0 hR'
  set ψ : ℕ → ℕ := fun j => φ j + N with hψdef
  have hψ : StrictMono ψ := fun a b hab => Nat.add_lt_add_right (hφ hab) N
  set ρ : ℕ → ℝ := fun j => R (ψ j) with hρdef
  have hρ0 : ∀ j, 0 < ρ j := fun j => hR'0 (φ j)
  have hρ : Tendsto ρ atTop atTop := hR'.comp hφ.tendsto_atTop
  set c : ℕ → ℝ := fun j => Real.exp (-2 * aCoord H (u ((ρ j : ℝ) : ℂ))) with hcdef
  have hcpos : ∀ j, 0 < c j := fun j => Real.exp_pos _
  set v : ℕ → ℂ → V n := fun j z => c j • u ((ρ j : ℂ) * z) with hvdef
  change JHolomorphic.TendstoCInftyLocOn v w {z | z ≠ 0} at hconv
  have hsmu : ContDiff ℝ ∞ u := contDiffOn_univ.1 hu.1
  have hvsm : ∀ j, ContDiff ℝ ∞ (v j) := fun j =>
    (hsmu.comp (contDiff_const.mul contDiff_id)).const_smul (c j)
  have hv0 : ∀ j z, v j z ≠ 0 := fun j z =>
    smul_ne_zero (hcpos j).ne' (hu.2.1 _ (Set.mem_univ _))
  -- the unit circle
  set γ : ℝ → ℂ := ccwLoop 1 with hγdef
  have hγ : ContDiff ℝ ∞ γ := contDiff_ccwLoop_aux 1
  have hγ0 : ∀ t, γ t ≠ 0 := ccwLoop_ne_zero_aux
  have hwsm : ContDiffOn ℝ ∞ w {z | z ≠ 0} := hw.1
  have hwne : ∀ z, z ≠ 0 → w z ≠ 0 := fun z hz => hw.2.1 z hz
  have hc1 := tendstoCInftyLocOn_comp (X := ℝ) (Y := ℂ) (Z := V n) isOpen_univ
    (isOpen_ne : IsOpen {z : ℂ | z ≠ 0}) (fun _ => γ) γ v w (fun _ => hγ.contDiffOn)
    hγ.contDiffOn (fun j => (hvsm j).contDiffOn) hwsm (fun _ t _ => hγ0 t) (fun t _ => hγ0 t)
    (tendstoCInftyLocOn_const_aux γ _) hconv
  have hwγ : ContDiff ℝ ∞ (w ∘ γ) := hwsm.comp_contDiff hγ hγ0
  have hc2 := tendstoCInftyLocOn_comp (X := ℝ) (Y := V n) (Z := V n) isOpen_univ
    (isOpen_ne : IsOpen {y : V n | y ≠ 0}) (fun j => v j ∘ γ) (w ∘ γ) (fun _ => proj H) (proj H)
    (fun j => ((hvsm j).comp hγ).contDiffOn) hwγ.contDiffOn (fun _ => hprojs) hprojs
    (fun j t _ => hv0 j _) (fun t _ => hwne _ (hγ0 t)) hc1 (tendstoCInftyLocOn_const_aux _ _)
  -- the loops of `u` are the loops of the rescalings
  set F : ℕ → ℝ → V n := fun j => loopInS H u (ccwLoop (R (ψ j))) with hFdef
  set F₀ : ℝ → V n := loopInS H w (ccwLoop 1) with hF₀def
  have hFeq : ∀ j, F j = proj H ∘ (v j ∘ γ) := by
    intro j
    funext t
    simp only [hFdef, loopInS, Function.comp_apply, hvdef, hγdef]
    rw [(proj_aCoord_smul_aux H hH (c j) (hcpos j) _ (hu.2.1 _ (Set.mem_univ _))).1]
    congr 2
    simp only [ccwLoop, hρdef]
    push_cast
    ring
  have hF₀eq : F₀ = proj H ∘ (w ∘ γ) := rfl
  have hunif : ∀ m, TendstoUniformlyOn (fun j => iteratedDeriv m (F j)) (iteratedDeriv m F₀)
      atTop (Set.Icc 0 1) := by
    intro m
    have h := tendstoUniformlyOn_iteratedDeriv_aux _ _ hc2 m _ (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    simp only [← hFeq, ← hF₀eq] at h
    exact h
  have hFsm : ∀ j, ContDiff ℝ ∞ (F j) := fun j => by
    rw [hFeq]; exact hprojs.comp_contDiff ((hvsm j).comp hγ) (fun t => hv0 j _)
  have hF₀sm : ContDiff ℝ ∞ F₀ := hprojs.comp_contDiff hwγ (fun t => hwne _ (hγ0 t))
  -- the action of the limit loop is `T`
  have hlimA := tendsto_loopAction_aux F F₀ hF₀sm.continuous (hF₀sm.continuous_deriv (by simp))
    (fun j => ⟨(hFsm j).continuous, (hFsm j).continuous_deriv (by simp)⟩)
    (by simpa using hunif 0) (by simpa [iteratedDeriv_one] using hunif 1)
  have hwact : loopAction H w (ccwLoop 1) = D.toReal :=
    tendsto_nhds_unique hlimA (hact.comp hρ)
  -- `w` is nonconstant
  have hnc' : ∃ z₁ : ℂ, z₁ ≠ 0 ∧ ∃ z₂ : ℂ, z₂ ≠ 0 ∧ w z₁ ≠ w z₂ := by
    by_contra hcon
    push_neg at hcon
    have hconst : F₀ = fun _ => F₀ 0 := by
      funext t
      simp only [hF₀def, loopInS]
      rw [hcon _ (hγ0 t) _ (hγ0 0)]
    have h0 : loopAction H w (ccwLoop 1) = 0 := by
      unfold loopAction
      rw [← hF₀def, hconst]
      simp [liouville, omega0, dot]
    linarith
  -- classification of the limit
  obtain ⟨P, k, -, c0, hc0, hwP⟩ :=
    eq_trivialCylinder_of_dlambdaEnergy_eq_zero H hH J hJ w hw hnc' hw0
  obtain ⟨hA', c', hloop, hactP⟩ := trivialCylinder_loop_spec H hH P k c0 hc0
  have hloopeq : F₀ = loopInS H (fun z => trivialCylinder P (c0 * z ^ k)) (ccwLoop 1) := by
    funext t
    simp only [hF₀def, loopInS]
    rw [hwP _ (hγ0 t)]
  have hkT : (k : ℝ) * P.T = D.toReal := by
    rw [← hactP, ← hwact]
    unfold loopAction
    rw [← hF₀def, hloopeq]
  have hkpos : (0 : ℝ) < k := by
    by_contra hle
    push_neg at hle
    nlinarith [P.T_pos]
  -- the orbit with period `k T_P`
  let P' : ReebOrbit H :=
    { x := P.x
      T := k * P.T
      T_pos := mul_pos hkpos P.T_pos
      mem := P.mem
      hasDerivAt := P.hasDerivAt
      periodic := fun τ => (Function.Periodic.int_mul (fun τ => P.periodic τ) k) τ }
  have hF₀P : F₀ = fun t => P'.x (P'.T * t + c') := by
    rw [hloopeq]
    funext t
    exact hloop t
  refine ⟨ψ, hψ, P', hkT, c', ?_, ?_⟩
  · intro m
    have hper : ∀ j, Function.Periodic (F j) 1 := fun j t => by
      simp only [hFdef, loopInS]
      rw [ccwLoop_periodic_aux]
    have hper0 : Function.Periodic F₀ 1 := fun t => by
      simp only [hF₀def, loopInS]
      rw [ccwLoop_periodic_aux]
    rw [← hF₀P]
    exact tendstoUniformly_of_periodic_aux _ _ (fun j => periodic_iteratedDeriv_aux _ (hper j) m)
      (periodic_iteratedDeriv_aux _ hper0 m) (hunif m)
  · intro L
    have hpt : ∀ z : ℂ, z ≠ 0 → Tendsto (fun j => aCoord H (v j z)) atTop (𝓝 (aCoord H (w z))) := by
      intro z hz
      have h1 := tendsto_of_tendstoCInftyLocOn_aux v w _ hconv z hz
      have hca : ContinuousAt (aCoord H) (w z) :=
        haCs.continuousOn.continuousAt ((isOpen_ne : IsOpen {y : V n | y ≠ 0}).mem_nhds (hwne z hz))
      exact hca.tendsto.comp h1
    have hvA : ∀ j z, aCoord H (v j z) = aCoord H (u ((ρ j : ℂ) * z)) + Real.log (c j) / 2 :=
      fun j z => (proj_aCoord_smul_aux H hH (c j) (hcpos j) _ (hu.2.1 _ (Set.mem_univ _))).2
    set z₁ : ℂ := ((Real.exp (2 * π * L) : ℝ) : ℂ) with hz₁def
    have hz₁ : z₁ ≠ 0 := by simp [hz₁def, (Real.exp_pos _).ne']
    have e : ∀ j, aCoord H (u ((Real.exp (2 * π * L) * R (ψ j) : ℝ) : ℂ)) -
        aCoord H (u ((R (ψ j) : ℝ) : ℂ)) = aCoord H (v j z₁) - aCoord H (v j 1) := by
      intro j
      rw [hvA, hvA, mul_one]
      have h1 : ((Real.exp (2 * π * L) * R (ψ j) : ℝ) : ℂ) = (ρ j : ℂ) * z₁ := by
        rw [Complex.ofReal_mul, mul_comm]
      rw [h1]
      ring
    simp_rw [e]
    have hlim := (hpt z₁ hz₁).sub (hpt 1 one_ne_zero)
    convert hlim using 2
    rw [hwP _ hz₁, hwP _ one_ne_zero, (hA' _ hz₁).2, (hA' _ one_ne_zero).2]
    have hc0n : 0 < ‖c0‖ := norm_pos_iff.2 hc0
    have hn : ‖c0 * z₁ ^ k‖ = ‖c0‖ * Real.exp (2 * π * L) ^ k := by
      rw [norm_mul, norm_zpow, hz₁def, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    rw [hn, one_zpow, mul_one, Real.log_mul hc0n.ne' (zpow_ne_zero _ (Real.exp_pos _).ne'),
      Real.log_zpow, Real.log_exp]
    show (k : ℝ) * P.T * L =
      P.T / (2 * π) * (Real.log ‖c0‖ + k * (2 * π * L)) - P.T / (2 * π) * Real.log ‖c0‖
    field_simp
    ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂)
    (hG : ∃ C : ℝ, ∀ z : ℂ, ‖z‖ * gradNorm H u z ≤ C) (R : ℕ → ℝ)
    (hR : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : ReebOrbit H,
      P.T = (dlambdaEnergy H Set.univ u).toReal ∧ ∃ c : ℝ,
        TendstoCInfty (fun j => loopInS H u (ccwLoop (R (φ j)))) (fun t => P.x (P.T * t + c)) ∧
        ∀ L : ℝ, Tendsto (fun j => aCoord H (u ((Real.exp (2 * π * L) * R (φ j) : ℝ) : ℂ)) -
          aCoord H (u ((R (φ j) : ℝ) : ℂ))) atTop (𝓝 (P.T * L)) :=
  exists_subseq_cylinder_limit_aux H hH J hJ u hu hnc hG R hR
