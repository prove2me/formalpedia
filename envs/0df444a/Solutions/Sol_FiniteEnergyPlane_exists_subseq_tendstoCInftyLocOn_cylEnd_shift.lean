-- Prove2me | solution 1 for FiniteEnergyPlane.exists_subseq_tendstoCInftyLocOn_cylEnd_shift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T21:56:38.236302+00:00
-- url     : https://prove2.me/submissions/ca175780-af30-4301-998e-0f6a1ed019b6

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Theorems.Thm_FiniteEnergyPlane_exists_norm_mul_gradNorm_le_near_puncture
import Theorems.Thm_FiniteEnergyPlane_exists_phase_eq_of_forall_close_shift
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendsto_rescaled_punctured
import Theorems.Thm_FiniteEnergyPlane_eq_trivialCylinder_of_dlambdaEnergy_eq_zero
import Theorems.Thm_FiniteEnergyPlane_trivialCylinder_loop_spec
import Theorems.Thm_FiniteEnergyPlane_tendstoCInftyLocOn_comp
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_reeb_spec



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem s2_cwLoop_scale (ρ t : ℝ) : cwLoop 0 ρ t = (ρ : ℂ) * cwLoop 0 1 t := by
  simp [cwLoop]

theorem s2_norm_cwLoop (t : ℝ) : ‖cwLoop 0 1 t‖ = 1 := by
  simp only [cwLoop, zero_add, Complex.ofReal_one, one_mul]
  rw [show (-((2 * π * t : ℝ) : ℂ)) * Complex.I = ((-(2 * π * t) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem s2_cylEnd_eq (s t : ℝ) :
    cylEnd s t = ((Real.exp (-(2 * π * s)) : ℝ) : ℂ) * cwLoop 0 1 t := by
  unfold cylEnd; rw [s2_cwLoop_scale]

theorem s2_norm_cylEnd (s t : ℝ) : ‖cylEnd s t‖ = Real.exp (-(2 * π * s)) := by
  rw [s2_cylEnd_eq, norm_mul, s2_norm_cwLoop, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

theorem s2_cylEnd_ne_zero (s t : ℝ) : cylEnd s t ≠ 0 := by
  rw [← norm_pos_iff, s2_norm_cylEnd]; exact Real.exp_pos _

theorem s2_cylEnd_add (s a t : ℝ) :
    cylEnd (s + a) t = ((Real.exp (-(2 * π * a)) : ℝ) : ℂ) * cylEnd s t := by
  rw [s2_cylEnd_eq, s2_cylEnd_eq, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3; ring

theorem s2_cylEnd_zero (s : ℝ) : cylEnd s 0 = ((Real.exp (-(2 * π * s)) : ℝ) : ℂ) := by
  rw [s2_cylEnd_eq]; simp [cwLoop]

theorem s2_cwLoop_periodic : Function.Periodic (cwLoop 0 1) 1 := by
  intro t
  simp only [cwLoop, zero_add, Complex.ofReal_one, one_mul]
  rw [show (-((2 * π * (t + 1) : ℝ) : ℂ)) * Complex.I =
      (-((2 * π * t : ℝ) : ℂ)) * Complex.I + -(2 * π * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]

theorem s2_contDiff_cwLoop : ContDiff ℝ ∞ (cwLoop 0 1) := by
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

/-- The cylindrical end map `p ↦ cylEnd p.1 p.2` is smooth. -/
theorem s2_contDiff_cyl : ContDiff ℝ ∞ (fun p : ℝ × ℝ => cylEnd p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => cylEnd p.1 p.2) =
      fun p => ((Real.exp (-(2 * π * p.1)) : ℝ) : ℂ) * cwLoop 0 1 p.2 :=
    funext fun p => s2_cylEnd_eq _ _
  rw [h]
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ((Real.exp (-(2 * π * p.1)) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_fst).neg))
  exact h1.mul (s2_contDiff_cwLoop.comp contDiff_snd)

/-- Trivial cylinders scale under positive real dilations. -/
theorem s2_trivialCylinder_real_mul {n : ℕ} {H : V n → ℝ} (P : ReebOrbit H) {r : ℝ} (hr : 0 < r)
    (ζ : ℂ) : trivialCylinder P ((r : ℂ) * ζ) = (r ^ (P.T / π)) • trivialCylinder P ζ := by
  unfold trivialCylinder
  rw [Complex.arg_real_mul _ hr, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
    Real.mul_rpow hr.le (norm_nonneg _), smul_smul]

/-- `C^∞_loc` convergence is inherited by a sequence agreeing on an open set with a shift of a
convergent sequence. -/
theorem s2_tendstoCInftyLocOn_of_eqOn_shift {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {U : Set X} (hU : IsOpen U)
    (f g : ℕ → X → Y) (h₀ : X → Y) (j₀ : ℕ)
    (heq : ∀ k, Set.EqOn (f (k + j₀)) (g k) U)
    (h : JHolomorphic.TendstoCInftyLocOn g h₀ U) : JHolomorphic.TendstoCInftyLocOn f h₀ U := by
  intro K hK hKc m
  have hg := Metric.tendstoUniformlyOn_iff.1 (h K hK hKc m)
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hg ε hε)
  refine eventually_atTop.2 ⟨N + j₀, fun k hk x hx => ?_⟩
  have hk' : k = (k - j₀) + j₀ := by omega
  have hd : iteratedFDeriv ℝ m (f k) x = iteratedFDeriv ℝ m (g (k - j₀)) x := by
    have he : f k =ᶠ[𝓝 x] g (k - j₀) := by
      rw [hk']
      refine (heq (k - j₀)).eventuallyEq_of_mem (hU.mem_nhds (hK hx)) |>.trans ?_
      rw [Nat.add_sub_cancel]
    exact (he.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds
  rw [hd]
  exact hN (k - j₀) (by omega) x hx

/-- `C^∞_loc` convergence passes to a tail and to an open subset. -/
theorem s2_tendstoCInftyLocOn_shift_mono {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {U W : Set X} (hWU : W ⊆ U)
    (f : ℕ → X → Y) (g : X → Y) (j₀ : ℕ) (h : JHolomorphic.TendstoCInftyLocOn f g U) :
    JHolomorphic.TendstoCInftyLocOn (fun k => f (k + j₀)) g W := by
  intro K hK hKc m
  have hg := Metric.tendstoUniformlyOn_iff.1 (h K (hK.trans hWU) hKc m)
  exact Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
    (tendsto_add_atTop_nat j₀).eventually (hg ε hε)

/-- `C^∞_loc` convergence on `ℝ × ℝ` follows from convergence on every strip `(-N, N) × ℝ`. -/
theorem s2_tendstoCInftyLocOn_univ_of_strips {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (f : ℕ → ℝ × ℝ → Y) (g : ℝ × ℝ → Y)
    (h : ∀ N : ℕ, JHolomorphic.TendstoCInftyLocOn f g (Set.Ioo (-(N : ℝ)) N ×ˢ Set.univ)) :
    JHolomorphic.TendstoCInftyLocOn f g Set.univ := by
  intro K _ hKc m
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).1 hKc.isBounded
  refine h (⌈R⌉₊ + 1) K (fun p hp => ?_) hKc m
  have hp' : ‖p‖ ≤ R := by simpa using hR hp
  have h1 : |p.1| ≤ ‖p‖ := by
    have := norm_fst_le p
    rwa [Real.norm_eq_abs] at this
  have h2 : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩ <;> push_cast <;>
    [linarith [neg_abs_le p.1]; linarith [le_abs_self p.1]]

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem s2_proj_aCoord_smul {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
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

theorem s2_tendsto_of_tendstoCInftyLocOn {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : ℕ → X → Y) (g : X → Y) (U : Set X)
    (h : JHolomorphic.TendstoCInftyLocOn f g U) (x : X) (hx : x ∈ U) :
    Tendsto (fun k => f k x) atTop (𝓝 (g x)) := by
  have h0 := (h {x} (Set.singleton_subset_iff.2 hx) isCompact_singleton 0).tendsto_at
    (Set.mem_singleton x)
  have hc := ((continuousMultilinearCurryFin0 ℝ X Y).continuous.tendsto _).comp h0
  simpa [iteratedFDeriv_zero_eq_comp, Function.comp_def] using hc

theorem s2_tendstoCInftyLocOn_const {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (g : X → Y) (U : Set X) :
    JHolomorphic.TendstoCInftyLocOn (fun _ : ℕ => g) g U := fun K _ _ m =>
  Metric.tendstoUniformlyOn_iff.2 fun ε hε => Eventually.of_forall fun _ x _ => by simpa using hε

theorem s2_cwLoop_eq_ccw (t : ℝ) : cwLoop 0 1 t = ccwLoop 1 (-t) := by
  simp only [cwLoop, ccwLoop, zero_add]
  congr 2
  push_cast
  ring

theorem s2_hasDerivAt_orbit {n : ℕ} {H : V n → ℝ} (Q : ReebOrbit H) (α c t : ℝ) :
    HasDerivAt (fun t => Q.x (α * t + c)) (α • reeb H (Q.x (α * t + c))) t := by
  have hlin : HasDerivAt (fun t : ℝ => α * t + c) α t := by
    simpa using ((hasDerivAt_id t).const_mul α).add_const c
  exact (Q.hasDerivAt _).scomp t hlin

theorem exists_subseq_tendstoCInftyLocOn_cylEnd_shift_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1)
    (hloop : ∀ ε : ℝ, 0 < ε → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∃ c' : ℝ, ∀ t : ℝ,
      ‖loopInS H u (cwLoop 0 r) t - P.x (σ * P.T * t + c')‖ ≤ ε)
    (s : ℕ → ℝ) (hs : Tendsto s atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c : ℝ,
      JHolomorphic.TendstoCInftyLocOn
        (fun j (p : ℝ × ℝ) => endA H u cylEnd (p + (s (φ j), 0)) - endA H u cylEnd (s (φ j), 0))
        (fun p => σ * P.T * p.1) Set.univ ∧
      JHolomorphic.TendstoCInftyLocOn
        (fun j (p : ℝ × ℝ) => endW H u cylEnd (p + (s (φ j), 0)))
        (fun p => P.x (σ * P.T * p.2 + c)) Set.univ := by
  classical
  obtain ⟨-, hprojs, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hσT : σ * P.T ≠ 0 :=
    mul_ne_zero (by rcases hσ with h | h <;> rw [h] <;> norm_num) P.T_pos.ne'
  have hR : ∀ y, y ∈ energySurface H → reeb H y ≠ 0 := fun y hy h0 => by
    have := (reeb_spec H hH y hy).2.1
    rw [h0] at this
    simp [liouville, omega0, dot] at this
  have hγ0 : ∀ t, cwLoop 0 1 t ≠ 0 := fun t => by
    rw [← norm_pos_iff, s2_norm_cwLoop]; exact one_pos
  -- radii
  obtain ⟨ρ, hρk⟩ : ∃ ρ : ℕ → ℝ, ∀ k, Real.exp (-(2 * π * s k)) = ρ k := ⟨_, fun _ => rfl⟩
  have hρ : ∀ k, 0 < ρ k := fun k => hρk k ▸ Real.exp_pos _
  have hρ0 : Tendsto ρ atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => -(2 * π * s k)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (hs.const_mul_atTop (by positivity))
    have h2 := Real.tendsto_exp_atBot.comp h1
    exact h2.congr fun k => hρk k
  obtain ⟨φ, hφ, w, hw, hw0, hconv⟩ := exists_subseq_tendsto_rescaled_punctured H hH J hJ u hu
    (exists_norm_mul_gradNorm_le_near_puncture H hH J hJ u hu) ρ hρ hρ0
  set cc : ℕ → ℝ := fun j => Real.exp (-2 * aCoord H (u ((ρ (φ j) : ℝ) : ℂ))) with hccdef
  have hccpos : ∀ j, 0 < cc j := fun j => Real.exp_pos _
  set v : ℕ → ℂ → V n := fun j z => cc j • u (((ρ (φ j) : ℝ) : ℂ) * z) with hvdef
  change JHolomorphic.TendstoCInftyLocOn v w {z | z ≠ 0} at hconv
  have hρφ : Tendsto (fun j => ρ (φ j)) atTop (𝓝 0) := hρ0.comp hφ.tendsto_atTop
  have hmem : ∀ j z, z ≠ 0 → ρ (φ j) * ‖z‖ < 1 →
      ((ρ (φ j) : ℝ) : ℂ) * z ∈ ball (0 : ℂ) 1 \ {0} := by
    intro j z hz h1
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ _).le]
      exact h1
    · exact mul_ne_zero (by exact_mod_cast (hρ _).ne') hz
  -- `v` in terms of `u`
  have hvpa : ∀ j z, z ≠ 0 → ρ (φ j) * ‖z‖ < 1 →
      proj H (v j z) = proj H (u (((ρ (φ j) : ℝ) : ℂ) * z)) ∧
      aCoord H (v j z) = aCoord H (u (((ρ (φ j) : ℝ) : ℂ) * z)) -
        aCoord H (u ((ρ (φ j) : ℝ) : ℂ)) := by
    intro j z hz h1
    obtain ⟨hp, ha⟩ := s2_proj_aCoord_smul H hH (cc j) (hccpos j) _ (hu.2.1 _ (hmem j z hz h1))
    refine ⟨hp, ?_⟩
    rw [ha, hccdef]
    simp only [Real.log_exp]
    ring
  have hev1 : ∀ᶠ j in atTop, ρ (φ j) < 1 := hρφ.eventually (Iio_mem_nhds one_pos)
  -- the limit loop
  set F : ℕ → ℝ → V n := fun j => loopInS H u (cwLoop 0 (ρ (φ j))) with hFdef
  set L : ℝ → V n := fun t => proj H (w (cwLoop 0 1 t)) with hLdef
  have hwne : ∀ z : ℂ, z ≠ 0 → w z ≠ 0 := fun z hz => hw.2.1 z hz
  have hF : ∀ t, Tendsto (fun j => F j t) atTop (𝓝 (L t)) := by
    intro t
    have hpt := s2_tendsto_of_tendstoCInftyLocOn v w _ hconv (cwLoop 0 1 t) (hγ0 t)
    have hcont : ContinuousAt (proj H) (w (cwLoop 0 1 t)) :=
      (hprojs.continuousOn.continuousAt (isOpen_ne.mem_nhds (hwne _ (hγ0 t))))
    refine (hcont.tendsto.comp hpt).congr' ?_
    filter_upwards [hev1] with j hj
    simp only [Function.comp_apply, hFdef, loopInS]
    rw [s2_cwLoop_scale (ρ (φ j)) t, (hvpa j _ (hγ0 t) (by rw [s2_norm_cwLoop, mul_one]; exact hj)).1]
  have hρw : Tendsto (fun j => ρ (φ j)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hρφ, Eventually.of_forall fun j => hρ _⟩
  have hclose : ∀ ε > 0, ∀ᶠ j in atTop, ∃ c : ℝ, ∀ t : ℝ,
      ‖F j t - P.x (σ * P.T * t + c)‖ ≤ ε := fun ε hε => hρw.eventually (hloop ε hε)
  have hPxc : Continuous P.x :=
    continuous_iff_continuousAt.2 fun τ => (P.hasDerivAt τ).continuousAt
  obtain ⟨cs, hcs⟩ := exists_phase_eq_of_forall_close_shift P.T_pos hPxc
    (fun τ => P.periodic τ) (σ * P.T) F L hF hclose
  -- the limit is nonconstant
  have hnc : ∃ z₁ : ℂ, z₁ ≠ 0 ∧ ∃ z₂ : ℂ, z₂ ≠ 0 ∧ w z₁ ≠ w z₂ := by
    by_contra hcon
    push_neg at hcon
    have hfun : (fun t => P.x (σ * P.T * t + cs)) = fun _ => L 0 := by
      funext t
      rw [← hcs t]
      simp only [hLdef]
      rw [hcon _ (hγ0 t) _ (hγ0 0)]
    have h1 := s2_hasDerivAt_orbit P (σ * P.T) cs 0
    rw [hfun] at h1
    exact smul_ne_zero hσT (hR _ (P.mem _)) (h1.unique (hasDerivAt_const 0 (L 0)))
  -- classification of the limit
  obtain ⟨P', k, -, c0, hc0, hwP⟩ :=
    eq_trivialCylinder_of_dlambdaEnergy_eq_zero H hH J hJ w hw hnc hw0
  obtain ⟨hY1, c', hY2, -⟩ := trivialCylinder_loop_spec H hH P' k c0 hc0
  have hLP' : ∀ t, L t = P'.x (-(k * P'.T) * t + c') := by
    intro t
    have := hY2 (-t)
    simp only [loopInS] at this
    simp only [hLdef]
    rw [hwP _ (hγ0 t), s2_cwLoop_eq_ccw, this]
    congr 1
    ring
  have hκ : -(k * P'.T) = σ * P.T := by
    have hfun : (fun t => P.x (σ * P.T * t + cs)) = fun t => P'.x (-(k * P'.T) * t + c') :=
      funext fun t => by rw [← hcs t, hLP' t]
    have d1 := s2_hasDerivAt_orbit P (σ * P.T) cs 0
    have hpt : P.x (σ * P.T * 0 + cs) = P'.x (-(k * P'.T) * 0 + c') := congrFun hfun 0
    rw [hfun, hpt] at d1
    have e := d1.unique (s2_hasDerivAt_orbit P' (-(k * P'.T)) c' 0)
    have e2 : (σ * P.T - -(k * P'.T)) • reeb H (P'.x (-(k * P'.T) * 0 + c')) = 0 := by
      rw [sub_smul, e, sub_self]
    rcases smul_eq_zero.1 e2 with h | h
    · linarith
    · exact absurd h (hR _ (P'.mem _))
  -- the limit in cylindrical coordinates
  have hwcyl : ∀ p : ℝ × ℝ, w (cylEnd p.1 p.2) =
      ((Real.exp (-(2 * π * p.1))) ^ k) ^ (P'.T / π) • w (cwLoop 0 1 p.2) := by
    intro p
    rw [hwP _ (s2_cylEnd_ne_zero _ _), hwP _ (hγ0 _), s2_cylEnd_eq, mul_zpow,
      ← Complex.ofReal_zpow,
      show c0 * (((Real.exp (-(2 * π * p.1)) ^ k : ℝ) : ℂ) * cwLoop 0 1 p.2 ^ k) =
        ((Real.exp (-(2 * π * p.1)) ^ k : ℝ) : ℂ) * (c0 * cwLoop 0 1 p.2 ^ k) by ring,
      s2_trivialCylinder_real_mul P' (zpow_pos (Real.exp_pos _) k)]
  have hlam : ∀ p : ℝ × ℝ, 0 < ((Real.exp (-(2 * π * p.1))) ^ k) ^ (P'.T / π) := fun p =>
    Real.rpow_pos_of_pos (zpow_pos (Real.exp_pos _) k) _
  set A0 : ℝ := P'.T / (2 * π) * Real.log ‖c0‖ with hA0def
  have haγ : ∀ t, aCoord H (w (cwLoop 0 1 t)) = A0 := by
    intro t
    rw [hwP _ (hγ0 t), (hY1 _ (hγ0 t)).2, norm_mul, norm_zpow, s2_norm_cwLoop, one_zpow, mul_one]
  have haW : ∀ p : ℝ × ℝ, aCoord H (w (cylEnd p.1 p.2)) = A0 + σ * P.T * p.1 := by
    intro p
    rw [hwcyl, (s2_proj_aCoord_smul H hH _ (hlam p) _ (hwne _ (hγ0 _))).2, haγ,
      Real.log_rpow (zpow_pos (Real.exp_pos _) k), Real.log_zpow, Real.log_exp, ← hκ]
    field_simp
  have hpW : ∀ p : ℝ × ℝ, proj H (w (cylEnd p.1 p.2)) = P.x (σ * P.T * p.2 + cs) := by
    intro p
    rw [hwcyl, (s2_proj_aCoord_smul H hH _ (hlam p) _ (hwne _ (hγ0 _))).1, ← hcs p.2]
  have hA0 : A0 = 0 := by
    have h1 : cylEnd 0 0 = 1 := by rw [s2_cylEnd_zero]; simp
    have hz : (1 : ℂ) ≠ 0 := one_ne_zero
    have hpt := s2_tendsto_of_tendstoCInftyLocOn v w _ hconv 1 hz
    have hcont : ContinuousAt (aCoord H) (w 1) :=
      haCs.continuousOn.continuousAt (isOpen_ne.mem_nhds (hwne _ hz))
    have hlim := hcont.tendsto.comp hpt
    have hlim0 : Tendsto (fun j => (aCoord H ∘ fun j => v j 1) j) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev1] with j hj
      simp only [Function.comp_apply]
      rw [(hvpa j 1 hz (by rw [norm_one, mul_one]; exact hj)).2, mul_one, sub_self]
    have := tendsto_nhds_unique hlim hlim0
    have h2 := haW (0, 0)
    simp only [h1, mul_zero, add_zero] at h2
    rw [← h2, this]
  -- convergence on each strip
  have hstrip : ∀ N : ℕ,
      JHolomorphic.TendstoCInftyLocOn
        (fun j (p : ℝ × ℝ) => endA H u cylEnd (p + (s (φ j), 0)) - endA H u cylEnd (s (φ j), 0))
        (fun p => σ * P.T * p.1) (Set.Ioo (-(N : ℝ)) N ×ˢ Set.univ) ∧
      JHolomorphic.TendstoCInftyLocOn
        (fun j (p : ℝ × ℝ) => endW H u cylEnd (p + (s (φ j), 0)))
        (fun p => P.x (σ * P.T * p.2 + cs)) (Set.Ioo (-(N : ℝ)) N ×ˢ Set.univ) := by
    intro N
    set U : Set (ℝ × ℝ) := Set.Ioo (-(N : ℝ)) N ×ˢ Set.univ with hUdef
    have hUo : IsOpen U := isOpen_Ioo.prod isOpen_univ
    set W : Set ℂ := {z | Real.exp (-(2 * π * N)) < ‖z‖ ∧ ‖z‖ < Real.exp (2 * π * N)}
      with hWdef
    have hWo : IsOpen W :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    have hW0 : W ⊆ {z | z ≠ 0} := fun z hz => norm_pos_iff.1 (lt_trans (Real.exp_pos _) hz.1)
    have hcylW : Set.MapsTo (fun p : ℝ × ℝ => cylEnd p.1 p.2) U W := by
      intro p hp
      have h1 := hp.1.1
      have h2 := hp.1.2
      show Real.exp (-(2 * π * N)) < ‖cylEnd p.1 p.2‖ ∧ ‖cylEnd p.1 p.2‖ < Real.exp (2 * π * N)
      rw [s2_norm_cylEnd]
      constructor <;> apply Real.exp_lt_exp.2 <;> nlinarith [Real.pi_pos]
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.1
      (hρφ.eventually (Iio_mem_nhds (Real.exp_pos (-(2 * π * N)))))
    have hsmall : ∀ k, ∀ z ∈ W, z ≠ 0 ∧ ρ (φ (k + j₀)) * ‖z‖ < 1 := by
      intro k z hz
      refine ⟨hW0 hz, ?_⟩
      have h1 : ρ (φ (k + j₀)) < Real.exp (-(2 * π * N)) := hj₀ _ (Nat.le_add_left _ _)
      calc ρ (φ (k + j₀)) * ‖z‖ < Real.exp (-(2 * π * N)) * Real.exp (2 * π * N) :=
            mul_lt_mul'' h1 hz.2 (hρ _).le (norm_nonneg _)
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    set v' : ℕ → ℂ → V n := fun k => v (k + j₀) with hv'def
    have hv'sm : ∀ k, ContDiffOn ℝ ∞ (v' k) W := fun k =>
      (hu.1.comp (contDiff_const.mul contDiff_id).contDiffOn fun z hz =>
        hmem _ z (hsmall k z hz).1 (hsmall k z hz).2).const_smul (cc _)
    have hv'0 : ∀ k, ∀ z ∈ W, v' k z ≠ 0 := fun k z hz =>
      smul_ne_zero (hccpos _).ne' (hu.2.1 _ (hmem _ z (hsmall k z hz).1 (hsmall k z hz).2))
    have hconvW : JHolomorphic.TendstoCInftyLocOn v' w W :=
      s2_tendstoCInftyLocOn_shift_mono hW0 v w j₀ hconv
    have hwsm : ContDiffOn ℝ ∞ w W := hw.1.mono hW0
    have hcyl := s2_contDiff_cyl
    have hc1 := tendstoCInftyLocOn_comp (X := ℝ × ℝ) (Y := ℂ) (Z := V n) hUo hWo
      (fun _ => fun p : ℝ × ℝ => cylEnd p.1 p.2) (fun p : ℝ × ℝ => cylEnd p.1 p.2) v' w
      (fun _ => hcyl.contDiffOn) hcyl.contDiffOn hv'sm hwsm (fun _ => hcylW) hcylW
      (s2_tendstoCInftyLocOn_const _ _) hconvW
    have hvc : ∀ k, ContDiffOn ℝ ∞ (v' k ∘ fun p : ℝ × ℝ => cylEnd p.1 p.2) U := fun k =>
      (hv'sm k).comp hcyl.contDiffOn hcylW
    have hwc : ContDiffOn ℝ ∞ (w ∘ fun p : ℝ × ℝ => cylEnd p.1 p.2) U :=
      hwsm.comp hcyl.contDiffOn hcylW
    have hvc0 : ∀ k, Set.MapsTo (v' k ∘ fun p : ℝ × ℝ => cylEnd p.1 p.2) U {y | y ≠ 0} :=
      fun k p hp => hv'0 k _ (hcylW hp)
    have hwc0 : Set.MapsTo (w ∘ fun p : ℝ × ℝ => cylEnd p.1 p.2) U {y | y ≠ 0} :=
      fun p hp => hwne _ (hW0 (hcylW hp))
    have hcA := tendstoCInftyLocOn_comp (X := ℝ × ℝ) (Y := V n) (Z := ℝ) hUo isOpen_ne
      _ _ (fun _ => aCoord H) (aCoord H) hvc hwc (fun _ => haCs) haCs hvc0 hwc0 hc1
      (s2_tendstoCInftyLocOn_const _ _)
    have hcW := tendstoCInftyLocOn_comp (X := ℝ × ℝ) (Y := V n) (Z := V n) hUo isOpen_ne
      _ _ (fun _ => proj H) (proj H) hvc hwc (fun _ => hprojs) hprojs hvc0 hwc0 hc1
      (s2_tendstoCInftyLocOn_const _ _)
    have hlimA : (aCoord H ∘ (w ∘ fun p : ℝ × ℝ => cylEnd p.1 p.2)) =
        fun p => σ * P.T * p.1 := funext fun p => by
      simp only [Function.comp_apply]; rw [haW, hA0, zero_add]
    have hlimW : (proj H ∘ (w ∘ fun p : ℝ × ℝ => cylEnd p.1 p.2)) =
        fun p => P.x (σ * P.T * p.2 + cs) := funext fun p => by
      simp only [Function.comp_apply]; rw [hpW]
    rw [hlimA] at hcA
    rw [hlimW] at hcW
    -- the shifted coordinates agree with the rescalings on the strip
    have hshift : ∀ k (p : ℝ × ℝ), p ∈ U →
        cylEnd (p + (s (φ (k + j₀)), 0)).1 (p + (s (φ (k + j₀)), 0)).2 =
          ((ρ (φ (k + j₀)) : ℝ) : ℂ) * cylEnd p.1 p.2 ∧
        cylEnd (s (φ (k + j₀))) 0 = ((ρ (φ (k + j₀)) : ℝ) : ℂ) ∧
        cylEnd p.1 p.2 ≠ 0 ∧ ρ (φ (k + j₀)) * ‖cylEnd p.1 p.2‖ < 1 := by
      intro k p hp
      refine ⟨?_, ?_, (hsmall k _ (hcylW hp)).1, (hsmall k _ (hcylW hp)).2⟩
      · simp only [Prod.fst_add, Prod.snd_add, add_zero]
        rw [s2_cylEnd_add, hρk]
      · rw [s2_cylEnd_zero, hρk]
    refine ⟨s2_tendstoCInftyLocOn_of_eqOn_shift hUo _ _ _ j₀ (fun k p hp => ?_) hcA,
      s2_tendstoCInftyLocOn_of_eqOn_shift hUo _ _ _ j₀ (fun k p hp => ?_) hcW⟩
    · obtain ⟨e1, e2, hz, hlt⟩ := hshift k p hp
      simp only [Function.comp_apply, endA]
      rw [e1, e2, (hvpa _ _ hz hlt).2]
    · obtain ⟨e1, -, hz, hlt⟩ := hshift k p hp
      simp only [Function.comp_apply, endW]
      rw [e1, (hvpa _ _ hz hlt).1]
  exact ⟨φ, hφ, cs, s2_tendstoCInftyLocOn_univ_of_strips _ _ fun N => (hstrip N).1,
    s2_tendstoCInftyLocOn_univ_of_strips _ _ fun N => (hstrip N).2⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1)
    (hloop : ∀ ε : ℝ, 0 < ε → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∃ c' : ℝ, ∀ t : ℝ,
      ‖loopInS H u (cwLoop 0 r) t - P.x (σ * P.T * t + c')‖ ≤ ε)
    (s : ℕ → ℝ) (hs : Tendsto s atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c : ℝ,
      JHolomorphic.TendstoCInftyLocOn
        (fun j (p : ℝ × ℝ) => endA H u cylEnd (p + (s (φ j), 0)) - endA H u cylEnd (s (φ j), 0))
        (fun p => σ * P.T * p.1) Set.univ ∧
      JHolomorphic.TendstoCInftyLocOn
        (fun j (p : ℝ × ℝ) => endW H u cylEnd (p + (s (φ j), 0)))
        (fun p => P.x (σ * P.T * p.2 + c)) Set.univ :=
  exists_subseq_tendstoCInftyLocOn_cylEnd_shift_aux H hH J hJ u hu P σ hσ hloop s hs
