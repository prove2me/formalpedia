-- Prove2me | solution 1 for FiniteEnergyPlane.exists_tendsto_cylEnd_of_isNondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T10:58:24.313983+00:00
-- url     : https://prove2.me/submissions/b99e8a8d-7652-4425-a9f4-3d87bf08065e

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Theorems.Thm_FiniteEnergyPlane_exists_reebTube_coords_of_drift
import Theorems.Thm_FiniteEnergyPlane_exists_expDecay_tubeNormal_of_drift
import Theorems.Thm_FiniteEnergyPlane_exists_dbar_bound_tubeTangent_of_drift
import Theorems.Thm_FiniteEnergyPlane_exists_tendsto_of_dbar_expDecay
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_of_tendstoZeroCInfty
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x



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
open scoped ContDiff Real

theorem hwze_cylEnd_mem {s : ℝ} (hs : 0 < s) (t : ℝ) : cylEnd s t ∈ ball (0 : ℂ) 1 \ {0} := by
  refine ⟨?_, s2_cylEnd_ne_zero _ _⟩
  rw [mem_ball_zero_iff, s2_norm_cylEnd]
  have := Real.exp_lt_exp.2 (show -(2 * π * s) < 0 by nlinarith [Real.pi_pos])
  rwa [Real.exp_zero] at this

theorem hwze_cylEnd_periodic (s t : ℝ) : cylEnd s (t + 1) = cylEnd s t := by
  rw [s2_cylEnd_eq, s2_cylEnd_eq, s2_cwLoop_periodic]

/-- `a` and `w` are smooth on `(0, ∞) × ℝ`, and `w` lies on `S` there. -/
theorem hwze_smooth {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) :
    ContDiffOn ℝ ∞ (endA H u cylEnd) (Set.Ioi 0 ×ˢ Set.univ) ∧
      ContDiffOn ℝ ∞ (endW H u cylEnd) (Set.Ioi 0 ×ˢ Set.univ) ∧
      ∀ s > 0, ∀ t : ℝ, H (endW H u cylEnd (s, t)) = 1 := by
  obtain ⟨-, hprojs, haCs, hproj1, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hcylU : Set.MapsTo (fun p : ℝ × ℝ => cylEnd p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)
      (ball 0 1 \ {0}) := fun p hp => hwze_cylEnd_mem hp.1 p.2
  have huc : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => u (cylEnd p.1 p.2)) (Set.Ioi 0 ×ˢ Set.univ) :=
    hu.1.comp s2_contDiff_cyl.contDiffOn hcylU
  have hu0 : Set.MapsTo (fun p : ℝ × ℝ => u (cylEnd p.1 p.2)) (Set.Ioi 0 ×ˢ Set.univ)
      {y | y ≠ 0} := fun p hp => hu.2.1 _ (hcylU hp)
  exact ⟨haCs.comp huc hu0, hprojs.comp huc hu0,
    fun s hs t => (hproj1 _ (hu.2.1 _ (hwze_cylEnd_mem hs t))).1⟩

/-- A periodic Reeb orbit is Lipschitz. -/
theorem hwze_x_lipschitz {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) : ∃ L : ℝ, ∀ a b : ℝ, ‖P.x a - P.x b‖ ≤ L * |a - b| := by
  have hx := ReebOrbit.contDiff_x H hH P
  have hcont : Continuous (deriv P.x) := hx.continuous_deriv (by simp)
  have hper : Function.Periodic (deriv P.x) P.T := by
    intro τ
    rw [(P.hasDerivAt (τ + P.T)).deriv, (P.hasDerivAt τ).deriv, P.periodic]
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := P.T)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hb : ∀ τ : ℝ, ‖deriv P.x τ‖ ≤ L := by
    intro τ
    obtain ⟨y, hy, hyeq⟩ := hper.exists_mem_Ico₀ P.T_pos τ
    rw [hyeq]
    exact hL y (Set.Ico_subset_Icc_self hy)
  refine ⟨L, fun a b => ?_⟩
  have := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (fun τ _ => (P.hasDerivAt τ).differentiableAt) (fun τ _ => hb τ) (Set.mem_univ b)
    (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using this

theorem hwze_bound {C δ δ' s x : ℝ} (hx : x ≤ C * Real.exp (-(δ * s))) (h : δ' ≤ δ) (hs : 0 ≤ s) :
    x ≤ |C| * Real.exp (-(δ' * s)) :=
  hx.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (abs_nonneg C)))

theorem hwze_partial_le {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {η : ℝ}
    (hf : ‖iteratedFDeriv ℝ 1 f p‖ ≤ η) : |fderiv ℝ f p (0, 1)| ≤ η := by
  rw [norm_iteratedFDeriv_one] at hf
  have h1 := (fderiv ℝ f p).le_opNorm ((0 : ℝ), (1 : ℝ))
  have h2 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp
  rw [h2, mul_one, Real.norm_eq_abs] at h1
  linarith

theorem exists_tendsto_cylEnd_of_isNondegenerate_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hA : ∀ m : ℕ, 1 ≤ m → ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => endA H u cylEnd p - σ * P.T * p.1) (s, t)‖ ≤ ε)
    (hW : ∀ m : ℕ, ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j
        (fun p : ℝ × ℝ => endW H u cylEnd p - P.x (σ * P.T * p.2 + c')) (s, t)‖ ≤ ε) :
    ∃ d c : ℝ,
      TendstoZeroUnif (fun p : ℝ × ℝ => endA H u cylEnd p - σ * P.T * p.1 - d) ∧
        TendstoZeroUnif (fun p : ℝ × ℝ => endW H u cylEnd p - P.x (σ * P.T * p.2 + c)) := by
  obtain ⟨hAsm, hWsm, hWS⟩ := hwze_smooth H hH J hJ u hu
  -- tube coordinates with a drifting phase
  obtain ⟨τ, h, s₁, K, hθs, hθ, hh, hT⟩ := exists_reebTube_coords_of_drift H hH P σ hσ
    (endW H u cylEnd) 0 hWsm hWS (fun s t => by simp only [endW, hwze_cylEnd_periodic]) hW
  have hrep : ∀ s ≥ s₁, ∀ t : ℝ,
      τ (s, t + 1) = τ (s, t) + σ * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧
        endW H u cylEnd (s, t) = proj H (P.x (τ (s, t)) + h (s, t)) :=
    fun s hs t => ⟨(hT s hs t).1, (hT s hs t).2.1, (hT s hs t).2.2.1, (hT s hs t).2.2.2.1⟩
  -- normal component decays exponentially, together with its first derivative
  obtain ⟨δ₁, hδ₁, C₁, s₂, hN⟩ :=
    exists_expDecay_tubeNormal_of_drift H hH J hJ u hu P hP σ hσ τ h s₁ hθs hθ hh hrep
  obtain ⟨-, hD⟩ := expDecayCInfty_of_tendstoZeroCInfty h hh δ₁ C₁ s₂ hN (δ₁ / 2) (by linarith)
  obtain ⟨C₂, s₃, hD1⟩ := hD 1
  -- tangential directions: Cauchy–Riemann defect
  obtain ⟨K₂, s₄, hdb⟩ :=
    exists_dbar_bound_tubeTangent_of_drift H hH J hJ u hu P σ hσ τ h s₁ hθs hθ hh hrep
  obtain ⟨s₇, hθs'⟩ := hθs
  set S := max (max (max s₁ s₂) (max s₃ s₄)) (max s₇ 0) with hS
  have hSle : ∀ s, S < s → s₁ ≤ s ∧ s₂ ≤ s ∧ s₃ ≤ s ∧ s₄ ≤ s ∧ s₇ ≤ s ∧ 0 ≤ s := by
    intro s hs
    have hs' := hs.le
    simp only [hS, max_le_iff] at hs'
    exact ⟨hs'.1.1.1, hs'.1.1.2, hs'.1.2.1, hs'.1.2.2, hs'.2.1, hs'.2.2⟩
  have hUsub : ∀ e, S ≤ e → Set.Ioi e ×ˢ (Set.univ : Set ℝ) ⊆ Set.Ioi 0 ×ˢ Set.univ := by
    intro e he p hp
    exact ⟨lt_of_le_of_lt ((le_max_right _ _).trans ((le_max_right _ _).trans he)) hp.1, trivial⟩
  have hf : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => endA H u cylEnd p - σ * P.T * p.1)
      (Set.Ioi S ×ˢ Set.univ) :=
    ((hAsm.mono (hUsub S le_rfl)).sub
      ((contDiff_const.mul contDiff_fst).contDiffOn)).of_le (by simp)
  have hg : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => τ p - σ * P.T * p.2) (Set.Ioi S ×ˢ Set.univ) := by
    refine (hθs'.mono ?_).of_le (by simp)
    intro p hp
    have h7 : s₇ ≤ S := (le_max_left s₇ 0).trans (le_max_right _ _)
    exact ⟨lt_of_le_of_lt h7 hp.1, trivial⟩
  have hper : ∀ s > S, ∀ t : ℝ,
      (fun p : ℝ × ℝ => endA H u cylEnd p - σ * P.T * p.1) (s, t + 1) =
          (fun p : ℝ × ℝ => endA H u cylEnd p - σ * P.T * p.1) (s, t) ∧
        (fun p : ℝ × ℝ => τ p - σ * P.T * p.2) (s, t + 1) =
          (fun p : ℝ × ℝ => τ p - σ * P.T * p.2) (s, t) := by
    intro s hs t
    refine ⟨by simp only [endA, hwze_cylEnd_periodic], ?_⟩
    simp only [(hT s (hSle s hs).1 t).1]
    ring
  have ht : ∀ η > 0, ∃ s₅ : ℝ, ∀ s ≥ s₅, ∀ t : ℝ,
      |fderiv ℝ (fun p : ℝ × ℝ => endA H u cylEnd p - σ * P.T * p.1) (s, t) (0, 1)| ≤ η ∧
        |fderiv ℝ (fun p : ℝ × ℝ => τ p - σ * P.T * p.2) (s, t) (0, 1)| ≤ η := by
    intro η hη
    obtain ⟨a₁, ha₁⟩ := hA 1 le_rfl η hη
    obtain ⟨a₂, ha₂⟩ := hθ 1 le_rfl η hη
    exact ⟨max a₁ a₂, fun s hs t => ⟨hwze_partial_le (ha₁ s (le_of_max_le_left hs) t),
      hwze_partial_le (ha₂ s (le_of_max_le_right hs) t)⟩⟩
  have hdbar : ∀ s > S, ∀ t : ℝ,
      |fderiv ℝ (fun p : ℝ × ℝ => endA H u cylEnd p - σ * P.T * p.1) (s, t) (1, 0) -
          fderiv ℝ (fun p : ℝ × ℝ => τ p - σ * P.T * p.2) (s, t) (0, 1)| +
        |fderiv ℝ (fun p : ℝ × ℝ => endA H u cylEnd p - σ * P.T * p.1) (s, t) (0, 1) +
          fderiv ℝ (fun p : ℝ × ℝ => τ p - σ * P.T * p.2) (s, t) (1, 0)| ≤
        (|K₂| * (|C₁| + |C₂|)) * Real.exp (-(δ₁ / 2 * s)) := by
    intro s hs t
    obtain ⟨-, h2, h3, h4, -, hs0⟩ := hSle s hs
    have e1 : ‖h (s, t)‖ ≤ |C₁| * Real.exp (-(δ₁ / 2 * s)) :=
      hwze_bound (hN s h2 t) (by linarith) hs0
    have e2 : ‖fderiv ℝ h (s, t)‖ ≤ |C₂| * Real.exp (-(δ₁ / 2 * s)) := by
      rw [← norm_iteratedFDeriv_one]
      exact hwze_bound (hD1 s h3 t) le_rfl hs0
    refine (hdb s h4 t).trans ?_
    calc K₂ * (‖h (s, t)‖ + ‖fderiv ℝ h (s, t)‖)
        ≤ |K₂| * (‖h (s, t)‖ + ‖fderiv ℝ h (s, t)‖) :=
          mul_le_mul_of_nonneg_right (le_abs_self K₂) (by positivity)
      _ ≤ |K₂| * ((|C₁| + |C₂|) * Real.exp (-(δ₁ / 2 * s))) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K₂)
      _ = (|K₂| * (|C₁| + |C₂|)) * Real.exp (-(δ₁ / 2 * s)) := by ring
  -- the means converge: fixed constant `d` and fixed phase `c`
  obtain ⟨d, c, hfd, hgc⟩ := exists_tendsto_of_dbar_expDecay _ _ S hf hg hper ht (δ₁ / 2) _
    (by linarith) hdbar
  refine ⟨d, c, hfd, ?_⟩
  -- `w - x(σTt + c) = (w - x(τ)) + (x(τ) - x(σTt + c))`
  obtain ⟨L, hL⟩ := hwze_x_lipschitz H hH P
  intro η hη
  set η' := η / (2 * (|K| + |L| + 1)) with hη'
  have hη'0 : 0 < η' := div_pos hη (by positivity)
  obtain ⟨b₁, hb₁⟩ := hh.2 0 η' hη'0
  obtain ⟨b₂, hb₂⟩ := hgc η' hη'0
  refine ⟨max (max b₁ b₂) s₁, fun s hs t => ?_⟩
  have hs1 : b₁ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hs2 : b₂ ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hs3 : s₁ ≤ s := le_trans (le_max_right _ _) hs
  have eh : ‖h (s, t)‖ ≤ η' := by
    have := hb₁ s hs1 t; rwa [norm_iteratedFDeriv_zero] at this
  have eg : |τ (s, t) - σ * P.T * t - c| ≤ η' := by
    have := hb₂ s hs2 t; simpa [Real.norm_eq_abs] using this
  have ew := (hT s hs3 t).2.2.2.2
  have ex := hL (τ (s, t)) (σ * P.T * t + c)
  have hsplit : endW H u cylEnd (s, t) - P.x (σ * P.T * t + c) =
      (endW H u cylEnd (s, t) - P.x (τ (s, t))) + (P.x (τ (s, t)) - P.x (σ * P.T * t + c)) := by
    abel
  have hrw : τ (s, t) - (σ * P.T * t + c) = τ (s, t) - σ * P.T * t - c := by ring
  rw [hrw] at ex
  show ‖endW H u cylEnd (s, t) - P.x (σ * P.T * t + c)‖ ≤ η
  rw [hsplit]
  have hK : K * ‖h (s, t)‖ ≤ |K| * η' :=
    (mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left eh (abs_nonneg K))
  have hLb : L * |τ (s, t) - σ * P.T * t - c| ≤ |L| * η' :=
    (mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left eg (abs_nonneg L))
  have htot : (|K| + |L|) * η' ≤ η := by
    rw [hη', mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg K, abs_nonneg L]
  calc ‖(endW H u cylEnd (s, t) - P.x (τ (s, t))) + (P.x (τ (s, t)) - P.x (σ * P.T * t + c))‖
      ≤ ‖endW H u cylEnd (s, t) - P.x (τ (s, t))‖ + ‖P.x (τ (s, t)) - P.x (σ * P.T * t + c)‖ :=
        norm_add_le _ _
    _ ≤ |K| * η' + |L| * η' := add_le_add (ew.trans hK) (ex.trans hLb)
    _ = (|K| + |L|) * η' := by ring
    _ ≤ η := htot

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hA : ∀ m : ℕ, 1 ≤ m → ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => endA H u cylEnd p - σ * P.T * p.1) (s, t)‖ ≤ ε)
    (hW : ∀ m : ℕ, ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j
        (fun p : ℝ × ℝ => endW H u cylEnd p - P.x (σ * P.T * p.2 + c')) (s, t)‖ ≤ ε) :
    ∃ d c : ℝ,
      TendstoZeroUnif (fun p : ℝ × ℝ => endA H u cylEnd p - σ * P.T * p.1 - d) ∧
        TendstoZeroUnif (fun p : ℝ × ℝ => endW H u cylEnd p - P.x (σ * P.T * p.2 + c)) :=
  exists_tendsto_cylEnd_of_isNondegenerate_aux H hH J hJ u hu P hP σ hσ hA hW
