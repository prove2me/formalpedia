-- Prove2me | solution 1 for FiniteEnergyPlane.forall_eq_zero_or_forall_ne_zero_of_halfCyl_solution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T13:30:29.106784+00:00
-- url     : https://prove2.me/submissions/dd406ed1-6057-40a4-bf0e-613e92e415b2

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_halfCyl_asymptotic_formula
import Theorems.Thm_FiniteEnergyPlane_isLoopEigen_ne_zero_hasLoopEigenWind
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_of_re_conj_mul_pos
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_ccwLoop_eq_sum
import Theorems.Thm_FiniteEnergyPlane_exists_hasLoopWind_of_norm_dbar_le
import Theorems.Thm_FiniteEnergyPlane_eventually_eq_zero_of_norm_dbar_le
import Theorems.Thm_JHolomorphic_eq_zero_of_norm_dbar_le_of_eqOn_zero



namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

theorem fz_norm_vecToC (a : CauchyRiemannIndex.Vec 1) : ‖vecToC a‖ = ‖a‖ := by
  rw [EuclideanSpace.norm_eq, Complex.norm_def, Complex.normSq_apply]
  simp [vecToC, Fintype.sum_sum_type, sq]

theorem fz_norm_cylInf (s t : ℝ) : ‖cylInf s t‖ = Real.exp (2 * π * s) := by
  unfold cylInf ccwLoop
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem fz_exists_cylInf (z : ℂ) (hz : z ≠ 0) : ∃ s t : ℝ, cylInf s t = z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  refine ⟨Real.log ‖z‖ / (2 * π), Complex.arg z / (2 * π), ?_⟩
  unfold cylInf ccwLoop
  rw [mul_div_cancel₀ _ hpi, Real.exp_log hn, mul_div_cancel₀ _ hpi]
  exact Complex.norm_mul_exp_arg_mul_I z

theorem fz_re_conj_mul_pos (a b : ℂ) (hlt : ‖b - a‖ < ‖a‖) :
    0 < (starRingEnd ℂ a * b).re := by
  have hapos : 0 < ‖a‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have h1 : starRingEnd ℂ a * b = (‖a‖ ^ 2 : ℝ) + starRingEnd ℂ a * (b - a) := by
    rw [mul_sub, Complex.conj_mul']
    push_cast
    ring
  rw [h1, Complex.add_re, Complex.ofReal_re]
  have h2 : -(‖a‖ * ‖b - a‖) ≤ (starRingEnd ℂ a * (b - a)).re := by
    have := Complex.abs_re_le_norm (starRingEnd ℂ a * (b - a))
    rw [norm_mul, Complex.norm_conj] at this
    exact (abs_le.1 this).1
  nlinarith

theorem forall_eq_zero_or_forall_ne_zero_of_halfCyl_solution_aux (ζ : ℂ → ℂ) (hζ : ContDiff ℝ ∞ ζ)
    (hM : ∀ z₀ : ℂ, ∃ ρ > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ ρ,
      ‖fderiv ℝ ζ z 1 + Complex.I * fderiv ℝ ζ z Complex.I‖ ≤ M * ‖ζ z‖)
    (S : ℝ × ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d)
    (w : ℝ × ℝ → CauchyRiemannIndex.Vec 1) (hw : IsHalfCylSolution S w)
    (hwz : ∀ s > 0, ∀ t : ℝ, vecToC (w (s, t)) = ζ (cylInf s t))
    (C δ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖w (s, t)‖ ≤ C * Real.exp (δ * s))
    (hwind : ∀ μ ≤ δ, ∀ k : ℤ, HasLoopEigenWind Sinf μ k → k ≤ 0) :
    (∀ z, ζ z = 0) ∨ ∀ z, ζ z ≠ 0 := by
  classical
  by_cases hall : ∀ z, ζ z = 0
  · exact Or.inl hall
  refine Or.inr ?_
  by_contra hex
  push_neg at hex
  obtain ⟨z₁, hz₁⟩ := hex
  -- `ζ` vanishes on no nonempty open set
  have hopen : ∀ U : Set ℂ, IsOpen U → U.Nonempty → ¬ ∀ z ∈ U, ζ z = 0 := by
    intro U hU hne h0
    refine hall (JHolomorphic.eq_zero_of_norm_dbar_le_of_eqOn_zero
      (fun _ => ContinuousLinearMap.mul ℝ ℂ Complex.I) contDiff_const ?_ ζ hζ ?_ U hU hne h0)
    · intro _
      ext v
      simp [← mul_assoc]
    · intro z₀
      obtain ⟨ρ, hρ, M, hb⟩ := hM z₀
      exact ⟨ρ, hρ, M, fun z hz => by simpa using hb z hz⟩
  have hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ w p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hopen {z | 1 < ‖z‖} (isOpen_lt continuous_const continuous_norm)
      ⟨2, by simp⟩ ?_
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz
      linarith
    obtain ⟨s, t, rfl⟩ := fz_exists_cylInf z hz0
    have hs : 0 < s := by
      by_contra hs
      have hz' : 1 < ‖cylInf s t‖ := hz
      rw [fz_norm_cylInf] at hz'
      have : Real.exp (2 * π * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
      linarith
    rw [← hwz s hs t, hcon (s, t) hs]
    apply Complex.ext <;> simp [vecToC]
  obtain ⟨μ, hμ, e, he, hT⟩ := halfCyl_asymptotic_formula S hS hSper Sinf hSinf hSinf' d hd hSas w hw
    hne C δ hgrowth
  obtain ⟨hen, k, hk⟩ := isLoopEigen_ne_zero_hasLoopEigenWind Sinf hSinf hSinf' μ e he
  have hk0 : k ≤ 0 := hwind μ hμ k hk
  have hke : HasLoopWind (fun t => vecToC (e t)) k := hk.2 e he
  -- a uniform lower bound for the eigenfunction
  obtain ⟨η, hη, hlow⟩ : ∃ η > (0 : ℝ), ∀ t, η ≤ ‖e t‖ := by
    have hcont : Continuous (fun t => ‖e t‖) := he.1.continuous.norm
    obtain ⟨t₀, -, ht₀⟩ := isCompact_Icc.exists_isMinOn (s := Set.Icc (0 : ℝ) 1)
      ⟨0, by simp⟩ hcont.continuousOn
    refine ⟨‖e t₀‖, norm_pos_iff.2 (hen t₀), fun t => ?_⟩
    have hper : Function.Periodic (fun t => ‖e t‖) 1 := fun t => by simp only [he.2.1 t]
    obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ one_pos t
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1, by simpa using hy.2.le⟩
    have := ht₀ hy'
    rw [hty]
    exact this
  obtain ⟨s₁, hs₁⟩ := hT.2 0 (η / 2) (by positivity)
  set s₂ := max s₁ 1 with hs₂
  have hs₂1 : 1 ≤ s₂ := le_max_right _ _
  have hclose : ∀ s ≥ s₂, ∀ t, 0 < (starRingEnd ℂ (vecToC (e t)) * ζ (cylInf s t)).re := by
    intro s hs t
    have hs0 : 0 < s := by linarith
    have hb := hs₁ s ((le_max_left _ _).trans hs) t
    rw [norm_iteratedFDeriv_zero] at hb
    have hE := Real.exp_pos (-(μ * s))
    have hval : vecToC (Real.exp (-(μ * s)) • w (s, t) - e t) =
        (Real.exp (-(μ * s)) : ℂ) * ζ (cylInf s t) - vecToC (e t) := by
      rw [← hwz s hs0 t]
      apply Complex.ext
      · rw [Complex.sub_re, Complex.re_ofReal_mul]
        simp [vecToC]
      · rw [Complex.sub_im, Complex.im_ofReal_mul]
        simp [vecToC]
    have hlt : ‖(Real.exp (-(μ * s)) : ℂ) * ζ (cylInf s t) - vecToC (e t)‖ < ‖vecToC (e t)‖ := by
      rw [← hval, fz_norm_vecToC, fz_norm_vecToC]
      have := hlow t
      simp only at hb
      linarith
    have hpos := fz_re_conj_mul_pos _ _ hlt
    have hscale : (starRingEnd ℂ (vecToC (e t)) * ((Real.exp (-(μ * s)) : ℂ) * ζ (cylInf s t))).re =
        Real.exp (-(μ * s)) * (starRingEnd ℂ (vecToC (e t)) * ζ (cylInf s t)).re := by
      rw [show starRingEnd ℂ (vecToC (e t)) * ((Real.exp (-(μ * s)) : ℂ) * ζ (cylInf s t)) =
        (Real.exp (-(μ * s)) : ℂ) * (starRingEnd ℂ (vecToC (e t)) * ζ (cylInf s t)) by ring,
        Complex.re_ofReal_mul]
    rw [hscale] at hpos
    exact (pos_iff_pos_of_mul_pos hpos).1 hE
  set R := Real.exp (2 * π * s₂) with hR_def
  have hR : 0 < R := Real.exp_pos _
  have hnon : ∀ z, R ≤ ‖z‖ → ζ z ≠ 0 := by
    intro z hz h0
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hz
      linarith
    obtain ⟨s, t, rfl⟩ := fz_exists_cylInf z hz0
    rw [fz_norm_cylInf] at hz
    have hss : s₂ ≤ s := by
      have := Real.exp_le_exp.1 hz
      have hp := Real.pi_pos
      nlinarith
    have := hclose s hss t
    rw [h0] at this
    simp at this
  have hloop : HasLoopWind (fun t => ζ ((0 : ℂ) + ccwLoop R t)) k := by
    have hcl : Continuous (ccwLoop R) := by
      unfold ccwLoop
      fun_prop
    have hper : Function.Periodic (ccwLoop R) 1 := by
      intro t
      unfold ccwLoop
      congr 1
      have : (((2 * π * (t + 1) : ℝ) : ℂ) * Complex.I) =
          ((2 * π * t : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I := by
        push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    refine hasLoopWind_of_re_conj_mul_pos hke (hζ.continuous.comp (continuous_const.add hcl))
      (fun t => by simp only [hper t]) (fun t => ?_)
    simpa [cylInf, hR_def] using hclose s₂ le_rfl t
  -- the zero set is finite
  have hsub : {z | ζ z = 0} ⊆ closedBall (0 : ℂ) R := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    by_contra hlt
    exact hnon z (le_of_lt (not_le.1 hlt)) hz
  have hfin : {z | ζ z = 0}.Finite := by
    by_contra hinf
    obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf (isCompact_closedBall _ _)
      hsub
    obtain ⟨ρ, hρ, M, hb⟩ := hM x
    have hfreq : ∃ᶠ z in 𝓝[≠] x, ζ z = 0 := accPt_iff_frequently_nhdsNE.1 hx
    have hev := eventually_eq_zero_of_norm_dbar_le ζ (ball x ρ) isOpen_ball hζ.contDiffOn M hb x
      (mem_ball_self hρ) hfreq
    obtain ⟨U, hU0, hUo, hxU⟩ := _root_.eventually_nhds_iff.1 hev
    exact hopen U hUo ⟨x, hxU⟩ hU0
  set Q := hfin.toFinset with hQ
  have hQm : ∀ z, z ∈ Q ↔ ζ z = 0 := fun z => by simp [hQ]
  -- each zero contributes a positive winding number
  have hidx : ∀ p ∈ Q, ∃ m : ℕ, 1 ≤ m ∧ ∃ r > (0 : ℝ), ∀ ρ ∈ Set.Ioo 0 r,
      HasLoopWind (fun t => ζ (p + ccwLoop ρ t)) m := by
    intro p hp
    obtain ⟨ρ, hρ, M, hb⟩ := hM p
    have hcl : IsClosed ({z | ζ z = 0} \ {p}) := (hfin.subset Set.diff_subset).isClosed
    refine exists_hasLoopWind_of_norm_dbar_le ζ (ball p ρ ∩ ({z | ζ z = 0} \ {p})ᶜ)
      (isOpen_ball.inter hcl.isOpen_compl) hζ.contDiffOn M (fun z hz => hb z hz.1) p
      ⟨mem_ball_self hρ, fun h => h.2 rfl⟩ ((hQm p).1 hp) ?_
    intro z hz h0
    by_contra hzp
    exact hz.2 ⟨h0, hzp⟩
  choose! m hm1 hm2 using hidx
  have hsum := hasLoopWind_ccwLoop_eq_sum ζ Q 0 R hR
    (fun p hp => by
      rw [mem_ball, dist_zero_right]
      by_contra hlt
      exact hnon p (not_lt.1 hlt) ((hQm p).1 hp))
    hζ.continuous.continuousOn
    (fun z hz h0 => hz.2 (by simpa using (hQm z).2 h0))
    (fun p => (m p : ℤ)) (fun p hp => hm2 p hp)
  have hk' := hasLoopWind_unique hloop hsum
  have h1 : (m z₁ : ℤ) ≤ ∑ p ∈ Q, (m p : ℤ) :=
    Finset.single_le_sum (f := fun p => (m p : ℤ)) (fun p _ => Int.natCast_nonneg _)
      ((hQm z₁).2 hz₁)
  have h2 : (1 : ℤ) ≤ m z₁ := by exact_mod_cast hm1 z₁ ((hQm z₁).2 hz₁)
  omega

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff

theorem solution (ζ : ℂ → ℂ) (hζ : ContDiff ℝ ∞ ζ)
    (hM : ∀ z₀ : ℂ, ∃ ρ > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ ρ,
      ‖fderiv ℝ ζ z 1 + Complex.I * fderiv ℝ ζ z Complex.I‖ ≤ M * ‖ζ z‖)
    (S : ℝ × ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d)
    (w : ℝ × ℝ → CauchyRiemannIndex.Vec 1) (hw : IsHalfCylSolution S w)
    (hwz : ∀ s > 0, ∀ t : ℝ, vecToC (w (s, t)) = ζ (cylInf s t))
    (C δ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖w (s, t)‖ ≤ C * Real.exp (δ * s))
    (hwind : ∀ μ ≤ δ, ∀ k : ℤ, HasLoopEigenWind Sinf μ k → k ≤ 0) :
    (∀ z, ζ z = 0) ∨ ∀ z, ζ z ≠ 0 :=
  forall_eq_zero_or_forall_ne_zero_of_halfCyl_solution_aux ζ hζ hM S hS hSper Sinf hSinf hSinf' d hd hSas w hw hwz C δ hgrowth hwind
