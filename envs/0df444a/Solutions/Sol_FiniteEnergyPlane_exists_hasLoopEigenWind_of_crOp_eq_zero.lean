-- Prove2me | solution 1 for FiniteEnergyPlane.exists_hasLoopEigenWind_of_crOp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T19:29:55.278837+00:00
-- url     : https://prove2.me/submissions/0cbabe5b-c757-4a55-b50a-29cce269127f

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_halfCyl_asymptotic_formula_eventually
import Theorems.Thm_FiniteEnergyPlane_isLoopEigen_ne_zero_hasLoopEigenWind
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_of_re_conj_mul_pos



namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

theorem fas_norm_vecToC (a : CauchyRiemannIndex.Vec 1) : ‖vecToC a‖ = ‖a‖ := by
  rw [EuclideanSpace.norm_eq, Complex.norm_def, Complex.normSq_apply]
  simp [vecToC, Fintype.sum_sum_type, sq]

theorem fas_norm_cylInf (s t : ℝ) : ‖cylInf s t‖ = Real.exp (2 * π * s) := by
  unfold cylInf ccwLoop
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem fas_exists_cylInf (z : ℂ) (hz : z ≠ 0) : ∃ s t : ℝ, cylInf s t = z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  refine ⟨Real.log ‖z‖ / (2 * π), Complex.arg z / (2 * π), ?_⟩
  unfold cylInf ccwLoop
  rw [mul_div_cancel₀ _ hpi, Real.exp_log hn, mul_div_cancel₀ _ hpi]
  exact Complex.norm_mul_exp_arg_mul_I z

theorem fas_re_conj_mul_pos (a b : ℂ) (hlt : ‖b - a‖ < ‖a‖) :
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

lemma fas_vecToC_cont : Continuous vecToC := by
  have e : vecToC = fun a : CauchyRiemannIndex.Vec 1 =>
      ((a (Sum.inl 0) : ℝ) : ℂ) + ((a (Sum.inr 0) : ℝ) : ℂ) * Complex.I :=
    funext fun a => Complex.ext (by simp [vecToC]) (by simp [vecToC])
  rw [e]
  have h1 : Continuous fun a : CauchyRiemannIndex.Vec 1 => a (Sum.inl 0) :=
    (EuclideanSpace.proj (Sum.inl 0 : Fin 1 ⊕ Fin 1)).continuous
  have h2 : Continuous fun a : CauchyRiemannIndex.Vec 1 => a (Sum.inr 0) :=
    (EuclideanSpace.proj (Sum.inr 0 : Fin 1 ⊕ Fin 1)).continuous
  exact (Complex.continuous_ofReal.comp h1).add
    ((Complex.continuous_ofReal.comp h2).mul continuous_const)

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

/-- The leading term of a solution on the end: its eigenvalue, winding and growth. -/
theorem exists_hasLoopEigenWind_of_crOp_eq_zero_aux (s₁ : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec 1) (hζ : ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ))
    (hper : ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t) ∧ ζ (s, t + 1) = ζ (s, t))
    (heq : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S ζ (s, t) = 0)
    (hne : ∀ s₀ : ℝ, ∃ s ≥ s₀, ∃ t : ℝ, ζ (s, t) ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > s₁, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ (μ : ℝ) (k : ℤ) (s₂ E : ℝ), μ ≤ δ₀ ∧ HasLoopEigenWind Sinf μ k ∧ 0 ≤ E ∧
      ∀ s ≥ s₂, HasLoopWind (fun t => vecToC (ζ (s, t))) k ∧
        ∀ t, ‖ζ (s, t)‖ ≤ E * Real.exp (μ * s) := by
  obtain ⟨μ, hμ, e, he, hT⟩ := halfCyl_asymptotic_formula_eventually s₁ S hS Sinf hSinf hSinf' d hd
    hSas ζ hζ hper heq hne C δ₀ hgrowth
  obtain ⟨hen, k, hk⟩ := isLoopEigen_ne_zero_hasLoopEigenWind Sinf hSinf hSinf' μ e he
  have hke : HasLoopWind (fun t => vecToC (e t)) k := hk.2 e he
  have hcont : Continuous (fun t => ‖e t‖) := he.1.continuous.norm
  have hperN : Function.Periodic (fun t => ‖e t‖) 1 := fun t => by simp only [he.2.1 t]
  obtain ⟨t₀, -, ht₀⟩ := isCompact_Icc.exists_isMinOn (s := Set.Icc (0 : ℝ) 1)
    ⟨0, by simp⟩ hcont.continuousOn
  obtain ⟨t₁, -, ht₁⟩ := isCompact_Icc.exists_isMaxOn (s := Set.Icc (0 : ℝ) 1)
    ⟨0, by simp⟩ hcont.continuousOn
  set η := ‖e t₀‖ with hη
  have hηpos : 0 < η := norm_pos_iff.2 (hen t₀)
  have hlow : ∀ t, η ≤ ‖e t‖ := fun t => by
    obtain ⟨y, hy, hty⟩ := hperN.exists_mem_Ico₀ one_pos t
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1, by simpa using hy.2.le⟩
    have := ht₀ hy'
    rw [hty]
    exact this
  have hup : ∀ t, ‖e t‖ ≤ ‖e t₁‖ := fun t => by
    obtain ⟨y, hy, hty⟩ := hperN.exists_mem_Ico₀ one_pos t
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1, by simpa using hy.2.le⟩
    have := ht₁ hy'
    rw [hty]
    exact this
  obtain ⟨s₃, hs₃⟩ := hT.2 0 (η / 2) (by positivity)
  set s₂ := max s₃ (s₁ + 1) with hs₂
  refine ⟨μ, k, s₂, ‖e t₁‖ + η / 2, hμ, hk, by positivity, fun s hs => ?_⟩
  have hs1 : s₁ < s := by
    have := le_trans (le_max_right s₃ (s₁ + 1)) hs
    linarith
  have hb : ∀ t, ‖Real.exp (-(μ * s)) • ζ (s, t) - e t‖ ≤ η / 2 := fun t => by
    have := hs₃ s ((le_max_left _ _).trans hs) t
    rw [norm_iteratedFDeriv_zero] at this
    exact this
  have hE := Real.exp_pos (-(μ * s))
  constructor
  · refine hasLoopWind_of_re_conj_mul_pos hke ?_ (fun t => by simp only [(hper s hs1 t).2]) ?_
    · have hm : Continuous fun t : ℝ => ((s, t) : ℝ × ℝ) := by fun_prop
      exact fas_vecToC_cont.comp
        (hζ.continuousOn.comp_continuous hm fun t => ⟨hs1, Set.mem_univ _⟩)
    · intro t
      have hval : vecToC (Real.exp (-(μ * s)) • ζ (s, t) - e t) =
          (Real.exp (-(μ * s)) : ℂ) * vecToC (ζ (s, t)) - vecToC (e t) := by
        apply Complex.ext
        · rw [Complex.sub_re, Complex.re_ofReal_mul]
          simp [vecToC]
        · rw [Complex.sub_im, Complex.im_ofReal_mul]
          simp [vecToC]
      have hlt : ‖(Real.exp (-(μ * s)) : ℂ) * vecToC (ζ (s, t)) - vecToC (e t)‖ < ‖vecToC (e t)‖ := by
        rw [← hval, fas_norm_vecToC, fas_norm_vecToC]
        have := hlow t
        have := hb t
        linarith
      have hpos := fas_re_conj_mul_pos _ _ hlt
      have hscale : (starRingEnd ℂ (vecToC (e t)) *
          ((Real.exp (-(μ * s)) : ℂ) * vecToC (ζ (s, t)))).re =
          Real.exp (-(μ * s)) * (starRingEnd ℂ (vecToC (e t)) * vecToC (ζ (s, t))).re := by
        rw [show starRingEnd ℂ (vecToC (e t)) * ((Real.exp (-(μ * s)) : ℂ) * vecToC (ζ (s, t))) =
          (Real.exp (-(μ * s)) : ℂ) * (starRingEnd ℂ (vecToC (e t)) * vecToC (ζ (s, t))) by ring,
          Complex.re_ofReal_mul]
      rw [hscale] at hpos
      exact (pos_iff_pos_of_mul_pos hpos).1 hE
  · intro t
    have h1 : ‖Real.exp (-(μ * s)) • ζ (s, t)‖ ≤ ‖e t₁‖ + η / 2 := by
      have h2 := norm_add_le (Real.exp (-(μ * s)) • ζ (s, t) - e t) (e t)
      rw [sub_add_cancel] at h2
      linarith [hb t, hup t]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hE] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (μ * s)).le
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h3
    linarith [mul_comm (‖e t₁‖ + η / 2) (Real.exp (μ * s))]

end FiniteEnergyPlane

open FiniteEnergyPlane

open scoped ContDiff

theorem solution (s₁ : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec 1) (hζ : ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ))
    (hper : ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t) ∧ ζ (s, t + 1) = ζ (s, t))
    (heq : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S ζ (s, t) = 0)
    (hne : ∀ s₀ : ℝ, ∃ s ≥ s₀, ∃ t : ℝ, ζ (s, t) ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > s₁, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ (μ : ℝ) (k : ℤ) (s₂ E : ℝ), μ ≤ δ₀ ∧ HasLoopEigenWind Sinf μ k ∧ 0 ≤ E ∧
      ∀ s ≥ s₂, HasLoopWind (fun t => vecToC (ζ (s, t))) k ∧
        ∀ t, ‖ζ (s, t)‖ ≤ E * Real.exp (μ * s) :=
  exists_hasLoopEigenWind_of_crOp_eq_zero_aux s₁ S hS Sinf hSinf hSinf' d hd hSas ζ hζ hper heq hne C δ₀ hgrowth
