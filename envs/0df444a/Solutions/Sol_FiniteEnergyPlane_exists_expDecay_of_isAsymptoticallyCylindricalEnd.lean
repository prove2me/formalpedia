-- Prove2me | solution 1 for FiniteEnergyPlane.exists_expDecay_of_isAsymptoticallyCylindricalEnd
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T21:34:12.420322+00:00
-- url     : https://prove2.me/submissions/210906e5-4752-40ce-957d-abf0e807faa4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_exists_reebTube_coords
import Theorems.Thm_FiniteEnergyPlane_exists_expDecay_tubeNormal
import Theorems.Thm_FiniteEnergyPlane_exists_dbar_bound_tubeTangent
import Theorems.Thm_FiniteEnergyPlane_expDecay_of_dbar_expDecay
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_of_tendstoZeroCInfty



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma k1_cylEnd_periodic (s t : ℝ) : cylEnd s (t + 1) = cylEnd s t := by
  simp only [cylEnd, cwLoop]
  have : Complex.exp (-((2 * π * (t + 1) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((2 * π * t : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨-1, by push_cast; ring⟩
  rw [this]

lemma k1_cylEnd_mem {s : ℝ} (hs : 0 < s) (t : ℝ) : cylEnd s t ∈ ball (0 : ℂ) 1 \ {0} := by
  have hn : ‖cylEnd s t‖ = Real.exp (-(2 * π * s)) := by
    simp only [cylEnd, cwLoop, zero_add, norm_mul, Complex.norm_exp]
    simp [abs_of_pos (Real.exp_pos _)]
    rw [Complex.norm_exp]
    simp
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff, hn, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])
  · intro h0
    rw [Set.mem_singleton_iff] at h0
    rw [h0, norm_zero] at hn
    exact (Real.exp_pos _).ne' hn.symm

lemma k1_H_proj {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n} (hy : y ≠ 0) :
    H (proj H y) = 1 := by
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (hH.2.1 y hy).exists
  unfold proj scaleToS
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).2

lemma k1_bound {C δ δ' s x : ℝ} (hx : x ≤ C * Real.exp (-(δ * s))) (h : δ' ≤ δ) (hs : 0 ≤ s) :
    x ≤ |C| * Real.exp (-(δ' * s)) :=
  hx.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (abs_nonneg C)))

theorem exists_expDecay_of_isAsymptoticallyCylindricalEnd_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (d c : ℝ)
    (ha : TendstoZeroCInfty (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1 - d))
    (hw : TendstoZeroCInfty (fun p : ℝ × ℝ => endW H u cylEnd p - P.x (ε * P.T * p.2 + c))) :
    ∃ δ > 0, ∃ C s₀ : ℝ, ∀ s ≥ s₀, ∀ t : ℝ,
      |endA H u cylEnd (s, t) - ε * P.T * s - d| ≤ C * Real.exp (-(δ * s)) ∧
        ‖endW H u cylEnd (s, t) - P.x (ε * P.T * t + c)‖ ≤ C * Real.exp (-(δ * s)) := by
  -- tube coordinates `w = proj (x(τ) + h)`
  obtain ⟨τ, h, s₁, K, hτ, hh, hT⟩ := exists_reebTube_coords H hH P ε hε c (endW H u cylEnd) 0
    (fun s hs t => k1_H_proj hH (hu.2.1 _ (k1_cylEnd_mem hs t)))
    (fun s t => by simp only [endW, k1_cylEnd_periodic]) hw
  have hrep : ∀ s ≥ s₁, ∀ t : ℝ,
      τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧
        endW H u cylEnd (s, t) = proj H (P.x (τ (s, t)) + h (s, t)) :=
    fun s hs t => ⟨(hT s hs t).1, (hT s hs t).2.1, (hT s hs t).2.2.1, (hT s hs t).2.2.2.1⟩
  -- normal component: `C⁰` decay, then decay of `Dh`
  obtain ⟨δ₁, hδ₁, C₁, s₂, hN⟩ :=
    exists_expDecay_tubeNormal H hH J hJ u hu P hP ε hε c τ h s₁ hτ hh hrep
  obtain ⟨-, hD⟩ := expDecayCInfty_of_tendstoZeroCInfty h hh δ₁ C₁ s₂ hN (δ₁ / 2) (by linarith)
  obtain ⟨C₂, s₃, hD1⟩ := hD 1
  -- tangential directions: Cauchy–Riemann defect
  obtain ⟨K₂, s₄, hA⟩ := exists_dbar_bound_tubeTangent H hH J hJ u hu P ε hε d c τ h s₁ hτ hh hrep
  set s₅ := max (max (max s₁ s₂) (max s₃ s₄)) 0 with hs₅
  have hdbar : ∀ s ≥ s₅, ∀ t : ℝ,
      |fderiv ℝ (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1 - d) (s, t) (1, 0) -
          fderiv ℝ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c) (s, t) (0, 1)| +
        |fderiv ℝ (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1 - d) (s, t) (0, 1) +
          fderiv ℝ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c) (s, t) (1, 0)| ≤
        (|K₂| * (|C₁| + |C₂|)) * Real.exp (-(δ₁ / 2 * s)) := by
    intro s hs t
    have hs0 : 0 ≤ s := le_trans (le_max_right _ _) hs
    have h1 : s₁ ≤ s := by simp only [hs₅, max_le_iff] at hs; exact hs.1.1.1
    have h2 : s₂ ≤ s := by simp only [hs₅, max_le_iff] at hs; exact hs.1.1.2
    have h3 : s₃ ≤ s := by simp only [hs₅, max_le_iff] at hs; exact hs.1.2.1
    have h4 : s₄ ≤ s := by simp only [hs₅, max_le_iff] at hs; exact hs.1.2.2
    have e1 : ‖h (s, t)‖ ≤ |C₁| * Real.exp (-(δ₁ / 2 * s)) :=
      k1_bound (hN s h2 t) (by linarith) hs0
    have e2 : ‖fderiv ℝ h (s, t)‖ ≤ |C₂| * Real.exp (-(δ₁ / 2 * s)) := by
      rw [← norm_iteratedFDeriv_one]
      exact k1_bound (hD1 s h3 t) le_rfl hs0
    refine (hA s h4 t).trans ?_
    calc K₂ * (‖h (s, t)‖ + ‖fderiv ℝ h (s, t)‖)
        ≤ |K₂| * (‖h (s, t)‖ + ‖fderiv ℝ h (s, t)‖) :=
          mul_le_mul_of_nonneg_right (le_abs_self K₂) (by positivity)
      _ ≤ |K₂| * ((|C₁| + |C₂|) * Real.exp (-(δ₁ / 2 * s))) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K₂)
      _ = (|K₂| * (|C₁| + |C₂|)) * Real.exp (-(δ₁ / 2 * s)) := by ring
  have hper : ∀ s ≥ s₅, ∀ t : ℝ,
      (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1 - d) (s, t + 1) =
          (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1 - d) (s, t) ∧
        (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c) (s, t + 1) =
          (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c) (s, t) := by
    intro s hs t
    have h1 : s₁ ≤ s := by simp only [hs₅, max_le_iff] at hs; exact hs.1.1.1
    refine ⟨by simp only [endA, k1_cylEnd_periodic], ?_⟩
    simp only [(hT s h1 t).1]
    ring
  obtain ⟨δ₂, hδ₂, C₃, s₆, hG⟩ := expDecay_of_dbar_expDecay _ _ ha hτ (δ₁ / 2) _ s₅
    (by linarith) hper hdbar
  -- assemble
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, |C₃| + |K| * (|C₁| + |C₃|), max s₅ s₆,
    fun s hs t => ?_⟩
  have h5 : s₅ ≤ s := le_trans (le_max_left _ _) hs
  have h6 : s₆ ≤ s := le_trans (le_max_right _ _) hs
  have hs0 : 0 ≤ s := le_trans (le_max_right _ _) h5
  have h1 : s₁ ≤ s := by simp only [hs₅, max_le_iff] at h5; exact h5.1.1.1
  have h2 : s₂ ≤ s := by simp only [hs₅, max_le_iff] at h5; exact h5.1.1.2
  obtain ⟨gf, gg⟩ := hG s h6 t
  dsimp only at gf gg
  have ef : |endA H u cylEnd (s, t) - ε * P.T * s - d| ≤
      |C₃| * Real.exp (-(min δ₁ δ₂ * s)) := k1_bound gf (min_le_right _ _) hs0
  have eg : |τ (s, t) - ε * P.T * t - c| ≤ |C₃| * Real.exp (-(min δ₁ δ₂ * s)) :=
    k1_bound gg (min_le_right _ _) hs0
  have eh : ‖h (s, t)‖ ≤ |C₁| * Real.exp (-(min δ₁ δ₂ * s)) :=
    k1_bound (hN s h2 t) (min_le_left _ _) hs0
  have hE := Real.exp_pos (-(min δ₁ δ₂ * s))
  have hKC : 0 ≤ |K| * (|C₁| + |C₃|) * Real.exp (-(min δ₁ δ₂ * s)) := by positivity
  refine ⟨?_, ?_⟩
  · nlinarith [abs_nonneg C₃]
  · have hw' := (hT s h1 t).2.2.2.2.2
    have : K * (‖h (s, t)‖ + |τ (s, t) - ε * P.T * t - c|) ≤
        |K| * ((|C₁| + |C₃|) * Real.exp (-(min δ₁ δ₂ * s))) :=
      (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)).trans
        (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K))
    nlinarith [abs_nonneg C₃]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (d c : ℝ)
    (ha : TendstoZeroCInfty (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1 - d))
    (hw : TendstoZeroCInfty (fun p : ℝ × ℝ => endW H u cylEnd p - P.x (ε * P.T * p.2 + c))) :
    ∃ δ > 0, ∃ C s₀ : ℝ, ∀ s ≥ s₀, ∀ t : ℝ,
      |endA H u cylEnd (s, t) - ε * P.T * s - d| ≤ C * Real.exp (-(δ * s)) ∧
        ‖endW H u cylEnd (s, t) - P.x (ε * P.T * t + c)‖ ≤ C * Real.exp (-(δ * s)) :=
  exists_expDecay_of_isAsymptoticallyCylindricalEnd_aux H hH J hJ u hu P hP ε hε d c ha hw
