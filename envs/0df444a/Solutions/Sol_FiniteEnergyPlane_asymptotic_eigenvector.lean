-- Prove2me | solution 1 for FiniteEnergyPlane.asymptotic_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T09:09:09.015147+00:00
-- url     : https://prove2.me/submissions/2451fb9d-d131-4b02-b740-3a61517667b3

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_cylEnd_tendsto_of_loops_tendstoUnif_mod_phase
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_of_tendstoZeroUnif_mod_phase
import Theorems.Thm_FiniteEnergyPlane_exists_reebTube_coords_bound
import Theorems.Thm_FiniteEnergyPlane_exists_dbar_bound_tubeTangent
import Theorems.Thm_FiniteEnergyPlane_expDecay_of_dbar_expDecay
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_of_tendstoZeroCInfty
import Theorems.Thm_FiniteEnergyPlane_asympOp_frame_bridge
import Theorems.Thm_FiniteEnergyPlane_exists_crEquation_tubeNormal_expDecay
import Theorems.Thm_FiniteEnergyPlane_halfCyl_asymptotic_formula_eventually
import Theorems.Thm_FiniteEnergyPlane_exists_endW_ne_proj_reeb_comp
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_comp_periodic
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_prodMk
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma ae_cylEnd_periodic (s t : ℝ) : cylEnd s (t + 1) = cylEnd s t := by
  simp only [cylEnd, cwLoop]
  have : Complex.exp (-((2 * π * (t + 1) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((2 * π * t : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨-1, by push_cast; ring⟩
  rw [this]

lemma ae_cylEnd_mem {s : ℝ} (hs : 0 < s) (t : ℝ) : cylEnd s t ∈ ball (0 : ℂ) 1 \ {0} := by
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

lemma ae_H_proj {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n} (hy : y ≠ 0) :
    H (proj H y) = 1 := by
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (hH.2.1 y hy).exists
  unfold proj scaleToS
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).2

lemma ae_bound {C δ δ' s x : ℝ} (hx : x ≤ C * Real.exp (-(δ * s))) (h : δ' ≤ δ) (hs : 0 ≤ s) :
    x ≤ |C| * Real.exp (-(δ' * s)) :=
  hx.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (abs_nonneg C)))

lemma ae_eps_sq {ε : ℝ} (hε : ε = 1 ∨ ε = -1) : ε * ε = 1 := by
  rcases hε with rfl | rfl <;> norm_num

lemma ae_periodic_eps {F : Type*} {f : ℝ → F} (hf : Function.Periodic f 1) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (x : ℝ) : f (x + ε) = f x := by
  rcases hε with rfl | rfl
  · exact hf x
  · exact hf.neg x

lemma ae_symLoop {n : ℕ} (Sinf : ℝ → CauchyRiemannIndex.Mat n)
    (hS : CauchyRiemannIndex.IsSymLoop Sinf) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (b : ℝ) :
    CauchyRiemannIndex.IsSymLoop (fun t => ε • Sinf (ε * t + b)) := by
  obtain ⟨hc, hp, hsym⟩ := hS
  have hl : Continuous fun t : ℝ => ε * t + b := by fun_prop
  refine ⟨(hc.comp hl).const_smul ε, fun t => ?_, fun t => (hsym _).smul ε⟩
  show ε • Sinf (ε * (t + 1) + b) = ε • Sinf (ε * t + b)
  rw [show ε * (t + 1) + b = ε * t + b + ε by ring, ae_periodic_eps hp hε]

lemma ae_smooth_affine {n : ℕ} (Sinf : ℝ → CauchyRiemannIndex.Mat n)
    (hSm : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (ε c : ℝ) :
    ∀ i j, ContDiff ℝ ∞ (fun t => (ε • Sinf (ε * t + c)) i j) := by
  intro i j
  have ha : ContDiff ℝ ∞ (fun t : ℝ => ε * t + c) := by fun_prop
  have h : ContDiff ℝ ∞ (fun t => ε * Sinf (ε * t + c) i j) :=
    contDiff_const.mul ((hSm i j).comp ha)
  simpa [Matrix.smul_apply] using h

lemma ae_J0_inj {n : ℕ} (a : CauchyRiemannIndex.Vec n)
    (h : ∀ b, inner ℝ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) a) b = 0) : a = 0 := by
  have h1 : Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) a = 0 :=
    inner_self_eq_zero.1 (h _)
  have h2 : Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n)
      (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) a) = -a := by
    rw [Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply]
    simp only [WithLp.ofLp_toLp, Matrix.mulVec_mulVec,
      show CauchyRiemannIndex.J₀ n * CauchyRiemannIndex.J₀ n = -1 from Matrix.J_squared _ _,
      Matrix.neg_mulVec, Matrix.one_mulVec]
    rfl
  rw [h1, map_zero] at h2
  exact neg_eq_zero.1 h2.symm

theorem asymptotic_eigenvector_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hnd : IsNondegenerateEnd H u cylEnd P ε) :
    (∃ b > 0, HasExpAsymptoticsEnd H u cylEnd P ε b) ∧
      ((∀ r > 0, ∃ z ∈ ball (0 : ℂ) r \ {0}, dlambdaDensity H u z ≠ 0) →
        ∃ (μ : ℝ) (v : ℝ → V n), HasAsymptoticEigenvector H J u cylEnd P ε μ v) := by
  have hT := P.T_pos
  obtain ⟨d, c, b₀, hb₀, hA0, hWe⟩ := hnd
  -- `C⁰` exponential decay of `w`
  obtain ⟨sW, hsW⟩ := hWe 1 one_pos
  have hWexp : ∀ s ≥ sW, ∀ t : ℝ,
      ‖endW H u cylEnd (s, t) - P.x (ε * P.T * t + c)‖ ≤ 1 * Real.exp (-(b₀ * s)) := by
    intro s hs t
    have h1 := hsW s hs t
    simp only at h1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
    have he : Real.exp (b₀ * s) * Real.exp (-(b₀ * s)) = 1 := by
      rw [← Real.exp_add]; simp
    have hE := Real.exp_pos (-(b₀ * s))
    nlinarith [norm_nonneg (endW H u cylEnd (s, t) - P.x (ε * P.T * t + c))]
  have hW0 : TendstoZeroUnif (fun p : ℝ × ℝ => endW H u cylEnd p - P.x (ε * P.T * p.2 + c)) := by
    intro η hη
    obtain ⟨s₀, hs₀⟩ := hWe η hη
    refine ⟨max s₀ 0, fun s hs t => ?_⟩
    have h1 := hs₀ s (le_trans (le_max_left _ _) hs) t
    simp only at h1 ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
    have h2 : 1 ≤ Real.exp (b₀ * s) :=
      Real.one_le_exp (mul_nonneg hb₀.le (le_trans (le_max_right _ _) hs))
    nlinarith [norm_nonneg (endW H u cylEnd (s, t) - P.x (ε * P.T * t + c))]
  -- loops are uniformly close to the orbit
  have hloop : ∀ η : ℝ, 0 < η → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∃ c' : ℝ, ∀ t : ℝ,
      ‖loopInS H u (cwLoop 0 r) t - P.x (ε * P.T * t + c')‖ ≤ η := by
    intro η hη
    obtain ⟨s₀, hs₀⟩ := hW0 η hη
    filter_upwards [Ioo_mem_nhdsGT (Real.exp_pos (-(2 * π * s₀)))] with r hr
    refine ⟨c, fun t => ?_⟩
    have hr0 : 0 < r := hr.1
    set s := -Real.log r / (2 * π) with hs
    have hlog : Real.log r < -(2 * π * s₀) := by
      have := Real.log_lt_log hr0 hr.2
      rwa [Real.log_exp] at this
    have hss : s₀ ≤ s := by
      rw [hs, le_div_iff₀ (by positivity)]; linarith
    have hcyl : cylEnd s t = cwLoop 0 r t := by
      simp only [cylEnd]
      rw [show -(2 * π * s) = Real.log r by rw [hs]; field_simp, Real.exp_log hr0]
    have := hs₀ s hss t
    simp only at this
    rwa [endW, hcyl] at this
  -- part 1: asymptotically cylindrical, then exponential decay
  obtain ⟨hsm, hA, hW⟩ :=
    cylEnd_tendsto_of_loops_tendstoUnif_mod_phase H hH J hJ u hu P ε hε hloop
  obtain ⟨ha, hw⟩ :=
    tendstoZeroCInfty_of_tendstoZeroUnif_mod_phase H hH P ε hε _ _ hsm hA hW d c hA0 hW0
  obtain ⟨τ, h, s₁, K, hτ, hh, hTb⟩ := exists_reebTube_coords_bound H hH P ε hε c
    (endW H u cylEnd) 0 (fun s hs t => ae_H_proj hH (hu.2.1 _ (ae_cylEnd_mem hs t)))
    (fun s t => by simp only [endW, ae_cylEnd_periodic]) hw
  set s₁' := max s₁ sW with hs₁'
  have hrep : ∀ s ≥ s₁', ∀ t : ℝ,
      τ (s, t + 1) = τ (s, t) + ε * P.T ∧ h (s, t + 1) = h (s, t) ∧
        IsInXi H (P.x (τ (s, t))) (h (s, t)) ∧
        endW H u cylEnd (s, t) = proj H (P.x (τ (s, t)) + h (s, t)) := by
    intro s hs t
    have h1 := hTb s (le_trans (le_max_left _ _) hs) t
    exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1⟩
  have hdec : ∀ s ≥ s₁', ∀ t : ℝ,
      |τ (s, t) - ε * P.T * t - c| + ‖h (s, t)‖ ≤ |K| * Real.exp (-(b₀ * s)) := by
    intro s hs t
    have h1 := (hTb s (le_trans (le_max_left _ _) hs) t).2.2.2.2.2.2
    have h2 := hWexp s (le_trans (le_max_right _ _) hs) t
    calc |τ (s, t) - ε * P.T * t - c| + ‖h (s, t)‖
        = ‖h (s, t)‖ + |τ (s, t) - ε * P.T * t - c| := add_comm _ _
      _ ≤ K * ‖endW H u cylEnd (s, t) - P.x (ε * P.T * t + c)‖ := h1
      _ ≤ |K| * ‖endW H u cylEnd (s, t) - P.x (ε * P.T * t + c)‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _)
      _ ≤ |K| * Real.exp (-(b₀ * s)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg K); linarith
  have hN : ∀ s ≥ s₁', ∀ t : ℝ, ‖h (s, t)‖ ≤ |K| * Real.exp (-(b₀ * s)) := by
    intro s hs t
    have := hdec s hs t
    linarith [abs_nonneg (τ (s, t) - ε * P.T * t - c)]
  obtain ⟨-, hD⟩ := expDecayCInfty_of_tendstoZeroCInfty h hh b₀ |K| s₁' hN (b₀ / 2) (by linarith)
  obtain ⟨C₂, s₃, hD1⟩ := hD 1
  obtain ⟨K₂, s₄, hAb⟩ :=
    exists_dbar_bound_tubeTangent H hH J hJ u hu P ε hε d c τ h s₁' hτ hh hrep
  set s₅ := max (max s₁' (max s₃ s₄)) 0 with hs₅
  have hdbar : ∀ s ≥ s₅, ∀ t : ℝ,
      |fderiv ℝ (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1 - d) (s, t) (1, 0) -
          fderiv ℝ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c) (s, t) (0, 1)| +
        |fderiv ℝ (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1 - d) (s, t) (0, 1) +
          fderiv ℝ (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c) (s, t) (1, 0)| ≤
        (|K₂| * (|K| + |C₂|)) * Real.exp (-(b₀ / 2 * s)) := by
    intro s hs t
    have hs0 : 0 ≤ s := le_trans (le_max_right _ _) hs
    have h1 : s₁' ≤ s := by simp only [hs₅, max_le_iff] at hs; exact hs.1.1
    have h3 : s₃ ≤ s := by simp only [hs₅, max_le_iff] at hs; exact hs.1.2.1
    have h4 : s₄ ≤ s := by simp only [hs₅, max_le_iff] at hs; exact hs.1.2.2
    have e1 : ‖h (s, t)‖ ≤ |K| * Real.exp (-(b₀ / 2 * s)) := by
      have := ae_bound (hN s h1 t) (show b₀ / 2 ≤ b₀ by linarith) hs0
      rwa [abs_abs] at this
    have e2 : ‖fderiv ℝ h (s, t)‖ ≤ |C₂| * Real.exp (-(b₀ / 2 * s)) := by
      rw [← norm_iteratedFDeriv_one]
      exact ae_bound (hD1 s h3 t) le_rfl hs0
    refine (hAb s h4 t).trans ?_
    calc K₂ * (‖h (s, t)‖ + ‖fderiv ℝ h (s, t)‖)
        ≤ |K₂| * (‖h (s, t)‖ + ‖fderiv ℝ h (s, t)‖) :=
          mul_le_mul_of_nonneg_right (le_abs_self K₂) (by positivity)
      _ ≤ |K₂| * ((|K| + |C₂|) * Real.exp (-(b₀ / 2 * s))) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K₂)
      _ = (|K₂| * (|K| + |C₂|)) * Real.exp (-(b₀ / 2 * s)) := by ring
  have hper : ∀ s ≥ s₅, ∀ t : ℝ,
      (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1 - d) (s, t + 1) =
          (fun p : ℝ × ℝ => endA H u cylEnd p - ε * P.T * p.1 - d) (s, t) ∧
        (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c) (s, t + 1) =
          (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c) (s, t) := by
    intro s hs t
    have h1 : s₁' ≤ s := by simp only [hs₅, max_le_iff] at hs; exact hs.1.1
    refine ⟨by simp only [endA, ae_cylEnd_periodic], ?_⟩
    simp only [(hrep s h1 t).1]
    ring
  obtain ⟨δ₂, hδ₂, C₃, s₆, hG⟩ := expDecay_of_dbar_expDecay _ _ ha hτ (b₀ / 2) _ s₅
    (by linarith) hper hdbar
  refine ⟨⟨min b₀ δ₂ / 2, by positivity, d, c, ?_, ?_⟩, ?_⟩
  · refine expDecayCInfty_of_tendstoZeroCInfty _ ha δ₂ C₃ s₆ (fun s hs t => ?_) _
      (by have := min_le_right b₀ δ₂; linarith)
    rw [Real.norm_eq_abs]
    exact (hG s hs t).1
  · exact expDecayCInfty_of_tendstoZeroCInfty _ hw b₀ 1 sW hWexp _
      (by have := min_le_left b₀ δ₂; linarith)
  -- part 2: the asymptotic eigenvector
  intro hden
  obtain ⟨⟨Z, hZ⟩, hall⟩ := asympOp_frame_bridge H hH J hJ P
  obtain ⟨Sinf, hSym, hSm, hId, -⟩ := hall Z hZ
  obtain ⟨s₂, dS, Cζ, S, ζ, hdS, hS, hSas, hζ, hrest⟩ :=
    exists_crEquation_tubeNormal_expDecay H hH J hJ u hu P Z hZ Sinf hSym hSm hId ε hε c τ h s₁'
      hτ hh hrep b₀ |K| hb₀ hdec
  -- `ζ` does not vanish identically near the puncture
  obtain ⟨sτ, hsτ⟩ := hτ.1
  have hτC : ContDiffOn ℝ 1 τ (Set.Ioi sτ ×ˢ Set.univ) := by
    have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (τ p - ε * P.T * p.2 - c) + (ε * P.T * p.2 + c))
        (Set.Ioi sτ ×ˢ Set.univ) :=
      hsτ.add ((contDiff_const.mul contDiff_snd).add contDiff_const).contDiffOn
    have h2 : (fun p : ℝ × ℝ => (τ p - ε * P.T * p.2 - c) + (ε * P.T * p.2 + c)) = τ := by
      funext p; ring
    rw [h2] at h1
    exact h1.of_le (by simp)
  have hne : ∀ s₀ : ℝ, ∃ s ≥ s₀, ∃ t : ℝ, ζ (s, t) ≠ 0 := by
    intro s₀
    by_contra hcon
    push_neg at hcon
    obtain ⟨s, hs, t, hne'⟩ := exists_endW_ne_proj_reeb_comp H hH J hJ u hu P hden τ sτ hτC
      (max s₀ (max (s₂ + 1) s₁'))
    apply hne'
    have hs2 : s₂ < s := by
      have := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hs); linarith
    have hs1 : s₁' ≤ s := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hs)
    have hζ0 : ζ (s, t) = 0 := hcon s (le_trans (le_max_left _ _) hs) t
    rw [(hrep s hs1 t).2.2.2, (hrest s hs2 t).2.2.2.1, hζ0, map_zero, add_zero]
  -- the asymptotic formula
  obtain ⟨μ', hμ', e, he, hconv⟩ := halfCyl_asymptotic_formula_eventually s₂ S hS _
    (ae_symLoop Sinf hSym hε (c / P.T)) (ae_smooth_affine Sinf hSm ε (c / P.T)) dS hdS hSas ζ hζ
    (fun s hs t => ⟨(hrest s hs t).1, (hrest s hs t).2.1⟩) (fun s hs t => (hrest s hs t).2.2.1)
    hne Cζ (-dS) (fun s hs t => by rw [neg_mul]; exact (hrest s hs t).2.2.2.2)
  obtain ⟨heC, heP, ⟨t₀, het₀⟩, heE⟩ := he
  have hεε := ae_eps_sq hε
  -- the eigenvector `v = Z ê`, `ê(θ) = e(ε(θ - c/T))`
  set ê : ℝ → CauchyRiemannIndex.Vec n := fun θ => e (ε * (θ - c / P.T)) with hê
  have hêC : ContDiff ℝ ∞ ê := heC.comp (by fun_prop)
  have hêP : Function.Periodic ê 1 := by
    intro θ
    simp only [hê]
    rw [show ε * (θ + 1 - c / P.T) = ε * (θ - c / P.T) + ε by ring, ae_periodic_eps heP hε]
  have hêt : ∀ t : ℝ, ê (ε * t + c / P.T) = e t := by
    intro t; simp only [hê]
    rw [show ε * (ε * t + c / P.T - c / P.T) = (ε * ε) * t by ring, hεε, one_mul]
  have hêd : ∀ θ : ℝ, deriv ê θ = ε • deriv e (ε * (θ - c / P.T)) := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => ε * (θ - c / P.T)) ε θ := by
      simpa using ((hasDerivAt_id θ).sub_const (c / P.T)).const_mul ε
    have h2 : HasDerivAt e (deriv e (ε * (θ - c / P.T))) (ε * (θ - c / P.T)) :=
      (heC.differentiable (by simp) _).hasDerivAt
    exact (h2.scomp θ h1).deriv
  set v : ℝ → V n := fun θ => Z θ (ê θ) with hv
  refine ⟨ε * μ', v, ⟨⟨hZ.1.clm_apply hêC, fun θ => ?_, fun θ => ?_⟩, ?_, fun θ => ?_⟩, ?_, ?_⟩
  · show Z (θ + 1) (ê (θ + 1)) = Z θ (ê θ)
    rw [hZ.2.1 θ, hêP θ]
  · exact (hZ.2.2 θ).1 _
  · refine ⟨ε * t₀ + c / P.T, fun h0 => het₀ ?_⟩
    rw [← hêt t₀]
    apply ae_J0_inj
    intro b
    rw [← (hZ.2.2 (ε * t₀ + c / P.T)).2.2.2]
    show omega0 (v (ε * t₀ + c / P.T)) _ = 0
    rw [h0]
    simp [omega0, j0, dot]
  · rw [hId ê hêC hêP θ, hêd θ]
    have hE := heE (ε * (θ - c / P.T))
    beta_reduce at hE
    rw [show ε * (ε * (θ - c / P.T)) + c / P.T = θ by
      rw [← mul_assoc, hεε, one_mul]; ring] at hE
    have hE2 : -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n)
        (ε • deriv e (ε * (θ - c / P.T)))) - Matrix.toEuclideanLin (Sinf θ) (ê θ) =
        (ε * μ') • ê θ := by
      rw [map_smul, LinearMap.smul_apply] at hE
      have hx : ê θ = e (ε * (θ - c / P.T)) := rfl
      rw [hx, map_smul, mul_smul, ← hE, smul_sub, smul_neg, smul_smul, hεε, one_smul]
    rw [hE2]
    exact (Z θ).map_smul _ _
  · rw [← mul_assoc, hεε, one_mul]; linarith
  -- the remainder
  set Φ : ℝ × (ℝ × CauchyRiemannIndex.Vec n) → V n := fun q =>
    Z ((q.1 + q.2.1) / P.T) (q.2.2 + ê (q.1 / P.T) - ê ((q.1 + q.2.1) / P.T)) with hΦ
  have hΦc : ContDiff ℝ ∞ Φ := by
    refine (hZ.1.comp (by fun_prop)).clm_apply ?_
    exact ((contDiff_snd.snd).add (hêC.comp (by fun_prop))).sub (hêC.comp (by fun_prop))
  have hΦp : ∀ (φ : ℝ) (y : ℝ × CauchyRiemannIndex.Vec n), ‖y‖ < 1 →
      Φ (φ + P.T, y) = Φ (φ, y) := by
    intro φ y _
    simp only [hΦ]
    rw [show (φ + P.T + y.1) / P.T = (φ + y.1) / P.T + 1 by field_simp; ring,
      show (φ + P.T) / P.T = φ / P.T + 1 by field_simp, hZ.2.1, hêP, hêP]
  have hΦ0 : ∀ φ : ℝ, Φ (φ, 0) = 0 := by intro φ; simp [hΦ]
  set q : ℝ × ℝ → ℝ × CauchyRiemannIndex.Vec n := fun p =>
    (τ p - ε * P.T * p.2 - c, Real.exp (-(μ' * p.1)) • ζ p - e p.2) with hq
  have hqC : TendstoZeroCInfty q := tendstoZeroCInfty_prodMk hτ hconv
  refine ⟨c, τ, fun p => Φ (ε * P.T * p.2 + c, q p), max (s₂ + 1) s₁', hτ,
    tendstoZeroCInfty_comp_periodic Φ P.T 1 (ε * P.T) c hT one_pos hΦc.contDiffOn hΦp hΦ0 q hqC,
    fun s hs t => ?_⟩
  have hs2 : s > s₂ := by have := le_trans (le_max_left _ _) hs; linarith
  have hs1 : s ≥ s₁' := le_trans (le_max_right _ _) hs
  have key : Real.exp (ε * (ε * μ') * s) •
      (v (τ (s, t) / P.T) + Φ (ε * P.T * t + c, q (s, t))) = h (s, t) := by
    have e1 : (ε * P.T * t + c + (τ (s, t) - ε * P.T * t - c)) / P.T = τ (s, t) / P.T := by ring
    have e2 : (ε * P.T * t + c) / P.T = ε * t + c / P.T := by field_simp
    simp only [hΦ, hq, hv, e1, e2, hêt]
    rw [← map_add, show ê (τ (s, t) / P.T) +
        (Real.exp (-(μ' * s)) • ζ (s, t) - e t + e t - ê (τ (s, t) / P.T)) =
        Real.exp (-(μ' * s)) • ζ (s, t) by abel, map_smul, ← (hrest s hs2 t).2.2.2.1, smul_smul,
      ← mul_assoc, hεε, one_mul, ← Real.exp_add, show μ' * s + -(μ' * s) = 0 by ring,
      Real.exp_zero, one_smul]
  dsimp only
  rw [key]
  exact ⟨(hrep s hs1 t).2.2.1, (hrep s hs1 t).2.2.2⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hnd : IsNondegenerateEnd H u cylEnd P ε) :
    (∃ b > 0, HasExpAsymptoticsEnd H u cylEnd P ε b) ∧
      ((∀ r > 0, ∃ z ∈ ball (0 : ℂ) r \ {0}, dlambdaDensity H u z ≠ 0) →
        ∃ (μ : ℝ) (v : ℝ → V n), HasAsymptoticEigenvector H J u cylEnd P ε μ v) :=
  asymptotic_eigenvector_aux H hH J hJ u hu P ε hε hnd
