-- Prove2me | solution 1 for DelaunayStretch.lemma_4_9_sliding_gate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:51:20.354904+00:00
-- url     : https://prove2.me/submissions/ea056922-c26b-46d1-a122-cdec96fadac3

import Theorems.Thm_DelaunayStretch_lemma_4_2_range_of_coordinates
import Theorems.Thm_DelaunayStretch_lemma_4_8_derivatives_along_curves
import Definitions.Def_DelaunayStretch_IsNextDisk

open DelaunayStretch

theorem clip_sub_abs' (h t : ℝ) (hh : 0 ≤ h) : |clip h t - t| = max (|t| - h) 0 := by
  unfold clip
  rcases le_total t h with h1 | h1 <;> rcases le_total (-h) t with h2 | h2
  · rw [min_eq_right h1, max_eq_right h2, sub_self, abs_zero]
    have : |t| ≤ h := abs_le.mpr ⟨h2, h1⟩
    rw [max_eq_right (by linarith)]
  · rw [min_eq_right h1, max_eq_left h2]
    rw [abs_of_nonpos (by linarith : t ≤ 0), abs_of_nonneg (by linarith : 0 ≤ -h - t)]
    rw [max_eq_left (by linarith)]; ring
  · rw [min_eq_left h1, max_eq_right (by linarith)]
    rw [abs_of_nonneg (by linarith : 0 ≤ t), abs_of_nonpos (by linarith : h - t ≤ 0)]
    rw [max_eq_left (by linarith)]; ring
  · have e1 : h = 0 := by linarith
    have e2 : t = 0 := by linarith
    subst e1; subst e2; simp

theorem abs_clip_le' (h t : ℝ) (hh : 0 ≤ h) : |clip h t| ≤ h := by
  unfold clip
  rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- Monotonicity of `H` in the direction `(0, Δφ, Δθ, 0)` with `Δθ ≥ |Δφ|`, from (H0), (H2) and
the chain rule of Lemma 4.8. -/
theorem H_mono_segment (H : R4 → ℝ) (P : PiecewiseC1 H) (h0 : CondH0 H) (h2 : CondH2 P)
    (γ φ θ φ' θ' ψ : ℝ) (hz : (γ, φ, θ) ∈ OmegaSet) (hz' : (γ, φ', θ') ∈ OmegaSet)
    (hdir : |φ' - φ| ≤ θ' - θ) : H (γ, φ, θ, ψ) ≤ H (γ, φ', θ', ψ) := by
  set z : ℝ → R4 := fun t => (γ, φ + t * (φ' - φ), θ + t * (θ' - θ), ψ) with hz_def
  have hzC : ContDiff ℝ 1 z := by
    rw [hz_def]; fun_prop
  have hmaps : Set.MapsTo z (Set.Icc 0 1) OmegaTimesR := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    obtain ⟨a1, a2⟩ := hz
    obtain ⟨b1, b2⟩ := hz'
    simp only at a1 a2 b1 b2
    show (γ, φ + t * (φ' - φ), θ + t * (θ' - θ)) ∈ OmegaSet
    have e1 : γ - (φ + t * (φ' - φ)) = (1 - t) * (γ - φ) + t * (γ - φ') := by ring
    have e2 : γ + (φ + t * (φ' - φ)) = (1 - t) * (γ + φ) + t * (γ + φ') := by ring
    have i1 : |γ - (φ + t * (φ' - φ))| ≤ (1 - t) * |γ - φ| + t * |γ - φ'| := by
      rw [e1]
      calc _ ≤ |(1 - t) * (γ - φ)| + |t * (γ - φ')| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg ht0]
    have i2 : |γ + (φ + t * (φ' - φ))| ≤ (1 - t) * |γ + φ| + t * |γ + φ'| := by
      rw [e2]
      calc _ ≤ |(1 - t) * (γ + φ)| + |t * (γ + φ')| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg ht0]
    constructor
    · show |γ - (φ + t * (φ' - φ))| < θ + t * (θ' - θ)
      rcases eq_or_lt_of_le ht0 with h | h
      · subst h; simpa using a1
      · nlinarith
    · show θ + t * (θ' - θ) < Real.pi - |γ + (φ + t * (φ' - φ))|
      rcases eq_or_lt_of_le ht0 with h | h
      · subst h; simp; linarith
      · nlinarith
  obtain ⟨hAC, hae⟩ := lemma_4_8_derivatives_along_curves H h0 P 0 1 zero_le_one z
    hzC.contDiffOn hmaps
  have hderz : ∀ t, deriv z t = (0, φ' - φ, θ' - θ, 0) := by
    intro t
    have : HasDerivAt z ((0 : ℝ), φ' - φ, θ' - θ, (0 : ℝ)) t := by
      rw [hz_def]
      refine (hasDerivAt_const t γ).prodMk ?_
      refine ((((hasDerivAt_id t).mul_const (φ' - φ)).const_add φ).congr_deriv (by simp)).prodMk ?_
      exact ((((hasDerivAt_id t).mul_const (θ' - θ)).const_add θ).congr_deriv
        (by simp)).prodMk (hasDerivAt_const t ψ)
    exact this.deriv
  have hderiv : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)),
      0 ≤ deriv (fun t => H (z t)) t := by
    have hmem : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)), t ∈ Set.Icc (0:ℝ) 1 :=
      MeasureTheory.ae_restrict_mem measurableSet_Icc
    filter_upwards [hae, hmem] with t ht htm
    obtain ⟨g, hg, hHd⟩ := ht
    rw [hHd.deriv, hderz, dot4]
    have hg2 := h2 (z t) (hmaps htm) g hg
    simp only [mul_zero, zero_add, add_zero]
    have h1 : -(|g.2.1| * |φ' - φ|) ≤ g.2.1 * (φ' - φ) := by
      rw [← abs_mul]; exact neg_abs_le _
    have h3 : |g.2.1| * |φ' - φ| ≤ g.2.2.1 * (θ' - θ) :=
      mul_le_mul hg2 hdir (abs_nonneg _) ((abs_nonneg _).trans hg2)
    linarith
  have hint := hAC.integral_deriv_eq_sub
  have hnn : 0 ≤ ∫ x in (0:ℝ)..1, deriv (fun t => H (z t)) x :=
    intervalIntegral.integral_nonneg_of_ae_restrict zero_le_one hderiv
  rw [hint] at hnn
  have e0 : z 0 = (γ, φ, θ, ψ) := by simp [hz_def]
  have e1 : z 1 = (γ, φ', θ', ψ) := by simp [hz_def]
  rw [e0, e1] at hnn
  linarith

theorem solution (U : ℝ) (H : R4 → ℝ)
    (hH : ∃ P : PiecewiseC1 H, CondH0 H ∧ CondH1 H ∧ CondH2 P)
    (s : GateState) (hs : s.IsGateState) (O' : Disk) (a' b' : ℂ) (hO' : IsNextDisk s O' a' b') :
    (⟨s.O, a', b', stepDiff s a' b'⟩ : GateState).IsGateState ∧
    stepCost s a' b' - U * stepProgress s a' b' +
        potential H U ⟨s.O, a', b', stepDiff s a' b'⟩ - potential H U s ≤ 0 := by
  obtain ⟨P, h0, h1, h2⟩ := hH
  obtain ⟨hSig, -, -, hcoord⟩ := lemma_4_2_range_of_coordinates
  obtain ⟨hint, ha', hb', -, -, hUN, hLN⟩ := hO'
  have haO : a' ∈ s.O.boundary := (show a' ∈ s.O.boundary ∩ O'.boundary by rw [hint]; simp).1
  have hbO : b' ∈ s.O.boundary := (show b' ∈ s.O.boundary ∩ O'.boundary by rw [hint]; simp).1
  set t : GateState := ⟨s.O, a', b', stepDiff s a' b'⟩ with ht
  have hgt : t.IsGateState := ⟨hs.1, haO, hbO, ha', hb', abs_clip_le' _ _ dist_nonneg⟩
  refine ⟨hgt, ?_⟩
  obtain ⟨-, -, hαs, hβs, -, -, -, -⟩ := hcoord s hs
  obtain ⟨-, -, hαt, hβt, -, -, -, -⟩ := hcoord t hgt
  have hzs := hSig s hs
  have hzt := hSig t hgt
  set r := s.O.radius with hr_def
  have hr : 0 < r := hs.1
  set γ := s.gammaCoord
  have hγt : t.gammaCoord = γ := rfl
  have hrt : t.O.radius = r := rfl
  set φ := s.phiCoord
  set θ := s.thetaCoord
  set ψ := s.psiCoord
  set φ' := t.phiCoord
  set θ' := t.thetaCoord
  set ψ' := t.psiCoord
  set α := s.O.upperArcLength s.aG a' with hα_def
  set β := s.O.lowerArcLength s.bG b' with hβ_def
  have hα : α = r * (θ' + γ - φ') - r * (θ + γ - φ) := by
    rw [hα_def]
    have e1 : s.O.upperArcLength s.O.wMinus a' = r * (θ' + γ - φ') := by
      rw [← hγt]; exact hαt
    rw [← e1, ← hαs]; unfold Disk.upperArcLength; ring
  have hβ : β = r * (θ' - γ + φ') - r * (θ - γ + φ) := by
    rw [hβ_def]
    have e1 : s.O.lowerArcLength s.O.wMinus b' = r * (θ' - γ + φ') := by
      rw [← hγt]; exact hβt
    rw [← e1, ← hβs]; unfold Disk.lowerArcLength; ring
  have hα0 : 0 ≤ α := by
    rw [hα_def]; unfold Disk.upperArcLength
    exact mul_nonneg hr.le (by unfold Disk.UpperNotAfter at hUN; linarith)
  have hβ0 : 0 ≤ β := by
    rw [hβ_def]; unfold Disk.lowerArcLength
    exact mul_nonneg hr.le (by unfold Disk.LowerNotAfter at hLN; linarith)
  have hdθ : θ' - θ = (α + β) / (2 * r) := by
    rw [hα, hβ]; field_simp; ring
  have hdφ : φ' - φ = (β - α) / (2 * r) := by
    rw [hα, hβ]; field_simp; ring
  have hdir : |φ' - φ| ≤ θ' - θ := by
    rw [hdθ, hdφ, abs_div, abs_of_pos (by linarith : 0 < 2 * r)]
    apply div_le_div_of_nonneg_right _ (by linarith)
    rw [abs_le]; constructor <;> linarith
  set G' := dist a' b'
  set ω := max (|s.δ + α - β| - G') 0 with hω
  have hδ' : stepDiff s a' b' = clip G' (s.δ + α - β) := rfl
  have hψ : ψ = φ + s.δ / (2 * r) := rfl
  have hψ' : ψ' = φ' + stepDiff s a' b' / (2 * r) := rfl
  have hdψ : |ψ' - ψ| = ω / (2 * r) := by
    rw [hω, ← clip_sub_abs' G' _ dist_nonneg, ← hδ', hψ', hψ]
    rw [show φ' + stepDiff s a' b' / (2 * r) - (φ + s.δ / (2 * r)) =
        (stepDiff s a' b' - (s.δ + α - β)) / (2 * r) by
        rw [show φ' = φ + (β - α) / (2 * r) by linarith [hdφ]]; field_simp; ring]
    rw [abs_div, abs_of_pos (by linarith : 0 < 2 * r)]
  have hcost : stepCost s a' b' = (α + β - ω) / 2 := rfl
  have hprog : stepProgress s a' b' = t.crossing.re - s.crossing.re := rfl
  have hpt : potential H U t = r * (Real.pi / 2 - θ' - H (γ, φ', θ', ψ')) +
      U * (t.crossing.re - s.O.center.re) := rfl
  have hps : potential H U s = r * (Real.pi / 2 - θ - H (γ, φ, θ, ψ)) +
      U * (s.crossing.re - s.O.center.re) := rfl
  rw [hcost, hprog, hpt, hps]
  -- (H1)
  have hΩt : (γ, φ', θ') ∈ OmegaSet := hzt.1
  have hΩs : (γ, φ, θ) ∈ OmegaSet := hzs.1
  have hH1 := h1 γ φ' θ' hΩt ψ' ψ
  rw [hdψ] at hH1
  have hle1 : H (γ, φ', θ', ψ) - ω / (2 * r) ≤ H (γ, φ', θ', ψ') := by
    have := abs_le.mp hH1; linarith [this.1]
  have hle2 := H_mono_segment H P h0 h2 γ φ θ φ' θ' ψ hΩs hΩt hdir
  have key : r * (H (γ, φ, θ, ψ) - ω / (2 * r)) ≤ r * H (γ, φ', θ', ψ') :=
    mul_le_mul_of_nonneg_left (by linarith) hr.le
  have e : r * (ω / (2 * r)) = ω / 2 := by field_simp
  rw [mul_sub, e] at key
  have hθ' : r * (θ' - θ) = (α + β) / 2 := by rw [hdθ]; field_simp
  nlinarith
