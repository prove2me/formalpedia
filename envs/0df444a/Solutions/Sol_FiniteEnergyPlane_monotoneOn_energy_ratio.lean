-- Prove2me | solution 1 for FiniteEnergyPlane.monotoneOn_energy_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-23T16:55:38.066805+00:00
-- url     : https://prove2.me/submissions/ffcad63c-8701-48c5-bf55-711db4e3fde5

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_FiniteEnergyPlane_bracket_le_of_norm_sub_le
import Theorems.Thm_FiniteEnergyPlane_integral_mul_bilin_fderiv_eq
import Theorems.Thm_FiniteEnergyPlane_monotoneOn_exp_mul_div_sq



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

set_option maxHeartbeats 1000000 in
/-- Monotone energy ratio near a complex structure. Let `J₀` be a complex structure on a real inner
product space with `‖J₀‖ ≤ b`, `1 ≤ b`, `γ = 1 + b²`, and `g(v, v') = ⟪v, v'⟫ + ⟪J₀ v, J₀ v'⟫`. Let
`Λ ≥ 0`, `S > 0` with `Λ S ≤ 1 / (4 γ² b)`, `U ⊆ ℂ` open, `u` a `C²` map on `U` with
`∂ₜu = A(z) ∂ₛu` and `‖A(z) - J₀‖ ≤ Λ ‖u z - q‖` wherever `‖u z - q‖ < S`, and with compact sets
`{z ∈ U | ‖u z - q‖ ≤ ρ}` for `ρ < S`. Let `φ` be a nonincreasing `C¹` cutoff in `[0, 1]`
vanishing on `[3/4, ∞)` with bounded derivative vanishing on `(3/4, ∞)`. Put
`Φ_s(z) = 1_U(z) φ(g(u z - q, u z - q) / s²) g(J₀ ∂ₛu, ∂ₜu)`. Then for `0 < s < S`, `Φ_s` is
integrable and nonnegative, and `s ↦ e^{2 C s} ∫ Φ_s / s²` is nondecreasing on `(0, S)`, where
`C = (γ b + 2 γ² b) Λ`. -/
theorem monotoneOn_energy_ratio_aux {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (J₀ : F →L[ℝ] F) (hJ : J₀.comp J₀ = -ContinuousLinearMap.id ℝ F) {b : ℝ} (hb1 : 1 ≤ b)
    (hJb : ‖J₀‖ ≤ b) {Λ S : ℝ} (hΛ : 0 ≤ Λ) (hS : 0 < S)
    (hΛS : Λ * S ≤ 1 / (4 * (1 + b ^ 2) ^ 2 * b)) (q : F) {U : Set ℂ} {u : ℂ → F}
    (A : ℂ → F →L[ℝ] F) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hhol : ∀ z ∈ U, ‖u z - q‖ < S → fderiv ℝ u z Complex.I = A z (fderiv ℝ u z 1) ∧
      ‖A z - J₀‖ ≤ Λ * ‖u z - q‖)
    (hprop : ∀ ρ, ρ < S → IsCompact {z | z ∈ U ∧ ‖u z - q‖ ≤ ρ})
    {φ : ℝ → ℝ} (hφc : ContDiff ℝ 1 φ) (hφ0 : ∀ t, 3 / 4 ≤ t → φ t = 0)
    (hφb : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) (hφd : ∀ t, deriv φ t ≤ 0)
    (hφd0 : ∀ t, 3 / 4 < t → deriv φ t = 0) {Mφ : ℝ} (hMφ : ∀ t, |deriv φ t| ≤ Mφ) :
    (∀ s ∈ Ioo 0 S, Integrable (fun z => U.indicator (fun z => φ ((s ^ 2)⁻¹ * (inner ℝ (u z - q) (u z - q) + inner ℝ (J₀ (u z - q)) (J₀ (u z - q))))) z *
          (inner ℝ (J₀ (fderiv ℝ u z 1)) (fderiv ℝ u z Complex.I) +
          inner ℝ (J₀ (J₀ (fderiv ℝ u z 1))) (J₀ (fderiv ℝ u z Complex.I)))) ∧ ∀ z, 0 ≤ U.indicator (fun z => φ ((s ^ 2)⁻¹ * (inner ℝ (u z - q) (u z - q) + inner ℝ (J₀ (u z - q)) (J₀ (u z - q))))) z *
          (inner ℝ (J₀ (fderiv ℝ u z 1)) (fderiv ℝ u z Complex.I) +
          inner ℝ (J₀ (J₀ (fderiv ℝ u z 1))) (J₀ (fderiv ℝ u z Complex.I)))) ∧
    MonotoneOn (fun s => Real.exp (2 * (((1 + b ^ 2) * b + 2 * (1 + b ^ 2) ^ 2 * b) * Λ) * s) *
      (∫ z, U.indicator (fun z => φ ((s ^ 2)⁻¹ * (inner ℝ (u z - q) (u z - q) + inner ℝ (J₀ (u z - q)) (J₀ (u z - q))))) z *
          (inner ℝ (J₀ (fderiv ℝ u z 1)) (fderiv ℝ u z Complex.I) +
          inner ℝ (J₀ (J₀ (fderiv ℝ u z 1))) (J₀ (fderiv ℝ u z Complex.I)))) / s ^ 2) (Ioo 0 S) := by
  have hb0 : 0 < b := by linarith
  set γ := 1 + b ^ 2 with hγ
  have hγ1 : 1 ≤ γ := by nlinarith
  have hγ0 : 0 < γ := by linarith
  have hJJ : ∀ v, J₀ (J₀ v) = -v := fun v => by
    simpa using congrArg (fun T : F →L[ℝ] F => T v) hJ
  have hJn : ∀ v, ‖J₀ v‖ ≤ b * ‖v‖ := fun v =>
    (J₀.le_opNorm v).trans (mul_le_mul_of_nonneg_right hJb (norm_nonneg _))
  have hMφ0 : 0 ≤ Mφ := (abs_nonneg _).trans (hMφ 0)
  have hφdc : Continuous (deriv φ) := hφc.continuous_deriv le_rfl
  have hφdiff : Differentiable ℝ φ := hφc.differentiable one_ne_zero
  -- the frozen inner product `g` and the form `σ(v, v') = g(J₀ v, v')`
  let gB : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ + (innerSL ℝ).bilinearComp J₀ J₀
  have hg : ∀ v v', gB v v' = inner ℝ v v' + inner ℝ (J₀ v) (J₀ v') := fun v v' => rfl
  let σ : F →L[ℝ] F →L[ℝ] ℝ := gB.comp J₀
  have hσ : ∀ v v', σ v v' = gB (J₀ v) v' := fun v v' => rfl
  have hgsymm : ∀ v v', gB v v' = gB v' v := fun v v' => by
    rw [hg, hg, real_inner_comm v, real_inner_comm (J₀ v)]
  have hσanti : ∀ v v', σ v v' = -σ v' v := by
    intro v v'
    rw [hσ, hσ, hg, hg, hJJ, hJJ, inner_neg_left, inner_neg_left, real_inner_comm (J₀ v') v,
      real_inner_comm v' (J₀ v)]
    ring
  have hgN : ∀ v, ‖v‖ ^ 2 ≤ gB v v := fun v => by
    rw [hg, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖J₀ v‖]
  have hgU : ∀ v, gB v v ≤ γ * ‖v‖ ^ 2 := fun v => by
    rw [hg, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    have h2 : ‖J₀ v‖ ^ 2 ≤ (b * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hJn v) 2
    nlinarith
  have hgle : ∀ v v', |gB v v'| ≤ γ * ‖v‖ * ‖v'‖ := by
    intro v v'
    have h1 := abs_real_inner_le_norm v v'
    have h2 := abs_real_inner_le_norm (J₀ v) (J₀ v')
    have h4 : ‖J₀ v‖ * ‖J₀ v'‖ ≤ b * ‖v‖ * (b * ‖v'‖) :=
      mul_le_mul (hJn v) (hJn v') (norm_nonneg _) (by positivity)
    rw [hg]
    calc |inner ℝ v v' + inner ℝ (J₀ v) (J₀ v')| ≤ ‖v‖ * ‖v'‖ + ‖J₀ v‖ * ‖J₀ v'‖ :=
          (abs_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ γ * ‖v‖ * ‖v'‖ := by rw [hγ]; nlinarith [mul_nonneg (norm_nonneg v) (norm_nonneg v')]
  -- the main functions
  set f : ℂ → ℝ := fun z => gB (u z - q) (u z - q) with hf
  set a : ℂ → ℝ := fun z => σ (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I) with ha
  set Bk : ℂ → ℝ := fun z => gB (u z - q) (fderiv ℝ u z 1) * σ (u z - q) (fderiv ℝ u z Complex.I) -
    gB (u z - q) (fderiv ℝ u z Complex.I) * σ (u z - q) (fderiv ℝ u z 1) with hBk
  set C := (γ * b + 2 * γ ^ 2 * b) * Λ with hC
  have hC0 : 0 ≤ C := by positivity
  have hCS : C * S ≤ 3 / 4 := by
    have h1 : C * S = (γ * b + 2 * γ ^ 2 * b) * (Λ * S) := by rw [hC]; ring
    have h2 : (γ * b + 2 * γ ^ 2 * b) * (Λ * S) ≤ (γ * b + 2 * γ ^ 2 * b) * (1 / (4 * γ ^ 2 * b)) :=
      mul_le_mul_of_nonneg_left hΛS (by positivity)
    have h3 : (γ * b + 2 * γ ^ 2 * b) * (1 / (4 * γ ^ 2 * b)) = 1 / (4 * γ) + 1 / 2 := by
      field_simp; ring
    have h4 : 1 / (4 * γ) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hgbΛS : γ * b * (Λ * S) ≤ 1 / 4 := by
    have h2 : γ * b * (Λ * S) ≤ γ * b * (1 / (4 * γ ^ 2 * b)) :=
      mul_le_mul_of_nonneg_left hΛS (by positivity)
    have h3 : γ * b * (1 / (4 * γ ^ 2 * b)) = 1 / (4 * γ) := by field_simp
    have h4 : 1 / (4 * γ) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  set K : ℝ → Set ℂ := fun ρ => {z | z ∈ U ∧ ‖u z - q‖ ≤ ρ} with hK
  have hKc : ∀ ρ, ρ < S → IsCompact (K ρ) := hprop
  have hKU : ∀ ρ, K ρ ⊆ U := fun ρ z hz => hz.1
  -- regularity on `U`
  have hu1 : ContDiffOn ℝ 1 (fderiv ℝ u) U := hu.fderiv_of_isOpen hU (by norm_num)
  have hDu : ∀ z ∈ U, HasFDerivAt u (fderiv ℝ u z) z := fun z hz =>
    ((hu.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  have hfC : ContDiffOn ℝ 2 f U :=
    (gB.contDiff.comp_contDiffOn (hu.sub contDiffOn_const)).clm_apply (hu.sub contDiffOn_const)
  have hfcont : ContinuousOn f U := hfC.continuousOn
  have hacont : ContinuousOn a U :=
    ((σ.continuous.comp_continuousOn (hu1.continuousOn.clm_apply continuousOn_const))).clm_apply
      (hu1.continuousOn.clm_apply continuousOn_const)
  have hBkcont : ContinuousOn Bk U := by
    have hw : ContinuousOn (fun z => u z - q) U := hu.continuousOn.sub continuousOn_const
    have hx : ContinuousOn (fun z => fderiv ℝ u z 1) U := hu1.continuousOn.clm_apply continuousOn_const
    have hy : ContinuousOn (fun z => fderiv ℝ u z Complex.I) U :=
      hu1.continuousOn.clm_apply continuousOn_const
    exact (((gB.continuous.comp_continuousOn hw).clm_apply hx).mul
      ((σ.continuous.comp_continuousOn hw).clm_apply hy)).sub
      (((gB.continuous.comp_continuousOn hw).clm_apply hy).mul
      ((σ.continuous.comp_continuousOn hw).clm_apply hx))
  have hfw : ∀ z, ‖u z - q‖ ^ 2 ≤ f z := fun z => hgN _
  have hf0 : ∀ z, 0 ≤ f z := fun z => (sq_nonneg _).trans (hfw z)
  -- where the cutoff (or its derivative) is active, `u` is `s`-close to `q`
  have hclose : ∀ s, 0 < s → ∀ z, (s ^ 2)⁻¹ * f z < 1 → ‖u z - q‖ < s := by
    intro s hs z hz
    have : f z < s ^ 2 := by
      rwa [inv_mul_lt_iff₀ (by positivity), mul_one] at hz
    nlinarith [hfw z, norm_nonneg (u z - q)]
  have hfar : ∀ s, 0 < s → ∀ z, s < ‖u z - q‖ → 1 < (s ^ 2)⁻¹ * f z := by
    intro s hs z hz
    rw [lt_inv_mul_iff₀ (by positivity), mul_one]
    nlinarith [hfw z]
  -- pointwise consequences of the bracket bounds at a point with `‖u z - q‖ < S`
  have hpt : ∀ z ∈ U, ‖u z - q‖ < S →
      Bk z ≤ f z * gB (fderiv ℝ u z 1) (fderiv ℝ u z 1) * (1 + 2 * γ ^ 2 * b * (Λ * ‖u z - q‖)) ∧
      gB (fderiv ℝ u z 1) (fderiv ℝ u z 1) * (1 - γ * b * (Λ * ‖u z - q‖)) ≤ a z := by
    intro z hz hzS
    obtain ⟨hI, hA⟩ := hhol z hz hzS
    have := bracket_le_of_norm_sub_le J₀ (A z) hJ hJb hA (u z - q) (fderiv ℝ u z 1)
    simp only [hBk, ha, hf, hσ, hg, hI]
    exact this
  -- cutoffs: `ψ s = 1_U φ(f / s²)`, its `s`-derivative weight `χ s`, its gradient weight `χ₂ s`
  set ψ : ℝ → ℂ → ℝ := fun s => U.indicator (fun z => φ ((s ^ 2)⁻¹ * f z)) with hψ
  set χ : ℝ → ℂ → ℝ := fun s =>
    U.indicator (fun z => deriv φ ((s ^ 2)⁻¹ * f z) * (-2 * f z / s ^ 3)) with hχ
  set χ₂ : ℝ → ℂ → ℝ := fun s =>
    U.indicator (fun z => -deriv φ ((s ^ 2)⁻¹ * f z) * (s ^ 2)⁻¹) with hχ₂
  have hKcl : ∀ ρ, ρ < S → IsClosed (K ρ) := fun ρ hρ => (hKc ρ hρ).isClosed
  have hloc0 : ∀ ρ, ρ < S → ∀ g : ℂ → ℝ, (∀ z, z ∉ K ρ → g z = 0) → ∀ z, z ∉ K ρ →
      g =ᶠ[𝓝 z] 0 := by
    intro ρ hρ g hg z hz
    filter_upwards [(hKcl ρ hρ).isOpen_compl.mem_nhds hz] with y hy using hg y hy
  have hnotK : ∀ s z, z ∈ U → z ∉ K s → s < ‖u z - q‖ := fun s z hzU hz => by
    by_contra h; exact hz ⟨hzU, le_of_not_gt h⟩
  have hψ0 : ∀ s, 0 < s → ∀ z, z ∉ K s → ψ s z = 0 := by
    intro s hs z hz
    by_cases hzU : z ∈ U
    · simp only [hψ, indicator_of_mem hzU]
      exact hφ0 _ (by linarith [hfar s hs z (hnotK s z hzU hz)])
    · simp [hψ, hzU]
  have hχ0 : ∀ s, 0 < s → ∀ z, z ∉ K s → χ s z = 0 := by
    intro s hs z hz
    by_cases hzU : z ∈ U
    · simp only [hχ, indicator_of_mem hzU]
      rw [hφd0 _ (by linarith [hfar s hs z (hnotK s z hzU hz)]), zero_mul]
    · simp [hχ, hzU]
  have hχ₂0 : ∀ s, 0 < s → ∀ z, z ∉ K s → χ₂ s z = 0 := by
    intro s hs z hz
    by_cases hzU : z ∈ U
    · simp only [hχ₂, indicator_of_mem hzU]
      rw [hφd0 _ (by linarith [hfar s hs z (hnotK s z hzU hz)])]; simp
    · simp [hχ₂, hzU]
  have hψeq : ∀ s, ∀ z ∈ U, ψ s =ᶠ[𝓝 z] fun y => φ ((s ^ 2)⁻¹ * f y) := fun s z hz => by
    filter_upwards [hU.mem_nhds hz] with y hy using indicator_of_mem hy _
  have hψC : ∀ s, 0 < s → s < S → ContDiff ℝ 1 (ψ s) := by
    intro s hs hsS
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · refine ContDiffAt.congr_of_eventuallyEq ?_ (hψeq s z hz)
      exact hφc.contDiffAt.comp z
        (contDiffAt_const.mul ((hfC.contDiffAt (hU.mem_nhds hz)).of_le (by norm_num)))
    · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (hloc0 s hsS _ (hψ0 s hs) z (fun h => hz h.1))
  have hψts : ∀ s, 0 < s → s < S → tsupport (ψ s) ⊆ K s := fun s hs hsS =>
    closure_minimal (fun z hz => by by_contra h; exact hz (hψ0 s hs z h)) (hKcl s hsS)
  have hψcs : ∀ s, 0 < s → s < S → HasCompactSupport (ψ s) := fun s hs hsS =>
    (hKc s hsS).of_isClosed_subset (isClosed_tsupport _) (hψts s hs hsS)
  have hχcont : ∀ s, ContinuousOn (χ s) U := fun s =>
    ((hφdc.comp_continuousOn (continuousOn_const.mul hfcont)).mul
      ((continuousOn_const.mul hfcont).div_const _)).congr (fun z hz => indicator_of_mem hz _)
  have hχ₂cont : ∀ s, ContinuousOn (χ₂ s) U := fun s =>
    ((hφdc.comp_continuousOn (continuousOn_const.mul hfcont)).neg.mul continuousOn_const).congr
      (fun z hz => indicator_of_mem hz _)
  -- products with functions continuous on `U`
  have hcontprod : ∀ ρ, ρ < S → ∀ g G : ℂ → ℝ, (∀ z, z ∉ K ρ → g z = 0) → ContinuousOn g U →
      ContinuousOn G U → Continuous (fun z => g z * G z) := by
    intro ρ hρ g G hg0 hg hG
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ U
    · exact (hg.continuousAt (hU.mem_nhds hz)).mul (hG.continuousAt (hU.mem_nhds hz))
    · have h1 : (fun z => g z * G z) =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [hloc0 ρ hρ g hg0 z (fun h => hz h.1)] with y hy
        simp [hy]
      exact (continuousAt_congr h1).2 continuousAt_const
  have hintprod : ∀ ρ, ρ < S → ∀ g G : ℂ → ℝ, (∀ z, z ∉ K ρ → g z = 0) → ContinuousOn g U →
      ContinuousOn G U → Integrable (fun z => g z * G z) := by
    intro ρ hρ g G hg0 hg hG
    refine (hcontprod ρ hρ g G hg0 hg hG).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (hKc ρ hρ) ?_
    intro z hz; simp [hg0 z hz]
  -- `I(s) = ∫ ψ_s a` and its derivative candidate `I'(s) = ∫ χ_s a`
  set I : ℝ → ℝ := fun s => ∫ z, ψ s z * a z with hI
  set I' : ℝ → ℝ := fun s => ∫ z, χ s z * a z with hI'
  have hfd : ∀ z ∈ U, HasFDerivAt f ((gB (u z - q)).comp (fderiv ℝ u z) +
      (gB.comp (fderiv ℝ u z)).flip (u z - q)) z := by
    intro z hz
    have h1 : HasFDerivAt (fun y => u y - q) (fderiv ℝ u z) z := (hDu z hz).sub_const q
    exact (gB.hasFDerivAt.comp z h1).clm_apply h1
  have hψd : ∀ s, ∀ z ∈ U, ∀ h : ℂ, fderiv ℝ (ψ s) z h =
      deriv φ ((s ^ 2)⁻¹ * f z) * ((s ^ 2)⁻¹ * (2 * gB (u z - q) (fderiv ℝ u z h))) := by
    intro s z hz h
    rw [(hψeq s z hz).fderiv_eq]
    have h3 := (hφdiff ((s ^ 2)⁻¹ * f z)).hasDerivAt.comp_hasFDerivAt z ((hfd z hz).const_mul (s ^ 2)⁻¹)
    rw [show (fun y => φ ((s ^ 2)⁻¹ * f y)) = φ ∘ (fun y => (s ^ 2)⁻¹ * f y) from rfl, h3.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
    rw [hgsymm (fderiv ℝ u z h)]; ring
  have hψd0 : ∀ s, 0 < s → s < S → ∀ z, z ∉ U → fderiv ℝ (ψ s) z = 0 := fun s hs hsS z hz =>
    fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := ψ s) (fun h => hz (hKU s (hψts s hs hsS h)))
  have hIform : ∀ s, 0 < s → s < S → I s = ∫ z, χ₂ s z * Bk z := by
    intro s hs hsS
    have hC := integral_mul_bilin_fderiv_eq σ hσanti hU hu (hψC s hs hsS) (hψcs s hs hsS)
      ((hψts s hs hsS).trans (hKU s)) q
    rw [show I s = ∫ z, ψ s z * σ (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I) from rfl, hC,
      ← integral_const_mul]
    congr 1; funext z
    by_cases hz : z ∈ U
    · rw [hψd s z hz, hψd s z hz]
      simp only [hχ₂, hBk, indicator_of_mem hz]
      ring
    · rw [hψd0 s hs hsS z hz]; simp [hχ₂, hz]
  -- the differential inequality
  have hineq : ∀ s ∈ Ioo 0 S, 2 * (1 - C * s) * I s ≤ s * I' s := by
    rintro s ⟨hs, hsS⟩
    have hint1 : Integrable (fun z => χ₂ s z * Bk z) :=
      hintprod s hsS _ _ (hχ₂0 s hs) (hχ₂cont s) hBkcont
    have hint2 : Integrable (fun z => χ s z * a z) :=
      hintprod s hsS _ _ (hχ0 s hs) (hχcont s) hacont
    have hCs : 0 ≤ 1 - C * s := by
      have : C * s ≤ C * S := mul_le_mul_of_nonneg_left hsS.le hC0
      linarith
    have key : ∀ z, (1 - C * s) * (χ₂ s z * Bk z) ≤ s / 2 * (χ s z * a z) := by
      intro z
      by_cases hz : z ∈ U
      · simp only [hχ₂, hχ, indicator_of_mem hz]
        by_cases hd : deriv φ ((s ^ 2)⁻¹ * f z) = 0
        · simp [hd]
        · have ht : (s ^ 2)⁻¹ * f z ≤ 3 / 4 := by
            by_contra h; exact hd (hφd0 _ (lt_of_not_ge h))
          have hw : ‖u z - q‖ < s := hclose s hs z (by linarith)
          obtain ⟨h1, h2⟩ := hpt z hz (hw.trans hsS)
          set N := gB (fderiv ℝ u z 1) (fderiv ℝ u z 1)
          have hN : 0 ≤ N := (sq_nonneg _).trans (hgN _)
          set ε := Λ * ‖u z - q‖ with hε
          have hε0 : 0 ≤ ε := mul_nonneg hΛ (norm_nonneg _)
          have hεs : ε ≤ Λ * s := mul_le_mul_of_nonneg_left hw.le hΛ
          have hk : (1 + 2 * γ ^ 2 * b * ε) * (1 - C * s) ≤ 1 - γ * b * ε := by
            have h3 : (γ * b + 2 * γ ^ 2 * b) * ε ≤ C * s := by
              have e : C * s = (γ * b + 2 * γ ^ 2 * b) * (Λ * s) := by rw [hC]; ring
              rw [e]; exact mul_le_mul_of_nonneg_left hεs (by positivity)
            have h4 : 0 ≤ 2 * γ ^ 2 * b * ε * (C * s) := by positivity
            nlinarith
          have e1 : (1 - C * s) * Bk z ≤ (1 - C * s) * (f z * N * (1 + 2 * γ ^ 2 * b * ε)) :=
            mul_le_mul_of_nonneg_left h1 hCs
          have e2 : (1 - C * s) * (f z * N * (1 + 2 * γ ^ 2 * b * ε)) ≤
              f z * N * (1 - γ * b * ε) := by
            have := mul_le_mul_of_nonneg_left hk (mul_nonneg (hf0 z) hN)
            linarith
          have e3 : f z * N * (1 - γ * b * ε) ≤ f z * a z := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 (hf0 z)
          have hd0 : 0 ≤ -deriv φ ((s ^ 2)⁻¹ * f z) * (s ^ 2)⁻¹ :=
            mul_nonneg (by linarith [hφd ((s ^ 2)⁻¹ * f z)]) (by positivity)
          calc (1 - C * s) * (-deriv φ ((s ^ 2)⁻¹ * f z) * (s ^ 2)⁻¹ * Bk z)
              = (-deriv φ ((s ^ 2)⁻¹ * f z) * (s ^ 2)⁻¹) * ((1 - C * s) * Bk z) := by ring
            _ ≤ (-deriv φ ((s ^ 2)⁻¹ * f z) * (s ^ 2)⁻¹) * (f z * a z) :=
              mul_le_mul_of_nonneg_left (e1.trans (e2.trans e3)) hd0
            _ = s / 2 * (deriv φ ((s ^ 2)⁻¹ * f z) * (-2 * f z / s ^ 3) * a z) := by
              field_simp
      · simp [hχ₂, hχ, hz]
    have := integral_mono (hint1.const_mul (1 - C * s)) (hint2.const_mul (s / 2)) key
    rw [integral_const_mul, integral_const_mul] at this
    rw [hIform s hs hsS]
    show 2 * (1 - C * s) * (∫ z, χ₂ s z * Bk z) ≤ s * ∫ z, χ s z * a z
    linarith
  -- `I` is differentiable with derivative `I'` on `(0, S)`
  have hderI : ∀ s ∈ Ioo 0 S, HasDerivAt I (I' s) s := by
    rintro s₀ ⟨hs₀, hs₀S⟩
    set s₁ := (s₀ + S) / 2 with hs₁
    have hs₁S : s₁ < S := by rw [hs₁]; linarith
    set δ := min (s₀ / 2) ((S - s₀) / 2) with hδ
    have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
    have hball : ∀ s ∈ ball s₀ δ, s₀ / 2 < s ∧ s < s₁ := by
      intro s hs
      rw [mem_ball, Real.dist_eq, abs_lt] at hs
      have h1 := min_le_left (s₀ / 2) ((S - s₀) / 2)
      have h2 := min_le_right (s₀ / 2) ((S - s₀) / 2)
      constructor
      · linarith
      · rw [hs₁]; linarith
    set bound : ℂ → ℝ :=
      (K s₁).indicator (fun z => Mφ * (2 * s₁ ^ 2 / (s₀ / 2) ^ 3) * |a z|) with hbound
    have hdiff : ∀ z, ∀ s ∈ ball s₀ δ, HasDerivAt (fun s => ψ s z * a z) (χ s z * a z) s := by
      intro z s hs
      have hs0 : 0 < s := by linarith [(hball s hs).1]
      by_cases hz : z ∈ U
      · simp only [hψ, hχ, indicator_of_mem hz]
        have h1 : HasDerivAt (fun y : ℝ => (y ^ 2)⁻¹ * f z) (-2 * f z / s ^ 3) s := by
          have h0 := ((hasDerivAt_pow 2 s).inv (by positivity)).mul_const (f z)
          refine h0.congr_deriv ?_
          have hs0' : s ≠ 0 := hs0.ne'
          simp only [Nat.cast_ofNat]
          field_simp
          ring
        exact ((hφdiff ((s ^ 2)⁻¹ * f z)).hasDerivAt.comp s h1).mul_const (a z)
      · simp only [hψ, hχ, indicator_of_notMem hz, zero_mul]
        exact hasDerivAt_const _ _
    have hmeas : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable (fun z => ψ s z * a z) volume := by
      filter_upwards [ball_mem_nhds s₀ hδ0] with s hs
      have := hball s hs
      have hs0 : 0 < s := by linarith
      exact (hcontprod s (by linarith) _ _ (hψ0 s hs0)
        (hψC s hs0 (by linarith)).continuous.continuousOn hacont).aestronglyMeasurable
    have hint0 : Integrable (fun z => ψ s₀ z * a z) :=
      hintprod s₀ hs₀S _ _ (hψ0 s₀ hs₀) (hψC s₀ hs₀ hs₀S).continuous.continuousOn hacont
    have hmeas' : AEStronglyMeasurable (fun z => χ s₀ z * a z) volume :=
      (hcontprod s₀ hs₀S _ _ (hχ0 s₀ hs₀) (hχcont s₀) hacont).aestronglyMeasurable
    have hbd : ∀ᵐ z ∂volume, ∀ s ∈ ball s₀ δ, ‖χ s z * a z‖ ≤ bound z := by
      refine Filter.Eventually.of_forall (fun z s hs => ?_)
      obtain ⟨hs1, hs2⟩ := hball s hs
      have hs0 : 0 < s := by linarith
      by_cases hzK : z ∈ K s₁
      · simp only [hbound, indicator_of_mem hzK, Real.norm_eq_abs, abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        simp only [hχ, indicator_of_mem hzK.1]
        by_cases hd : deriv φ ((s ^ 2)⁻¹ * f z) = 0
        · rw [hd, zero_mul, abs_zero]; positivity
        · have ht : (s ^ 2)⁻¹ * f z ≤ 3 / 4 := by
            by_contra h; exact hd (hφd0 _ (lt_of_not_ge h))
          have hfz : f z ≤ s ^ 2 := by
            rw [inv_mul_le_iff₀ (by positivity)] at ht; nlinarith
          rw [abs_mul]
          refine mul_le_mul (hMφ _) ?_ (abs_nonneg _) hMφ0
          rw [abs_div, abs_mul, abs_of_nonneg (hf0 z), abs_of_pos (by positivity : (0 : ℝ) < s ^ 3)]
          norm_num
          apply div_le_div₀ (by positivity) _ (by positivity) (pow_le_pow_left₀ (by linarith) hs1.le 3)
          nlinarith [pow_le_pow_left₀ hs0.le hs2.le 2]
      · have hzK' : z ∉ K s := fun h => hzK ⟨h.1, h.2.trans hs2.le⟩
        simp [hbound, indicator_of_notMem hzK, hχ0 s hs0 z hzK']
    have hbint : Integrable bound := by
      rw [hbound]
      refine IntegrableOn.integrable_indicator ?_ (hKcl s₁ hs₁S).measurableSet
      exact ContinuousOn.integrableOn_compact (hKc s₁ hs₁S)
        ((continuousOn_const.mul hacont.abs).mono (hKU s₁))
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds s₀ hδ0) hmeas hint0
      hmeas' hbd hbint (Filter.Eventually.of_forall hdiff)).2
  have hmono := monotoneOn_exp_mul_div_sq hderI hineq
  -- the integrand `ψ_s a` is nonnegative
  have hψnn : ∀ s, 0 < s → s < S → ∀ z, 0 ≤ ψ s z * a z := by
    intro s hs hsS z
    by_cases hz : z ∈ U
    · by_cases hp : φ ((s ^ 2)⁻¹ * f z) = 0
      · simp [hψ, indicator_of_mem hz, hp]
      · have ht : (s ^ 2)⁻¹ * f z < 3 / 4 := by
          by_contra h; exact hp (hφ0 _ (le_of_not_gt h))
        have hw : ‖u z - q‖ < s := hclose s hs z (by linarith)
        have h2 := (hpt z hz (hw.trans hsS)).2
        have hε : γ * b * (Λ * ‖u z - q‖) ≤ 1 / 4 := by
          have : Λ * ‖u z - q‖ ≤ Λ * S := mul_le_mul_of_nonneg_left (hw.trans hsS).le hΛ
          exact (mul_le_mul_of_nonneg_left this (by positivity)).trans hgbΛS
        have hN : 0 ≤ gB (fderiv ℝ u z 1) (fderiv ℝ u z 1) := (sq_nonneg _).trans (hgN _)
        have ha0 : 0 ≤ a z := le_trans (mul_nonneg hN (by linarith)) h2
        simp only [hψ, indicator_of_mem hz]
        exact mul_nonneg (hφb _).1 ha0
    · simp [hψ, hz]
  have hI0 : ∀ s, 0 < s → s < S → 0 ≤ I s := fun s hs hsS => integral_nonneg (hψnn s hs hsS)
  refine ⟨fun s hs => ⟨?_, hψnn s hs.1 hs.2⟩, hmono⟩
  exact hintprod s hs.2 _ _ (hψ0 s hs.1) (hψC s hs.1 hs.2).continuous.continuousOn hacont

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (J₀ : F →L[ℝ] F) (hJ : J₀.comp J₀ = -ContinuousLinearMap.id ℝ F) {b : ℝ} (hb1 : 1 ≤ b)
    (hJb : ‖J₀‖ ≤ b) {Λ S : ℝ} (hΛ : 0 ≤ Λ) (hS : 0 < S)
    (hΛS : Λ * S ≤ 1 / (4 * (1 + b ^ 2) ^ 2 * b)) (q : F) {U : Set ℂ} {u : ℂ → F}
    (A : ℂ → F →L[ℝ] F) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hhol : ∀ z ∈ U, ‖u z - q‖ < S → fderiv ℝ u z Complex.I = A z (fderiv ℝ u z 1) ∧
      ‖A z - J₀‖ ≤ Λ * ‖u z - q‖)
    (hprop : ∀ ρ, ρ < S → IsCompact {z | z ∈ U ∧ ‖u z - q‖ ≤ ρ})
    {φ : ℝ → ℝ} (hφc : ContDiff ℝ 1 φ) (hφ0 : ∀ t, 3 / 4 ≤ t → φ t = 0)
    (hφb : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) (hφd : ∀ t, deriv φ t ≤ 0)
    (hφd0 : ∀ t, 3 / 4 < t → deriv φ t = 0) {Mφ : ℝ} (hMφ : ∀ t, |deriv φ t| ≤ Mφ) :
    (∀ s ∈ Ioo 0 S, Integrable (fun z => U.indicator (fun z => φ ((s ^ 2)⁻¹ * (inner ℝ (u z - q) (u z - q) + inner ℝ (J₀ (u z - q)) (J₀ (u z - q))))) z *
          (inner ℝ (J₀ (fderiv ℝ u z 1)) (fderiv ℝ u z Complex.I) +
          inner ℝ (J₀ (J₀ (fderiv ℝ u z 1))) (J₀ (fderiv ℝ u z Complex.I)))) ∧ ∀ z, 0 ≤ U.indicator (fun z => φ ((s ^ 2)⁻¹ * (inner ℝ (u z - q) (u z - q) + inner ℝ (J₀ (u z - q)) (J₀ (u z - q))))) z *
          (inner ℝ (J₀ (fderiv ℝ u z 1)) (fderiv ℝ u z Complex.I) +
          inner ℝ (J₀ (J₀ (fderiv ℝ u z 1))) (J₀ (fderiv ℝ u z Complex.I)))) ∧
    MonotoneOn (fun s => Real.exp (2 * (((1 + b ^ 2) * b + 2 * (1 + b ^ 2) ^ 2 * b) * Λ) * s) *
      (∫ z, U.indicator (fun z => φ ((s ^ 2)⁻¹ * (inner ℝ (u z - q) (u z - q) + inner ℝ (J₀ (u z - q)) (J₀ (u z - q))))) z *
          (inner ℝ (J₀ (fderiv ℝ u z 1)) (fderiv ℝ u z Complex.I) +
          inner ℝ (J₀ (J₀ (fderiv ℝ u z 1))) (J₀ (fderiv ℝ u z Complex.I)))) / s ^ 2) (Ioo 0 S) :=
  monotoneOn_energy_ratio_aux J₀ hJ hb1 hJb hΛ hS hΛS q A hU hu hhol hprop hφc hφ0 hφb hφd hφd0 hMφ
