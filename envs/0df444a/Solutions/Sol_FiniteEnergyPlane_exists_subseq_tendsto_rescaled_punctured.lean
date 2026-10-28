-- Prove2me | solution 1 for FiniteEnergyPlane.exists_subseq_tendsto_rescaled_punctured
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-26T22:02:16.277139+00:00
-- url     : https://prove2.me/submissions/d6f5d045-78df-4c85-8cc9-446d0150f6fb

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInftyLocOn_punctured
import Theorems.Thm_FiniteEnergyPlane_rescale_isFiniteEnergyCurve
import Theorems.Thm_FiniteEnergyPlane_lintegral_energyDensity_le_liminf
import Theorems.Thm_FiniteEnergyPlane_isCompact_aCoord_slab
import Theorems.Thm_FiniteEnergyPlane_norm_fderiv_le_mul_gradNorm
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg
import Theorems.Thm_FiniteEnergyPlane_tendsto_dlambdaEnergy_punctured
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Limits of the normalized rescalings of a finite-energy curve at a puncture with the gradient
bound, on the punctured plane. -/
theorem exists_subseq_tendsto_rescaled_punctured_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C)
    (ρ : ℕ → ℝ) (hρ : ∀ k, 0 < ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → V n, IsFiniteEnergyCurve H J {z | z ≠ 0} w ∧
      dlambdaEnergy H {z | z ≠ 0} w = 0 ∧
      JHolomorphic.TendstoCInftyLocOn
        (fun j z => Real.exp (-2 * aCoord H (u ((ρ (φ j) : ℝ) : ℂ))) • u (((ρ (φ j) : ℝ) : ℂ) * z))
        w {z | z ≠ 0} := by
  classical
  obtain ⟨hJt, -, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨r, hr, C, hC⟩ := hG
  set r₁ : ℝ := min r 1 with hr₁
  have hr₁0 : 0 < r₁ := lt_min hr one_pos
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set O : Set (V n) := {y | y ≠ 0} with hO
  have hOo : IsOpen O := isOpen_ne
  set U : Set ℂ := {z | z ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne
  set U₀ : Set ℂ := ball 0 1 \ {0} with hU₀
  have hU₀o : IsOpen U₀ := isOpen_ball.sdiff isClosed_singleton
  set c : ℕ → ℝ := fun k => Real.exp (-2 * aCoord H (u ((ρ k : ℝ) : ℂ))) with hcdef
  have hcpos : ∀ k, 0 < c k := fun k => Real.exp_pos _
  set v : ℕ → ℂ → V n := fun k z => c k • u (((ρ k : ℝ) : ℂ) * z) with hvdef
  have hρw : Tendsto ρ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hρ0, Eventually.of_forall hρ⟩
  set Rk : ℕ → ℝ := fun k => r₁ / ρ k with hRkdef
  have hRk : Tendsto Rk atTop atTop := by
    have h2 := (tendsto_inv_nhdsGT_zero.comp hρw).const_mul_atTop hr₁0
    simpa [hRkdef, div_eq_mul_inv, Function.comp_def] using h2
  set P : ℕ → Set ℂ := fun k => {z | z ≠ 0 ∧ ‖z‖ < Rk k} with hPdef
  have hPo : ∀ k, IsOpen (P k) := fun k =>
    isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)
  have hnormρ : ∀ k z, ‖((ρ k : ℝ) : ℂ) * z‖ = ρ k * ‖z‖ := fun k z => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ k).le]
  have hPρ : ∀ k, ∀ z ∈ P k, ((ρ k : ℝ) : ℂ) * z ≠ 0 ∧ ‖((ρ k : ℝ) : ℂ) * z‖ < r₁ := by
    intro k z hz
    refine ⟨mul_ne_zero (by exact_mod_cast (hρ k).ne') hz.1, ?_⟩
    rw [hnormρ]
    have h := hz.2
    simp only [hRkdef] at h
    rw [lt_div_iff₀ (hρ k)] at h
    linarith
  have hPU₀ : ∀ k, ∀ z ∈ P k, ((ρ k : ℝ) : ℂ) * z ∈ U₀ := by
    intro k z hz
    obtain ⟨h0, h1⟩ := hPρ k z hz
    exact ⟨mem_ball_zero_iff.2 (lt_of_lt_of_le h1 (min_le_right _ _)), h0⟩
  -- the rescaling identities
  have hfun : ∀ k, (fun w : ℂ => c k • u (0 + ρ k • w)) = v k := fun k => by
    funext w
    simp [hvdef, Complex.real_smul]
  have hresc := fun k => rescale_isFiniteEnergyCurve H hH J hJ U₀ hU₀o u hu 0 (ρ k) (hρ k) (c k)
    (hcpos k)
  have hmemD : ∀ k z, ((ρ k : ℝ) : ℂ) * z ∈ U₀ → 0 + ρ k • z ∈ U₀ := fun k z h => by
    simpa [Complex.real_smul] using h
  have hvk : ∀ k, IsFiniteEnergyCurve H J {w | 0 + ρ k • w ∈ U₀} (v k) := fun k => by
    have h := (hresc k).1
    rw [hfun k] at h
    exact h
  have hPD : ∀ k, P k ⊆ {w | 0 + ρ k • w ∈ U₀} := fun k z hz => hmemD k z (hPU₀ k z hz)
  have hvA : ∀ k z, ((ρ k : ℝ) : ℂ) * z ∈ U₀ →
      aCoord H (v k z) = aCoord H (u (((ρ k : ℝ) : ℂ) * z)) + Real.log (c k) / 2 :=
    fun k z hz => by
      have h := (hresc k).2.1 z (hmemD k z hz)
      simpa [hvdef, Complex.real_smul] using h
  have hvG : ∀ k z, ((ρ k : ℝ) : ℂ) * z ∈ U₀ →
      gradNorm H (v k) z = ρ k * gradNorm H u (((ρ k : ℝ) : ℂ) * z) :=
    fun k z hz => by
      have h := (hresc k).2.2.1 z (hmemD k z hz)
      rw [hfun k] at h
      simpa [Complex.real_smul] using h
  have hpre : ∀ k (A : Set ℂ), {w : ℂ | 0 + ρ k • w ∈ A} = {w | ((ρ k : ℝ) : ℂ) * w ∈ A} :=
    fun k A => by ext w; simp [Complex.real_smul]
  have hvE : ∀ k (A : Set ℂ), A ⊆ U₀ → MeasurableSet A →
      energy H {w | ((ρ k : ℝ) : ℂ) * w ∈ A} (v k) = energy H A u ∧
        dlambdaEnergy H {w | ((ρ k : ℝ) : ℂ) * w ∈ A} (v k) = dlambdaEnergy H A u :=
    fun k A hA hAm => by
      have h := (hresc k).2.2.2 A hA hAm
      rw [hfun k, hpre k A] at h
      exact h
  have hv1 : ∀ k, 1 < Rk k → aCoord H (v k 1) = 0 := fun k hk => by
    have h1 : (1 : ℂ) ∈ P k := ⟨one_ne_zero, by simpa using hk⟩
    rw [hvA k 1 (hPU₀ k 1 h1), mul_one, hcdef]
    simp only [Real.log_exp]
    ring
  have hvC : ∀ k, ∀ z ∈ P k, ‖z‖ * gradNorm H (v k) z ≤ C' := fun k z hz => by
    obtain ⟨h0, h1⟩ := hPρ k z hz
    have h := hC _ h0 (lt_of_lt_of_le h1 (min_le_left _ _))
    rw [hnormρ] at h
    rw [hvG k z (hPU₀ k z hz)]
    calc ‖z‖ * (ρ k * gradNorm H u (((ρ k : ℝ) : ℂ) * z))
        = ρ k * ‖z‖ * gradNorm H u (((ρ k : ℝ) : ℂ) * z) := by ring
      _ ≤ C := h
      _ ≤ C' := le_max_left _ _
  have hsm : ∀ k, ContDiffOn ℝ ∞ (v k) (P k) := fun k => (hvk k).1.mono (hPD k)
  have hne : ∀ k, ∀ z ∈ P k, v k z ≠ 0 := fun k z hz => (hvk k).2.1 z (hPD k hz)
  have hdiff : ∀ k, ∀ z ∈ P k, DifferentiableAt ℝ (v k) z := fun k z hz =>
    ((hsm k).contDiffAt ((hPo k).mem_nhds hz)).differentiableAt (by simp)
  have haCd : ∀ y : V n, y ≠ 0 → DifferentiableAt ℝ (aCoord H) y := fun y hy =>
    (haCs.differentiableOn (by simp) y hy).differentiableAt (hOo.mem_nhds hy)
  have hexpP : ∀ k ζ, ζ.re < Real.log (Rk k) → 0 < Rk k → Complex.exp ζ ∈ P k :=
    fun k ζ hζ hR => by
      refine ⟨Complex.exp_ne_zero ζ, ?_⟩
      show ‖Complex.exp ζ‖ < Rk k
      rw [Complex.norm_exp]
      calc Real.exp ζ.re < Real.exp (Real.log (Rk k)) := Real.exp_lt_exp.2 hζ
        _ = Rk k := Real.exp_log hR
  -- `a ∘ v_k` in logarithmic coordinates
  have hlog : ∀ k, 1 < Rk k → ∀ z ∈ P k, |aCoord H (v k z)| ≤ C' * ‖Complex.log z‖ := by
    intro k hk z hz
    have hR0 : 0 < Rk k := by linarith
    set S : Set ℂ := {ζ | ζ.re < Real.log (Rk k)} with hS
    have hSc : Convex ℝ S := convex_halfSpace_re_lt _
    set f : ℂ → ℝ := fun ζ => aCoord H (v k (Complex.exp ζ)) with hf
    have hfd : ∀ ζ ∈ S, DifferentiableAt ℝ f ζ := fun ζ hζ =>
      ((haCd _ (hne k _ (hexpP k ζ hζ hR0))).comp _ (hdiff k _ (hexpP k ζ hζ hR0))).comp ζ
        ((Complex.hasDerivAt_exp ζ).hasFDerivAt.restrictScalars ℝ).differentiableAt
    have hfb : ∀ ζ ∈ S, ‖fderiv ℝ f ζ‖ ≤ C' := by
      intro ζ hζ
      have hP := hexpP k ζ hζ hR0
      have he : HasFDerivAt Complex.exp
          (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (Complex.exp ζ))).restrictScalars ℝ) ζ :=
        (Complex.hasDerivAt_exp ζ).hasFDerivAt.restrictScalars ℝ
      have hg := ((haCd _ (hne k _ hP)).comp (Complex.exp ζ) (hdiff k _ hP)).hasFDerivAt
      have hfe : HasFDerivAt f ((fderiv ℝ (aCoord H ∘ v k) (Complex.exp ζ)).comp
          (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (Complex.exp ζ))).restrictScalars ℝ))
          ζ := hg.comp ζ he
      rw [hfe.fderiv]
      have hL : ‖((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
          (Complex.exp ζ))).restrictScalars ℝ‖ ≤ ‖Complex.exp ζ‖ :=
        ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
          simp [norm_mul, mul_comm]
      have hA : ‖fderiv ℝ (fun z => aCoord H (v k z)) (Complex.exp ζ)‖ ≤
          gradNorm H (v k) (Complex.exp ζ) :=
        le_add_of_nonneg_right (norm_nonneg _)
      calc _ ≤ ‖fderiv ℝ (aCoord H ∘ v k) (Complex.exp ζ)‖ *
            ‖((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
              (Complex.exp ζ))).restrictScalars ℝ‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ gradNorm H (v k) (Complex.exp ζ) * ‖Complex.exp ζ‖ :=
            mul_le_mul hA hL (norm_nonneg _) ((norm_nonneg _).trans hA)
        _ = ‖Complex.exp ζ‖ * gradNorm H (v k) (Complex.exp ζ) := mul_comm _ _
        _ ≤ C' := hvC k _ hP
    have h0S : (0 : ℂ) ∈ S := by
      show (0 : ℂ).re < _
      simpa using Real.log_pos hk
    have hlS : Complex.log z ∈ S := by
      show (Complex.log z).re < _
      rw [Complex.log_re]
      exact Real.log_lt_log (norm_pos_iff.2 hz.1) hz.2
    have := hSc.norm_image_sub_le_of_norm_fderiv_le hfd hfb h0S hlS
    simp only [hf, Complex.exp_zero, Complex.exp_log hz.1, hv1 k hk, sub_zero,
      Real.norm_eq_abs] at this
    exact this
  have hlogn : ∀ z : ℂ, ‖Complex.log z‖ ≤ |Real.log ‖z‖| + π := fun z => by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im]
    linarith [Complex.abs_arg_le_pi z]
  -- uniform bounds on compact subsets of the punctured plane
  have hbd : ∀ K ⊆ U, IsCompact K → ∃ K' : Set (V n), IsCompact K' ∧ K' ⊆ O ∧ ∃ M : ℝ,
      ∀ᶠ k in atTop, ∀ z ∈ K, v k z ∈ K' ∧ ‖fderiv ℝ (v k) z‖ ≤ M := by
    intro K hKU hK
    have hgc : ContinuousOn (fun z : ℂ => |Real.log ‖z‖| + ‖z‖⁻¹ + ‖z‖) K := by
      refine (((continuous_norm.continuousOn.log fun z hz =>
        norm_ne_zero_iff.2 (hKU hz)).abs).add
        (continuous_norm.continuousOn.inv₀ fun z hz => norm_ne_zero_iff.2 (hKU hz))).add
        continuous_norm.continuousOn
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hgc
    have hB' : ∀ z ∈ K, |Real.log ‖z‖| ≤ B ∧ ‖z‖⁻¹ ≤ B ∧ ‖z‖ ≤ B := by
      intro z hz
      have h := hB z hz
      have h0 : 0 ≤ ‖z‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
      have h1 := abs_nonneg (Real.log ‖z‖)
      have h2 := norm_nonneg z
      rw [Real.norm_of_nonneg (by positivity)] at h
      exact ⟨by linarith, by linarith, by linarith⟩
    set A : ℝ := C' * (B + π) with hAdef
    obtain ⟨M, hM⟩ := norm_fderiv_le_mul_gradNorm H hH J hJ A
    refine ⟨_, isCompact_aCoord_slab H hH J hJ A, fun y hy => hy.1, max M 0 * (C' * B), ?_⟩
    filter_upwards [hRk.eventually (eventually_gt_atTop (max 1 B))] with k hk z hz
    have hk1 : 1 < Rk k := lt_of_le_of_lt (le_max_left _ _) hk
    have hzP : z ∈ P k :=
      ⟨hKU hz, lt_of_le_of_lt (hB' z hz).2.2 (lt_of_le_of_lt (le_max_right _ _) hk)⟩
    have hz0 : z ≠ 0 := hKU hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have ha : |aCoord H (v k z)| ≤ A :=
      (hlog k hk1 z hzP).trans (mul_le_mul_of_nonneg_left
        ((hlogn z).trans (by linarith [(hB' z hz).1])) hC'0)
    refine ⟨⟨hne k z hzP, ha⟩, ?_⟩
    have hgn : 0 ≤ gradNorm H (v k) z := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hg : gradNorm H (v k) z ≤ C' * B := by
      have h1 : ‖z‖ * gradNorm H (v k) z ≤ C' := hvC k z hzP
      have h2 : gradNorm H (v k) z ≤ C' * ‖z‖⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hzpos, mul_comm]
        exact h1
      exact h2.trans (mul_le_mul_of_nonneg_left (hB' z hz).2.1 hC'0)
    calc ‖fderiv ℝ (v k) z‖ ≤ M * gradNorm H (v k) z := hM _ _ (hdiff k z hzP) (hne k z hzP) ha
      _ ≤ max M 0 * gradNorm H (v k) z := mul_le_mul_of_nonneg_right (le_max_left _ _) hgn
      _ ≤ max M 0 * (C' * B) := mul_le_mul_of_nonneg_left hg (le_max_right _ _)
  obtain ⟨φ, hφ, w, hwsm, hwhol, hwO, hconv⟩ :=
    exists_subseq_tendstoCInftyLocOn_punctured (Jtilde H J) O hJt v Rk hRk hsm
      (fun k z hz => (hvk k).2.2.1 z (hPD k hz)) hbd
  have hφt := hφ.tendsto_atTop
  -- pointwise `C¹` convergence on the punctured plane
  have hpt : ∀ z ∈ U, Tendsto (fun j => v (φ j) z) atTop (𝓝 (w z)) ∧
      Tendsto (fun j => fderiv ℝ (v (φ j)) z) atTop (𝓝 (fderiv ℝ w z)) := by
    intro z hzU
    have hz : z ∈ ({z} : Set ℂ) := rfl
    have hKU : ({z} : Set ℂ) ⊆ U := Set.singleton_subset_iff.2 hzU
    have h0 := (hconv {z} hKU isCompact_singleton 0).tendsto_at hz
    have h1 := (hconv {z} hKU isCompact_singleton 1).tendsto_at hz
    constructor
    · have := ((continuous_eval_const (Fin.elim0 : Fin 0 → ℂ)).tendsto _).comp h0
      simpa [Function.comp_def, iteratedFDeriv_zero_apply] using this
    · have hfd : ∀ f : ℂ → V n, fderiv ℝ f z =
          continuousMultilinearCurryFin1 ℝ ℂ (V n) (iteratedFDeriv ℝ 1 f z) := by
        intro f
        ext x
        rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
        rfl
      have := ((continuousMultilinearCurryFin1 ℝ ℂ (V n)).continuous.tendsto _).comp h1
      simpa only [Function.comp_def, ← hfd] using this
  -- Fatou on open subsets eventually inside the domains
  have hfatou : ∀ W ⊆ U, IsOpen W → (∀ᶠ k in atTop, W ⊆ P k) → ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ →
      ∫⁻ z in W, ENNReal.ofReal (energyDensity H ψ w z) ≤
        liminf (fun j => ∫⁻ z in W, ENNReal.ofReal (energyDensity H ψ (v (φ j)) z)) atTop :=
    fun W hWU hW hWP ψ hψ =>
      lintegral_energyDensity_le_liminf H hH J hJ W hW (fun j => v (φ j)) w
        ((hφt.eventually hWP).mono fun j hj =>
          ⟨((hsm _).mono hj).of_le (by simp), fun z hz => hne _ z (hj hz)⟩)
        ((hwsm.of_le (by simp)).mono hWU) (fun z hz => hwO (hWU hz))
        (fun z hz => hpt z (hWU hz)) ψ hψ
  -- the exhausting annuli
  set An : ℕ → Set ℂ := fun N => {z | ((N : ℝ) + 1)⁻¹ < ‖z‖ ∧ ‖z‖ < (N : ℝ) + 1} with hAndef
  have hAno : ∀ N, IsOpen (An N) := fun N =>
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hAnU : ∀ N, An N ⊆ U := fun N z hz =>
    norm_pos_iff.1 (lt_trans (by positivity) hz.1)
  have hAnP : ∀ N : ℕ, ∀ᶠ k in atTop, An N ⊆ P k := fun N =>
    (hRk.eventually (eventually_gt_atTop ((N : ℝ) + 1))).mono fun k hk z hz =>
      ⟨hAnU N hz, hz.2.trans hk⟩
  have hAnmono : Monotone An := by
    intro a b hab z hz
    have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hab 1
    refine ⟨lt_of_le_of_lt ?_ hz.1, lt_of_lt_of_le hz.2 hab'⟩
    exact inv_anti₀ (by positivity) hab'
  have hUeq : U = ⋃ N : ℕ, An N := by
    ext z
    simp only [hU, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hz
      have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
      obtain ⟨N, hN⟩ := exists_nat_gt (max ‖z‖ ‖z‖⁻¹)
      refine ⟨N, ?_, ?_⟩
      · rw [inv_lt_comm₀ (by positivity) hzp]
        linarith [le_max_right ‖z‖ ‖z‖⁻¹]
      · linarith [le_max_left ‖z‖ ‖z‖⁻¹]
    · rintro ⟨N, hN⟩
      exact hAnU N hN
  -- finite energy
  have hEv : ∀ k, ∀ ψ, Admissible ψ →
      ∫⁻ z in P k, ENNReal.ofReal (energyDensity H ψ (v k) z) ≤ energy H U₀ u := by
    intro k ψ hψ
    calc ∫⁻ z in P k, ENNReal.ofReal (energyDensity H ψ (v k) z)
        ≤ ∫⁻ z in {w | ((ρ k : ℝ) : ℂ) * w ∈ U₀}, ENNReal.ofReal (energyDensity H ψ (v k) z) :=
          lintegral_mono_set (fun z hz => hPU₀ k z hz)
      _ ≤ energy H {w | ((ρ k : ℝ) : ℂ) * w ∈ U₀} (v k) :=
          le_iSup₂ (f := fun (ψ : ℝ → ℝ) (_ : Admissible ψ) =>
            ∫⁻ z in {w | ((ρ k : ℝ) : ℂ) * w ∈ U₀}, ENNReal.ofReal (energyDensity H ψ (v k) z))
            ψ hψ
      _ = energy H U₀ u := (hvE k U₀ subset_rfl hU₀o.measurableSet).1
  have hEw : energy H U w ≤ energy H U₀ u := by
    refine iSup₂_le fun ψ hψ => ?_
    set μψ := (volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal (energyDensity H ψ w z))
      with hμψdef
    have hμψ : ∀ s : Set ℂ, MeasurableSet s →
        ∫⁻ z in s, ENNReal.ofReal (energyDensity H ψ w z) = μψ s := fun s hs =>
      (withDensity_apply _ hs).symm
    have hN : ∀ N, (μψ ∘ An) N ≤ energy H U₀ u := by
      intro N
      rw [Function.comp_apply, ← hμψ _ (hAno N).measurableSet]
      refine (hfatou (An N) (hAnU N) (hAno N) (hAnP N) ψ (hψ.1.of_le (by simp))).trans
        (liminf_le_of_frequently_le ?_)
      refine ((hφt.eventually (hAnP N)).mono fun j hj => ?_).frequently
      exact (lintegral_mono_set hj).trans (hEv _ ψ hψ)
    have h := tendsto_measure_iUnion_atTop (μ := μψ) hAnmono
    rw [← hUeq, ← hμψ _ hUo.measurableSet] at h
    exact le_of_tendsto' h hN
  have hwfe : IsFiniteEnergyCurve H J U w :=
    ⟨hwsm, fun z hz => hwO hz, hwhol, lt_of_le_of_lt hEw hu.2.2.2⟩
  -- the `dλ`-energy of the limit vanishes on every annulus
  have hd1 : ∀ (f : ℂ → V n) z, energyDensity H (fun _ => (1 : ℝ)) f z = dlambdaDensity H f z := by
    intro f z
    simp [energyDensity, dlambdaDensity]
  have hDtop : dlambdaEnergy H U₀ u ≠ ⊤ :=
    ne_top_of_le_ne_top hu.2.2.2.ne (energyDensity_nonneg H hH J hJ U₀ hU₀o u hu).2.2.1
  have hU₀eq : {x : ℂ | x ≠ 0 ∧ ‖x‖ < 1} = U₀ := by
    ext x
    simp only [hU₀, Set.mem_setOf_eq, Set.mem_diff, mem_ball_zero_iff, Set.mem_singleton_iff]
    tauto
  have htail := tendsto_dlambdaEnergy_punctured H u (by rw [hU₀eq]; exact hDtop)
  have hWr : ∀ N : ℕ, dlambdaEnergy H (An N) w = 0 := by
    intro N
    have h := hfatou _ (hAnU N) (hAno N) (hAnP N) (fun _ => 1) contDiff_const
    simp only [hd1] at h
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hρN : Tendsto (fun k => ρ k * ((N : ℝ) + 1)) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mul_pos (hρ k) hN1⟩
      simpa using hρ0.mul_const ((N : ℝ) + 1)
    have hle : ∀ᶠ k in atTop, dlambdaEnergy H (An N) (v k) ≤
        dlambdaEnergy H {x : ℂ | x ≠ 0 ∧ ‖x‖ < ρ k * ((N : ℝ) + 1)} u := by
      filter_upwards [(hρN.mono_right nhdsWithin_le_nhds).eventually (Iio_mem_nhds zero_lt_one)]
        with k hk
      have hk' : ρ k * ((N : ℝ) + 1) < 1 := hk
      set A' : Set ℂ := {y | ρ k * ((N : ℝ) + 1)⁻¹ < ‖y‖ ∧ ‖y‖ < ρ k * ((N : ℝ) + 1)}
        with hA'def
      have hA'0 : ∀ y ∈ A', y ≠ 0 := fun y hy =>
        norm_pos_iff.1 (lt_trans (mul_pos (hρ k) (inv_pos.2 hN1)) hy.1)
      have hA'U₀ : A' ⊆ U₀ := fun y hy =>
        ⟨mem_ball_zero_iff.2 (hy.2.trans hk'), hA'0 y hy⟩
      have hA'm : MeasurableSet A' :=
        ((isOpen_lt continuous_const continuous_norm).inter
          (isOpen_lt continuous_norm continuous_const)).measurableSet
      have heq : {w | ((ρ k : ℝ) : ℂ) * w ∈ A'} = An N := by
        ext z
        simp only [hA'def, hAndef, Set.mem_setOf_eq, hnormρ]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨lt_of_mul_lt_mul_left h1 (hρ k).le, lt_of_mul_lt_mul_left h2 (hρ k).le⟩
        · rintro ⟨h1, h2⟩
          exact ⟨mul_lt_mul_of_pos_left h1 (hρ k), mul_lt_mul_of_pos_left h2 (hρ k)⟩
      rw [← heq, (hvE k A' hA'U₀ hA'm).2]
      exact lintegral_mono_set fun y hy => ⟨hA'0 y hy, hy.2⟩
    have hlim : Tendsto (fun j => dlambdaEnergy H (An N) (v (φ j))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        ((htail.comp hρN).comp hφt) (Eventually.of_forall fun _ => bot_le)
        (hφt.eventually hle)
    change dlambdaEnergy H _ w ≤ liminf (fun j => dlambdaEnergy H _ (v (φ j))) atTop at h
    rw [hlim.liminf_eq] at h
    exact le_antisymm h bot_le
  have hD0 : dlambdaEnergy H U w = 0 := by
    set μw := (volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal (dlambdaDensity H w z))
    have hμw : ∀ s : Set ℂ, MeasurableSet s → dlambdaEnergy H s w = μw s := fun s hs =>
      (withDensity_apply _ hs).symm
    rw [hμw _ hUo.measurableSet, hUeq]
    refine measure_iUnion_null fun N => ?_
    rw [← hμw _ (hAno N).measurableSet]
    exact hWr N
  exact ⟨φ, hφ, w, hwfe, hD0, hconv⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C)
    (ρ : ℕ → ℝ) (hρ : ∀ k, 0 < ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → V n, IsFiniteEnergyCurve H J {z | z ≠ 0} w ∧
      dlambdaEnergy H {z | z ≠ 0} w = 0 ∧
      JHolomorphic.TendstoCInftyLocOn
        (fun j z => Real.exp (-2 * aCoord H (u ((ρ (φ j) : ℝ) : ℂ))) • u (((ρ (φ j) : ℝ) : ℂ) * z))
        w {z | z ≠ 0} :=
  FiniteEnergyPlane.exists_subseq_tendsto_rescaled_punctured_aux H hH J hJ u hu hG ρ hρ hρ0
