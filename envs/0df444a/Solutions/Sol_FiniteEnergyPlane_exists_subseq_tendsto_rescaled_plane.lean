-- Prove2me | solution 1 for FiniteEnergyPlane.exists_subseq_tendsto_rescaled_plane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-26T16:07:59.528143+00:00
-- url     : https://prove2.me/submissions/a2924795-f8a8-4c75-b948-cc53eb15b419

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInftyLocOn_of_isOpen
import Theorems.Thm_FiniteEnergyPlane_rescale_isFiniteEnergyCurve
import Theorems.Thm_FiniteEnergyPlane_lintegral_energyDensity_le_liminf
import Theorems.Thm_FiniteEnergyPlane_isCompact_aCoord_slab
import Theorems.Thm_FiniteEnergyPlane_norm_fderiv_le_mul_gradNorm
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Limits of the normalized rescalings of a finite-energy plane on the punctured plane. -/
theorem exists_subseq_tendsto_rescaled_plane_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (hG : ∃ C : ℝ, ∀ z : ℂ, ‖z‖ * gradNorm H u z ≤ C) (R : ℕ → ℝ) (hR0 : ∀ k, 0 < R k)
    (hR : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → V n, IsFiniteEnergyCurve H J {z | z ≠ 0} w ∧
      dlambdaEnergy H {z | z ≠ 0} w = 0 ∧
      JHolomorphic.TendstoCInftyLocOn
        (fun j z => Real.exp (-2 * aCoord H (u ((R (φ j) : ℝ) : ℂ))) • u (((R (φ j) : ℝ) : ℂ) * z))
        w {z | z ≠ 0} := by
  classical
  obtain ⟨hJt, -, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨C, hC⟩ := hG
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set O : Set (V n) := {y | y ≠ 0} with hO
  have hOo : IsOpen O := isOpen_ne
  set U : Set ℂ := {z | z ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne
  set c : ℕ → ℝ := fun k => Real.exp (-2 * aCoord H (u ((R k : ℝ) : ℂ))) with hcdef
  have hcpos : ∀ k, 0 < c k := fun k => Real.exp_pos _
  set v : ℕ → ℂ → V n := fun k z => c k • u (((R k : ℝ) : ℂ) * z) with hvdef
  -- the rescaling identities
  have hfun : ∀ k, (fun w : ℂ => c k • u (0 + R k • w)) = v k := fun k => by
    funext w
    simp [hvdef, Complex.real_smul]
  have hresc := fun k => rescale_isFiniteEnergyCurve H hH J hJ Set.univ isOpen_univ u hu 0 (R k)
    (hR0 k) (c k) (hcpos k)
  have hpre : ∀ k (A : Set ℂ), {w : ℂ | 0 + R k • w ∈ A} = {w | ((R k : ℝ) : ℂ) * w ∈ A} :=
    fun k A => by ext w; simp [Complex.real_smul]
  have hvk : ∀ k, IsFiniteEnergyCurve H J Set.univ (v k) := fun k => by
    have h := (hresc k).1
    rw [hfun k] at h
    simpa using h
  have hvA : ∀ k z, aCoord H (v k z) = aCoord H (u (((R k : ℝ) : ℂ) * z)) + Real.log (c k) / 2 :=
    fun k z => by
      have h := (hresc k).2.1 z (Set.mem_univ _)
      simpa [hvdef, Complex.real_smul] using h
  have hvG : ∀ k z, gradNorm H (v k) z = R k * gradNorm H u (((R k : ℝ) : ℂ) * z) :=
    fun k z => by
      have h := (hresc k).2.2.1 z (Set.mem_univ _)
      rw [hfun k] at h
      simpa [Complex.real_smul] using h
  have hvE : ∀ k (A : Set ℂ), MeasurableSet A →
      energy H {w | ((R k : ℝ) : ℂ) * w ∈ A} (v k) = energy H A u ∧
        dlambdaEnergy H {w | ((R k : ℝ) : ℂ) * w ∈ A} (v k) = dlambdaEnergy H A u :=
    fun k A hA => by
      have h := (hresc k).2.2.2 A (Set.subset_univ _) hA
      rw [hfun k, hpre k A] at h
      exact h
  have hv1 : ∀ k, aCoord H (v k 1) = 0 := fun k => by
    rw [hvA, mul_one, hcdef]
    simp only [Real.log_exp]
    ring
  have hvC : ∀ k z, ‖z‖ * gradNorm H (v k) z ≤ C := fun k z => by
    have h := hC (((R k : ℝ) : ℂ) * z)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hR0 k).le] at h
    rw [hvG]
    calc ‖z‖ * (R k * gradNorm H u (((R k : ℝ) : ℂ) * z))
        = R k * ‖z‖ * gradNorm H u (((R k : ℝ) : ℂ) * z) := by ring
      _ ≤ C := h
  have hsm : ∀ k, ContDiff ℝ ∞ (v k) := fun k => contDiffOn_univ.1 (hvk k).1
  have hne : ∀ k z, v k z ≠ 0 := fun k z => (hvk k).2.1 z (Set.mem_univ _)
  have hdiff : ∀ k z, DifferentiableAt ℝ (v k) z := fun k z => (hsm k).differentiable (by simp) z
  have haCd : ∀ y : V n, y ≠ 0 → DifferentiableAt ℝ (aCoord H) y := fun y hy =>
    (haCs.differentiableOn (by simp) y hy).differentiableAt (hOo.mem_nhds hy)
  -- `a ∘ v_k` in logarithmic coordinates
  have hlog : ∀ k z, z ≠ 0 → |aCoord H (v k z)| ≤ C' * ‖Complex.log z‖ := by
    intro k z hz
    set f : ℂ → ℝ := fun ζ => aCoord H (v k (Complex.exp ζ)) with hf
    have hfd : ∀ ζ, DifferentiableAt ℝ f ζ := fun ζ =>
      ((haCd _ (hne k _)).comp _ (hdiff k _)).comp ζ
        ((Complex.hasDerivAt_exp ζ).hasFDerivAt.restrictScalars ℝ).differentiableAt
    have hfb : ∀ ζ ∈ (Set.univ : Set ℂ), ‖fderiv ℝ f ζ‖ ≤ C' := by
      intro ζ _
      have he : HasFDerivAt Complex.exp
          (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (Complex.exp ζ))).restrictScalars ℝ) ζ :=
        (Complex.hasDerivAt_exp ζ).hasFDerivAt.restrictScalars ℝ
      have hg := ((haCd _ (hne k (Complex.exp ζ))).comp (Complex.exp ζ)
        (hdiff k (Complex.exp ζ))).hasFDerivAt
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
        _ ≤ C' := (hvC k _).trans (le_max_left _ _)
    have := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun ζ _ => hfd ζ) hfb
      (Set.mem_univ 0) (Set.mem_univ (Complex.log z))
    simp only [hf, Complex.exp_zero, Complex.exp_log hz, hv1, sub_zero, Real.norm_eq_abs] at this
    exact this
  have hlogn : ∀ z : ℂ, ‖Complex.log z‖ ≤ |Real.log ‖z‖| + π := fun z => by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im]
    linarith [Complex.abs_arg_le_pi z]
  -- uniform bounds on compact subsets of the punctured plane
  have hbd : ∀ K ⊆ U, IsCompact K → ∃ K' : Set (V n), IsCompact K' ∧ K' ⊆ O ∧ ∃ M : ℝ,
      ∀ k, ∀ z ∈ K, v k z ∈ K' ∧ ‖fderiv ℝ (v k) z‖ ≤ M := by
    intro K hKU hK
    have hgc : ContinuousOn (fun z : ℂ => |Real.log ‖z‖| + ‖z‖⁻¹) K := by
      refine ((continuous_norm.continuousOn.log fun z hz => norm_ne_zero_iff.2 (hKU hz)).abs).add
        (continuous_norm.continuousOn.inv₀ fun z hz => norm_ne_zero_iff.2 (hKU hz))
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hgc
    have hB' : ∀ z ∈ K, |Real.log ‖z‖| ≤ B ∧ ‖z‖⁻¹ ≤ B := by
      intro z hz
      have h := hB z hz
      have h0 : 0 ≤ ‖z‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
      rw [Real.norm_of_nonneg (add_nonneg (abs_nonneg _) h0)] at h
      exact ⟨by linarith [abs_nonneg (Real.log ‖z‖)], by linarith [abs_nonneg (Real.log ‖z‖)]⟩
    set A : ℝ := C' * (B + π) with hAdef
    obtain ⟨M, hM⟩ := norm_fderiv_le_mul_gradNorm H hH J hJ A
    refine ⟨_, isCompact_aCoord_slab H hH J hJ A, fun y hy => hy.1, max M 0 * (C' * B),
      fun k z hz => ?_⟩
    have hz0 : z ≠ 0 := hKU hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have ha : |aCoord H (v k z)| ≤ A :=
      (hlog k z hz0).trans (mul_le_mul_of_nonneg_left
        ((hlogn z).trans (by linarith [(hB' z hz).1])) hC'0)
    refine ⟨⟨hne k z, ha⟩, ?_⟩
    have hgn : 0 ≤ gradNorm H (v k) z := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hg : gradNorm H (v k) z ≤ C' * B := by
      have h1 : ‖z‖ * gradNorm H (v k) z ≤ C' := (hvC k z).trans (le_max_left _ _)
      have h2 : gradNorm H (v k) z ≤ C' * ‖z‖⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hzpos, mul_comm]
        exact h1
      exact h2.trans (mul_le_mul_of_nonneg_left (hB' z hz).2 hC'0)
    calc ‖fderiv ℝ (v k) z‖ ≤ M * gradNorm H (v k) z := hM _ _ (hdiff k z) (hne k z) ha
      _ ≤ max M 0 * gradNorm H (v k) z := mul_le_mul_of_nonneg_right (le_max_left _ _) hgn
      _ ≤ max M 0 * (C' * B) := mul_le_mul_of_nonneg_left hg (le_max_right _ _)
  obtain ⟨φ, hφ, w, hwsm, hwhol, hwO, hconv⟩ :=
    exists_subseq_tendstoCInftyLocOn_of_isOpen (Jtilde H J) O hJt U hUo v
      (fun k => (hsm k).contDiffOn) (fun k z _ => (hvk k).2.2.1 z (Set.mem_univ _)) hbd
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
  -- Fatou on open subsets of the punctured plane
  have hfatou : ∀ W ⊆ U, IsOpen W → ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ →
      ∫⁻ z in W, ENNReal.ofReal (energyDensity H ψ w z) ≤
        liminf (fun j => ∫⁻ z in W, ENNReal.ofReal (energyDensity H ψ (v (φ j)) z)) atTop :=
    fun W hWU hW ψ hψ =>
      lintegral_energyDensity_le_liminf H hH J hJ W hW (fun j => v (φ j)) w
        (Eventually.of_forall fun j => ⟨(hsm _).contDiffOn.of_le (by simp), fun z _ => hne _ z⟩)
        ((hwsm.of_le (by simp)).mono hWU) (fun z hz => hwO (hWU hz)) (fun z hz => hpt z (hWU hz))
        ψ hψ
  -- finite energy
  have hEu : ∀ k, energy H Set.univ (v k) = energy H Set.univ u := fun k => by
    have h := (hvE k Set.univ MeasurableSet.univ).1
    simpa using h
  have hEw : energy H U w ≤ energy H Set.univ u := by
    refine iSup₂_le fun ψ hψ => ?_
    refine (hfatou U le_rfl hUo ψ (hψ.1.of_le (by simp))).trans (liminf_le_of_frequently_le ?_)
    refine Eventually.frequently (Eventually.of_forall fun j => ?_)
    calc ∫⁻ z in U, ENNReal.ofReal (energyDensity H ψ (v (φ j)) z)
        ≤ ∫⁻ z in Set.univ, ENNReal.ofReal (energyDensity H ψ (v (φ j)) z) :=
          lintegral_mono_set (Set.subset_univ _)
      _ ≤ energy H Set.univ (v (φ j)) :=
          le_iSup₂ (f := fun (ψ : ℝ → ℝ) (_ : Admissible ψ) =>
            ∫⁻ z in Set.univ, ENNReal.ofReal (energyDensity H ψ (v (φ j)) z)) ψ hψ
      _ = energy H Set.univ u := hEu _
  have hwfe : IsFiniteEnergyCurve H J U w :=
    ⟨hwsm, fun z hz => hwO hz, hwhol, lt_of_le_of_lt hEw hu.2.2.2⟩
  -- the `dλ`-energy of `u` outside large discs tends to `0`
  have hd1 : ∀ (f : ℂ → V n) z, energyDensity H (fun _ => (1 : ℝ)) f z = dlambdaDensity H f z := by
    intro f z
    simp [energyDensity, dlambdaDensity]
  have hDtop : dlambdaEnergy H Set.univ u ≠ ⊤ :=
    ne_top_of_le_ne_top hu.2.2.2.ne (energyDensity_nonneg H hH J hJ Set.univ isOpen_univ u hu).2.2.1
  set μ := (volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal (dlambdaDensity H u z))
    with hμdef
  have hμ : ∀ s : Set ℂ, MeasurableSet s → dlambdaEnergy H s u = μ s := fun s hs =>
    (withDensity_apply _ hs).symm
  have hmeas : ∀ s : ℝ, MeasurableSet {y : ℂ | s < ‖y‖} := fun s =>
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have htail : Tendsto (fun s : ℝ => dlambdaEnergy H {y : ℂ | s < ‖y‖} u) atTop (𝓝 0) := by
    have hfin : μ {y : ℂ | (0 : ℝ) < ‖y‖} ≠ ⊤ := by
      rw [← hμ _ (hmeas 0)]
      exact ne_top_of_le_ne_top hDtop (lintegral_mono_set (Set.subset_univ _))
    have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun s : ℝ => {y : ℂ | s < ‖y‖})
      (fun s => (hmeas s).nullMeasurableSet)
      (fun a b hab y hy => lt_of_le_of_lt hab hy) ⟨0, hfin⟩
    have he : (⋂ s : ℝ, {y : ℂ | s < ‖y‖}) = ∅ := by
      ext y
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
        not_lt]
      exact ⟨‖y‖, le_rfl⟩
    rw [he, measure_empty] at h
    exact h.congr fun s => (hμ _ (hmeas s)).symm
  have hWr : ∀ r : ℝ, 0 < r → dlambdaEnergy H {z : ℂ | r < ‖z‖} w = 0 := by
    intro r hr
    have hWU : {z : ℂ | r < ‖z‖} ⊆ U := fun z hz =>
      norm_pos_iff.1 (lt_trans hr hz)
    have h := hfatou _ hWU (isOpen_lt continuous_const continuous_norm) (fun _ => 1) contDiff_const
    simp only [hd1] at h
    have hk : ∀ k, dlambdaEnergy H {z : ℂ | r < ‖z‖} (v k) =
        dlambdaEnergy H {y : ℂ | R k * r < ‖y‖} u := fun k => by
      rw [← (hvE k _ (hmeas _)).2]
      congr 1
      ext z
      simp only [Set.mem_setOf_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hR0 k).le]
      exact ⟨fun h => mul_lt_mul_of_pos_left h (hR0 k), fun h => lt_of_mul_lt_mul_left h (hR0 k).le⟩
    have hlim : Tendsto (fun j => dlambdaEnergy H {z : ℂ | r < ‖z‖} (v (φ j))) atTop (𝓝 0) := by
      simp only [hk]
      exact htail.comp ((hR.comp hφt).atTop_mul_const hr)
    change dlambdaEnergy H _ w ≤ liminf (fun j => dlambdaEnergy H _ (v (φ j))) atTop at h
    rw [hlim.liminf_eq] at h
    exact le_antisymm h bot_le
  have hD0 : dlambdaEnergy H U w = 0 := by
    set μw := (volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal (dlambdaDensity H w z))
    have hμw : ∀ s : Set ℂ, MeasurableSet s → dlambdaEnergy H s w = μw s := fun s hs =>
      (withDensity_apply _ hs).symm
    have hUeq : U = ⋃ N : ℕ, {z : ℂ | 1 / ((N : ℝ) + 1) < ‖z‖} := by
      ext z
      simp only [hU, Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro hz
        exact exists_nat_one_div_lt (norm_pos_iff.2 hz)
      · rintro ⟨N, hN⟩
        exact norm_pos_iff.1 (lt_trans (by positivity) hN)
    rw [hμw _ hUo.measurableSet, hUeq]
    refine measure_iUnion_null fun N => ?_
    rw [← hμw _ (hmeas _)]
    exact hWr _ (by positivity)
  exact ⟨φ, hφ, w, hwfe, hD0, hconv⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (hG : ∃ C : ℝ, ∀ z : ℂ, ‖z‖ * gradNorm H u z ≤ C) (R : ℕ → ℝ) (hR0 : ∀ k, 0 < R k)
    (hR : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → V n, IsFiniteEnergyCurve H J {z | z ≠ 0} w ∧
      dlambdaEnergy H {z | z ≠ 0} w = 0 ∧
      JHolomorphic.TendstoCInftyLocOn
        (fun j z => Real.exp (-2 * aCoord H (u ((R (φ j) : ℝ) : ℂ))) • u (((R (φ j) : ℝ) : ℂ) * z))
        w {z | z ≠ 0} :=
  exists_subseq_tendsto_rescaled_plane_aux H hH J hJ u hu hG R hR0 hR
