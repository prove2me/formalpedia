-- Prove2me | solution 1 for FiniteEnergyPlane.exists_subseq_tendstoCInftyLocOn_of_dlambdaEnergy_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T17:17:52.0582+00:00
-- url     : https://prove2.me/submissions/2aee0db3-2612-4542-88d6-cbca038b0e69

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.Topology.Compactness.Compact
import Theorems.Thm_FiniteEnergyPlane_exists_gradNorm_le_of_dlambdaEnergy_le
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInftyLocOn_of_exhaustion
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_norm_fderiv_le_mul_gradNorm
import Theorems.Thm_FiniteEnergyPlane_isCompact_aCoord_slab
import Theorems.Thm_FiniteEnergyPlane_lintegral_energyDensity_le_liminf
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A compact subset of `ℂ \ {0}` lies in all large members of a monotone open exhaustion. -/
theorem eventually_subset_of_exhaustion (D : ℕ → Set ℂ) (hDo : ∀ k, IsOpen (D k))
    (hDm : Monotone D) (hDu : ⋃ k, D k = {z : ℂ | z ≠ 0}) (K : Set ℂ) (hK : IsCompact K)
    (hK0 : K ⊆ {z : ℂ | z ≠ 0}) : ∀ᶠ k in atTop, K ⊆ D k := by
  obtain ⟨k₀, hk₀⟩ := hK.elim_directed_cover D hDo (by rwa [hDu]) hDm.directed_le
  filter_upwards [eventually_ge_atTop k₀] with k hk
  exact hk₀.trans (hDm hk)

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Limits of curves on a monotone exhaustion of `ℂ \ {0}` with `dλ`-energy below every period. -/
theorem exists_subseq_tendstoCInftyLocOn_of_dlambdaEnergy_le_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (U : ℕ → Set ℂ) (hUo : ∀ k, IsOpen (U k))
    (hUm : Monotone U) (hUu : ⋃ k, U k = {z : ℂ | z ≠ 0}) (v : ℕ → ℂ → V n)
    (hv : ∀ k, IsFiniteEnergyCurve H J (U k) (v k)) (C e : ℝ)
    (hE : ∀ k, energy H (U k) (v k) ≤ ENNReal.ofReal C)
    (hd : ∀ k, dlambdaEnergy H (U k) (v k) ≤ ENNReal.ofReal e)
    (he₁ : ∀ Q : ReebOrbit H, Q.T ≤ C → e < Q.T)
    (ha1 : ∀ k, aCoord H (v k 1) = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → V n, IsFiniteEnergyCurve H J {z | z ≠ 0} w ∧
      energy H {z | z ≠ 0} w ≤ ENNReal.ofReal C ∧
      dlambdaEnergy H {z | z ≠ 0} w ≤ ENNReal.ofReal e ∧
      JHolomorphic.TendstoCInftyLocOn (fun j => v (φ j)) w {z | z ≠ 0} := by
  classical
  obtain ⟨hJt, hprojs, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  set O : Set (V n) := {y | y ≠ 0} with hO
  have hOo : IsOpen O := isOpen_ne
  set Uz : Set ℂ := {z | z ≠ 0} with hUz
  have hUzo : IsOpen Uz := isOpen_ne
  have hsm : ∀ k, ContDiffOn ℝ ∞ (v k) (U k) := fun k => (hv k).1
  have hne : ∀ k, ∀ z ∈ U k, v k z ≠ 0 := fun k => (hv k).2.1
  have hdiff : ∀ k, ∀ z ∈ U k, DifferentiableAt ℝ (v k) z := fun k z hz =>
    ((hsm k).contDiffAt ((hUo k).mem_nhds hz)).differentiableAt (by simp)
  have haCd : ∀ y : V n, y ≠ 0 → DifferentiableAt ℝ (aCoord H) y := fun y hy =>
    (haCs.differentiableOn (by simp) y hy).differentiableAt (hOo.mem_nhds hy)
  -- the closed annuli
  set Cl : ℝ → Set ℂ := fun B => {z | B⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ B} with hCl
  have hClc : ∀ B, IsCompact (Cl B) := fun B =>
    (isCompact_closedBall (0 : ℂ) B).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)) fun z hz => by
      rw [mem_closedBall_zero_iff]; exact hz.2
  have hCl0 : ∀ B, 0 < B → Cl B ⊆ Uz := fun B hB z hz =>
    norm_pos_iff.1 (lt_of_lt_of_le (inv_pos.2 hB) hz.1)
  -- the bounds on the closed annuli
  have hbdB : ∀ B : ℝ, 1 ≤ B → ∃ A M : ℝ, ∀ᶠ k in atTop, Cl B ⊆ U k ∧ ∀ z ∈ Cl B,
      |aCoord H (v k z)| ≤ A ∧ gradNorm H (v k) z ≤ M := by
    intro B hB
    have hB0 : 0 < B := by linarith
    obtain ⟨M, hM⟩ := exists_gradNorm_le_of_dlambdaEnergy_le H hH J hJ U hUo hUm hUu v hv C e
      hE hd he₁ (Cl B) (hClc B) (hCl0 B hB0)
    have hsubev := eventually_subset_of_exhaustion U hUo hUm hUu (Cl B) (hClc B) (hCl0 B hB0)
    set M' := max M 0 with hM'
    have hM'0 : 0 ≤ M' := le_max_right _ _
    refine ⟨B * M' * (Real.log B + π), M', ?_⟩
    filter_upwards [hM, hsubev] with k hkM hkU
    refine ⟨hkU, fun z hz => ⟨?_, (hkM z hz).trans (le_max_left _ _)⟩⟩
    have hz0 : z ≠ 0 := hCl0 B hB0 hz
    have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have hL0 : 0 ≤ Real.log B := Real.log_nonneg hB
    set L := Real.log B with hL
    set S : Set ℂ := {ζ | -L ≤ ζ.re} ∩ {ζ | ζ.re ≤ L} with hS
    have hSc : Convex ℝ S := (convex_halfSpace_re_ge _).inter (convex_halfSpace_re_le _)
    have hexpC : ∀ ζ ∈ S, Complex.exp ζ ∈ Cl B := by
      intro ζ hζ
      show B⁻¹ ≤ ‖Complex.exp ζ‖ ∧ ‖Complex.exp ζ‖ ≤ B
      rw [Complex.norm_exp]
      constructor
      · calc B⁻¹ = Real.exp (-L) := by rw [Real.exp_neg, hL, Real.exp_log hB0]
          _ ≤ Real.exp ζ.re := Real.exp_le_exp.2 hζ.1
      · calc Real.exp ζ.re ≤ Real.exp L := Real.exp_le_exp.2 hζ.2
          _ = B := Real.exp_log hB0
    set f : ℂ → ℝ := fun ζ => aCoord H (v k (Complex.exp ζ)) with hf
    have hfd : ∀ ζ ∈ S, DifferentiableAt ℝ f ζ := fun ζ hζ =>
      ((haCd _ (hne k _ (hkU (hexpC ζ hζ)))).comp _ (hdiff k _ (hkU (hexpC ζ hζ)))).comp ζ
        ((Complex.hasDerivAt_exp ζ).hasFDerivAt.restrictScalars ℝ).differentiableAt
    have hfb : ∀ ζ ∈ S, ‖fderiv ℝ f ζ‖ ≤ B * M' := by
      intro ζ hζ
      have hP := hkU (hexpC ζ hζ)
      have he : HasFDerivAt Complex.exp
          (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (Complex.exp ζ))).restrictScalars ℝ) ζ :=
        (Complex.hasDerivAt_exp ζ).hasFDerivAt.restrictScalars ℝ
      have hg := ((haCd _ (hne k _ hP)).comp (Complex.exp ζ) (hdiff k _ hP)).hasFDerivAt
      have hfe : HasFDerivAt f ((fderiv ℝ (aCoord H ∘ v k) (Complex.exp ζ)).comp
          (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (Complex.exp ζ))).restrictScalars ℝ))
          ζ := hg.comp ζ he
      rw [hfe.fderiv]
      have hL' : ‖((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
          (Complex.exp ζ))).restrictScalars ℝ‖ ≤ ‖Complex.exp ζ‖ :=
        ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
          simp [norm_mul, mul_comm]
      have hA : ‖fderiv ℝ (fun z => aCoord H (v k z)) (Complex.exp ζ)‖ ≤
          gradNorm H (v k) (Complex.exp ζ) :=
        le_add_of_nonneg_right (norm_nonneg _)
      have hgM : gradNorm H (v k) (Complex.exp ζ) ≤ M' :=
        (hkM _ (hexpC ζ hζ)).trans (le_max_left _ _)
      calc _ ≤ ‖fderiv ℝ (aCoord H ∘ v k) (Complex.exp ζ)‖ *
            ‖((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
              (Complex.exp ζ))).restrictScalars ℝ‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M' * B := mul_le_mul (hA.trans hgM) (hL'.trans (hexpC ζ hζ).2) (norm_nonneg _) hM'0
        _ = B * M' := mul_comm _ _
    have h0S : (0 : ℂ) ∈ S := ⟨by show -L ≤ (0 : ℂ).re; simpa using hL0,
      by show (0 : ℂ).re ≤ L; simpa using hL0⟩
    have hlogabs : |Real.log ‖z‖| ≤ L := by
      rw [abs_le]
      constructor
      · have := Real.log_le_log (inv_pos.2 hB0) hz.1
        rw [Real.log_inv] at this
        linarith
      · exact Real.log_le_log hzp hz.2
    have hlS : Complex.log z ∈ S := by
      refine ⟨?_, ?_⟩
      · show -L ≤ (Complex.log z).re
        rw [Complex.log_re]; exact (abs_le.1 hlogabs).1
      · show (Complex.log z).re ≤ L
        rw [Complex.log_re]; exact (abs_le.1 hlogabs).2
    have := hSc.norm_image_sub_le_of_norm_fderiv_le hfd hfb h0S hlS
    simp only [hf, Complex.exp_zero, Complex.exp_log hz0, ha1 k, sub_zero,
      Real.norm_eq_abs] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hB0.le hM'0))
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im]
    linarith [Complex.abs_arg_le_pi z]
  -- uniform bounds on compact subsets of the punctured plane
  have hbd : ∀ K ⊆ Uz, IsCompact K → ∃ K' : Set (V n), IsCompact K' ∧ K' ⊆ O ∧ ∃ M : ℝ,
      ∀ᶠ k in atTop, ∀ z ∈ K, v k z ∈ K' ∧ ‖fderiv ℝ (v k) z‖ ≤ M := by
    intro K hKU hK
    have hgc : ContinuousOn (fun z : ℂ => ‖z‖⁻¹ + ‖z‖) K :=
      (continuous_norm.continuousOn.inv₀ fun z hz => norm_ne_zero_iff.2 (hKU hz)).add
        continuous_norm.continuousOn
    obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn hgc
    set B := max 1 B₀ with hBdef
    have hB1 : 1 ≤ B := le_max_left _ _
    have hBpos : 0 < B := by linarith
    have hKC : K ⊆ Cl B := by
      intro z hz
      have h := hB₀ z hz
      have h0 : 0 ≤ ‖z‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
      have h2 := norm_nonneg z
      have hzp : 0 < ‖z‖ := norm_pos_iff.2 (hKU hz)
      rw [Real.norm_of_nonneg (by positivity)] at h
      have hb : B₀ ≤ B := le_max_right _ _
      refine ⟨?_, by linarith⟩
      rw [inv_le_comm₀ hBpos hzp]
      linarith
    obtain ⟨A, M, hAM⟩ := hbdB B hB1
    obtain ⟨Mf, hMf⟩ := norm_fderiv_le_mul_gradNorm H hH J hJ A
    refine ⟨_, isCompact_aCoord_slab H hH J hJ A, fun y hy => hy.1, max Mf 0 * max M 0, ?_⟩
    filter_upwards [hAM] with k hk z hz
    have hzU := hk.1 (hKC hz)
    obtain ⟨ha, hg⟩ := hk.2 z (hKC hz)
    refine ⟨⟨hne k z hzU, ha⟩, ?_⟩
    have hgn : 0 ≤ gradNorm H (v k) z := add_nonneg (norm_nonneg _) (norm_nonneg _)
    calc ‖fderiv ℝ (v k) z‖ ≤ Mf * gradNorm H (v k) z := hMf _ _ (hdiff k z hzU) (hne k z hzU) ha
      _ ≤ max Mf 0 * gradNorm H (v k) z := mul_le_mul_of_nonneg_right (le_max_left _ _) hgn
      _ ≤ max Mf 0 * max M 0 :=
        mul_le_mul_of_nonneg_left (hg.trans (le_max_left _ _)) (le_max_right _ _)
  obtain ⟨φ, hφ, w, hwsm, hwhol, hwO, hconv⟩ :=
    exists_subseq_tendstoCInftyLocOn_of_exhaustion (Jtilde H J) O hJt U hUo hUm hUu v hsm
      (fun k => (hv k).2.2.1) hbd
  have hφt := hφ.tendsto_atTop
  -- pointwise `C¹` convergence on the punctured plane
  have hpt : ∀ z ∈ Uz, Tendsto (fun j => v (φ j) z) atTop (𝓝 (w z)) ∧
      Tendsto (fun j => fderiv ℝ (v (φ j)) z) atTop (𝓝 (fderiv ℝ w z)) := by
    intro z hzU
    have hz : z ∈ ({z} : Set ℂ) := rfl
    have hKU : ({z} : Set ℂ) ⊆ Uz := Set.singleton_subset_iff.2 hzU
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
  have hfatou : ∀ W ⊆ Uz, IsOpen W → (∀ᶠ k in atTop, W ⊆ U k) → ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ →
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
  have hAnU : ∀ N, An N ⊆ Uz := fun N z hz =>
    norm_pos_iff.1 (lt_trans (by positivity) hz.1)
  have hAnP : ∀ N : ℕ, ∀ᶠ k in atTop, An N ⊆ U k := fun N =>
    (eventually_subset_of_exhaustion U hUo hUm hUu (Cl ((N : ℝ) + 1)) (hClc _)
      (hCl0 _ (by positivity))).mono fun k hk z hz => hk ⟨hz.1.le, hz.2.le⟩
  have hAnmono : Monotone An := by
    intro a b hab z hz
    have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hab 1
    refine ⟨lt_of_le_of_lt ?_ hz.1, lt_of_lt_of_le hz.2 hab'⟩
    exact inv_anti₀ (by positivity) hab'
  have hUeq : Uz = ⋃ N : ℕ, An N := by
    ext z
    simp only [hUz, Set.mem_setOf_eq, Set.mem_iUnion]
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
  -- the bound on the limit
  have hlim : ∀ (ψ : ℝ → ℝ) (B : ℝ≥0∞), ContDiff ℝ 1 ψ →
      (∀ k, ∫⁻ z in U k, ENNReal.ofReal (energyDensity H ψ (v k) z) ≤ B) →
      ∫⁻ z in Uz, ENNReal.ofReal (energyDensity H ψ w z) ≤ B := by
    intro ψ B hψ hB
    set μψ := (volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal (energyDensity H ψ w z))
      with hμψdef
    have hμψ : ∀ s : Set ℂ, MeasurableSet s →
        ∫⁻ z in s, ENNReal.ofReal (energyDensity H ψ w z) = μψ s := fun s hs =>
      (withDensity_apply _ hs).symm
    have hN : ∀ N, (μψ ∘ An) N ≤ B := by
      intro N
      rw [Function.comp_apply, ← hμψ _ (hAno N).measurableSet]
      refine (hfatou (An N) (hAnU N) (hAno N) (hAnP N) ψ hψ).trans
        (liminf_le_of_frequently_le ?_)
      refine ((hφt.eventually (hAnP N)).mono fun j hj => ?_).frequently
      exact (lintegral_mono_set hj).trans (hB _)
    have h := tendsto_measure_iUnion_atTop (μ := μψ) hAnmono
    rw [← hUeq, ← hμψ _ hUzo.measurableSet] at h
    exact le_of_tendsto' h hN
  have hEw : energy H Uz w ≤ ENNReal.ofReal C := by
    refine iSup₂_le fun ψ hψ => hlim ψ _ (hψ.1.of_le (by simp)) fun k => ?_
    exact (le_iSup₂ (f := fun (ψ : ℝ → ℝ) (_ : Admissible ψ) =>
      ∫⁻ z in U k, ENNReal.ofReal (energyDensity H ψ (v k) z)) ψ hψ).trans (hE k)
  have hd1 : ∀ (f : ℂ → V n) z, energyDensity H (fun _ => (1 : ℝ)) f z = dlambdaDensity H f z := by
    intro f z
    simp [energyDensity, dlambdaDensity]
  have hDw : dlambdaEnergy H Uz w ≤ ENNReal.ofReal e := by
    have := hlim (fun _ => 1) (ENNReal.ofReal e) contDiff_const fun k => by
      simp only [hd1]; exact hd k
    simp only [hd1] at this
    exact this
  exact ⟨φ, hφ, w, ⟨hwsm, fun z hz => hwO hz, hwhol, lt_of_le_of_lt hEw ENNReal.ofReal_lt_top⟩,
    hEw, hDw, hconv⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (U : ℕ → Set ℂ) (hUo : ∀ k, IsOpen (U k))
    (hUm : Monotone U) (hUu : ⋃ k, U k = {z : ℂ | z ≠ 0}) (v : ℕ → ℂ → V n)
    (hv : ∀ k, IsFiniteEnergyCurve H J (U k) (v k)) (C e : ℝ)
    (hE : ∀ k, energy H (U k) (v k) ≤ ENNReal.ofReal C)
    (hd : ∀ k, dlambdaEnergy H (U k) (v k) ≤ ENNReal.ofReal e)
    (he₁ : ∀ Q : ReebOrbit H, Q.T ≤ C → e < Q.T)
    (ha1 : ∀ k, aCoord H (v k 1) = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → V n, IsFiniteEnergyCurve H J {z | z ≠ 0} w ∧
      energy H {z | z ≠ 0} w ≤ ENNReal.ofReal C ∧
      dlambdaEnergy H {z | z ≠ 0} w ≤ ENNReal.ofReal e ∧
      JHolomorphic.TendstoCInftyLocOn (fun j => v (φ j)) w {z | z ≠ 0} :=
  exists_subseq_tendstoCInftyLocOn_of_dlambdaEnergy_le_aux H hH J hJ U hUo hUm hUu v hv C e hE hd he₁ ha1
