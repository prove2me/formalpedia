-- Prove2me | solution 1 for FunctionalInequalities.Probability.Diffusion.exists_isDiffusion_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:43:10.505266+00:00
-- url     : https://prove2.me/submissions/c418994e-4439-4e65-9e16-d212efd88222

import Definitions.Def_KLSModular_LevyStochCalc_Poisson_Compensated
import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardLocality
import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardGlobal
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcessVersion
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Existence
import Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_isVectorItoVersion_of_unbounded_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_vectorItoProcess_ae_eq_zero_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_exists_globalSolution_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_itoIntegral_congr_ae_readable
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_diffusionCoeffs_lipschitz_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/Compensated.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
section
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
section Integral
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ
    : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))
  (h_progMeas : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
include hℱ in
/-- The Itô–Lévy isometry of the stochastic integral at every time `T > 0`. -/
theorem LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [← process_lintegral_sq' N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hT.le]
  refine lintegral_congr_ae ?_
  filter_upwards [stochasticIntegral_ae_eq_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global T]
    with ω hω
  rw [hω]
end Integral
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardLocality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
section
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
/-- The compensated-Poisson integral is measurable at each time. -/
theorem LevyStochCalc.Ito.Picard.measurable_compensatedIntegral_slice {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (t : ℝ) :
    Measurable fun ω =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ hm hp hs t ω :=
  ((LevyStochCalc.Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱN φ hm hp hs
    t).stronglyMeasurable).measurable.mono (ℱ.rightCont.le t) le_rfl
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardGlobal.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
section
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
section Glue
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
/-- A solution on a window starts at the initial datum. -/
theorem LevyStochCalc.Ito.Picard.ae_eq_initial_of_solvesOn (x₀ : Fin n → ℝ) {X : ℝ → Ω → (Fin n → ℝ)} {T : ℝ}
    (hT : 0 ≤ T) (h : SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) :
    ∀ᵐ ω ∂P, X 0 ω = x₀ := by
  filter_upwards [h.eqn 0 ⟨le_rfl, hT⟩,
    ae_picardStep_zero W N ℱ hℱW hℱN coeffs X x₀ h.h_σ_meas h.h_σ_progMeas h.h_σ_sq
      h.h_γ_meas h.h_γ_progMeas h.h_γ_sq] with ω h1 h2
  funext i
  rw [h1 i, h2 i]
end Glue
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcessVersion.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section VectorVersion
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
variable {W ℱ hcoord H hHm hHp hHs} {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
  {X : ℝ → Ω → Fin n → ℝ}
/-- A version's time slices are measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (t : ℝ) :
    Measurable (X t) := ((h.adapted t).mono (ℱ.le t)).measurable
/-- A version's paths are jointly measurable in the sample point and the time. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable_uncurry
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) :
    Measurable (Function.uncurry fun ω s => X s ω) := by
  have hjoint : Measurable (Function.uncurry X) :=
    measurable_uncurry_of_continuous_of_measurable h.continuous_path h.measurable
  exact hjoint.comp measurable_swap
/-- A continuous function of a version is progressively measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.progressivelyMeasurable_comp
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) {φ : (Fin n → ℝ) → ℝ}
    (hφ : Continuous φ) : Probability.ProgressivelyMeasurable ℱ fun ω s => φ (X s ω) := by
  refine Probability.ProgressivelyMeasurable.of_isStronglyProgressive ?_
  refine MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous
    (fun t => hφ.comp_stronglyMeasurable (h.adapted t)) fun ω => ?_
  exact hφ.comp (h.continuous_path ω)
/-- A measurable function of a version is jointly measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable_uncurry_comp
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) {φ : (Fin n → ℝ) → ℝ}
    (hφ : Measurable φ) : Measurable (Function.uncurry fun ω s => φ (X s ω)) :=
  hφ.comp h.measurable_uncurry
end VectorVersion
end
end

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
  LevyStochCalc.Brownian.Ito
universe u
private theorem FunctionalInequalities.Probability.Diffusion.zeroPoisson_filtration {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    Poisson.IsPoissonFiltration (FunctionalInequalities.Probability.Diffusion.zeroPoisson P) ℱ := by
  constructor
  · intro t B _ _
    exact measurable_const
  · intro s _
    change Indep (ℱ s)
      (⨆ D ∈ {D : Set (ℝ × Unit) |
          D ⊆ Set.Ioi s ×ˢ Set.univ ∧ MeasurableSet D},
        MeasurableSpace.comap (fun _ : Ω => (0 : ℝ≥0∞)) inferInstance) P
    simp only [MeasurableSpace.comap_const, iSup_bot]
    exact indep_bot_right _
private theorem FunctionalInequalities.Probability.Diffusion.diffusionCoeffs_regular {N d : ℕ}
    {b : (Fin N → ℝ) → Fin N → ℝ}
    {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ}
    (hb : Measurable b) (hσ : ∀ k, Measurable fun x => σ x k) :
    (FunctionalInequalities.Probability.Diffusion.diffusionCoeffs b σ).IsRegular (0 : Measure Unit) := by
  refine ⟨hb.comp measurable_snd, ?_, measurable_const, ?_, ?_, ?_⟩
  · exact measurable_pi_lambda _ fun i =>
      measurable_pi_lambda _ fun k => ((hσ k).eval (a := i)).comp measurable_snd
  · intro T _
    change (∫⁻ _s in Set.Icc (0 : ℝ) T, (‖b 0‖₊ : ℝ≥0∞) ^ 2 ∂volume) < ⊤
    rw [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
      isCompact_Icc.measure_lt_top
  · intro T _
    change (∫⁻ _s in Set.Icc (0 : ℝ) T,
      ∑ i, ∑ k, (‖σ 0 k i‖₊ : ℝ≥0∞) ^ 2 ∂volume) < ⊤
    rw [lintegral_const, Measure.restrict_apply_univ]
    refine ENNReal.mul_lt_top ?_ isCompact_Icc.measure_lt_top
    exact ENNReal.sum_lt_top.mpr fun _ _ =>
      ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.pow_lt_top ENNReal.coe_lt_top
  · intro T _
    change (∫⁻ _s in Set.Icc (0 : ℝ) T,
      ∫⁻ _e, (‖(0 : Fin N → ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂(0 : Measure Unit) ∂volume) < ⊤
    simp
section Diffusion
variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure P] {N d : ℕ}
open LevyStochCalc.Ito.Picard in
/-- Globally Lipschitz bounded autonomous coefficients with zero jumps: an everywhere continuous adapted
solution with Itô representation along itself exists on any Brownian setup with a usual filtration. -/
theorem solution (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {b : (Fin N → ℝ) → Fin N → ℝ} {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {K : ℝ≥0}
    (hb : LipschitzWith K b) (hσ : ∀ k, LipschitzWith K fun x => σ x k)
    {B : ℝ} (hbB : ∀ x, ‖b x‖ ≤ B) (hσB : ∀ x k, ‖σ x k‖ ≤ B) (x₀ : Fin N → ℝ) :
    ∃ Y : ℝ → Ω → Fin N → ℝ, FunctionalInequalities.Probability.Diffusion.IsDiffusion W ℱ hW b σ x₀ Y := by
  classical
  let C := FunctionalInequalities.Probability.Diffusion.diffusionCoeffs b σ
  let Z := FunctionalInequalities.Probability.Diffusion.zeroPoisson P
  have hZ : LevyStochCalc.Poisson.IsPoissonFiltration Z ℱ := FunctionalInequalities.Probability.Diffusion.zeroPoisson_filtration P ℱ
  have hReg : C.IsRegular (0 : Measure Unit) :=
    FunctionalInequalities.Probability.Diffusion.diffusionCoeffs_regular hb.continuous.measurable
      (fun k => (hσ k).continuous.measurable)
  obtain ⟨L, hLip⟩ := FunctionalInequalities.Probability.Diffusion.diffusionCoeffs_lipschitz_readable hb hσ
  obtain ⟨X, hXm, hXp, _hX0, _hXcad, _hXS, hSol⟩ :=
    LevyStochCalc.Ito.Picard.exists_globalSolution_readable W Z ℱ hW hZ C hℱ0 hnull hReg hLip x₀
  let S := hSol 0
  let H : Fin N → Fin d → Ω → ℝ → ℝ := fun i k ω s => σ (X s ω) k i
  let a : Fin N → Ω → ℝ → ℝ := fun i ω s => b (X s ω) i
  have hm : ∀ i k, Measurable (Function.uncurry (H i k)) := S.h_σ_meas
  have hp : ∀ i k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H i k) := S.h_σ_progMeas
  have hq : ∀ i k (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H i k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := S.h_σ_sq
  have ham : ∀ i, Measurable (Function.uncurry (a i)) :=
    LevyStochCalc.Ito.Picard.measurable_mu_comp_state C hReg hXm
  have hap : ∀ i, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (a i) := by
    intro i
    exact LevyStochCalc.Ito.Picard.progressivelyMeasurable_comp_state (X := X)
      (f := fun _ x => b x i) hXp
      ((hb.continuous.measurable.eval (a := i)).comp measurable_snd)
  have haq : ∀ i (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖a i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro i
    exact LevyStochCalc.Brownian.Ito.energy_lt_top_of_bounded
      (fun ω s => (norm_le_pi_norm (b (X s ω)) i).trans (hbB (X s ω)))
  obtain ⟨Y, hY⟩ := LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_of_unbounded_readable W ℱ hW H hm hp hq
    hℱ0 hnull (X₀ := fun _ => x₀) (fun _ => measurable_const) a ham hap haq
  have hXrep : ∀ t : ℝ, 0 ≤ t →
      X t =ᵐ[P] LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hW H hm hp hq (fun _ => x₀) a t := by
    intro t ht
    rcases eq_or_lt_of_le ht with he | ht
    · rw [← he]
      filter_upwards
        [LevyStochCalc.Ito.Picard.ae_eq_initial_of_solvesOn W Z ℱ hW hZ C x₀ le_rfl (hSol 0),
          LevyStochCalc.Brownian.Ito.vectorItoProcess_ae_eq_zero_readable W ℱ hW hm hp hq (fun _ => x₀) a]
        with ω hXω hVω
      exact hXω.trans hVω.symm
    · have hj : ∀ᵐ ω ∂P, ∀ i : Fin N,
          LevyStochCalc.Ito.Picard.picardStep_jump Z ℱ hZ C X S.h_γ_meas S.h_γ_progMeas S.h_γ_sq t ω i = 0 := by
        apply ae_all_iff.mpr
        intro i
        have hiso := LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral Z ℱ hZ
          (fun ω s e => C.γ s (X s ω) e i)
          (S.h_γ_meas i) (S.h_γ_progMeas i) (S.h_γ_sq i) t ht
        have hjm := LevyStochCalc.Ito.Picard.measurable_compensatedIntegral_slice Z ℱ hZ
          (fun ω s e => C.γ s (X s ω) e i)
          (S.h_γ_meas i) (S.h_γ_progMeas i) (S.h_γ_sq i) t
        have hz : (∫⁻ ω,
            (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral Z ℱ hZ
              (fun ω s e => C.γ s (X s ω) e i)
              (S.h_γ_meas i) (S.h_γ_progMeas i) (S.h_γ_sq i) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) = 0 := by
          simpa using hiso
        filter_upwards [(lintegral_eq_zero_iff
          ((hjm.nnnorm.coe_nnreal_ennreal).pow_const 2)).mp hz] with ω hω
        change LevyStochCalc.Poisson.Compensated.stochasticIntegral Z ℱ hZ
          (fun ω s e => C.γ s (X s ω) e i)
          (S.h_γ_meas i) (S.h_γ_progMeas i) (S.h_γ_sq i) t ω = 0
        simpa using hω
      filter_upwards [(hSol t).eqn t ⟨ht.le, le_rfl⟩, hj] with ω heq hz
      funext i
      have hi := heq i
      change X t ω i =
        LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hW H hm hp hq (fun _ => x₀) a t ω i +
          LevyStochCalc.Ito.Picard.picardStep_jump Z ℱ hZ C X S.h_γ_meas S.h_γ_progMeas S.h_γ_sq t ω i at hi
      simpa only [hz i, add_zero] using hi
  have hXY : ∀ t : ℝ, 0 ≤ t → X t =ᵐ[P] Y t :=
    fun t ht => (hXrep t ht).trans (hY.ae_eq t ht).symm
  have hXY_window : ∀ t : ℝ,
      ∀ᵐ ω ∂P, ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) t), X s ω = Y s ω := by
    intro t
    have he : MeasurableSet {p : Ω × ℝ | X p.2 p.1 = Y p.2 p.1} :=
      measurableSet_eq_fun (hXm.comp measurable_swap) hY.measurable_uncurry
    apply (Measure.ae_ae_comm (p := fun ω s => X s ω = Y s ω) he).mpr
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with s hs
    exact hXY s hs.1
  let G : Fin N → Fin d → Ω → ℝ → ℝ := fun i k ω s => σ (Y s ω) k i
  let c : Fin N → Ω → ℝ → ℝ := fun i ω s => b (Y s ω) i
  have gm : ∀ i k, Measurable (Function.uncurry (G i k)) := by
    intro i k
    exact hY.measurable_uncurry_comp ((hσ k).continuous.measurable.eval (a := i))
  have gp : ∀ i k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (G i k) := by
    intro i k
    exact hY.progressivelyMeasurable_comp ((continuous_apply i).comp (hσ k).continuous)
  have gq : ∀ i k (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖G i k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro i k
    exact LevyStochCalc.Brownian.Ito.energy_lt_top_of_bounded
      (fun ω s => (norm_le_pi_norm (σ (Y s ω) k) i).trans (hσB (Y s ω) k))
  refine ⟨Y, gm, gp, gq, hY.continuous_path, hY.adapted, ?_⟩
  intro t ht
  refine (hY.ae_eq t ht).trans ?_
  rcases eq_or_lt_of_le ht with he | ht
  · subst t
    exact (LevyStochCalc.Brownian.Ito.vectorItoProcess_ae_eq_zero_readable W ℱ hW hm hp hq (fun _ => x₀) a).trans
      (LevyStochCalc.Brownian.Ito.vectorItoProcess_ae_eq_zero_readable W ℱ hW gm gp gq (fun _ => x₀) c).symm
  · have hI : ∀ᵐ ω ∂P, ∀ (i : Fin N) (k : Fin d),
        LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hW H hm hp hq i k t ω =
          LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hW G gm gp gq i k t ω := by
      apply ae_all_iff.mpr
      intro i
      apply ae_all_iff.mpr
      intro k
      apply LevyStochCalc.Ito.Picard.itoIntegral_congr_ae_readable (W.W k) ℱ (hW k)
        (H i k) (G i k) (hm i k) (hp i k) (hq i k)
        (gm i k) (gp i k) (gq i k) ht
      filter_upwards [hXY_window t] with ω hω
      filter_upwards [hω] with s hs
      exact congrArg (fun x => σ x k i) hs
    filter_upwards [hXY_window t, hI] with ω hω hIω
    funext i
    have ha : (∫ s in Set.Icc (0 : ℝ) t, a i ω s ∂volume) =
        ∫ s in Set.Icc (0 : ℝ) t, c i ω s ∂volume := by
      apply integral_congr_ae
      filter_upwards [hω] with s hs
      exact congrArg (fun x => b x i) hs
    have hM : LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hW H hm hp hq i t ω =
        LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hW G gm gp gq i t ω :=
      Finset.sum_congr rfl fun k _ => hIω i k
    change x₀ i + (∫ s in Set.Icc (0 : ℝ) t, a i ω s ∂volume) +
        LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hW H hm hp hq i t ω =
      x₀ i + (∫ s in Set.Icc (0 : ℝ) t, c i ω s ∂volume) +
        LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hW G gm gp gq i t ω
    rw [ha, hM]
