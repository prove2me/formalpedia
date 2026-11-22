-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_zerojump_arbitrary_bounded_stop_exact_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:40:19.023552+00:00
-- url     : https://prove2.me/submissions/3254bdf6-4f13-44fd-b271-d25bb6c7420f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_continuous_L1_bounded_stop_initial_condexp

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- Adapted stopped-martingale expectation argument from dufeteller/lean-lsv,
   LSV/LocalizedOptionalExpectation.lean (CC BY 4.0,
   commit a5f604de2e1ae431de4cbecde23e5694a12ba719).
   Uses Prove2Me's proved original zero-jump compensated-square martingale
   and global path continuity for an arbitrary genuine bounded stop. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) :
    Integrable (fun ω =>
      (X.X (τ ω) ω - (τ ω : ℝ) * X.c)^2) P ∧
    (∫ ω, (X.X (τ ω) ω - (τ ω : ℝ) * X.c)^2 ∂P) =
      ∫ ω, (τ ω : ℝ) * X.σ^2 ∂P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c
  let Q : ℝ≥0 → Ω → ℝ := fun t ω =>
    (M t ω)^2 - (t : ℝ) * X.σ^2
  have hQ : Martingale Q 𝓕.rightCont P :=
    avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
      X hν
  have hMcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => M t ω) := by
    filter_upwards [avram_ubv_top11_original_zero_nu_global_continuous_ae
      X hν] with ω hω
    exact hω.sub (NNReal.continuous_coe.mul continuous_const)
  have hQcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => Q t ω) := by
    filter_upwards [hMcont] with ω hω
    exact (hω.pow 2).sub (NNReal.continuous_coe.mul continuous_const)
  have hQzero : ∀ᵐ ω ∂P, Q 0 ω = 0 := by
    exact ae_of_all _ (fun ω => by simp [Q, M, X.X_zero])
  have hQstop :=
    avram_jump6_A_continuous_L1_bounded_stop_initial_condexp
      Q (fun t => (hQ.stronglyMeasurable t).measurable)
        hQzero hQcont (fun t => hQ.integrable t)
        (fun s t hst => hQ.condExp_ae_eq hst)
        n hn τ hτstop hτbound
  have hti : Integrable (fun ω => (τ ω : ℝ)) P := by
    apply (integrable_const (n : ℝ)).mono'
      hτmeas.aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      have hle : (τ ω : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hτbound ω
      simpa [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using hle)
  have hAi : Integrable (fun ω => (τ ω : ℝ) * X.σ^2) P :=
    hti.mul_const _
  have hSq : (fun ω => (M (τ ω) ω)^2) =
      (fun ω => Q (τ ω) ω + (τ ω : ℝ) * X.σ^2) := by
    funext ω
    dsimp [Q]
    ring
  have hSqI : Integrable (fun ω => (M (τ ω) ω)^2) P := by
    rw [hSq]
    exact hQstop.1.add hAi
  have he := integral_congr_ae hQstop.2
  rw [integral_condExp ((𝓕.rightCont).le 0)] at he
  have hQmean : (∫ ω, Q (τ ω) ω ∂P) = 0 := by
    simpa using he
  change Integrable (fun ω => (M (τ ω) ω)^2) P ∧
    (∫ ω, (M (τ ω) ω)^2 ∂P) =
      ∫ ω, (τ ω : ℝ) * X.σ^2 ∂P
  refine ⟨hSqI, ?_⟩
  have hQmean' :
      (∫ ω, (M (τ ω) ω)^2 - (τ ω : ℝ) * X.σ^2 ∂P) = 0 := by
    exact hQmean
  rw [integral_sub hSqI hAi] at hQmean'
  exact sub_eq_zero.mp hQmean'

