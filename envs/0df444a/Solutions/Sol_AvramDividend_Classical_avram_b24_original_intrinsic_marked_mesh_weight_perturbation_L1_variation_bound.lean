-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_intrinsic_marked_mesh_weight_perturbation_L1_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:59:12.803652+00:00
-- url     : https://prove2.me/submissions/f686bd34-6264-442b-a761-a7361bc67c85

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (S : Finset ℕ) (a b : ℕ → ℝ≥0)
    (WG WJ : ℕ → Ω → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hClose : ∀ i ∈ S, ∀ ω, ‖WG i ω - WJ i ω‖ ≤ ε)
    (hMeshI : Integrable (fun ω =>
      ∑ i ∈ S, (WG i ω - WJ i ω) *
        (Jsmall (b i) ω - Jsmall (a i) ω)) P)
    (hVarI : Integrable (fun ω => ∑ i ∈ S,
      ‖Jsmall (b i) ω - Jsmall (a i) ω‖) P)
    (V : ℝ) (hV : 0 ≤ V)
    (hVarMean : (∫ ω, ∑ i ∈ S,
      ‖Jsmall (b i) ω - Jsmall (a i) ω‖ ∂P) ≤ V) :
    (∫ ω, ‖∑ i ∈ S, (WG i ω - WJ i ω) *
      (Jsmall (b i) ω - Jsmall (a i) ω)‖ ∂P) ≤ ε * V := by
  let Z : ℕ → Ω → ℝ := fun i ω =>
    Jsmall (b i) ω - Jsmall (a i) ω
  let Vfun : Ω → ℝ := fun ω => ∑ i ∈ S, ‖Z i ω‖
  let G : Ω → ℝ := fun ω =>
    ∑ i ∈ S, (WG i ω - WJ i ω) * Z i ω
  have hMajorI : Integrable (fun ω => ε * Vfun ω) P :=
    hVarI.const_mul ε
  have hPath (ω : Ω) : ‖G ω‖ ≤ ε * Vfun ω := by
    calc
      ‖G ω‖ ≤ ∑ i ∈ S,
        ‖(WG i ω - WJ i ω) * Z i ω‖ :=
        norm_sum_le S _
      _ = ∑ i ∈ S,
        ‖WG i ω - WJ i ω‖ * ‖Z i ω‖ := by
        simp only [norm_mul]
      _ ≤ ∑ i ∈ S, ε * ‖Z i ω‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right
          (hClose i hi ω) (norm_nonneg _)
      _ = ε * Vfun ω := by
        simp only [Vfun, Finset.mul_sum]
  have hCmp :
      (∫ ω, ‖G ω‖ ∂P) ≤
      (∫ ω, ε * Vfun ω ∂P) :=
    integral_mono_ae hMeshI.norm hMajorI
      (Filter.Eventually.of_forall hPath)
  calc
    (∫ ω, ‖G ω‖ ∂P) ≤
        (∫ ω, ε * Vfun ω ∂P) := hCmp
    _ = ε * (∫ ω, Vfun ω ∂P) := integral_const_mul _ _
    _ ≤ ε * V :=
      mul_le_mul_of_nonneg_left hVarMean hε
