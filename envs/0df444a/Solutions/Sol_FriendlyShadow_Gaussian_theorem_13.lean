-- Prove2me | solution 1 for FriendlyShadow.Gaussian.theorem_13
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T04:31:01.488217+00:00
-- url     : https://prove2.me/submissions/0e2e84f1-0e07-4f95-a15b-d733a519fd82
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model
import Theorems.Thm_FriendlyShadow_Gaussian_lemma_45
import Theorems.Thm_FriendlyShadow_Gaussian_lemma_46
import Theorems.Thm_FriendlyShadow_Gaussian_theorem_22

set_option autoImplicit false

open MeasureTheory
open scoped RealInnerProductSpace ENNReal


theorem arith_30c62726 (d n : ℕ) (σ : ℝ) (hσ : 0 < σ) :
    1 + (2 + 8 * Real.pi * Real.exp 2 * ((d : ℝ) * Real.sqrt d) *
        ((4 * σ⁻¹ * Real.sqrt (d * Real.log n)) / (σ / 4)) *
        (1 + 4 * σ * Real.sqrt (d * Real.log n)) * (1 + 4 * (4 * σ * Real.sqrt (Real.log n))))
      = 3 + 128 * Real.pi * Real.exp 2 * (d : ℝ) ^ 2 * Real.sqrt (Real.log n) /
        σ ^ 2 * (1 + 4 * σ * Real.sqrt (d * Real.log n)) *
        (1 + 16 * σ * Real.sqrt (Real.log n)) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hs : Real.sqrt (d * Real.log n) = Real.sqrt d * Real.sqrt (Real.log n) :=
    Real.sqrt_mul hd0 _
  have hdd : Real.sqrt (d : ℝ) * Real.sqrt d = d := Real.mul_self_sqrt hd0
  rw [hs]
  have hσ' : σ ≠ 0 := hσ.ne'
  field_simp
  have : (d : ℝ) ^ 2 = d * (Real.sqrt d * Real.sqrt d) := by rw [hdd]; ring
  rw [this]
  ring

open MeasureTheory FriendlyShadow.Gaussian in
theorem solution {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1)
    (σ : ℝ) (hσ : 0 < σ) :
    AEMeasurable (fun a => (edgeCount (polygon W a) : ℝ≥0∞))
        (Measure.pi (fun i => SmoothedSimplex.Shadow.gaussian (abar i) σ)) ∧
    ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞)
        ∂(Measure.pi (fun i => SmoothedSimplex.Shadow.gaussian (abar i) σ)) ≤
      ENNReal.ofReal (3 + 128 * Real.pi * Real.exp 2 * (d : ℝ) ^ 2 * Real.sqrt (Real.log n) /
        σ ^ 2 * (1 + 4 * σ * Real.sqrt (d * Real.log n)) *
        (1 + 16 * σ * Real.sqrt (Real.log n))) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlogn : 0 < Real.log n := Real.log_pos hn1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsq : 0 < Real.sqrt (d * Real.log n) := Real.sqrt_pos.mpr (mul_pos hd0 hlogn)
  let μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun i => lgPdf (abar i) σ (4 * Real.sqrt (d * Real.log n))
  have h45 := fun i => lemma_45 hd hdn σ hσ (abar i) (μ i) rfl
  obtain ⟨-, h22⟩ := theorem_22 hd hdn W hW μ (fun i => (h45 i).1) abar
    (fun i => (h45 i).2.1) habar (4 * σ⁻¹ * Real.sqrt (d * Real.log n)) (σ / 4)
    (4 * σ * Real.sqrt (d * Real.log n)) (4 * σ * Real.sqrt (Real.log n))
    (by positivity) (by positivity) (by positivity) (by positivity)
    (fun i => (h45 i).2.2.1) (fun i => (h45 i).2.2.2.2.2)
    (fun i => (h45 i).2.2.2.1) (fun i => (h45 i).2.2.2.2.1)
  obtain ⟨hmeas, -, h46⟩ := lemma_46 hd hdn W hW abar σ hσ
  refine ⟨hmeas, h46.trans ?_⟩
  have h22' : ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞)
      ∂(Measure.pi (fun i => lg (abar i) σ (4 * Real.sqrt (d * Real.log n)))) ≤
      ENNReal.ofReal (2 + 8 * Real.pi * Real.exp 2 * ((d : ℝ) * Real.sqrt d) *
        ((4 * σ⁻¹ * Real.sqrt (d * Real.log n)) / (σ / 4)) *
        (1 + 4 * σ * Real.sqrt (d * Real.log n)) *
        (1 + 4 * (4 * σ * Real.sqrt (Real.log n)))) := h22
  refine (add_le_add (le_refl (1 : ℝ≥0∞)) h22').trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity),
    arith_30c62726 d n σ hσ]
