-- Prove2me | solution 1 for FiniteEnergyPlane.nhdsWithin_energySurface_le_map
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T12:38:00.558153+00:00
-- url     : https://prove2.me/submissions/46fee75d-b24c-4789-a17a-3ad45e925e13

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_proj_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_proj_smul_eq_of_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_exists_equiv_hasStrictFDerivAt_exp_smul_of_injective



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma pfo_ne_zero {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : H x = 1) : x ≠ 0 := by
  rintro rfl
  have := hH.2.2 0 hx
  simp at this

lemma pfo_proj_mem {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n} (hy : y ≠ 0) :
    H (proj H y) = 1 := proj_mem_energySurface H hH y hy

lemma pfo_proj_smul {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : H x = 1) {r : ℝ} (hr : 0 < r) : proj H (r • x) = x :=
  proj_smul_eq_of_mem_energySurface H hH x hx r hr

lemma pfo_proj_self {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : H x = 1) : proj H x = x := by
  simpa using pfo_proj_smul hH hx one_pos

lemma pfo_eq_smul {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n}
    (hy : y ≠ 0) : ∃ r : ℝ, y = Real.exp r • proj H y := by
  obtain ⟨s, hs, hsy⟩ := (hH.2.1 _ hy).exists
  refine ⟨-Real.log s, ?_⟩
  have h := pfo_proj_smul hH hsy (inv_pos.2 hs)
  rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] at h
  rw [h, Real.exp_neg, Real.exp_log hs, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

lemma pfo_smul_eq {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x q : V n} {r : ℝ}
    (hx : H x = 1) (hq : H q = 1) (h : Real.exp r • x = q) : x = q := by
  rw [← pfo_proj_smul hH hx (Real.exp_pos r), h, pfo_proj_self hH hq]

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem nhdsWithin_energySurface_le_map_aux {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 2 * n + 1) (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (F : E → V n) (p : E) (hF : ContDiffAt ℝ 1 F p)
    (hFS : ∀ᶠ q in 𝓝 p, F q ∈ energySurface H) (hinj : Function.Injective (fderiv ℝ F p)) :
    𝓝[energySurface H] (F p) ≤ map F (𝓝 p) := by
  obtain ⟨-, L, -, hs⟩ := exists_equiv_hasStrictFDerivAt_exp_smul_of_injective hE H hH F p hF hFS hinj
  have hm := hs.map_nhds_eq_of_equiv
  simp only [Real.exp_zero, one_smul] at hm
  intro N hN
  rw [mem_map] at hN
  have h1 : (fun q : ℝ × E => Real.exp q.1 • F q.2) ''
      (Prod.snd ⁻¹' (F ⁻¹' N ∩ {q | F q ∈ energySurface H})) ∈ 𝓝 (F p) := by
    rw [← hm]
    exact image_mem_map (continuous_snd.continuousAt.preimage_mem_nhds (inter_mem hN hFS))
  refine mem_of_superset (inter_mem_nhdsWithin _ h1) ?_
  rintro _ ⟨hq, ⟨r, q⟩, ⟨h2, h3⟩, rfl⟩
  have := pfo_smul_eq hH h3 hq rfl
  simp only at this ⊢
  rw [← this]
  exact h2

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 2 * n + 1) (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (F : E → V n) (p : E) (hF : ContDiffAt ℝ 1 F p)
    (hFS : ∀ᶠ q in 𝓝 p, F q ∈ energySurface H) (hinj : Function.Injective (fderiv ℝ F p)) :
    𝓝[energySurface H] (F p) ≤ map F (𝓝 p) :=
  nhdsWithin_energySurface_le_map_aux hE H hH F p hF hFS hinj
