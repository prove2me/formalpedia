-- Prove2me | solution 1 for FiniteEnergyPlane.range_eq_of_proj_eq_of_mem_embeddedFastPlaneSet
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T13:36:43.197745+00:00
-- url     : https://prove2.me/submissions/b7f5092c-f7d0-4b8c-9fc1-8262c0b9db79

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_proj_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_proj_smul_eq_of_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_proj_not_mem_range_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_range_eq_or_disjoint_of_isFastPlane



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

theorem range_eq_of_proj_eq_of_mem_embeddedFastPlaneSet_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ γ' : ℝ) (K K' : Set (V 1)) (u v : ℂ → V 1)
    (hu : u ∈ embeddedFastPlaneSet H J P K γ) (hv : v ∈ embeddedFastPlaneSet H J P K' γ')
    (z z' : ℂ) (h : proj H (u z) = proj H (v z')) :
    Set.range (fun z => proj H (u z)) = Set.range (fun z => proj H (v z)) := by
  have hum := proj_not_mem_range_of_isFastPlane H hH J hJ P hcz u hu.1.1 hu.1.2.1 hu.2
  have hvm := proj_not_mem_range_of_isFastPlane H hH J hJ P hcz v hv.1.1 hv.1.2.1 hv.2
  refine (range_eq_or_disjoint_of_isFastPlane H hH J hJ P u v hu.1.1 hu.1.2.1 hu.2 hv.1.1 hv.1.2.1
    hv.2 hum hvm).resolve_right fun hd => ?_
  exact Set.disjoint_left.1 hd ⟨z, rfl⟩ ⟨z', h.symm⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ γ' : ℝ) (K K' : Set (V 1)) (u v : ℂ → V 1)
    (hu : u ∈ embeddedFastPlaneSet H J P K γ) (hv : v ∈ embeddedFastPlaneSet H J P K' γ')
    (z z' : ℂ) (h : proj H (u z) = proj H (v z')) :
    Set.range (fun z => proj H (u z)) = Set.range (fun z => proj H (v z)) :=
  range_eq_of_proj_eq_of_mem_embeddedFastPlaneSet_aux H hH J hJ P hcz γ γ' K K' u v hu hv z z' h
