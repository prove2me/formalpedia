-- Prove2me | solution 1 for CoVaRMC.Batching.cond_density
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:22:48.2558+00:00
-- url     : https://prove2.me/submissions/312493fc-1e73-41cb-b18b-49c7a65933f7

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting

open MeasureTheory ProbabilityTheory Filter Topology

open CoVaRMC.Batching in
theorem solution (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (v c : ℝ) (𝒳 𝒴 : Set ℝ)
    (hFc : IsCondCDFVersion D Fc) (hA1 : Assumption1 D Fc v c 𝒳 𝒴)
    (x : ℝ) (hx : x ∈ 𝒳) (y : ℝ) (hy : y ∈ 𝒴) :
    HasDerivAt (fun y' => Fc y' x) (D.condDensity y x) y ∧ 0 < D.condDensity y x := by
  obtain ⟨h𝒳o, -, h𝒴o, -, -, hfXpos, hfC, hfpos, -⟩ := hA1
  have hX : 0 < D.fX x := hfXpos x hx
  set g : ℝ → ℝ := fun w => D.f (x, w) with hg
  have hgm : Measurable g := D.measurable.comp measurable_prodMk_left
  have hgi : Integrable g := by
    by_contra hni
    have : D.fX x = 0 := by
      show ∫ w, D.f (x, w) = 0
      exact integral_undef hni
    linarith
  have hgc : ContinuousAt g y := by
    have hopen : IsOpen (𝒳 ×ˢ 𝒴) := h𝒳o.prod h𝒴o
    have hmem : (x, y) ∈ 𝒳 ×ˢ 𝒴 := ⟨hx, hy⟩
    have hca : ContinuousAt D.f (x, y) :=
      (hfC.continuousOn).continuousAt (hopen.mem_nhds hmem)
    exact hca.comp (Continuous.prodMk_right x).continuousAt
  have hFeq : (fun y' => Fc y' x) = fun y' => (∫ w in Set.Iic y', g w) / D.fX x := by
    funext y'
    rw [hFc x hX y']
    rfl
  have hsplit : (fun y' => ∫ w in Set.Iic y', g w) =
      fun y' => (∫ w in Set.Iic y, g w) + ∫ w in y..y', g w := by
    funext y'
    rw [← intervalIntegral.integral_Iic_sub_Iic hgi.integrableOn hgi.integrableOn]
    ring
  have hd : HasDerivAt (fun y' => ∫ w in y..y', g w) (g y) y :=
    intervalIntegral.integral_hasDerivAt_right (hgi.intervalIntegrable)
      (hgm.stronglyMeasurable.stronglyMeasurableAtFilter) hgc
  refine ⟨?_, ?_⟩
  · rw [hFeq]
    have : HasDerivAt (fun y' => ∫ w in Set.Iic y', g w) (g y) y := by
      rw [hsplit]; exact hd.const_add _
    exact this.div_const _
  · exact div_pos (hfpos (x, y) ⟨hx, hy⟩) hX
