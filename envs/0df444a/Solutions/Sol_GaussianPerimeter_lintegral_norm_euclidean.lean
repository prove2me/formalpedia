-- Prove2me | solution 1 for GaussianPerimeter.lintegral_norm_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:24:00.857144+00:00
-- url     : https://prove2.me/submissions/1345b354-fa8b-4aef-b25e-711604397db7

module
public import Definitions.Def_GaussianPerimeter_Radial
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Definitions.Def_GaussianPerimeter_RadialIntegration

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped ENNReal Topology
open GaussianPerimeter
local notation "Euc" => fun n => EuclideanSpace ℝ (Fin n)
namespace GaussianPerimeter
theorem _root_.solution (n : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : Euc (n + 1), f ‖x‖) =
      ((n + 1 : ℕ) : ℝ≥0∞) * volume (Metric.ball (0 : Euc (n + 1)) 1) *
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) * f r) := by
  let E := Euc (n + 1)
  let μ : Measure E := volume
  let e := homeomorphUnitSphereProd E
  let g : Ioi (0 : ℝ) → ℝ≥0∞ := fun r => f r
  have hg : Measurable g := hf.comp measurable_subtype_coe
  have hdim : Module.finrank ℝ E = n + 1 := finrank_euclideanSpace_fin
  have hpres : MeasurePreserving e (μ.comap Subtype.val)
      (μ.toSphere.prod (.volumeIoiPow n)) := by
    simpa [e, hdim] using μ.measurePreserving_homeomorphUnitSphereProd
  calc
    _ = ∫⁻ x : ({(0 : E)}ᶜ : Set E), f ‖(x : E)‖ ∂(μ.comap Subtype.val) := by
      rw [lintegral_subtype_comap (μ := μ) (measurableSet_singleton (0 : E)).compl
        (fun x : E => f ‖x‖), restrict_compl_singleton]
    _ = ∫⁻ z, g z.2 ∂(μ.toSphere.prod (.volumeIoiPow n)) := by
      simpa only [g, e, Function.comp_apply, homeomorphUnitSphereProd_apply_snd_coe] using
        hpres.lintegral_comp_emb e.measurableEmbedding (g ∘ Prod.snd)
    _ = μ.toSphere univ * ∫⁻ r, g r ∂(Measure.volumeIoiPow n) := by
      rw [lintegral_prod (fun z : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) => g z.2)
        (hg.comp measurable_snd).aemeasurable]
      change (∫⁻ _x, ∫⁻ y, g y ∂(Measure.volumeIoiPow n) ∂μ.toSphere) = _
      rw [lintegral_const, mul_comm]
    _ = _ := by
      rw [Measure.toSphere_apply_univ, hdim, Measure.volumeIoiPow,
        lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hg]
      simp only [Pi.mul_apply, g, μ]
      rw [lintegral_subtype_comap measurableSet_Ioi (fun r : ℝ => ENNReal.ofReal (r ^ n) * f r)]
end GaussianPerimeter
