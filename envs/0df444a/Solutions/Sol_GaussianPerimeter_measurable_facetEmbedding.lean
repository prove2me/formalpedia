-- Prove2me | solution 1 for GaussianPerimeter.measurable_facetEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:05:44.043425+00:00
-- url     : https://prove2.me/submissions/667c3f4f-b36a-4df8-89f6-6babb293a023

module
public import Definitions.Def_GaussianPerimeter_Definitions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Definitions.Def_GaussianPerimeter_Geometry

set_option autoImplicit true
@[expose] public section
public section
open Function Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace RealInnerProductSpace Function
open GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)
namespace GaussianPerimeter
theorem _root_.solution {k : ℕ} (ρ : ℝ) :
    Measurable (fun p : {u : Euc (k + 1) // ‖u‖ = 1} × Euc k =>
      facetEmbedding p.1.1 p.1.2 ρ p.2) := by
  let N := {u : Euc (k + 1) // ‖u‖ = 1}
  let v (p : N × Euc k) := referenceNormal k - (p.1 : Euc (k + 1))
  let w (p : N × Euc k) : Euc (k + 1) := referenceTangent p.2
  have hm : Measurable (fun p : N × Euc k => (p.1 : Euc (k + 1))) :=
    measurable_subtype_coe.comp measurable_fst
  have hv : Measurable v := measurable_const.sub hm
  have hTangent : Continuous (fun y : Euc k => (referenceTangent y : Euc (k + 1))) :=
    continuous_subtype_val.comp
      (facetBasis (referenceNormal k) (norm_referenceNormal k)).repr.symm.isometry.continuous
  have hw : Measurable w := hTangent.measurable.comp measurable_snd
  have hinner : Measurable (fun p => ⟪v p, w p⟫_ℝ) :=
    Continuous.measurable2 continuous_inner hv hw
  have hcoef : Measurable (fun p => ⟪v p, w p⟫_ℝ / ‖v p‖ ^ 2) :=
    hinner.div (hv.norm.pow_const 2)
  have hp : Measurable (fun p => (⟪v p, w p⟫_ℝ / ‖v p‖ ^ 2) • v p) :=
    hcoef.smul hv
  have heq (p : N × Euc k) :
      facetEmbedding p.1.1 p.1.2 ρ p.2 =
        ρ • (p.1 : Euc (k + 1)) +
          (w p - ((⟪v p, w p⟫_ℝ / ‖v p‖ ^ 2) • v p +
            (⟪v p, w p⟫_ℝ / ‖v p‖ ^ 2) • v p)) := by
    simp only [facetEmbedding, facetTangent, normalReflection, Submodule.reflection_orthogonal_apply,
      Submodule.reflection_singleton_apply, neg_sub, v, w, RCLike.ofReal_real_eq_id, id_eq,
      two_nsmul]
  simp_rw [heq]
  exact ((measurable_const (a := ρ)).smul hm).add (hw.sub (hp.add hp))
end GaussianPerimeter
