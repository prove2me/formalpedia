-- Prove2me | solution 1 for DedekindZeta.volume_pi_complex_map_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:30:39.591251+00:00
-- url     : https://prove2.me/submissions/dcd5e12e-1b86-48d6-82ce-4f7a9a879b0b

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_volume_complex_map_inv
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply


section
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
namespace DedekindZeta.GammaIntegral
open Classical
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
end
end DedekindZeta.GammaIntegral
namespace DedekindZeta
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
variable {K : Type*} [Field K] [NumberField K]
noncomputable section
private theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
        (MeasurableEquiv.measurableEmbedding _)]
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
        Fin.zero_succAbove, Fin.cons_zero]
      rw [← ih (fun i ↦ f (Fin.succ i)) (fun i ↦ hf _)]
      haveI : ∀ j : Fin n, SigmaFinite (μ j.succ) := fun j ↦ inferInstance
      have hpm := lintegral_prod_mul (μ := μ 0) (ν := Measure.pi fun i : Fin n ↦ μ i.succ)
        (f := fun a ↦ f 0 a)
        (g := fun y : (i : Fin n) → E (Fin.succ i) ↦ ∏ i, f (Fin.succ i) (y i))
        ((hf 0).aemeasurable)
        ((Finset.measurable_prod _ fun i _ ↦ (hf _).comp (measurable_pi_apply i)).aemeasurable)
      exact hpm
private theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  haveI : ∀ j : Fin (Fintype.card ι), SigmaFinite (μ (e j)) := fun j ↦ inferInstance
  have hpm := lintegral_fin_nat_prod_eq_prod (E := fun j ↦ E (e j)) (mE := fun j ↦ mE (e j))
    (μ := fun j ↦ μ (e j)) (fun j ↦ f (e j)) (fun j ↦ hf _)
  exact hpm
private theorem pi_withDensity_const_eq {ι : Type*} [Fintype ι] {E : Type*}
    [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] {g : E → ℝ≥0∞} (hg : Measurable g)
    [SigmaFinite (μ.withDensity g)] :
    Measure.pi (fun _ : ι ↦ μ.withDensity g)
      = (Measure.pi (fun _ : ι ↦ μ)).withDensity (fun x ↦ ∏ i, g (x i)) := by
  refine Measure.pi_eq (μ := fun _ : ι ↦ μ.withDensity g) fun s hs ↦ ?_
  haveI : ∀ i : ι, SigmaFinite (μ.restrict (s i)) := fun i ↦ inferInstance
  have hLI : ∫⁻ x : ι → E, ∏ i, g (x i) ∂(Measure.pi fun _ : ι ↦ μ.restrict (s _))
      = ∏ i, ∫⁻ x, g x ∂(μ.restrict (s i)) :=
    lintegral_fintype_prod_eq_prod (μ := fun _ : ι ↦ μ.restrict (s _)) (fun _ ↦ g) (fun _ ↦ hg)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi, hLI]
  exact Finset.prod_congr rfl fun i _ ↦ (withDensity_apply g (hs i)).symm
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
end
end DedekindZeta
namespace DedekindZeta.GammaIntegral
open DedekindZeta DedekindZeta.Theta
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped nonZeroDivisors
end
end DedekindZeta.GammaIntegral
end

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
variable {K : Type*} [Field K] [NumberField K]
noncomputable section
open Classical
namespace DedekindZeta
theorem _root_.solution :
    Measure.map (fun x : {w : InfinitePlace K // IsComplex w} → ℂ => fun w => (x w)⁻¹) volume
      = volume.withDensity
          (fun x : {w : InfinitePlace K // IsComplex w} → ℂ => ∏ w, ENNReal.ofReal (‖x w‖ ^ 4)⁻¹) := by
  classical
  -- the per-coordinate inversion Jacobian density.
  set g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ 4)⁻¹ with hg
  have hgmeas : Measurable g := by
    rw [hg]; exact ((measurable_norm.pow_const 4).inv).ennreal_ofReal
  -- σ-finiteness of the per-coordinate push-forward `map (·⁻¹) volume = volume.withDensity g`.
  have hsf : SigmaFinite ((volume : Measure ℂ).map (fun z : ℂ => z⁻¹)) := by
    rw [volume_complex_map_inv]; infer_instance
  haveI hsf' : ∀ _i : {w : InfinitePlace K // IsComplex w},
      SigmaFinite ((volume : Measure ℂ).map (fun z : ℂ => z⁻¹)) := fun _ => hsf
  -- identify `volume` on the product with `Measure.pi (fun _ => volume)` and push forward
  -- componentwise (`pi_map_pi`).
  rw [volume_pi]
  have hmap := Measure.pi_map_pi (μ := fun _ : {w : InfinitePlace K // IsComplex w} => (volume : Measure ℂ))
    (f := fun _ : {w : InfinitePlace K // IsComplex w} => fun z : ℂ => z⁻¹)
    (fun _ => measurable_inv.aemeasurable)
  rw [hmap]
  -- replace each per-coordinate map by its `withDensity` form, then collapse the product.
  simp_rw [volume_complex_map_inv]
  rw [pi_withDensity_const_eq (volume : Measure ℂ) hgmeas]
end DedekindZeta
