-- Prove2me | solution 1 for DedekindZeta.map_inv_volume_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:30:47.142889+00:00
-- url     : https://prove2.me/submissions/0e844436-b736-4a5a-8bfc-53725b4aa339

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_map_inv_volume_real_one
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
private theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (e : α ≃ᵐ β) (ρ : Measure α) {h : β → ℝ≥0∞}
    (hh : Measurable h) :
    Measure.map e (ρ.withDensity (fun x => h (e x)))
      = (Measure.map e ρ).withDensity h := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hhe : Measurable (fun x => h (e x)) := hh.comp e.measurable
  have hfe : Measurable (fun a => f (e a)) := hf.comp e.measurable
  rw [lintegral_map hf e.measurable,
    lintegral_withDensity_eq_lintegral_mul _ hhe hfe,
    lintegral_withDensity_eq_lintegral_mul _ hh hf]
  simp only [Pi.mul_apply]
  rw [lintegral_map (by fun_prop : Measurable (fun a => h a * f a)) e.measurable]
private theorem pi_const_withDensity_fin {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] {g : E → ℝ≥0∞} (hg : Measurable g)
    [SigmaFinite (μ.withDensity g)] (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ.withDensity g)
      = (Measure.pi (fun _ : Fin n => μ)).withDensity (fun x : Fin n → E => ∏ i, g (x i)) := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty, Measure.pi_of_empty]
    have : (fun x : Fin 0 → E => ∏ i, g (x i)) = (fun _ => (1 : ℝ≥0∞)) := by
      funext x; simp
    rw [this]
    simp
  | succ n ih =>
    have hgprod : Measurable (fun x : Fin n → E => ∏ i, g (x i)) :=
      Finset.measurable_prod _ fun i _ => hg.comp (measurable_pi_apply i)
    have hgprod' : Measurable (fun x : Fin (n + 1) → E => ∏ i, g (x i)) :=
      Finset.measurable_prod _ fun i _ => hg.comp (measurable_pi_apply i)
    set e : (Fin (n + 1) → E) ≃ᵐ E × (Fin n → E) :=
      MeasurableEquiv.piFinSuccAbove (fun _ => E) 0 with he
    -- The density commutes with `Fin.cons`-insertion `e.symm`.
    have hcomp : (fun z : E × (Fin n → E) =>
          g z.1 * ∏ j : Fin n, g (z.2 j))
        = fun z => (fun x : Fin (n + 1) → E => ∏ i, g (x i)) (e.symm z) := by
      funext z
      have hz : (e.symm z) = Fin.cons z.1 z.2 := by
        simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv_zero]
        rfl
      change g z.1 * ∏ j, g (z.2 j) = ∏ i, g ((e.symm z) i)
      rw [hz, Fin.prod_univ_succ, Fin.cons_zero]
      simp [Fin.cons_succ]
    calc
      Measure.pi (fun _ : Fin (n + 1) => μ.withDensity g)
          = Measure.map e.symm
              ((μ.withDensity g).prod
                (Measure.pi fun _ : Fin n => μ.withDensity g)) :=
            ((measurePreserving_piFinSuccAbove
              (fun _ : Fin (n + 1) => μ.withDensity g) 0).symm.map_eq).symm
      _ = Measure.map e.symm
              ((μ.withDensity g).prod
                ((Measure.pi fun _ : Fin n => μ).withDensity
                  (fun y : Fin n → E => ∏ j, g (y j)))) := by rw [ih]
      _ = Measure.map e.symm
              (((μ).prod (Measure.pi fun _ : Fin n => μ)).withDensity
                (fun z : E × (Fin n → E) => g z.1 * ∏ j, g (z.2 j))) := by
            rw [prod_withDensity hg hgprod]
      _ = (Measure.map e.symm
              ((μ).prod (Measure.pi fun _ : Fin n => μ))).withDensity
                (fun x : Fin (n + 1) → E => ∏ i, g (x i)) := by
            rw [hcomp, map_withDensity_comp e.symm _ hgprod']
      _ = (Measure.pi (fun _ : Fin (n + 1) => μ)).withDensity
                (fun x : Fin (n + 1) → E => ∏ i, g (x i)) := by
            rw [(measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm.map_eq]
private theorem pi_const_withDensity {ι : Type*} [Fintype ι] {E : Type*}
    [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] {g : E → ℝ≥0∞}
    (hg : Measurable g) [SigmaFinite (μ.withDensity g)] :
    Measure.pi (fun _ : ι => μ.withDensity g)
      = (Measure.pi (fun _ : ι => μ)).withDensity (fun x : ι → E => ∏ i, g (x i)) := by
  classical
  have hgprod : Measurable (fun x : ι → E => ∏ i, g (x i)) :=
    Finset.measurable_prod _ fun i _ => hg.comp (measurable_pi_apply i)
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with he
  set P : (Fin (Fintype.card ι) → E) ≃ᵐ (ι → E) :=
    MeasurableEquiv.piCongrLeft (fun _ : ι => E) e with hP
  have hcomp : (fun y : Fin (Fintype.card ι) → E => ∏ i', g (y i'))
      = fun y => (fun x : ι → E => ∏ i, g (x i)) (P y) := by
    funext y
    change ∏ i', g (y i') = ∏ i, g ((P y) i)
    rw [← e.prod_comp (fun i => g ((P y) i))]
    refine Finset.prod_congr rfl fun i' _ => ?_
    rw [hP, MeasurableEquiv.piCongrLeft_apply_apply]
  calc
    Measure.pi (fun _ : ι => μ.withDensity g)
        = Measure.map P (Measure.pi (fun _ : Fin (Fintype.card ι) => μ.withDensity g)) := by
          rw [hP, (measurePreserving_piCongrLeft (α := fun _ : ι => E)
            (μ := fun _ => μ.withDensity g) e).map_eq]
    _ = Measure.map P ((Measure.pi (fun _ : Fin (Fintype.card ι) => μ)).withDensity
            (fun y : Fin (Fintype.card ι) → E => ∏ i', g (y i'))) := by
          rw [pi_const_withDensity_fin μ hg]
    _ = (Measure.map P (Measure.pi (fun _ : Fin (Fintype.card ι) => μ))).withDensity
            (fun x : ι → E => ∏ i, g (x i)) := by
          rw [hcomp, map_withDensity_comp P _ hgprod]
    _ = (Measure.pi (fun _ : ι => μ)).withDensity (fun x : ι → E => ∏ i, g (x i)) := by
          rw [hP, (measurePreserving_piCongrLeft (α := fun _ : ι => E) (μ := fun _ => μ) e).map_eq]
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
    Measure.map
        (fun x : {w : InfinitePlace K // IsReal w} → ℝ => fun w => (x w)⁻¹)
        volume
      = volume.withDensity
          (fun x : {w : InfinitePlace K // IsReal w} → ℝ =>
            ∏ w, ENNReal.ofReal (‖x w‖ ^ 2)⁻¹) := by
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (‖t‖ ^ 2)⁻¹ with hg_def
  have hg : Measurable g := ((measurable_norm.pow_const 2).inv).ennreal_ofReal
  -- The 1-D push-forward `map (·⁻¹) volume` is `SigmaFinite` (its density is
  -- everywhere finite, since `ENNReal.ofReal _ ≠ ∞`).
  have hsf : SigmaFinite ((volume : Measure ℝ).map (fun t : ℝ => t⁻¹)) := by
    rw [map_inv_volume_real_one]
    exact SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  haveI : ∀ _ : {w : InfinitePlace K // IsReal w},
      SigmaFinite ((volume : Measure ℝ).map (fun t : ℝ => t⁻¹)) := fun _ => hsf
  haveI : SigmaFinite ((volume : Measure ℝ).withDensity g) :=
    SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  -- Rewrite the target `volume` as a product measure first (only on the RHS).
  conv_rhs => rw [show (volume : Measure ({w : InfinitePlace K // IsReal w} → ℝ))
        = Measure.pi (fun _ => (volume : Measure ℝ)) from volume_pi]
  -- `volume = Measure.pi (fun _ => volume)` and componentwise push-forward.
  rw [show (volume : Measure ({w : InfinitePlace K // IsReal w} → ℝ))
        = Measure.pi (fun _ => (volume : Measure ℝ)) from volume_pi,
    Measure.pi_map_pi (fun _ => measurable_inv.aemeasurable)]
  -- Each factor is the 1-D Jacobian; reassemble via the product `withDensity`.
  simp_rw [map_inv_volume_real_one]
  rw [pi_const_withDensity (volume : Measure ℝ) hg]
end DedekindZeta
