-- Prove2me | solution 1 for FourierJacobi.Analysis.integrable_hasSum_of_countable_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:03.868465+00:00
-- url     : https://prove2.me/submissions/381acc3c-da20-444b-b3b2-5a2bf9e2c817

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_FiberIntegration

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open MeasureTheory
namespace FourierJacobi.Analysis
theorem _root_.solution {X ι : Type*}
    [MeasurableSpace X] [Countable ι] (μ : Measure X)
    (s : ι → Set X) (f : X → ℂ) (F : ι → ℂ)
    (hm : ∀ i, MeasurableSet (s i)) (hfinite : ∀ i, μ (s i) ≠ ⊤)
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hcover : (⋃ i, s i) =ᵐ[μ] Set.univ)
    (hvalue : ∀ i x, x ∈ s i → f x = F i)
    (hn : Summable (fun i => μ.real (s i) * ‖F i‖)) :
    Integrable f μ ∧ HasSum (fun i => (μ.real (s i) : ℂ) * F i) (∫ x, f x ∂μ) := by
  have hi (i : ι) : IntegrableOn f (s i) μ :=
    (integrableOn_const (hfinite i)).congr_fun
      (fun x hx => (hvalue i x hx).symm) (hm i)
  have hnorm (i : ι) : (∫ x in s i, ‖f x‖ ∂μ) = μ.real (s i) * ‖F i‖ := by
    rw [setIntegral_congr_fun (hm i) (fun x hx => congrArg norm (hvalue i x hx))]
    simp only [setIntegral_const, smul_eq_mul]
  have hu : IntegrableOn f (⋃ i, s i) μ := by
    apply integrableOn_iUnion_of_summable_integral_norm hi
    simpa only [hnorm] using hn
  have hg : Integrable f μ := by
    simpa only [integrableOn_univ] using hu.congr_set_ae hcover.symm
  have he (i : ι) : (∫ x in s i, f x ∂μ) = (μ.real (s i) : ℂ) * F i := by
    rw [setIntegral_congr_fun (hm i) (hvalue i), setIntegral_const]
    exact Complex.real_smul
  have heU : (∫ x in ⋃ i, s i, f x ∂μ) = ∫ x, f x ∂μ := by
    rw [setIntegral_congr_set hcover, setIntegral_univ]
  refine ⟨hg, ?_⟩
  simpa only [he, heU] using hasSum_integral_iUnion hm hd hu
end FourierJacobi.Analysis
