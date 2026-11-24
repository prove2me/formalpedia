-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteTensorRep_memLp_of_realHermite1D_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:24:04.475609+00:00
-- url     : https://prove2.me/submissions/b34a1301-e546-4bef-b15f-fd2c0d9dee41

module
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ExactModulusRecovery
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (alpha : Idx d)
    (hmem1 : ∀ n : Nat, MemLp (realHermite1D n) 2 (volume : Measure ℝ)) :
    MemLp (realHermiteTensorRep alpha) 2 (volume : Measure (RealVec d)) := by
  classical
  let g : (Fin d → ℝ) → ℂ := fun y => ∏ q : Fin d, realHermite1D (alpha q) (y q)
  have hcoord_meas (q : Fin d) :=
    (hmem1 (alpha q)).aestronglyMeasurable.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_eval
        (μ := fun _ : Fin d => (volume : Measure ℝ)) q)
  have hg_meas := Finset.univ.aestronglyMeasurable_fun_prod
    (f := fun q (y : Fin d → ℝ) => realHermite1D (alpha q) (y q))
    (fun q _ => hcoord_meas q)
  have hg_int := MeasureTheory.Integrable.fintype_prod
    (μ := fun _ : Fin d => (volume : Measure ℝ))
    (fun q => (hmem1 (alpha q)).integrable_norm_rpow (by norm_num) (by norm_num))
  have hnorm : Integrable (fun y => ‖g y‖ ^ (2 : ℝ))
      (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))) :=
    hg_int.congr (Filter.Eventually.of_forall fun y => by
      simpa only [g, norm_prod, ENNReal.toReal_ofNat] using
        (Real.finsetProd_rpow (s := Finset.univ)
          (f := fun q : Fin d => ‖realHermite1D (alpha q) (y q)‖)
          (fun _ _ => norm_nonneg _) (2 : ℝ)))
  have hg := (integrable_norm_rpow_iff (p := (2 : ℝ≥0∞)) hg_meas
    (by norm_num) (by norm_num)).1 hnorm
  have hcomp := hg.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin d))
  refine MeasureTheory.MemLp.ae_eq ?_ hcomp
  filter_upwards with x
  simp only [Function.comp_apply, realHermiteTensorRep]
end DimdPolyLEAN
