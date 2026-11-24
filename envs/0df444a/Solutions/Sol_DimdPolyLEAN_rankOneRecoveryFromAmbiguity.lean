-- Prove2me | solution 1 for DimdPolyLEAN.rankOneRecoveryFromAmbiguity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:01.116378+00:00
-- url     : https://prove2.me/submissions/44095f0d-f58f-44f2-a9b7-a7d38ca97d70

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
public import Theorems.Thm_DimdPolyLEAN_equalAmbiguity_to_rankOneKernel_ae
public import Theorems.Thm_DimdPolyLEAN_rankOneKernel_ae_to_unimodular_phase

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} {f g : L2Real d} {fRep gRep : RealVec d -> ℂ}
    (hf_rep : IsL2Rep f fRep) (hg_rep : IsL2Rep g gRep)
    (hAmb : ∀ ξ : PhaseSpace d, ambiguityRep f f ξ = ambiguityRep g g ξ) :
    (f = 0 ∧ g = 0) ∨ ∃ w : ℂ, ‖w‖ = 1 ∧ g = w • f :=
  rankOneKernel_ae_to_unimodular_phase hf_rep hg_rep
    (equalAmbiguity_to_rankOneKernel_ae hf_rep hg_rep hAmb)
end DimdPolyLEAN
