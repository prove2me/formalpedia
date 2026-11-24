-- Prove2me | solution 1 for DimdPolyLEAN.spectrogram_ambiguity_identity_of_product_moyal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:08.347555+00:00
-- url     : https://prove2.me/submissions/e795fe50-92e5-4e02-b6f3-7c1c2abd7197

module
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_RotationalAveraging
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Theorems.Thm_DimdPolyLEAN_spectrogramRep_eq_stft_mul_star

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat}
    (hmoyal : ∀ (h f : L2Real d) (ξ : PhaseSpace d),
      symplecticFourierRep
          (fun η : PhaseSpace d => stftRep h f η * star (stftRep h f η)) ξ =
        ambiguityRep f f ξ * star (ambiguityRep h h ξ))
    (h f : L2Real d) (ξ : PhaseSpace d) :
    symplecticFourierRep
        (fun η : PhaseSpace d => ((‖stftRep h f η‖ ^ 2 : ℝ) : ℂ)) ξ =
      ambiguityRep f f ξ * star (ambiguityRep h h ξ) := by
  rw [show (fun η : PhaseSpace d => ((‖stftRep h f η‖ ^ 2 : ℝ) : ℂ)) =
      fun η : PhaseSpace d => stftRep h f η * star (stftRep h f η) by
    funext η
    exact spectrogramRep_eq_stft_mul_star h f η]
  exact hmoyal h f ξ
end DimdPolyLEAN
