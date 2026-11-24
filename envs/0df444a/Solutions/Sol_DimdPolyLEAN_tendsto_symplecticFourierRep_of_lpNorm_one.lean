-- Prove2me | solution 1 for DimdPolyLEAN.tendsto_symplecticFourierRep_of_lpNorm_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:43.712181+00:00
-- url     : https://prove2.me/submissions/295aa0e2-1359-4187-aefd-212f845b704c

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
public import Theorems.Thm_DimdPolyLEAN_symplecticFourierRep_sub_le_lpNorm_one

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution {d : Nat}
    {G : PhaseSpace d -> ℂ} {Gₙ : Nat -> PhaseSpace d -> ℂ}
    (hG : Integrable G (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (hGₙ : ∀ n, Integrable (Gₙ n) (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (hLp : Tendsto
      (fun n : Nat => MeasureTheory.lpNorm (fun η : PhaseSpace d => Gₙ n η - G η) 1
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
      atTop (nhds 0))
    (ξ : PhaseSpace d) :
    Tendsto (fun n : Nat => symplecticFourierRep (Gₙ n) ξ) atTop
      (nhds (symplecticFourierRep G ξ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) ?_ hLp
  intro n
  simpa using symplecticFourierRep_sub_le_lpNorm_one (h1 := hGₙ n) (h2 := hG) ξ
end DimdPolyLEAN
