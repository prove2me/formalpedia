-- Prove2me | solution 1 for DimdPolyLEAN.symplecticFourierRep_eq_of_lpNorm_one_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:20.696153+00:00
-- url     : https://prove2.me/submissions/9247145f-ef71-49bb-9ac0-4ab47fe35ee3

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
public import Theorems.Thm_DimdPolyLEAN_tendsto_symplecticFourierRep_of_lpNorm_one

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
    {A : ℂ} {Aₙ : Nat -> ℂ}
    (hG : Integrable G (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (hGₙ : ∀ n, Integrable (Gₙ n) (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (hLp : Tendsto
      (fun n : Nat => MeasureTheory.lpNorm (fun η : PhaseSpace d => Gₙ n η - G η) 1
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
      atTop (nhds 0))
    (hA : Tendsto Aₙ atTop (nhds A))
    (ξ : PhaseSpace d)
    (hEq : ∀ n : Nat, symplecticFourierRep (Gₙ n) ξ = Aₙ n) :
    symplecticFourierRep G ξ = A := by
  have hleft := tendsto_symplecticFourierRep_of_lpNorm_one hG hGₙ hLp ξ
  have hright :
      Tendsto (fun n : Nat => symplecticFourierRep (Gₙ n) ξ) atTop (nhds A) := by
    rw [show (fun n : Nat => symplecticFourierRep (Gₙ n) ξ) = Aₙ by
      funext n
      exact hEq n]
    exact hA
  exact tendsto_nhds_unique hleft hright
end DimdPolyLEAN
