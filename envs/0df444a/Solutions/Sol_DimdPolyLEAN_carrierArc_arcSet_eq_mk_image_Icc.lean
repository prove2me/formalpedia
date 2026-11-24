-- Prove2me | solution 1 for DimdPolyLEAN.carrierArc_arcSet_eq_mk_image_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:19.896196+00:00
-- url     : https://prove2.me/submissions/5927565c-1eb2-49c9-b289-0c608212db8a

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
public import Theorems.Thm_DimdPolyLEAN_carrierArc_length_pos

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =
      QuotientAddGroup.mk ''
        Set.Icc ((carrierArc N k).left) ((carrierArc N k).right) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨t, ht, rfl⟩
    refine ⟨(carrierArc N k).left + t * arcLength (carrierArc N k), ?_, rfl⟩
    have hlen_nonneg : 0 <= arcLength (carrierArc N k) :=
      le_of_lt (carrierArc_length_pos k)
    constructor
    · dsimp [arcLength] at hlen_nonneg ⊢
      nlinarith only [ht.1, hlen_nonneg]
    · dsimp [arcLength] at hlen_nonneg ⊢
      nlinarith only [ht.2, hlen_nonneg]
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    let t : ℝ := (y - (carrierArc N k).left) / arcLength (carrierArc N k)
    refine ⟨t, ?_, ?_⟩
    · have hlen_pos : 0 < arcLength (carrierArc N k) :=
        carrierArc_length_pos k
      constructor
      · dsimp [t]
        exact div_nonneg (sub_nonneg.mpr hy.1) (le_of_lt hlen_pos)
      · dsimp [t]
        rw [div_le_one hlen_pos]
        dsimp [arcLength]
        linarith only [hy.2]
    · dsimp [arcParam, t]
      have hlen_pos : 0 < arcLength (carrierArc N k) :=
        carrierArc_length_pos k
      apply congrArg (fun r : ℝ => (QuotientAddGroup.mk r : Circle))
      field_simp [ne_of_gt hlen_pos]
      ring_nf
end DimdPolyLEAN
