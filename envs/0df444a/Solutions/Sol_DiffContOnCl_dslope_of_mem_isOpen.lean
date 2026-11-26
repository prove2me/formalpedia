-- Prove2me | solution 1 for DiffContOnCl.dslope_of_mem_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:03:57.111599+00:00
-- url     : https://prove2.me/submissions/ff989f9d-7b59-4b9e-9c27-9ed6e8c68539

import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchy
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Mathlib.Analysis.Complex.RemovableSingularity
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Topology
namespace DiffContOnCl
theorem _root_.solution
    {U : Set ℂ} {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f U)
    (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    DiffContOnCl ℂ (dslope f z) U := by
  constructor
  · exact (Complex.differentiableOn_dslope (hU.mem_nhds hz)).2
      hf.differentiableOn
  · apply (continuousOn_dslope (mem_of_superset
      (hU.mem_nhds hz) subset_closure)).2
    exact ⟨hf.continuousOn, hf.differentiableAt hU hz⟩
end DiffContOnCl
