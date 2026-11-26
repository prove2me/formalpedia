-- Prove2me | solution 1 for FourierJacobi.Analysis.i1r8ao_value_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:34.938213+00:00
-- url     : https://prove2.me/submissions/646aa31d-9eb0-44df-ba1b-0860542ab707

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1r10DepthEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1r10Equiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_norm_one_sub_ne_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i1r10DepthEquiv_val
attribute [local simp] FourierJacobi.Analysis.i1r10Equiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
open FourierJacobi.Algebra
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) = ((1-t^2)^2 * (T*U) * 1 * t^2 * (1 - (T * V) * t / d)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring
end FourierJacobi.Analysis
