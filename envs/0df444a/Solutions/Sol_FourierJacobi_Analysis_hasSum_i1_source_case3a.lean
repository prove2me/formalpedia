-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i1_source_case3a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:49.95517+00:00
-- url     : https://prove2.me/submissions/9f430479-6d2f-4b2a-bcb5-298981d899d5

import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Definitions.Def_FourierJacobi_Analysis_I1SourceRows
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r3ae_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r3ao_master
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1r10DepthEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1r10Equiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1r3ae_value_eq
import Theorems.Thm_FourierJacobi_Analysis_i1r3ao_value_eq
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i1r10DepthEquiv_val
attribute [local simp] FourierJacobi.Analysis.i1r10Equiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (Sum.elim (fun p : I1Cell 2 => masterTerm q t d U V T 1 p.val)
        (fun p : I1Cell 3 => masterTerm q t d U V T 1 p.val))
      (regionTerms t d (T*U) (T*V) 12) := by
  have h1 := hasSum_i1r3ae_master q t d U V T ht hq0 hq1 hqt h
  have h2 := hasSum_i1r3ao_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r3ae_value_eq q t d U V T ht hd hqt h] at h1
  rw [i1r3ao_value_eq q t d U V T ht hd hqt h] at h2
  have hs := h1.sum (f := (Sum.elim (fun p : I1Cell 2 => masterTerm q t d U V T 1 p.val)
        (fun p : I1Cell 3 => masterTerm q t d U V T 1 p.val))) h2
  convert hs using 1
  change regionTerm12 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4) = _
  unfold regionTerm12
  simp only [pow_one]
  ring
end FourierJacobi.Analysis
