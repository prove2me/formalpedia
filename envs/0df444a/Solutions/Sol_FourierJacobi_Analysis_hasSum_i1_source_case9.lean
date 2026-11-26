-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i1_source_case9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:52:35.95275+00:00
-- url     : https://prove2.me/submissions/55fda69f-0da3-4cb9-9277-6ea4ea0c3df0

import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Definitions.Def_FourierJacobi_Analysis_I1SourceRows
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r9_master
import Theorems.Thm_FourierJacobi_Analysis_i1r9_value_eq


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 15 => masterTerm q t d U V T 1 p.val)
      (regionTerms t d (T*U) (T*V) 23) := by
  have hs := hasSum_i1r9_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r9_value_eq q t d U V T ht hd hqt h] at hs
  exact hs
end FourierJacobi.Analysis
