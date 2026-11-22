-- Prove2me | solution 1 for Egrs75.MathlibAPI.denseRange_log_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:35.736729+00:00
-- url     : https://prove2.me/submissions/e177c0ae-2c6b-44fd-8548-9b609d109114

module
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Definitions.Def_LeanPool_Egrs75_LogIrrationality
public import Theorems.Thm_Egrs75_MathlibAPI_irrational_log_div_log

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.MathlibAPI
open Nat
open Egrs75
namespace Egrs75.MathlibAPI
theorem _root_.solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    DenseRange (· • Real.log p : ℤ → AddCircle (Real.log q)) := by
  rw [AddCircle.denseRange_zsmul_coe_iff]
  exact irrational_log_div_log hp hq hpq
end Egrs75.MathlibAPI
