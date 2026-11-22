-- Prove2me | solution 1 for Egrs75.SeedWindow.lt_of_log_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:52.872603+00:00
-- url     : https://prove2.me/submissions/8c341d2b-a499-4966-aad2-9dab03ca9adf

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_Egrs75_LogIrrationality
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Definitions.Def_LeanPool_Egrs75_SeedWindow

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.SeedWindow
open Nat
open Egrs75
namespace Egrs75.SeedWindow
theorem _root_.solution {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : Real.log a < Real.log b) : a < b := by
  have := Real.exp_lt_exp.mpr h
  rwa [Real.exp_log ha, Real.exp_log hb] at this
end Egrs75.SeedWindow
