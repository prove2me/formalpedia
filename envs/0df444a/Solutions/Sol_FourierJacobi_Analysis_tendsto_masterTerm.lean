-- Prove2me | solution 1 for FourierJacobi.Analysis.tendsto_masterTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:14.184441+00:00
-- url     : https://prove2.me/submissions/3c99af43-03e2-413a-84c8-6909a6183250

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Analysis_MasterDamping
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_damping
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations Filter
open scoped Topology
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V : ℂ) (r : ℤ) (p : LatticeIndex) :
    Tendsto (fun T : ℝ => masterTerm q t d U V (T : ℂ) r p)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (masterTerm q t d U V 1 r p)) := by
  have he : (fun T : ℝ => masterTerm q t d U V (T : ℂ) r p) =
      (fun T : ℝ => (T : ℂ) ^ shellHeight r (p.1, p.2.1, p.2.2.1) *
        masterTerm q t d U V 1 r p) := by
    funext T
    exact masterTerm_damping q t d U V (T : ℂ) r p
  rw [he]
  have hc : ContinuousAt (fun T : ℝ =>
      (T : ℂ) ^ shellHeight r (p.1, p.2.1, p.2.2.1) *
        masterTerm q t d U V 1 r p) 1 := by fun_prop
  simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
end FourierJacobi.Analysis
