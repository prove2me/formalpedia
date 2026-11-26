-- Prove2me | solution 1 for FourierJacobi.Analysis.masterTerm_damping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:36.916794+00:00
-- url     : https://prove2.me/submissions/f2c0462c-841d-4654-aec0-9c2514485a36

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Analysis_MasterDamping
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_damping

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations Filter
open scoped Topology
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V T : ℂ) (r : ℤ) (p : LatticeIndex) :
    masterTerm q t d U V T r p =
      T ^ shellHeight r (p.1, p.2.1, p.2.2.1) * masterTerm q t d U V 1 r p := by
  unfold masterTerm
  rw [shellMonomial_damping]
  ring
end FourierJacobi.Analysis
