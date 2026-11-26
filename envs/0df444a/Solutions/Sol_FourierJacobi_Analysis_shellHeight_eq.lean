-- Prove2me | solution 1 for FourierJacobi.Analysis.shellHeight_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:36:59.334967+00:00
-- url     : https://prove2.me/submissions/fd4c596c-22cf-410b-b6f9-f9bdd186c409

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Analysis_MasterDamping
import Theorems.Thm_FourierJacobi_Analysis_shell_exponents_nonnegative
import Theorems.Thm_FourierJacobi_Analysis_shell_height_eq


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations Filter
open scoped Topology
namespace FourierJacobi.Analysis
theorem _root_.solution (r : ℤ) (p : ℤ × ℤ × ℤ) (c : ℕ) :
    shellHeight r p = ((cartanIndices r p.1 p.2.1 p.2.2 c).1 / 2).toNat +
      (cartanIndices r p.1 p.2.1 p.2.2 c).2.toNat := by
  have hh := shell_height_eq r p.1 p.2.1 p.2.2 c
  have hn := shell_exponents_nonnegative r p.1 p.2.1 p.2.2 c
  unfold shellHeight
  omega
end FourierJacobi.Analysis
