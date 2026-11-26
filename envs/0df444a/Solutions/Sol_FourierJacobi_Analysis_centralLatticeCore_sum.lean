-- Prove2me | solution 1 for FourierJacobi.Analysis.centralLatticeCore_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:11:18.37009+00:00
-- url     : https://prove2.me/submissions/3d67f42d-f2ac-4fc3-a978-d087a3537f52

import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
import Definitions.Def_FourierJacobi_Analysis_CentralWeylSeries

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (a b d : ℂ) (T : ℝ) :
    (∑ r : Fin 3, centralLatticeCore q a b d T r) = latticeCore q a b d T := by
  unfold centralLatticeCore latticeCore
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  ring
end FourierJacobi.Analysis
