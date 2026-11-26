-- Prove2me | solution 1 for BKAR.Forest.differentialIdentityAt_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:33:16.145577+00:00
-- url     : https://prove2.me/submissions/a4e77973-5032-454c-89c3-02e64c86925a

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_empty_activeEdgePartialSum
import Theorems.Thm_BKAR_Forest_differentialIdentityAt_of_differentiableAt
import Theorems.Thm_BKAR_Forest_empty_interpWithFill


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (u : (Forest.empty V).EdgeParam → ℝ)
    {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ (constantConfig t)) :
    deriv (fun s : ℝ => ρ (constantConfig s)) t =
      Finset.sum (Finset.univ : Finset (Edge V))
        (fun e => partialDeriv e ρ (constantConfig t)) := by
  have hρ' :
      DifferentiableAt ℝ ρ ((Forest.empty V).interpWithFill u t) := by
    rw [Forest.empty_interpWithFill u t]
    exact hρ
  have hidentity :=
    (Forest.empty V).differentialIdentityAt_of_differentiableAt u hρ'
  rw [ActiveEdgeDerivIdentityAt] at hidentity
  have hcurve :
      (fun s : ℝ => ρ ((Forest.empty V).interpWithFill u s)) =
        fun s : ℝ => ρ (constantConfig s) := by
    funext s
    rw [Forest.empty_interpWithFill u s]
  rw [hcurve, empty_activeEdgePartialSum u ρ t] at hidentity
  exact hidentity
end BKAR.Forest
