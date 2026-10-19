-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.nsComparison_restrict_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:10:59.094677+00:00
-- url     : https://prove2.me/submissions/ab653f62-e5b0-44f4-ba93-2ebfd5a69048

import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.nsComparison_restrict_eq
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa




open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}


theorem solution (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    (diagMax (nsSymbol d p q)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (nsSymbol d p q)))
      = (lpFiniteModes ℕ).subtype.comp (diagComparisonData d p q).comparison := by
  refine LinearMap.ext fun x => lp.ext (funext fun k => ?_)
  rw [LinearMap.comp_apply, diagMax_coe]
  show _ = ((((diagComparisonData d p q).comparison x : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) k
  unfold ComparisonData.comparison
  erw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.sum_apply]
  simp only [LinearMap.id_apply, Submodule.coe_add,
    Submodule.coe_sum, lp.coeFn_add, lp.coeFn_sum, Pi.add_apply, Finset.sum_apply, LinearMap.comp_apply]
  simp [diagComparisonData, BookProof.NavierStokesFlow.DiagonalEsa.diagFun,
    MomentumEsa.nsSymbol, Finset.sum_mul, add_mul, pow_two, mul_assoc]
  rfl

