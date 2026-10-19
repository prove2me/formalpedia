-- Prove2me | solution 2 for BookProof.NavierStokesFlow.MomentumEsa.nsComparison_ikebeKato
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:12:20.82852+00:00
-- url     : https://prove2.me/submissions/b62f8df4-2b20-447a-aefd-37a3c32998b0

import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_symmetricOn
-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.nsComparison_ikebeKato
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
theorem h43_diag_esa {ι : Type*} (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((diagMax c).comp (Submodule.inclusion (finiteModes_le_maxDom c))) :=
  IkebeKato.essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds c hc (diagMax c) 1 0 0
    (IkebeKato.diagMax_symmetricOn c) le_rfl (fun x => by simp) (fun x => by simp [commForm])

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.MomentumEsa BookProof.NavierStokesFlow.FarisLavineLift BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData LpNat BookProof.FarisLavine IkebeKato DiagonalEsa in
theorem h44_restrict (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    (diagMax (MomentumEsa.nsSymbol d p q)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (MomentumEsa.nsSymbol d p q)))
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

theorem solution (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((lpFiniteModes ℕ).subtype.comp (diagComparisonData d p q).comparison) := by
  have h := h43_diag_esa (MomentumEsa.nsSymbol d p q) fun k => by
    unfold MomentumEsa.nsSymbol; positivity
  rw [h44_restrict] at h
  exact h

