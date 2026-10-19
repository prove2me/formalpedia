-- Prove2me | solution 2 for BookProof.QgCouplingDGammaSum.coupling_quadForm_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:44:53.321716+00:00
-- url     : https://prove2.me/submissions/80e05a93-ac0e-4b29-b6fa-b1d656f052c3

import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_finsetSum_col_eq
import Theorems.Thm_BookProof_FockSecondQuantization_dGammaOp_quadForm_nonneg
import Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_add_col
import Theorems.Thm_BookProof_QgCouplingDGammaSum_isPosCol_numberCol
-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.coupling_quadForm_le
open BookProof.FockSecondQuantization
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}
theorem h44qg_quad_sum {κ : Type*} (s : Finset κ) (cols : κ → ℕ → (ℕ →₀ ℂ))
    (x : lpFiniteModes Conf) :
    quadForm (dGammaOp (fun k => ∑ i ∈ s, cols i k)) x
      = ∑ i ∈ s, quadForm (dGammaOp (cols i)) x := by
  unfold quadForm
  rw [BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col_eq, LinearMap.sum_apply, inner_sum,
    Complex.re_sum]

theorem h44qg_le {κ : Type*} {s : Finset κ} {cols : κ → ℕ → (ℕ →₀ ℂ)}
    (hpos : ∀ i ∈ s, IsPosCol (cols i)) {i : κ} (hi : i ∈ s) (x : lpFiniteModes Conf) :
    quadForm (dGammaOp (cols i)) x
      ≤ quadForm (dGammaOp (fun k => ∑ j ∈ s, cols j k)) x := by
  rw [h44qg_quad_sum]
  exact Finset.single_le_sum (f := fun j => quadForm (dGammaOp (cols j)) x)
    (fun j hj => BookProof.FockSecondQuantization.dGammaOp_quadForm_nonneg (hpos j hj) x) hi

theorem solution {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)}
    (hpos : ∀ i ∈ s, IsPosCol (cols i)) {i : ι} (hi : i ∈ s) (x : lpFiniteModes Conf) :
    quadForm (dGammaOp (cols i)) x
      ≤ quadForm (dGammaOp (fun k => ∑ j ∈ s, cols j k)) x := by
  exact h44qg_le hpos hi x

