-- Prove2me | solution 2 for BookProof.QgCouplingDGammaSum.coupling_quadForm_le_comparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:45:09.173753+00:00
-- url     : https://prove2.me/submissions/3af4bec3-d454-4e44-ba23-79d3424ea32e

import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_finsetSum_col_eq
import Theorems.Thm_BookProof_FockSecondQuantization_dGammaOp_quadForm_nonneg
import Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_add_col
import Theorems.Thm_BookProof_QgCouplingDGammaSum_isPosCol_numberCol
-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.coupling_quadForm_le_comparison
open BookProof.FockOneParticleGap
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
    quadForm (dGammaOp (cols i)) x ≤ quadForm (dGammaOp (comparisonCol s cols)) x := by
  have h1 : quadForm (dGammaOp (comparisonCol s cols)) x
      = quadForm (dGammaOp (fun k => ∑ j ∈ s, cols j k)) x
        + quadForm (dGammaOp BookProof.QgCouplingDGammaSum.numberCol) x := by
    unfold quadForm comparisonCol
    rw [BookProof.QgCouplingDGammaSum.dGammaOp_add_col (fun k => ∑ j ∈ s, cols j k)
      BookProof.QgCouplingDGammaSum.numberCol, inner_add_right, Complex.add_re]
  rw [h1]
  exact le_add_of_le_of_nonneg (h44qg_le hpos hi x)
    (BookProof.FockSecondQuantization.dGammaOp_quadForm_nonneg
      BookProof.QgCouplingDGammaSum.isPosCol_numberCol x)

