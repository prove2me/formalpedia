-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.coupling_quadForm_le_comparison
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:36:13.788618+00:00
-- url     : https://prove2.me/submissions/7102d459-6e54-474a-abe7-a41d0c0c7e64
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.coupling_quadForm_le_comparison
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Theorems.Thm_BookProof_QgCouplingDGammaSum_coupling_quadForm_le
import Theorems.Thm_BookProof_QgCouplingDGammaSum_isPosCol_numberCol
import Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_add_col
import Theorems.Thm_BookProof_FockSecondQuantization_dGammaOp_quadForm_nonneg
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.QgCouplingDGammaSum




open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)}
    (hpos : ∀ i ∈ s, IsPosCol (cols i)) {i : ι} (hi : i ∈ s) (x : lpFiniteModes Conf) :
    quadForm (dGammaOp (cols i)) x ≤ quadForm (dGammaOp (comparisonCol s cols)) x := by

  have hadd : quadForm (dGammaOp (comparisonCol s cols)) x
      = quadForm (dGammaOp (fun k => ∑ j ∈ s, cols j k)) x
        + quadForm (dGammaOp numberCol) x := by
    have hsplit : dGammaOp (comparisonCol s cols) x
        = dGammaOp (fun k => ∑ j ∈ s, cols j k) x + dGammaOp numberCol x :=
      dGammaOp_add_col (fun k => ∑ j ∈ s, cols j k) numberCol x
    simp only [quadForm, hsplit, inner_add_right, Complex.add_re]
  rw [hadd]
  have h1 : quadForm (dGammaOp (cols i)) x
      ≤ quadForm (dGammaOp (fun k => ∑ j ∈ s, cols j k)) x :=
    coupling_quadForm_le hpos hi x
  have h2 : 0 ≤ quadForm (dGammaOp numberCol) x :=
    dGammaOp_quadForm_nonneg isPosCol_numberCol x
  linarith
