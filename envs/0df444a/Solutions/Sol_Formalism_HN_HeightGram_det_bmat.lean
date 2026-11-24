-- Prove2me | solution 1 for Formalism.HN.HeightGram.det_bmat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:21.958281+00:00
-- url     : https://prove2.me/submissions/96f6afed-3ecf-43cc-878a-6bf7fdeb65e0

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Theorems.Thm_Formalism_HN_HeightGram_det_realif

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.HeightGram
variable {P S : Type} [Fintype P] [DecidableEq P] [Fintype S] [DecidableEq S] {j : ℕ}
namespace Formalism.HN.HeightGram
theorem _root_.solution (G : P → Matrix (Fin j) (Fin j) ℂ) :
    (bmat G).det = ∏ v, Complex.normSq (G v).det := by
  let f : (P × Fin 2) × Fin j ≃ (Fin 2 × Fin j) × P :=
    { toFun := fun x => ((x.1.2, x.2), x.1.1)
      invFun := fun y => ((y.2, y.1.1), y.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : (bmat G).submatrix f.symm f.symm = Matrix.blockDiagonal fun v => realif (G v) := by
    ext ⟨⟨s, k⟩, v⟩ ⟨⟨t, k'⟩, w⟩
    simp only [Matrix.submatrix_apply, Matrix.blockDiagonal_apply, bmat, Matrix.of_apply, f,
      Equiv.coe_fn_symm_mk]
    <;> split_ifs <;> simp_all
  rw [← Matrix.det_submatrix_equiv_self f.symm (bmat G), h, Matrix.det_blockDiagonal]
  simp only [det_realif]
end Formalism.HN.HeightGram
