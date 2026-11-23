-- Prove2me | solution 1 for DensInertW.diag_of_hyps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:37.776873+00:00
-- url     : https://prove2.me/submissions/a52f6f66-1727-4e95-8cbc-867bbf772ffc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_HermitianDiagonalization
import Theorems.Thm_DensInertW_diag_orth_family
import Theorems.Thm_DensInertW_Sub_hf_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
open DensInertW
open DensInertW.Sub
variable {L : Type} [Field L]
namespace DensInertW
theorem _root_.solution {m q : ℕ} (B : Matrix (Fin m) (Fin m) L)
    (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (hinv : ∀ a : L, (a ^ q) ^ q = a)
    (hB : IsHerm q B) (htr : ∀ z : L, z ≠ 0 → ∃ c : L, c * z + (c * z) ^ q ≠ 0) :
    ∃ P : Matrix (Fin m) (Fin m) L, IsUnit P.det ∧ ∃ (w : Fin m → L) (r : ℕ), r ≤ m ∧
        P * B * (P.map (fun y => y ^ q)).transpose = Matrix.diagonal w ∧
        (∀ i, w i ≠ 0 ↔ i.val < r) ∧ (∀ i, w i ^ q = w i) := by
  obtain ⟨v, r, hr, -, hli, horth, hdiag⟩ := diag_orth_family hadd hinv hB htr m ⊤
    (by rw [finrank_top, Module.finrank_fin_fun])
  refine ⟨Matrix.of fun i => v i, ?_, fun i => hf q B (v i) (v i), r, hr, ?_, hdiag, fun i => ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hli)
  · ext i j
    have e : (Matrix.of (fun i => v i) * B * ((Matrix.of fun i => v i).map fun y => y ^ q).transpose) i j =
        hf q B (v i) (v j) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, hf,
        Finset.sum_mul]
      exact Finset.sum_comm
    rw [e, Matrix.diagonal_apply]
    split_ifs with h
    · rw [h]
    · exact horth i j h
  · exact (hf_symm hadd hinv hB (v i) (v i)).symm
end DensInertW
