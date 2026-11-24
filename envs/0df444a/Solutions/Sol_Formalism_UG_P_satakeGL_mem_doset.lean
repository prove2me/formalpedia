-- Prove2me | solution 1 for Formalism.UG.P.satakeGL_mem_doset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:09:29.678395+00:00
-- url     : https://prove2.me/submissions/8ded5077-6885-48b3-b9a5-715c80549adf

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Theorems.Thm_Formalism_UG_P_satakeU_mem
import Theorems.Thm_Formalism_UG_P_permMatrix_mem_integralGL
import Theorems.Thm_Formalism_UG_P_satake_exists_perm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L] (O : Subring L) {n : ℕ}
variable {O}
variable (O)
namespace Formalism.UG.P
theorem _root_.solution {π : L} (hπ : π ≠ 0) (S : Finset (Fin n)) (c : satakePairs S → O) :
    ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O,
      ((satakeGL O hπ S c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        (a : Matrix (Fin n) (Fin n) L) * diagJ n π S.card * (b : Matrix (Fin n) (Fin n) L) := by
  obtain ⟨σ, hσ⟩ := satake_exists_perm S
  refine ⟨satakeU O S c * satakeP σ, mul_mem (satakeU_mem O S c) (permMatrix_mem_integralGL O σ),
    satakeP σ.symm, permMatrix_mem_integralGL O σ.symm, ?_⟩
  show (1 + satakeN O S c) * satakeD π S =
    (1 + satakeN O S c) * σ.toPEquiv.toMatrix * diagJ n π S.card * σ.symm.toPEquiv.toMatrix
  rw [Matrix.mul_assoc (1 + satakeN O S c), Matrix.mul_assoc (1 + satakeN O S c)]
  congr 1
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
  ext a b
  simp only [Matrix.submatrix_apply, id_eq, satakeD, diagJ, Matrix.diagonal_apply, σ.injective.eq_iff, hσ]
end Formalism.UG.P
