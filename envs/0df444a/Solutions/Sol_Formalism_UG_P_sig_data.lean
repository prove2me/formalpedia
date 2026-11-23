-- Prove2me | solution 1 for Formalism.UG.P.sig_data
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:45.606469+00:00
-- url     : https://prove2.me/submissions/3f4c29b9-d12e-429b-b5a0-5d1dbdbf9c34

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Theorems.Thm_Formalism_UG_P_cT_conj_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (J : Matrix n n ℂ) (p q : ℕ) (h : HasSignature J p q) :
    Fintype.card n = p + q ∧ ∃ Q : Matrix n (Fin p ⊕ Fin q) ℂ, Qᴴ * J * Q = Jpq p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨by rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin], ?_⟩
  refine ⟨(P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e id, ?_⟩
  rw [cT_conj_eq] at hP

  have hJ : J = (J.reindex e e).submatrix e e := by
    ext i j; simp
  rw [hJ, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id]
  exact hP
end Formalism.UG.P
