-- Prove2me | solution 1 for Formalism.UG.P.satakeGL_inv_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:07.394938+00:00
-- url     : https://prove2.me/submissions/600eeb3e-2da3-45b1-b56d-244723d8e7b6

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat

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
theorem _root_.solution {π : L} (hπ : π ≠ 0) (S S' : Finset (Fin n)) (c : satakePairs S → O)
    (c' : satakePairs S' → O) (a l : Fin n) :
    (((satakeGL O hπ S c)⁻¹ * satakeGL O hπ S' c' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a l =
      (if a ∈ S then π⁻¹ else 1) * ((1 - satakeN O S c) * (1 + satakeN O S' c')) a l *
        (if l ∈ S' then π else 1) := by
  show (satakeD π⁻¹ S * (1 - satakeN O S c) * ((1 + satakeN O S' c') * satakeD π S')) a l = _
  rw [← Matrix.mul_assoc, satakeD, satakeD, Matrix.mul_diagonal, Matrix.mul_assoc, Matrix.diagonal_mul]
end Formalism.UG.P
