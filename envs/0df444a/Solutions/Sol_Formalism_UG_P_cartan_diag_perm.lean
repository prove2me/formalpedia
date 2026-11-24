-- Prove2me | solution 1 for Formalism.UG.P.cartan_diag_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:07.866801+00:00
-- url     : https://prove2.me/submissions/9f4d8da5-341b-4afd-b0b2-1d66c2bf4a75

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan

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
variable {L : Type} [Field L] (O : Subring L) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
namespace Formalism.UG.P
theorem _root_.solution {m : ℕ} (d : Fin m → L) (σ : Equiv.Perm (Fin m)) :
    Matrix.diagonal d = σ.symm.toPEquiv.toMatrix * Matrix.diagonal (d ∘ σ) * σ.toPEquiv.toMatrix := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply, h]
end Formalism.UG.P
