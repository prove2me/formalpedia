-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crRho_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:14:32.745723+00:00
-- url     : https://prove2.me/submissions/793bdf96-8829-45ef-8727-a5450729f1fb

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n)
    (hβ : Function.Injective β) (τ : T) (kk : Fin (r τ)) :
    (crRho R β).mapMatrix (crMinor r n R β τ kk) =
      Matrix.diagonal (fun q => X ⟨τ, Fin.castLE kk.isLt q, β ⟨τ, Fin.castLE kk.isLt q⟩⟩) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [crMinor, crRho]
  · have hne : β ⟨τ, Fin.castLE kk.isLt j⟩ ≠ β ⟨τ, Fin.castLE kk.isLt i⟩ := by
      intro h'
      have h3 : Fin.castLE kk.isLt j = Fin.castLE kk.isLt i := eq_of_heq (Sigma.mk.inj (hβ h')).2
      exact h (Fin.castLE_injective _ h3).symm
    simp [crMinor, crRho, Matrix.diagonal_apply_ne _ h, hne]
end Formalism.L2.Pj.Crude
