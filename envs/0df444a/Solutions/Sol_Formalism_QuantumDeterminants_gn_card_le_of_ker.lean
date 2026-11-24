-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gn_card_le_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:46.634246+00:00
-- url     : https://prove2.me/submissions/e55c53f2-8495-45db-9c74-98955884e9c0

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution {S : Type*} [Fintype S] {m : ℕ} (f : (S → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hf : ∀ v, f v = 0 → v = 0) : Fintype.card S ≤ m := by
  have hinj : Function.Injective f := by
    intro a b hab
    exact sub_eq_zero.mp (hf (a - b) (by rw [map_sub, hab, sub_self]))
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card] using h
end Formalism.QuantumDeterminants
