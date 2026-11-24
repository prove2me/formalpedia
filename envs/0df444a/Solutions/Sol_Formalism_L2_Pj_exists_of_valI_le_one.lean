-- Prove2me | solution 1 for Formalism.L2.Pj.exists_of_valI_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:16:51.277411+00:00
-- url     : https://prove2.me/submissions/f2ddb68c-b249-4c5a-a76c-c1cc5b8126ed

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open Matrix IsDedekindDomain
variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]
namespace Formalism.L2.Pj
theorem _root_.solution {x : F} (h : valI V x ≤ 1) : ∃ a : V, algebraMap V F a = x := by
  have hall : ∀ w : IsDedekindDomain.HeightOneSpectrum V, w = IsDiscreteValuationRing.maximalIdeal V := by
    intro w
    first
    | exact IsDedekindDomain.HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal w.isMaximal)
    | (ext1; exact IsLocalRing.eq_maximalIdeal w.isMaximal)
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F x
    (fun w => by rw [hall w]; exact h)
  exact ⟨a, ha⟩
end Formalism.L2.Pj
