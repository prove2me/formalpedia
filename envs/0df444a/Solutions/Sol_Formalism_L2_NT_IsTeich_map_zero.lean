-- Prove2me | solution 1 for Formalism.L2.NT.IsTeich.map_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:58:30.40071+00:00
-- url     : https://prove2.me/submissions/e9706c73-4c2e-46ff-8e1b-22645ebe9f55

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.Host
namespace Formalism.L2.NT
namespace IsTeich
theorem _root_.solution {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {p : ℕ} [Fact p.Prime]
    {κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p} {t : Formalism.CyclotomicNorms.Fbar p →* Ω} (h : IsTeich A κ t) : t 0 = 0 := by
  have h0 : t 0 * t 0 = t 0 := by rw [← map_mul, mul_zero]
  by_contra hne
  have h1 : t 0 = 1 := mul_left_cancel₀ hne (by rw [h0, mul_one])
  obtain ⟨hx, ex⟩ := h 0
  have : (⟨t 0, hx⟩ : A) = 1 := Subtype.ext h1
  rw [this, map_one, map_one] at ex
  exact one_ne_zero ex
end IsTeich
end Formalism.L2.NT
