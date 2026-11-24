-- Prove2me | solution 1 for Formalism.L2.NT.IsTeich.injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:59:42.825084+00:00
-- url     : https://prove2.me/submissions/d6e74abf-4808-434a-87d6-cc847fc31aaa

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
    {κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p} {t : Formalism.CyclotomicNorms.Fbar p →* Ω} (h : IsTeich A κ t) :
    Function.Injective t := by
  intro x y hxy
  obtain ⟨hx, ex⟩ := h x
  obtain ⟨hy, ey⟩ := h y
  rw [← ex, ← ey]
  congr 2
  exact Subtype.ext hxy
end IsTeich
end Formalism.L2.NT
