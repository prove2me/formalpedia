-- Prove2me | solution 1 for Formalism.L2.NT.redThrough_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:58:28.186605+00:00
-- url     : https://prove2.me/submissions/233bd1ab-8185-4799-b4f8-92229dfb2b42

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
variable {Ω : Type} [Field Ω]
variable (B : ValuationSubring Ω) {l : ℕ} [Fact l.Prime] (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l)
namespace Formalism.L2.NT
theorem _root_.solution : redThrough B κ 1 = 1 := by
  unfold redThrough
  rw [dif_pos (one_mem B)]
  have : (⟨1, one_mem B⟩ : B) = 1 := rfl
  rw [this, map_one, map_one]
end Formalism.L2.NT
