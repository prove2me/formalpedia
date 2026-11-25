-- Prove2me | solution 1 for Formalism.UG.P.fSatake_nontriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:23:51.475999+00:00
-- url     : https://prove2.me/submissions/7edead06-d5bc-4c32-9ba3-4e8997bbf1f3

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace Formalism.UG.P
theorem _root_.solution {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) :
    (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial := by
  obtain ⟨-, -, -, hv, -⟩ := hU
  refine ⟨ϖ, ?_, ?_⟩
  · rw [hv]; exact WithZero.coe_ne_zero
  · rw [hv]
    intro h1
    have := WithZero.coe_injective (h1.trans WithZero.coe_one.symm)
    exact absurd (Multiplicative.ofAdd.injective (this.trans ofAdd_zero.symm)) (by norm_num)
end Formalism.UG.P
