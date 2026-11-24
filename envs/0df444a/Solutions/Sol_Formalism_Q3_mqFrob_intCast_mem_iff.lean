-- Prove2me | solution 1 for Formalism.Q3.mqFrob_intCast_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:12:11.41293+00:00
-- url     : https://prove2.me/submissions/ddf9dfad-8b86-446c-88a9-cefb49626457

import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQFrob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution {E : Type} [Field E] [NumberField E] (p : ℕ)
    (P : Ideal (𝓞 E)) [P.LiesOver (span {(p : ℤ)})] (n : ℤ) :
    (n : 𝓞 E) ∈ P ↔ (p : ℤ) ∣ n := by
  rw [← Ideal.mem_span_singleton, Ideal.over_def P (span {(p : ℤ)}), Ideal.under_def,
    Ideal.mem_comap, eq_intCast]
end Formalism.Q3
