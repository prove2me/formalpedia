-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:10.000691+00:00
-- url     : https://prove2.me/submissions/c83de423-5a3d-4c83-a62d-a795ed0dc965

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaC
import Theorems.Thm_Formalism_UG_P_fIwasawa_gram_un

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (ρ : Fin n)
    (hρ : ρ < Fin.rev ρ) : ∑ j, σ (M (Fin.rev j) ρ) * M j ρ = 0 := by
  rw [fIwasawa_gram_un σ M hM ρ ρ, if_neg (ne_of_lt hρ)]
end Formalism.UG.P
