-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.GeV.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:14:35.53383+00:00
-- url     : https://prove2.me/submissions/93042b13-12d0-4c1c-8f9a-d1d1285847f0

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_GeV_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
open Formalism Formalism.PairingDivisionLocalBalance
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.PairingDivisionLocalBalance
namespace GeV
theorem _root_.solution {w : Pl K} {c : ℝ} {ι : Type} (s : Finset ι) (f : ι → K)
    (h : ∀ i ∈ s, GeV w c (f i)) : GeV w c (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f (GeV w c) (fun a b ha hb => GeV.add ha hb) (Or.inl rfl) h
end GeV
end Formalism.PairingDivisionLocalBalance
