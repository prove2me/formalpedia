-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.GeV.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:59:06.74179+00:00
-- url     : https://prove2.me/submissions/70e136c5-c6f6-4cf8-bf19-6ad7bad49884

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_vw_add

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
theorem _root_.solution {w : Pl K} {c : ℝ} {x y : K} (hx : GeV w c x) (hy : GeV w c y) :
    GeV w c (x + y) := by
  unfold GeV at *
  rcases hx with hx | hx
  · rw [hx, zero_add]; exact hy
  rcases hy with hy | hy
  · rw [hy, add_zero]; exact Or.inr hx
  by_cases hx0 : x = 0
  · rw [hx0, zero_add]; exact Or.inr hy
  by_cases hy0 : y = 0
  · rw [hy0, add_zero]; exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  right
  have h := vw_add w x y hx0 hy0 hxy
  have h2 : min (vw w x : ℝ) (vw w y : ℝ) ≤ (vw w (x + y) : ℝ) := by exact_mod_cast h
  exact le_trans (le_min hx hy) h2
end GeV
end Formalism.PairingDivisionLocalBalance
