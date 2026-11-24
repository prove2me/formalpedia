-- Prove2me | solution 1 for Formalism.UG.P.entries_mem_of_mem_stabGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:08.934929+00:00
-- url     : https://prove2.me/submissions/ce9c769d-45d4-41d8-98dd-57bb987a5284

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Theorems.Thm_P2M_Formalism_UG_P_mem_stdLat_iff__3723b4f8990e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Matrix
variable {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (h : GL n A) (hh : h ∈ stabGL (stdLat (n := n) (A := A) R))
    (i j : n) : (h : Matrix n n A) i j ∈ Set.range (algebraMap R A) := by
  have hmem : (Pi.single j 1 : n → A) ∈ stdLat (n := n) (A := A) R := by
    rw [mem_stdLat_iff']
    intro k
    by_cases hk : k = j
    · subst hk; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.single_apply, hk]⟩
  have h2 := ((hh (Pi.single j 1)).1 hmem)
  rw [mem_stdLat_iff'] at h2
  have h3 := h2 i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h3
end Formalism.UG.P
