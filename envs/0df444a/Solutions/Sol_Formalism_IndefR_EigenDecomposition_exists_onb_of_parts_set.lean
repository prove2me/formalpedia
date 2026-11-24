-- Prove2me | solution 1 for Formalism.IndefR.EigenDecomposition.exists_onb_of_parts_set
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:39.250965+00:00
-- url     : https://prove2.me/submissions/78d43ffd-24fd-4937-9f6c-0b98cbc089e7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_EigenDecomposition
import Theorems.Thm_Formalism_IndefR_EigenDecomposition_exists_onb_of_parts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Formalism Formalism.IndefR Formalism.IndefR.EigenDecomposition
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
namespace Formalism.IndefR.EigenDecomposition
theorem _root_.solution {L : Type*} (S : Set L) (hS : S.Finite) (P : L → Submodule ℂ H)
    (horth : ∀ c ∈ S, ∀ d ∈ S, c ≠ d → P c ⟂ P d) (htop : ⨆ c ∈ S, P c = ⊤) :
    ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ H) (lab : Fin n → L),
      (∀ k, lab k ∈ S) ∧ ∀ k, b k ∈ P (lab k) := by
  classical
  have hfin : Finite S := hS.to_subtype
  obtain ⟨n, b, lab, hb⟩ := exists_onb_of_parts (fun c : S => P c.1)
    (fun c d hcd => horth c.1 c.2 d.1 d.2 (fun h => hcd (Subtype.ext h)))
    (by rw [← htop, iSup_subtype'])
  exact ⟨n, b, fun k => (lab k).1, fun k => (lab k).2, hb⟩
end Formalism.IndefR.EigenDecomposition
