-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.unimodUnramUnique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:11:33.49588+00:00
-- url     : https://prove2.me/submissions/df2cf453-8e43-416f-8053-8a5021d53cc0

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
open Polynomial IsLocalRing Matrix
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : UnimodUnramUnique := by
  intro R _ σ hσ R₀ hR₀ _ _ hθ n A hA hdet
  obtain ⟨θ, hθ⟩ := hθ
  let _ : StarRing R :=
    { star := σ
      star_involutive := hσ
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := fun a b => map_add σ a b }
  have hR₀' : ∀ x, x ∈ R₀ ↔ star x = x := hR₀
  have hA' : Aᴴ = A := hA
  obtain ⟨g, hg, hgA⟩ := unimodUnramUnique_main hR₀' hθ n (Fin n) (by simp) A hA' hdet
  exact ⟨g, hg, hgA⟩
end Formalism.HermitianLatticesTheory
