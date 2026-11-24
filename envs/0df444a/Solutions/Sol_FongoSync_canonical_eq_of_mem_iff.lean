-- Prove2me | solution 1 for FongoSync.canonical_eq_of_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:52.608145+00:00
-- url     : https://prove2.me/submissions/a00f951b-2b2d-47fe-a6d0-be9641b4ca98

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
import Theorems.Thm_FongoSync_IsCanonical_unique
import Theorems.Thm_FongoSync_canonical_spec
import Theorems.Thm_FongoSync_isCanonical_of_mem_iff

set_option autoImplicit false
open FongoSync
namespace FongoSync
theorem _root_.solution (E₁ E₂ : List Edge) (same : ∀ e, e ∈ E₁ ↔ e ∈ E₂) :
    canonical E₁ = canonical E₂ := by
  funext g
  exact (isCanonical_of_mem_iff same (canonical_spec E₁ g)).unique (canonical_spec E₂ g)
end FongoSync
