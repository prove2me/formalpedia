-- Prove2me | solution 1 for FongoSync.canonical_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:05:09.050785+00:00
-- url     : https://prove2.me/submissions/c0df073f-f4cd-41e1-ac28-13ba3b0500be

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
import Theorems.Thm_FongoSync_canonical_eq_of_mem_iff

set_option autoImplicit false
open FongoSync
namespace FongoSync
theorem _root_.solution {E₁ E₂ : List Edge} (p : E₁.Perm E₂) : canonical E₁ = canonical E₂ :=
  canonical_eq_of_mem_iff E₁ E₂ fun _ => p.mem_iff
end FongoSync
