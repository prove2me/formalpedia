-- Prove2me | solution 1 for FairChores.cbarSum_univ_le_nsmul_MMS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:23:24.38455+00:00
-- url     : https://prove2.me/submissions/b58e2074-f2dd-4d39-9c48-84accbb02bb4

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresExamples
import Theorems.Thm_FairChores_cbarSum_le_wtSum
import Theorems.Thm_FairChores_wtSum_univ_le_nsmul_MMS


set_option autoImplicit true
open scoped BigOperators
open FairChores
namespace FairChores
theorem _root_.solution {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
    {c p : T → ℝ} (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) :
    cbarSum c p Finset.univ ≤ n * MMS n c p :=
  le_trans (cbarSum_le_wtSum Finset.univ) (wtSum_univ_le_nsmul_MMS hc hn)
end FairChores
