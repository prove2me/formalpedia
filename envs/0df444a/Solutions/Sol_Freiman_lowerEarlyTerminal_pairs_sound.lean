-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_pairs_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:04:52.89895+00:00
-- url     : https://prove2.me/submissions/65de6d11-98fc-4a39-8eea-069f6b303ec8

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_cert_witness_excludes

open Freiman

theorem solution (C : LowerEarlyTerminalCatalog) (hp : ∀ p ∈ C.pairs, lowerEarlyTerminalPairValid C p) : lowerEarlyTerminalPairSound C := by
  intro p hp' r s q hm
  have hw : certWitnessValid (lowerEarlyTerminalWitness C p) := (hp p hp').2.2.2.2
  exact cert_witness_excludes (lowerEarlyTerminalWitness C p) hw r s q hm
