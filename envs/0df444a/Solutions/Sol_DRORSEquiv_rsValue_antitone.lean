-- Prove2me | solution 1 for DRORSEquiv.rsValue_antitone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T13:49:32.601121+00:00
-- url     : https://prove2.me/submissions/fd2306f6-e5be-4cc2-bbc3-842c3887af6c

import Mathlib
import Definitions.Def_DRORSEquiv_rsValue

open DRORSEquiv in
theorem solution {E Ω : Type*} {S : ℕ} (M : Model E Ω S) : Antitone (rsValue M) := by
  intro τ τ' h
  unfold rsValue
  refine iInf_mono fun x => iInf_mono fun k => ?_
  refine iInf_mono' fun hf => ⟨⟨hf.1, hf.2.1, le_trans hf.2.2 (by exact_mod_cast h)⟩, le_rfl⟩
