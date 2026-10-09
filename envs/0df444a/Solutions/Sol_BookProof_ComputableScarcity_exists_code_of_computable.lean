-- Prove2me | solution 1 for BookProof.ComputableScarcity.exists_code_of_computable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:40:56.843416+00:00
-- url     : https://prove2.me/submissions/2fdb48a7-2e5d-4189-8727-8d2b46becc7c

-- Generated from ChapterComputableScarcity.lean — solution of BookProof.ComputableScarcity.exists_code_of_computable
import Mathlib
import Definitions.Def_ChapterComputableScarcity
open BookProof.ComputableScarcity




open Nat.Partrec

open Classical

set_option maxHeartbeats 1000000 in
theorem solution {f : ℕ → ℕ} (hf : Computable f) :
    ∃ c : Code, evalTotal c = f := by

  have h1 : Nat.Partrec (fun n => Part.some (f n)) := Partrec.nat_iff.mp hf.partrec
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp h1
  refine ⟨c, ?_⟩
  funext n
  simp [evalTotal, hc]
