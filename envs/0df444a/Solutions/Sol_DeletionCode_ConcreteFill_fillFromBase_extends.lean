-- Prove2me | solution 1 for DeletionCode.ConcreteFill.fillFromBase_extends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:22.139647+00:00
-- url     : https://prove2.me/submissions/378581a7-3256-4f30-a8ff-57ae1e35ee98

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SeedLookup
import Definitions.Def_DeletionCode_ConcreteFill
import Theorems.Thm_DeletionCode_PartialWords_writeBits_extends


set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteFill
open Windows PartialWords
namespace DeletionCode.ConcreteFill
theorem _root_.solution (x : Letters) (n k L : ℕ)
    (s t : Memory) (m start r : ℕ)
    (h : fillFromBase x n k L s m start r = some t) : Extends s t := by
  unfold fillFromBase at h
  cases hseed : readBits s (start + r) k with
  | none => simp [hseed] at h
  | some seed =>
    simp only [hseed, Option.bind_some] at h
    cases hbits : SeedLookup.recoverWindow x n k L r seed with
    | none => simp [hbits] at h
    | some bits =>
      simp only [hbits, Option.bind_some] at h
      exact writeBits_extends s t m start L bits h
end DeletionCode.ConcreteFill
