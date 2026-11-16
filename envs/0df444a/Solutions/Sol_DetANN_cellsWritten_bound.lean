-- Prove2me | solution 1 for DetANN.cellsWritten_bound
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-15T08:17:34.797194+00:00
-- url     : https://prove2.me/submissions/d0994eb9-f259-4382-b10a-4c12e12d57bf

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_DetANN_DataStructure
import Theorems.Thm_PNormRegLib_bounded_run

open DetANN

theorem solution (P : PNormReg.Program) (X : ℤ) (s : PNormReg.State)
    (hs : PNormRegLib.PBounded X s) (hlit : PNormRegLib.LitBound P X) (hX : 1 ≤ X) (t : ℕ) :
    ∀ c ∈ cellsWritten P s t, |c.2| ≤ X * 2 ^ t := by
  intro c hc
  simp only [cellsWritten, Finset.mem_biUnion, Finset.mem_range, Option.mem_toFinset,
    Option.mem_def] at hc
  obtain ⟨i, hi, hc⟩ := hc
  have hb := PNormRegLib.bounded_run P detTape X s hs hlit hX i
  have hmono : X * 2 ^ i ≤ X * 2 ^ t :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hi.le) (by linarith)
  unfold writtenCell at hc
  split_ifs at hc
  split at hc
  · cases hc; exact (hb.1 _).trans hmono
  · cases hc; exact (hb.1 _).trans hmono
  · cases hc
