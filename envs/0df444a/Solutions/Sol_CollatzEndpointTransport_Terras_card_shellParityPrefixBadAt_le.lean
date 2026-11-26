-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_shellParityPrefixBadAt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:49:20.099168+00:00
-- url     : https://prove2.me/submissions/74b6dca6-50bb-47a4-8b96-8cc02ab0c611

import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Theorems.Thm_CollatzEndpointTransport_Terras_parityLowerCutoff_cast_le
import Theorems.Thm_CollatzEndpointTransport_Terras_card_dyadic_shell_oddCount_ge_sub_le_hoeffding
import Theorems.Thm_CollatzEndpointTransport_Terras_card_dyadic_shell_oddCount_le_hoeffding


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {M H : ℕ} {t : ℝ} (hHM : H ≤ M)
    (ht0 : 0 ≤ t) (htHalf : t ≤ 1 / 2) :
    ((shellParityPrefixBadAt M H t).card : ℝ) ≤
      (2 : ℝ) ^ M * (2 * Real.exp (-2 * t ^ 2 * H)) := by
  have hcut :
      (parityLowerCutoff t H : ℝ) ≤ (1 / 2 - t) * H :=
    parityLowerCutoff_cast_le htHalf H
  have hlower :
      ((shellLowerPrefixBad M H t).card : ℝ) ≤
        (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) := by
    simpa only [shellLowerPrefixBad] using
      card_dyadic_shell_oddCount_le_hoeffding hHM ht0 hcut
  have hupper :
      ((shellUpperPrefixBad M H t).card : ℝ) ≤
        (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) := by
    simpa only [shellUpperPrefixBad] using
      card_dyadic_shell_oddCount_ge_sub_le_hoeffding hHM ht0 hcut
  have hcardNat :
      (shellParityPrefixBadAt M H t).card ≤
        (shellLowerPrefixBad M H t).card +
          (shellUpperPrefixBad M H t).card := by
    exact Finset.card_union_le _ _
  have hcardReal :
      ((shellParityPrefixBadAt M H t).card : ℝ) ≤
        (shellLowerPrefixBad M H t).card +
          (shellUpperPrefixBad M H t).card := by
    exact_mod_cast hcardNat
  calc
    ((shellParityPrefixBadAt M H t).card : ℝ) ≤
        (shellLowerPrefixBad M H t).card +
          (shellUpperPrefixBad M H t).card := hcardReal
    _ ≤ (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) +
          (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) :=
      add_le_add hlower hupper
    _ = (2 : ℝ) ^ M * (2 * Real.exp (-2 * t ^ 2 * H)) := by ring
end CollatzEndpointTransport.Terras
