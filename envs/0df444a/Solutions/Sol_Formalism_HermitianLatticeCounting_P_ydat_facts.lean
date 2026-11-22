-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ydat_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:08.152895+00:00
-- url     : https://prove2.me/submissions/d3aba5d5-fbe6-4486-a1ee-e8406f666069

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {n f : ℕ} {rd g b : ℝ} (hn : 1 ≤ n) (hf : 1 ≤ f) (hrd : 1 ≤ rd) (hg : 1 ≤ g)
    (hb : 2 ≤ b) : 2 ≤ Ydat n f rd g b ∧ (n:ℝ) ≤ Ydat n f rd g b ∧ (f:ℝ) ≤ Ydat n f rd g b ∧
      rd ≤ Ydat n f rd g b ∧ g ≤ Ydat n f rd g b ∧ b ≤ Ydat n f rd g b := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hb1 : (1:ℝ) ≤ b := by linarith
  unfold Ydat
  have hbY : b ≤ (n:ℝ) * f * rd * g * b := by
    calc b = 1 * 1 * 1 * 1 * b := by ring
      _ ≤ _ := by gcongr
  refine ⟨hb.trans hbY, ?_, ?_, ?_, ?_, hbY⟩
  · calc (n:ℝ) = n * 1 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  · calc (f:ℝ) = 1 * f * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  · calc rd = 1 * 1 * rd * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  · calc g = 1 * 1 * 1 * g * 1 := by ring
      _ ≤ _ := by gcongr
end Formalism.HermitianLatticeCounting.P
