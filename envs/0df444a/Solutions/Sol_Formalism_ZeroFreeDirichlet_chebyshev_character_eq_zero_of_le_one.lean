-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.chebyshev_character_eq_zero_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:05.898991+00:00
-- url     : https://prove2.me/submissions/99ca85c6-6c57-4ce1-9685-3bf4b4e0394b

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {x : ℝ} (hx : x ≤ 1) : Schi χ x = 0 := by
  unfold Schi
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_Icc] at hn
  have h1 : ⌊x⌋₊ ≤ 1 := (Nat.floor_mono hx).trans_eq Nat.floor_one
  have hn1 : n = 1 := by omega
  subst hn1
  simp
end Formalism.ZeroFreeDirichlet
