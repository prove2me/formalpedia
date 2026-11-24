-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:04.99568+00:00
-- url     : https://prove2.me/submissions/b2ae1c04-ae53-4f41-95ef-56e28aa7d622

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : CostBound := by
  intro C C₂ r Db Del NT Ncc hr hDel hDD hNT hN0 hN
  have hDb : 1 ≤ Db := le_trans hDel hDD
  set X := Db * NT with hX
  have hX1 : 1 ≤ X := by nlinarith
  have hY : Db * Del * NT ≤ X ^ 2 := by
    have : Db * Del * NT ≤ Db * Db * NT := by gcongr
    nlinarith [mul_nonneg (by positivity : 0 ≤ Db * Db * NT) (by linarith : 0 ≤ NT - 1)]
  have hY0 : 0 ≤ Db * Del * NT := by positivity
  have hN' : Ncc ≤ X ^ (2 * (C * r)) := by
    calc Ncc ≤ (Db * Del * NT) ^ (C * r) := hN
      _ ≤ (X ^ 2) ^ (C * r) := by gcongr
      _ = X ^ (2 * (C * r)) := by rw [← pow_mul]
  have hG : Del * NT ≤ X := by rw [hX]; gcongr
  have hG0 : 0 ≤ Del * NT := by positivity
  calc Ncc ^ (2 * (2 * r + 1) ^ 2) * (Del * NT) ^ (2 * (2 * r + 1)) * (Ncc ^ 2) ^ (C₂ * r ^ 2)
      ≤ (X ^ (2 * (C * r))) ^ (2 * (2 * r + 1) ^ 2) * X ^ (2 * (2 * r + 1)) *
          ((X ^ (2 * (C * r))) ^ 2) ^ (C₂ * r ^ 2) := by gcongr
    _ = X ^ (2 * (C * r) * (2 * (2 * r + 1) ^ 2) + 2 * (2 * r + 1) + 2 * (C * r) * 2 * (C₂ * r ^ 2)) := by
        rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
    _ ≤ X ^ ((36 * C + 4 * C * C₂ + 6) * r ^ 3) := by
        apply pow_le_pow_right₀ hX1
        have h1 : (2 * r + 1) ^ 2 ≤ 9 * r ^ 2 := by nlinarith
        have h2 : 2 * (2 * r + 1) ≤ 6 * r ^ 3 := by nlinarith [Nat.pow_le_pow_left hr 3, Nat.pow_le_pow_left hr 2, mul_le_mul hr hr]
        calc 2 * (C * r) * (2 * (2 * r + 1) ^ 2) + 2 * (2 * r + 1) + 2 * (C * r) * 2 * (C₂ * r ^ 2)
            ≤ 2 * (C * r) * (2 * (9 * r ^ 2)) + 6 * r ^ 3 + 2 * (C * r) * 2 * (C₂ * r ^ 2) := by gcongr
          _ = (36 * C + 4 * C * C₂ + 6) * r ^ 3 := by ring
end Formalism.HermitianLatticeCounting.P
