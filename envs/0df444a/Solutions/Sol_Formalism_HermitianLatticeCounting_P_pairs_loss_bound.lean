-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.pairs_loss_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:44.931962+00:00
-- url     : https://prove2.me/submissions/310a86b5-6b8a-46c4-a627-d30d5b8afc68

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition

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
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open CellDecomposition
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.PairsLoss := by
  intro C s k D' D'' NT Hh S' S'' hsk hH hS' hS'' hD' hD'' hNT h1 h2 h3
  have hb : D' * D'' * NT ≤ Hh ^ 3 * (S' * S'') ^ 2 := by
    calc D' * D'' * NT ≤ (Hh * S' ^ 2) * (Hh * S'' ^ 2) * Hh := by gcongr
      _ = Hh ^ 3 * (S' * S'') ^ 2 := by ring
  have hSS : 1 ≤ S' * S'' := by nlinarith
  calc (D' * D'' * NT) ^ (C * s) ≤ (Hh ^ 3 * (S' * S'') ^ 2) ^ (C * s) :=
        pow_le_pow_left₀ (by positivity) hb _
    _ = Hh ^ (3 * C * s) * (S' * S'') ^ (2 * C * s) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc 3, mul_assoc 2]
    _ ≤ Hh ^ (3 * C * s) * (S' * S'') ^ (2 * C * k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_right₀ hSS (Nat.mul_le_mul_left _ hsk)
end Formalism.HermitianLatticeCounting.P
