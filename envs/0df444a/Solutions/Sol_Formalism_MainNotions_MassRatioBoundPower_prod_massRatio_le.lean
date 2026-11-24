-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioBoundPower.prod_massRatio_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:45:14.145072+00:00
-- url     : https://prove2.me/submissions/a5e0111d-e2b4-4541-b7c8-208ad5ad7a44

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBoundPower
import Theorems.Thm_Formalism_MainNotions_MassRatioBoundPower_mass_ratio_rhs_nonneg
import Theorems.Thm_Formalism_MainNotions_MassRatioBoundPower_mass_ratio_rhs_le_pow_Y

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioBoundPower
open NumberField Formalism.MainNotions.MassRatioZetaBound
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioBoundPower
theorem _root_.solution [StarRing K] (hd : Module.finrank ℚ K ≤ 2 * Formalism.HermitianLatticesTheory.fDeg K) (n : ℕ) {Y : ℝ} (hY : 2 ≤ Y)
    (hn : (n : ℝ) ≤ Y) (hv : 2 * Formalism.HermitianLatticesTheory.vInv K ≤ Y) :
    ∏ M ∈ Finset.Icc 3 n, Formalism.HermitianLatticesTheory.massRatioRightSide K M ≤ Y ^ ((2 * n + cZ) * n * Formalism.HermitianLatticesTheory.fDeg K) := by
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  calc ∏ M ∈ Finset.Icc 3 n, Formalism.HermitianLatticesTheory.massRatioRightSide K M
      ≤ ∏ _M ∈ Finset.Icc 3 n, Y ^ ((2 * n + cZ) * Formalism.HermitianLatticesTheory.fDeg K) :=
        Finset.prod_le_prod (fun M hM => mass_ratio_rhs_nonneg (Finset.mem_Icc.1 hM).1)
          (fun M hM => mass_ratio_rhs_le_pow_Y hd (Finset.mem_Icc.1 hM).1 (Finset.mem_Icc.1 hM).2 hY hn hv)
    _ = (Y ^ ((2 * n + cZ) * Formalism.HermitianLatticesTheory.fDeg K)) ^ (Finset.Icc 3 n).card := Finset.prod_const _
    _ ≤ (Y ^ ((2 * n + cZ) * Formalism.HermitianLatticesTheory.fDeg K)) ^ n := by
        refine pow_le_pow_right₀ (one_le_pow₀ hY1) ?_
        rw [Nat.card_Icc]; omega
    _ = Y ^ ((2 * n + cZ) * n * Formalism.HermitianLatticesTheory.fDeg K) := by rw [← pow_mul]; congr 1; ring
end Formalism.MainNotions.MassRatioBoundPower
