-- Prove2me | solution 1 for Formalism.L2.Th1.G.jetsIn1_rest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:51:43.917559+00:00
-- url     : https://prove2.me/submissions/d4943876-8a81-4c46-b5fd-582b92a084bc

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Several
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_jetAdditive


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
namespace Formalism.L2.Th1.G
theorem _root_.solution {K : Type} [Field K] [CharZero K] {R : Subring K} {l linv ph : PowerSeries K}
    (h : IsLogPair l linv) (h0 : PowerSeries.constantCoeff ph = 0)
    (hj : ∀ i : ℕ, 1 ≤ i → i ≠ 2 → jet l ph i ∈ R) :
    JetsIn1 R (PowerSeries.subst linv ph - PowerSeries.C (jet l ph 2 / 2) * PowerSeries.X ^ 2) := by
  intro k
  rw [map_sub, mul_sub, ← jetAdditive K l linv ph h k, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow]
  by_cases h2 : k = 2
  · subst h2
    have : jet l ph 2 - ((Nat.factorial 2 : ℕ) : K) * (jet l ph 2 / 2 * if 2 = 2 then 1 else 0) = 0 := by
      simp only [Nat.factorial, if_true]
      push_cast
      field_simp
      ring
    rw [this]
    exact R.zero_mem
  · rw [if_neg h2, mul_zero, mul_zero, sub_zero]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have : jet l ph 0 = 0 := h0
      rw [this]
      exact R.zero_mem
    · exact hj k hk h2
end Formalism.L2.Th1.G
