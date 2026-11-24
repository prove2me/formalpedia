-- Prove2me | solution 1 for Formalism.HC.Landau.lseries_real_im
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:55.837984+00:00
-- url     : https://prove2.me/submissions/c11fdf6d-684a-46a5-9e6c-cde1edea057b

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism Formalism.HC Formalism.HC.Landau
open Formalism ArithmeticFunction
open DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace Formalism.HC.Landau
theorem _root_.solution (a : ℕ → ℝ) (σ : ℝ) : (LSeries (fun n => (a n : ℂ)) σ).im = 0 := by
  have : LSeries (fun n => (a n : ℂ)) σ = ((∑' n : ℕ, (if n = 0 then 0 else a n / (n : ℝ) ^ σ) : ℝ) : ℂ) := by
    rw [ofReal_tsum]
    unfold LSeries
    refine tsum_congr fun n => ?_
    rw [LSeries.term_def]
    split_ifs
    · simp
    · rw [ofReal_div, ofReal_cpow (Nat.cast_nonneg n)]; simp
  rw [this, ofReal_im]
end Formalism.HC.Landau
