-- Prove2me | solution 1 for Formalism.LT.LTL.stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:58:18.740804+00:00
-- url     : https://prove2.me/submissions/21195430-2dfa-444f-ba13-8aba23d6553a

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_seq_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
variable {p q : ℕ} {π : K} {e e' : PowerSeries K} {a : ι → K}
namespace Formalism.LT.LTL
theorem _root_.solution (hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    (ha : ∀ i, ‖a i‖ ≤ 1) (d : ι →₀ ℕ) : ∀ k : ℕ, d.degree < k + 1 →
    MvPowerSeries.coeff d (seq e e' π a (k + 1)) =
      MvPowerSeries.coeff d (seq e e' π a (d.degree + 1)) := by
  intro k
  induction k with
  | zero => intro hd; rw [show d.degree = 0 by omega]
  | succ j ih =>
    intro hd
    by_cases h : d.degree = j + 1
    · rw [h]
    · rw [← ih (by omega)]
      have := seq_sub hS he he' ha j d (by omega)
      rw [map_sub] at this
      exact sub_eq_zero.mp this
end Formalism.LT.LTL
