-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_choose_nonpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:32.12199+00:00
-- url     : https://prove2.me/submissions/8d59b50e-55ac-425d-8e02-f5230f983ad4

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_choose_lucas

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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPowerSeries Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {l : ℕ} (hl : l.Prime) (m : ℕ) (hm0 : m ≠ 0) (hm : ∀ e, m ≠ l ^ e) :
    ∃ j, 0 < j ∧ j < m ∧ ¬ l ∣ m.choose j := by
  obtain ⟨v, c, hc, hm'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 l hl.ne_one
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hm v (by rw [hm', mul_one])
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hm0 (by rw [hm', mul_zero])
  have hp := pow_pos hl.pos v
  refine ⟨l ^ v, hp, ?_, ?_⟩
  · have h2 : 2 ≤ c := by omega
    rw [hm']
    nlinarith
  · intro hd
    have h := bnx_choose_lucas hl c v
    rw [← hm'] at h
    exact hc (Nat.modEq_zero_iff_dvd.1 (h.symm.trans (Nat.modEq_zero_iff_dvd.2 hd)))
end Formalism.DworkPowerSeriesWeights
