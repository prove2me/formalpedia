-- Prove2me | solution 1 for Formalism.LT.InvIntP.coeff_expand_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:33:53.474857+00:00
-- url     : https://prove2.me/submissions/67244fd3-8b41-4adf-966e-0f47045a0bfa

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt

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
universe u v
open Formalism Formalism.LT Formalism.LT.InvIntP
open Formalism.G Formalism.G.LogCR
namespace Formalism.LT.InvIntP
theorem _root_.solution {K : Type u} [NormedField K] {ι : Type v} (q : ℕ) (hq : q ≠ 0)
    (hq2 : 2 ≤ q) (σ : K →+* K) (D : MvPowerSeries ι K) (N : ℕ) (hN : 1 ≤ N)
    (hlow : ∀ d : ι →₀ ℕ, d.degree < N → MvPowerSeries.coeff d D = 0)
    (d : ι →₀ ℕ) (hd : d.degree = N) :
    MvPowerSeries.coeff d (MvPowerSeries.expand q hq (MvPowerSeries.map σ D)) = 0 := by
  classical
  by_cases hall : ∀ i, q ∣ d i
  · set m : ι →₀ ℕ := Finsupp.mapRange (fun k => k / q) (Nat.zero_div q) d with hm
    have hdm : d = q • m := by
      ext i
      simp only [Finsupp.smul_apply, smul_eq_mul, hm, Finsupp.mapRange_apply]
      exact (Nat.mul_div_cancel' (hall i)).symm
    have hdeg : d.degree = q * m.degree := by rw [hdm, map_nsmul, smul_eq_mul]
    have hmlt : m.degree < N := by
      rcases Nat.eq_zero_or_pos m.degree with h0 | hpos
      · omega
      · nlinarith
    rw [hdm, MvPowerSeries.coeff_expand_smul, MvPowerSeries.coeff_map, hlow m hmlt, map_zero]
  · push_neg at hall
    obtain ⟨i, hi⟩ := hall
    exact MvPowerSeries.coeff_expand_of_not_dvd q hq _ hi
end Formalism.LT.InvIntP
