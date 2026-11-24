-- Prove2me | solution 1 for Formalism.LT.InvIntP.invIntegralOfClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:29:31.636304+00:00
-- url     : https://prove2.me/submissions/0011a62d-f6c0-4dca-952e-f3f4a0fa0611

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Theorems.Thm_Formalism_LT_InvIntP_agree_psubst
import Theorems.Thm_Formalism_LT_InvIntP_low_of_agree
import Theorems.Thm_Formalism_LT_InvIntP_key

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
theorem _root_.solution (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v)
    [Finite ι] (C : MvPowerSeries ι K → Prop) (f : PowerSeries K)
    (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1)
    (hsub : ∀ a b, C a → C b → C (a - b))
    (hP : ∀ P : MvPowerSeries ι K, MvPowerSeries.constantCoeff P = 0 → IntegralMv P →
      C (f.subst P))
    (hlowC : ∀ D, C D → ∀ N : ℕ, 1 ≤ N →
      (∀ d : ι →₀ ℕ, d.degree < N → MvPowerSeries.coeff d D = 0) →
      ∀ d : ι →₀ ℕ, d.degree = N → ‖MvPowerSeries.coeff d D‖ ≤ 1)
    (h : MvPowerSeries ι K) (hh0 : MvPowerSeries.constantCoeff h = 0) (hCh : C (f.subst h)) :
    IntegralMv h := by
  have main : ∀ N : ℕ, ∀ d : ι →₀ ℕ, d.degree < N → ‖MvPowerSeries.coeff d h‖ ≤ 1 := by
    intro N
    induction N with
    | zero =>
      intro d hd
      omega
    | succ N ih =>
      intro d hd
      rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hlt | heq
      · exact ih d hlt
      · rcases Nat.eq_zero_or_pos N with hN0 | hNpos
        · subst hN0
          have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).1 heq
          subst hd0
          rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh0, norm_zero]
          exact zero_le_one
        · let T : MvPowerSeries ι K := fun e => if e.degree < N then MvPowerSeries.coeff e h else 0
          have hTc : ∀ e, MvPowerSeries.coeff e T = if e.degree < N then MvPowerSeries.coeff e h else 0 :=
            fun e => rfl
          have hT0 : MvPowerSeries.constantCoeff T = 0 := by
            rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hTc]
            simp [hNpos, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh0]
          have hTint : IntegralMv T := by
            intro e
            rw [hTc]
            split_ifs with he
            · exact ih e he
            · simp
          have hAg : Agree N h T := by
            intro e he
            rw [hTc, if_pos he]
          have hCD := hsub _ _ hCh (hP T hT0 hTint)
          have hLowD : Low N (f.subst h - f.subst T) := low_of_agree (agree_psubst f hh0 hT0 hAg)
          have hk := key f h0 h1 hh0 hT0 hAg d (by omega)
          have hb := hlowC _ hCD N hNpos hLowD d heq
          rw [map_sub, map_sub, map_sub, hTc, if_neg (by omega), sub_zero] at hk
          have hcd : MvPowerSeries.coeff d h = MvPowerSeries.coeff d (f.subst h - f.subst T) := by
            rw [map_sub]
            linear_combination -hk
          rw [hcd]
          exact hb
  intro d
  exact main (d.degree + 1) d (Nat.lt_succ_self _)
end Formalism.LT.InvIntP
