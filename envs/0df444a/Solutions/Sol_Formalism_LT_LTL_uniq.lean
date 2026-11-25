-- Prove2me | solution 1 for Formalism.LT.LTL.uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:23:48.567055+00:00
-- url     : https://prove2.me/submissions/7306ef96-f1b4-42db-a267-92ce49dfd9c1

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_master
import Theorems.Thm_Formalism_LT_LTL_norm_pi_sub_pow

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
    {ψ φ : MvPowerSeries ι K} (hψ0 : MvPowerSeries.constantCoeff ψ = 0)
    (hφ0 : MvPowerSeries.constantCoeff φ = 0)
    (h1 : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) ψ =
      MvPowerSeries.coeff (Finsupp.single i 1) φ)
    (hLψ : Ldef e e' ψ = 0) (hLφ : Ldef e e' φ = 0) : ψ = φ := by
  have hπ0 : 0 < ‖π‖ := hS.2.2.1
  have hπ1 : ‖π‖ < 1 := hS.2.2.2.1
  have H : ∀ N : ℕ, Low (N + 2) (ψ - φ) := by
    intro N
    induction N with
    | zero =>
      intro d hd
      rw [map_sub, sub_eq_zero]
      rcases Nat.lt_or_ge d.degree 1 with h0 | h0
      · have : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
        subst this
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
          MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hψ0, hφ0]
      · obtain ⟨i, hi⟩ : ∃ i, d = Finsupp.single i 1 := by
          have hd1 : d.degree = 1 := by omega
          obtain ⟨i, hi⟩ : d.support.Nonempty := by
            rw [Finsupp.support_nonempty_iff]
            rintro rfl
            simp at hd1
          refine ⟨i, ?_⟩
          have hle : Finsupp.single i (d i) ≤ d := by
            intro j
            by_cases hj : j = i
            · subst hj; simp
            · simp [Ne.symm hj]
          have hdi : d i = 1 := by
            have h2 := Finsupp.degree_mono hle
            rw [Finsupp.degree_single] at h2
            have : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
            omega
          obtain ⟨r, hr⟩ := le_iff_exists_add.mp hle
          have : r.degree = 0 := by
            have := congrArg Finsupp.degree hr
            rw [map_add, Finsupp.degree_single] at this
            omega
          rw [(Finsupp.degree_eq_zero_iff r).mp this, add_zero, hdi] at hr
          exact hr
        subst hi
        exact h1 i
    | succ N ih =>
      intro d hd
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hd) with hlt | heq
      · exact ih d hlt
      · have hm := master e e' he.2.1 he'.2.1 π he.2.2.1 he'.2.2.1 hψ0 hφ0 ih d (by omega)
        rw [hLψ, hLφ, map_zero, sub_zero] at hm
        have hnorm := norm_pi_sub_pow hπ0 hπ1 (r := N + 2) (by omega)
        have hne : π ^ (N + 2) - π ≠ 0 := by
          intro h0
          rw [← neg_sub, h0, neg_zero, norm_zero] at hnorm
          linarith
        exact (mul_eq_zero.mp hm.symm).resolve_left hne
  ext d
  have := H d.degree d (by omega)
  rw [map_sub] at this
  exact sub_eq_zero.mp this
end Formalism.LT.LTL
