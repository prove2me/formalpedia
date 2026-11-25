-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FormalGermZero.isT_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:58:40.934749+00:00
-- url     : https://prove2.me/submissions/59553b19-1d74-4185-a37d-6cac1cfb5c06

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_low_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.FormalGermZero
theorem _root_.solution {V : VF C} {d : ℕ} {I₁ J₁ : Type} [Fintype I₁] [Fintype J₁] {X₁ : Cart V d I₁ J₁} (S : Sys X₁)
    {t : I₁ → MvPowerSeries I₁ C} (ht : S.IsT t) (x : I₁) :
    ∑ c, PowerSeries.subst (t c) (tyS V.l (fun s => S.al c s x)) = MvPowerSeries.X x := by
  have hl : 2 ≤ V.l := V.l_prime.two_le
  ext μ
  have key : ∀ c, MvPowerSeries.coeff μ (PowerSeries.subst (t c) (tyS V.l (fun s => S.al c s x))) =
      ∑ s ∈ Finset.range (μ.degree + 1), S.al c s x * MvPowerSeries.coeff μ (t c ^ (V.l ^ s)) := by
    intro c
    have hS : PowerSeries.HasSubst (t c) := PowerSeries.HasSubst.of_constantCoeff_zero (ht.1 c)
    have hlow : ∀ n, μ.degree < n → MvPowerSeries.coeff μ (t c ^ n) = 0 := fun n hn =>
      Formalism.FG.SolveVAux.low_pow ((Formalism.FG.SolveVAux.low_one_iff _).2 (ht.1 c)) n μ hn
    rw [PowerSeries.coeff_subst hS, finsum_eq_sum_of_support_subset (s := Finset.range (μ.degree + 1))]
    · have e1 : ∀ n ∈ Finset.range (μ.degree + 1),
          PowerSeries.coeff n (tyS V.l fun s => S.al c s x) • MvPowerSeries.coeff μ (t c ^ n) =
            ∑ s ∈ Finset.range (μ.degree + 1),
              if V.l ^ s = n then S.al c s x * MvPowerSeries.coeff μ (t c ^ n) else 0 := by
        intro n hn
        rw [Finset.mem_range] at hn
        unfold tyS
        rw [PowerSeries.coeff_mk, smul_eq_mul, Finset.sum_mul]
        simp only [ite_mul, zero_mul]
        apply Finset.sum_subset
        · intro s hs
          rw [Finset.mem_range] at hs ⊢
          omega
        · intro s _ hs
          rw [Finset.mem_range] at hs
          have : s < V.l ^ s := Nat.lt_pow_self (by omega)
          rw [if_neg (by omega)]
      rw [Finset.sum_congr rfl e1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · rw [Finset.mem_range] at h
        rw [hlow _ (by omega), mul_zero]
    · intro n hn
      rw [Function.mem_support] at hn
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      exact hn (by rw [hlow n (by omega), smul_zero])
  rw [map_sum]
  simp only [key]
  rw [Finset.sum_comm, MvPowerSeries.coeff_X]
  exact ht.2 x μ
end Formalism.L2.FormalSeriesBounds.FormalGermZero
