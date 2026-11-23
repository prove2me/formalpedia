-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_torus_cong
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:59.063704+00:00
-- url     : https://prove2.me/submissions/6f279e95-ff69-4bb1-aee5-1606c8b620a3

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_pow_mod
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
universe u
namespace Formalism.DworkPowerSeriesWeights
open MvPowerSeries Formalism.IncomingBounds
section Blocks
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]
end Blocks
section Subst
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]
end Subst
section De
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]
end De
section NormNat
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end NormNat
private theorem finsupp_prod_torus_pow_eq_C_mul_monomial {K : Type u} [Field K] {d : ℕ} [NeZero d] (l : ℕ) (ζ : K)
    (dd : ZMod d →₀ ℕ) :
    (dd.prod fun t e => (torus l ζ t : MvPowerSeries (ZMod d) K) ^ e) =
      C (∏ t, (ζ ^ lw l t) ^ dd t) * monomial dd 1 := by
  rw [Finsupp.prod_fintype _ _ (fun t => pow_zero _)]
  simp only [torus, mul_pow, ← map_pow, Finset.prod_mul_distrib, map_prod]
  congr 1
  have hmono : ∀ S : Finset (ZMod d), ∏ t ∈ S, (X t ^ dd t : MvPowerSeries (ZMod d) K) =
      monomial (∑ t ∈ S, Finsupp.single t (dd t)) 1 := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simp [monomial_zero_eq_C_apply]
    · intro a S ha ih
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X_pow_eq, monomial_mul_monomial, one_mul]
  rw [hmono]
  rw [show ∑ t, Finsupp.single t (dd t) = dd from by
    ext u
    simp [Finsupp.finset_sum_apply, Finsupp.single_apply]]
section Sides
variable {K : Type u} [NormedField K] {d : ℕ} [NeZero d]
end Sides
end Formalism.DworkPowerSeriesWeights
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPowerSeries Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [Field K] (l d : ℕ) [NeZero d] (hl : l.Prime) (hl3 : 3 ≤ l)
    (hd2 : 2 ≤ d) (hde : Even d) (ζ : K) (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
    (be : MvPowerSeries (ZMod d) K) (htor : subst (torus l ζ) be = be)
    (s s' : ZMod d) (hs : s.val % 2 = 0) (hs' : s'.val % 2 ≠ 0) (α β : ℕ)
    (hc : coeff (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) be ≠ 0) :
    s + (α : ZMod d) = s' + (β : ZMod d) := by
  have hk0 : 0 < l ^ d - 1 := by
    have : l ≤ l ^ d := Nat.le_self_pow (by omega) l
    omega
  have hss : s ≠ s' := by
    rintro rfl
    exact hs' hs
  have ha : HasSubst (torus l ζ : ZMod d → MvPowerSeries (ZMod d) K) :=
    hasSubst_of_constantCoeff_zero fun t => by simp [torus]
  have hcoef := congrArg (coeff (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))) htor
  rw [coeff_subst ha, finsum_eq_single _ (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))] at hcoef
  swap
  · intro dd hdd
    rw [finsupp_prod_torus_pow_eq_C_mul_monomial, coeff_C_mul, coeff_monomial, if_neg (Ne.symm hdd), mul_zero, smul_zero]
  rw [finsupp_prod_torus_pow_eq_C_mul_monomial, coeff_C_mul, coeff_monomial, if_pos rfl, mul_one, smul_eq_mul] at hcoef
  have hprod := mul_left_cancel₀ hc (hcoef.trans (mul_one _).symm)
  rw [Finset.prod_eq_mul s s' hss
    (fun t _ ht => by simp [Finsupp.single_apply, Ne.symm ht.1, Ne.symm ht.2])
    (fun h => absurd (Finset.mem_univ s) h) (fun h => absurd (Finset.mem_univ s') h)] at hprod
  have hv1 : (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) s = l ^ α := by
    simp [Finsupp.single_apply, Ne.symm hss]
  have hv2 : (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) s' = l ^ β := by
    simp [Finsupp.single_apply, hss]
  rw [hv1, hv2] at hprod
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hk0.ne'
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0,
    hζ.zpow_eq_one_iff_dvd] at hprod
  unfold lw at hprod
  rw [if_pos hs, if_neg hs'] at hprod
  have hmod : l ^ (s.val + α) ≡ l ^ (s'.val + β) [MOD l ^ d - 1] := by
    rw [Nat.modEq_iff_dvd]
    have e : ((l ^ (s'.val + β) : ℕ) : ℤ) - ((l ^ (s.val + α) : ℕ) : ℤ) =
        -((1 : ℤ) * (l : ℤ) ^ s.val * ((l ^ α : ℕ) : ℤ) +
          (-1) * (l : ℤ) ^ s'.val * ((l ^ β : ℕ) : ℤ)) := by
      push_cast
      ring
    rw [e]
    first
    | exact dvd_neg.2 hprod
    | exact dvd_neg.2 (by exact_mod_cast hprod)
  have key := bnx_pow_mod l d _ _ hl3 (by omega) hmod
  have h2 := congrArg (fun x : ℕ => (x : ZMod d)) key
  first
  | (simp only [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_zmod_val] at h2; exact h2)
  | (simp at h2; exact h2)
end Formalism.DworkPowerSeriesWeights
