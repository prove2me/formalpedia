-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_g_pascal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:08:25.733659+00:00
-- url     : https://prove2.me/submissions/9928c29c-0cb5-4a6d-b1d8-ed4060956d41

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
open Classical
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
theorem _root_.solution (R : Type*) [CommRing R] {σ : Type*} (m be : σ →₀ ℕ) (a : σ) :
    flt_g R (m + Finsupp.single a 1) be =
      flt_g R m be * X a + (if a ∈ be.support then flt_g R m (be - Finsupp.single a 1) else 0) := by
  unfold flt_g
  rw [X, monomial_mul, mul_one]
  by_cases ha : a ∈ be.support
  · rw [if_pos ha]
    have hba : be a ≠ 0 := Finsupp.mem_support_iff.1 ha
    have hsub : (be - Finsupp.single a 1).support ⊆ be.support := by
      intro k hk
      rw [Finsupp.mem_support_iff] at hk ⊢
      rw [Finsupp.tsub_apply] at hk
      omega
    rw [Finsupp.prod_of_support_subset _ hsub _ (fun k _ => Nat.choose_zero_right _)]
    simp only [Finsupp.prod]
    rw [← Finset.mul_prod_erase _ _ ha, ← Finset.mul_prod_erase _ _ ha, ← Finset.mul_prod_erase _ _ ha]
    have hrest1 : ∏ k ∈ be.support.erase a, ((m + Finsupp.single a 1 : σ →₀ ℕ) k).choose (be k) =
        ∏ k ∈ be.support.erase a, (m k).choose (be k) :=
      Finset.prod_congr rfl fun k hk => by
        rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hk).symm, add_zero]
    have hrest2 : ∏ k ∈ be.support.erase a, (m k).choose ((be - Finsupp.single a 1 : σ →₀ ℕ) k) =
        ∏ k ∈ be.support.erase a, (m k).choose (be k) :=
      Finset.prod_congr rfl fun k hk => by
        rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hk).symm, tsub_zero]
    rw [hrest1, hrest2]
    obtain ⟨b, hb⟩ : ∃ b, be a = b + 1 := ⟨be a - 1, by omega⟩
    have hA : (m + Finsupp.single a 1 : σ →₀ ℕ) a = m a + 1 := by simp
    have hB : (be - Finsupp.single a 1 : σ →₀ ℕ) a = b := by rw [Finsupp.tsub_apply, hb]; simp
    rw [hA, hB, hb, Nat.choose_succ_succ]
    rcases Nat.lt_or_ge (m a) b with hlt | hge
    · rw [Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt (by omega : m a < b + 1)]
      simp
    · have e3 : m - (be - Finsupp.single a 1) = m + Finsupp.single a 1 - be := by
        ext k
        by_cases hk : k = a
        · subst hk
          simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same, hb]
          omega
        · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hk)]
          omega
      rcases Nat.lt_or_ge (m a) (b + 1) with hlt2 | hge2
      · rw [Nat.choose_eq_zero_of_lt hlt2, e3]
        simp
      · have e2 : m - be + Finsupp.single a 1 = m + Finsupp.single a 1 - be := by
          ext k
          by_cases hk : k = a
          · subst hk
            simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same, hb]
            omega
          · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hk)]
            omega
        rw [e2, e3, ← map_add]
        congr 1
        push_cast
        ring
  · rw [if_neg ha, add_zero]
    have hba : be a = 0 := by simpa [Finsupp.mem_support_iff] using ha
    have e2 : m - be + Finsupp.single a 1 = m + Finsupp.single a 1 - be := by
      ext k
      by_cases hk : k = a
      · subst hk
        simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same, hba]
        omega
      · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hk)]
        omega
    have hc : (be.prod fun k j => ((m + Finsupp.single a 1 : σ →₀ ℕ) k).choose j) = be.prod fun k j => (m k).choose j := by
      simp only [Finsupp.prod]
      refine Finset.prod_congr rfl fun k hk => ?_
      have hka : a ≠ k := fun h => ha (h ▸ hk)
      rw [Finsupp.add_apply, Finsupp.single_apply, if_neg hka, add_zero]
    rw [e2, hc]
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
