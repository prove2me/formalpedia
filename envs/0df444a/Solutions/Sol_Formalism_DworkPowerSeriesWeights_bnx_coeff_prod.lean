-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_coeff_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:32.163073+00:00
-- url     : https://prove2.me/submissions/bb296692-c311-46fc-a20c-0c2e2851e736

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_lin_pow_supp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnxRes_apply
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs

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
private theorem coeff_prod_bnxA_pow_eq_ite {K : Type u} [Field K] {d : ℕ} [NeZero d]
    (a b : ZMod d → K) (k : ZMod d → ℕ) (S : Finset (ZMod d)) (m : V2 d →₀ ℕ) :
    coeff m (∏ s ∈ S, bnxA a b s ^ k s) =
      if ∀ z : V2 d, z.2 ∉ S → m z = 0 then
        ∏ s ∈ S, coeff (bnxRes m s) (bnxA a b s ^ k s) else 0 := by
  revert m
  refine Finset.induction_on S ?_ ?_
  · intro m
    rw [Finset.prod_empty, Finset.prod_empty, coeff_one]
    by_cases hm : m = 0
    · subst hm
      simp
    · rw [if_neg hm, if_neg]
      intro h
      apply hm
      ext z
      exact h z (by simp)
  · intro c S ha ih m
    have hr : ∀ z, bnxRes m c z = if z.2 = c then m z else 0 := bnxRes_apply m c
    rw [Finset.prod_insert ha, Finset.prod_insert ha, coeff_mul]
    rw [Finset.sum_eq_single (bnxRes m c, m - bnxRes m c)]
    · rw [ih]
      have hcond : (∀ z : V2 d, z.2 ∉ S → (m - bnxRes m c) z = 0) ↔
          (∀ z : V2 d, z.2 ∉ insert c S → m z = 0) := by
        constructor
        · intro h z hz
          have h1 := h z (fun hS => hz (Finset.mem_insert_of_mem hS))
          have hza : z.2 ≠ c := fun e => hz (by rw [e]; exact Finset.mem_insert_self c S)
          rw [Finsupp.tsub_apply, hr, if_neg hza] at h1
          omega
        · intro h z hz
          rw [Finsupp.tsub_apply, hr]
          split_ifs with hza
          · omega
          · have h2 := h z (by simp [hza, hz])
            omega
      by_cases hc : ∀ z : V2 d, z.2 ∉ insert c S → m z = 0
      · rw [if_pos (hcond.2 hc), if_pos hc]
        congr 1
        refine Finset.prod_congr rfl fun s hs => ?_
        have hsa : s ≠ c := fun e => ha (by rw [← e]; exact hs)
        have hres : bnxRes (m - bnxRes m c) s = bnxRes m s := by
          ext z
          simp only [bnxRes_apply, Finsupp.tsub_apply]
          by_cases h1 : z.2 = s
          · simp [h1, hsa]
          · simp [h1]
        rw [hres]
      · rw [if_neg (mt hcond.1 hc), if_neg hc, mul_zero]
    · intro p hp hne
      first
        | rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        | simp only [Finset.mem_antidiagonal] at hp
      by_contra hnz
      have h1 : coeff p.1 (bnxA a b c ^ k c) ≠ 0 := left_ne_zero_of_mul hnz
      have h2 : coeff p.2 (∏ s ∈ S, bnxA a b s ^ k s) ≠ 0 := right_ne_zero_of_mul hnz
      rw [ih] at h2
      have hP : ∀ z : V2 d, z.2 ∉ S → p.2 z = 0 := by
        by_contra hP
        exact h2 (if_neg hP)
      have hs1 : ∀ z : V2 d, z.2 ≠ c → p.1 z = 0 := by
        intro z hz
        by_contra hz0
        rcases bnx_lin_pow_supp (false, c) (true, c) (a c) (b c) (k c) p.1 h1 z hz0 with h | h <;>
          (subst h; exact hz rfl)
      apply hne
      have e1 : p.1 = bnxRes m c := by
        ext z
        rw [hr]
        split_ifs with hz
        · have h4 := hP z (by rw [hz]; exact ha)
          have h3 := DFunLike.congr_fun hp z
          rw [Finsupp.add_apply] at h3
          omega
        · exact hs1 z hz
      have e2 : p.2 = m - bnxRes m c := by
        ext z
        have h3 := DFunLike.congr_fun hp z
        rw [Finsupp.add_apply] at h3
        rw [Finsupp.tsub_apply, ← e1]
        omega
      exact Prod.ext e1 e2
    · intro h
      exfalso
      apply h
      first
      | rw [Finset.HasAntidiagonal.mem_antidiagonal]
      | simp only [Finset.mem_antidiagonal]
      ext z
      rw [Finsupp.add_apply, Finsupp.tsub_apply, hr]
      split_ifs <;> omega
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
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (a b : ZMod d → K) (k : ZMod d → ℕ) (m : V2 d →₀ ℕ) :
    coeff m (∏ s, bnxA a b s ^ k s) = ∏ s, coeff (bnxRes m s) (bnxA a b s ^ k s) := by
  rw [coeff_prod_bnxA_pow_eq_ite, if_pos (fun z hz => absurd (Finset.mem_univ _) hz)]
end Formalism.DworkPowerSeriesWeights
