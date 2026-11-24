-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_pow_class_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:51:02.000269+00:00
-- url     : https://prove2.me/submissions/2754d62d-879a-4747-99b7-b13d7889add2

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRBBCard
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRBBDivides
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRExcludedCount
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_class_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_div_le_rpow
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_residuesLe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (S : Finset ℕ) (Y : ℝ) (l j d : ℕ) (hl : l.Prime) (hd : 1 ≤ d)
    (hY : 1 ≤ Y) (hj : Y < (l : ℝ) ^ (4 * j))
    (hS : ∀ g ∈ S, Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y ∧ l ^ j ∣ g ^ d - 1) :
    (S.card : ℝ) ≤ 2 * d * (Y ^ ((3 : ℝ) / 4) + 1) := by
  classical
  set M := l ^ j with hMdef
  have hM : 0 < M := pow_pos hl.pos j
  have hM' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  set R := (Finset.range M).filter (fun x => x ^ d ≡ 1 [MOD M]) with hR
  have hRcard : R.card ≤ 2 * d := Formalism.GaloisIrreducibility.residuesLe l j d hl hd
  have hmaps : ∀ g ∈ S, g % M ∈ R := by
    intro g hg
    obtain ⟨h1, _, h3⟩ := hS g hg
    have hg1 : 1 ≤ g := by
      have : (1 : ℝ) ≤ (g : ℝ) := hY.trans h1
      exact_mod_cast this
    have hgd : 1 ≤ g ^ d := Nat.one_le_pow _ _ hg1
    have hmod : 1 ≡ g ^ d [MOD M] := (Nat.modEq_iff_dvd' hgd).mpr h3
    rw [hR, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hM, ?_⟩
    exact ((Nat.mod_modEq g M).pow d).trans hmod.symm
  have hcard : S.card = ∑ r ∈ R, (S.filter (fun g => g % M = r)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ r ∈ R, ((S.filter (fun g => g % M = r)).card : ℝ) ≤ Y ^ ((3 : ℝ) / 4) + 1 := by
    intro r _
    have h1 := card_class_le (S.filter (fun g => g % M = r)) Y M r hM (by linarith) (by
      intro g hg
      obtain ⟨hgS, hgr⟩ := Finset.mem_filter.mp hg
      exact ⟨(hS g hgS).1, (hS g hgS).2.1, hgr⟩)
    have h2 : Y / (M : ℝ) ≤ Y ^ ((3 : ℝ) / 4) := by
      apply div_le_rpow Y M hY hM'
      have : ((M : ℝ)) ^ 4 = (l : ℝ) ^ (4 * j) := by
        rw [hMdef]; push_cast; rw [← pow_mul, mul_comm]
      rw [this]; exact hj
    linarith
  have hc0 : (0 : ℝ) ≤ Y ^ ((3 : ℝ) / 4) + 1 := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) ((3 : ℝ) / 4)
    linarith
  calc (S.card : ℝ) = ∑ r ∈ R, ((S.filter (fun g => g % M = r)).card : ℝ) := by
        rw [hcard]; push_cast; rfl
    _ ≤ ∑ _r ∈ R, (Y ^ ((3 : ℝ) / 4) + 1) := Finset.sum_le_sum hfib
    _ = (R.card : ℝ) * (Y ^ ((3 : ℝ) / 4) + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * d * (Y ^ ((3 : ℝ) / 4) + 1) := by
        apply mul_le_mul_of_nonneg_right _ hc0
        exact_mod_cast hRcard
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
