-- Prove2me | solution 1 for BCFGJPSSV26.Combine.thm11_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:52:48.252687+00:00
-- url     : https://prove2.me/submissions/0a03d4d3-8598-4733-81d4-8936427607f4

module

public import Definitions.Def_BCFGJPSSV26_Combine_Analysis
public import Definitions.Def_BCFGJPSSV26_Combine_PolyTime
public import Definitions.Def_BCFGJPSSV26_Combine
import all Definitions.Def_BCFGJPSSV26_Combine

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Combine

open Encoding

namespace Prm

variable (P : Prm)

end Prm

/-- **Theorem 1.1 from Theorems 1.2 and 1.3.** -/
theorem thm11_of (h12 : Thm12) (h13 : Thm13) : Thm11 := by
  obtain ⟨C, hC⟩ := h12
  obtain ⟨A₂, hA₂, hA₂I⟩ := hC ε₁ (by unfold ε₁; norm_num)
  obtain ⟨A, a, b, C₃, hA, hAI⟩ := h13
  obtain ⟨c₃, hA₃⟩ := runsInTime_fix hA (ε₃ C₃)
  set P : Prm := ⟨A₂, fun y ↦ A ((y.1, ε₃ C₃), y.2), a * (⌈1 / ε₃ C₃⌉₊ + 1) ^ b,
    ⌈max C 0 / ε₁ ^ 2⌉₊, 100001⟩
  obtain ⟨D, hD⟩ := Turing.MultiTapeTM.exists_computableInTimeAndSpace_take
    (P.alg'_polytime hA₂ hA₃) P.coinLen_polytime P.coinLen_le
  set E := max D ((P.K + 1) * (2 ^ (P.e * P.M * (P.K + 1)) * 2 ^ P.e) +
    (P.e * P.M * P.K + P.e + 1))
  obtain ⟨c, hc⟩ := hD E (le_max_left _ _)
  refine ⟨P.alg, E, ⟨c, hc⟩, fun I hI ↦ ⟨fun r ↦ P.isCenterList_alg hI r, ?_⟩⟩
  have hN : P.coinLen I ≤ ((encInstance I).length + 2) ^ E :=
    (P.coinLen_le I).trans (le_pow_add.trans (Nat.pow_le_pow_right (by omega) (le_max_right _ _)))
  have hk₀ := one_le_k₀ hI
  have hO := opt_nonneg hI (k₀ I)
  have hL : 1 ≤ P.Lp I := Nat.mul_le_mul (by norm_num : 1 ≤ 100001) (P.one_le_cnt I)
  have hρ : (1 + 1 / (P.Lp I : ℝ)) ^ P.cnt I ≤ 1 + ε₂ := by
    have h := one_add_pow_le (M := 100001) (by norm_num) (P.one_le_cnt I)
    unfold ε₂
    refine h.trans (le_of_eq ?_)
    norm_num
  by_cases hA' : P.cnt I < k₀ I ∧ I.opt (k₀ I - P.cnt I) ≤ (1 + ε₂) * I.opt (k₀ I)
  · rw [coinProb_of_forall fun r ↦ P.cost_alg_of_run₂ rfl hA₂I hI hA'.1 hA'.2 r]
    norm_num
  obtain ⟨j, hj, hst, hOj⟩ := exists_stable I.opt hk₀
    (by have : (0 : ℝ) ≤ 1 / (P.Lp I : ℝ) := by positivity
        linarith) hρ hO hA'
  have hLpos : (0 : ℝ) < 1 / (P.Lp I : ℝ) := by
    have : (1 : ℝ) ≤ P.Lp I := by exact_mod_cast hL
    positivity
  obtain ⟨hall, hprobβ⟩ := hAI (atK I j) (setK_valid hI (by omega))
    (by change k₀ I - j ≤ I.m; have := min_le_right I.k I.m; unfold k₀; omega) (P.Lp I) (ε₃ C₃)
  have hprob := hprobβ (ε₃_pos C₃) (ε₃_lt C₃) (1 / (P.Lp I : ℝ)) hLpos hst
    (by rw [one_div_one_div])
  have hjc : j < P.cnt I := lt_of_lt_of_le hj (min_le_left _ _)
  have hwin := (P.window_le hjc).trans hN
  calc (2 / 3 : ℝ) ≤ 1 - (ε₃ C₃ : ℝ) := by
        have : ((ε₃ C₃ : ℚ) : ℝ) < ((1 / 200 : ℚ) : ℝ) := Rat.cast_lt.2 (ε₃_lt C₃)
        push_cast at this
        linarith
    _ ≤ _ := hprob
    _ = coinProb (((encInstance I).length + 2) ^ E) (fun r ↦ (atK I j).cost ((atK I j).centers
          (A (((atK I j, P.Lp I), ε₃ C₃), (r.drop (j * P.blockLen I)).take
            (stableTime P.e (atK I j, P.Lp I)))))
          ≤ (1.89 + C₃ * (ε₃ C₃ : ℝ)) * (atK I j).opt (atK I j).k) :=
        (coinProb_window _ hwin).symm
    _ ≤ _ := coinProb_mono fun r hr ↦
        P.cost_alg_of_run₃ (abs_mul_ε₃_le C₃) hI hj hall hOj r hr

end BCFGJPSSV26.Combine

end

public section

theorem solution : type_of% @BCFGJPSSV26.Combine.thm11_of := @BCFGJPSSV26.Combine.thm11_of
