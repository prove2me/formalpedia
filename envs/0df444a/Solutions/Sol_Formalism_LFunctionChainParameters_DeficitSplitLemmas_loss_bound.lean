-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.loss_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:38:57.818935+00:00
-- url     : https://prove2.me/submissions/d2c47da8-07f9-457c-9d2f-c9edff737806

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_split_classes_count
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_top_loss_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_d_term_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_interval_count
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_high_bucket_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_floor_bucket_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_cp_bucket_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_pr_bucket_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_or_bucket_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_dsum_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.DeficitSplitLemmas
open Finset Classical
noncomputable section
namespace Formalism.LFunctionChainParameters.DeficitSplitLemmas
theorem _root_.solution : SecondKindLoss := by
  intro ι κ τ W below l Ps cl J TT TTp Iex at_ wz Id wd d gainW tauW gain tau lo fl
    a th w'' X'' X' C f N Sk Q₁ Q₂ lx La k K₀ L₁ p₀
    hU hPr hw'' hth0 hth hX'' haX ha1 hX' hp₀ hd hC hf hSk hQ₁ hQ₂ hlx hLa hk hK₀
    hat hIex hId hserved hhigh hled hdrop hfl hlo hL
  have h0 := split_classes_count ι κ τ W below l Ps cl J TT TTp
    (fun j t p => askAt (Iex j t p) (at_ t) p (wz j t p))
    (fun j t => Real.log d * askAt (Id j t) (at_ t) d (wd j t))
    gainW tauW gain tau lo fl hU hled hdrop
  generalize hask : (fun j t p => askAt (Iex j t p) (at_ t) (p : ℝ) (wz j t p) :
    κ → τ → ℕ → ℝ) = vonMangoldtClassSum at h0 hled ⊢
  generalize hdT : (fun j t => Real.log d * askAt (Id j t) (at_ t) d (wd j t) : κ → τ → ℝ) = dT
    at h0 ⊢
  generalize hm : (J.card : ℝ) = m at h0 ⊢
  generalize hT : (TT.card : ℝ) = T at h0 ⊢
  have hm0 : 0 ≤ m := by rw [← hm]; exact Nat.cast_nonneg _
  have hT0 : 0 ≤ T := by rw [← hT]; exact Nat.cast_nonneg _
  have ha0 : 0 ≤ a := by linarith
  have hat32 : ∀ t ∈ TT, at_ t ≤ 3 / 2 * a := by
    intro t ht
    have := (hat t ht).2
    nlinarith
  have hTop : ∀ j ∈ J, ∀ t ∈ TT, ∀ p ∈ Ps,
      2 * Real.log p * vonMangoldtClassSum j t p ≤ 4 * a * Real.log p / p := by
    intro j hj t ht p hp
    rw [← hask]
    exact top_loss_bound (Iex j t p) a (at_ t) p (wz j t p) (hPr p hp).two_le (hat t ht).1
      (hat32 t ht) (fun i hi => by linarith [(hIex j hj t ht p hp i hi).2])
      (fun i hi => (hIex j hj t ht p hp i hi).1)
  have hWhole : ∀ p ∈ Ps,
      2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p ≤ 4 * m * T * a * (Real.log p / p) := by
    intro p hp
    unfold wholeAsk
    simp only [Finset.mul_sum]
    refine (dsum_le J TT _ _ (fun j hj t ht => hTop j hj t ht p hp)).trans (le_of_eq ?_)
    rw [hm, hT]; ring
  have hS : ∀ c : PClass,
      ∑ p ∈ Ps.filter (fun p => cl p = c), 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p ≤
      4 * m * T * a * ∑ p ∈ Ps.filter (fun p => cl p = c), Real.log p / p := by
    intro c
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p hp => hWhole p (Finset.mem_filter.1 hp).1)
  have hHigh : ∑ p ∈ Ps.filter (fun p => cl p = PClass.high),
      2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p ≤
      m * T * (2 * Real.log (2 * X'') * (a * th ^ 2 + w'' * th)) := by
    unfold wholeAsk
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun j _ => Finset.sum_comm), ← hm, ← hT]
    apply dsum_le
    intro j hj t ht
    rw [← hask]
    exact high_bucket_bound a (at_ t) w'' X'' th _ (fun p => Iex j t p) (fun p => wz j t p)
      hw'' hth0 (by linarith) hX'' haX (hat t ht).1 (hat t ht).2
      (fun p hp => hhigh p (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hp).2)
      (fun p hp i hi => (hIex j hj t ht p (Finset.mem_filter.1 hp).1 i hi).1.pos)
      (fun p hp i hi => (hIex j hj t ht p (Finset.mem_filter.1 hp).1 i hi).2)
  have hD : ∑ j ∈ J, ∑ t ∈ TT, dT j t ≤ m * T * (2 * a * Real.log d / d) := by
    rw [← hm, ← hT]
    apply dsum_le
    intro j hj t ht
    rw [← hdT]
    exact d_term_bound (Id j t) a (at_ t) d (wd j t) hd (hat t ht).1 (hat32 t ht)
      (fun i hi => (hId j hj t ht i hi).2) (fun i hi => (hId j hj t ht i hi).1)
  have hServ : ∀ p ∈ Ps.filter (fun p => cl p = PClass.served),
      2 * Real.log p * servedLoss J TT TTp vonMangoldtClassSum lo fl p ≤
        4 * m * a * (Real.log p / p) * ((TT \ TTp p).card : ℝ) +
        2 * Real.log p * (m * T * cpF C Sk a p) +
        (if (p : ℝ) < X' then m * T * (2 * Real.log p * prF p₀ Q₁ Q₂ p) else 0) +
        (if (p : ℝ) < X' then m * T * (2 * Real.log p * orF C lx La a k L₁ p₀ p) else 0) +
        m * (2 * Real.log p * flF C f N a p) := by
    intro p hp
    obtain ⟨hpP, hc⟩ := Finset.mem_filter.1 hp
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hPr p hpP).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hsub := (hled p hpP hc).1
    have h1 : 2 * Real.log p * ∑ j ∈ J, ∑ t ∈ TT \ TTp p, vonMangoldtClassSum j t p ≤
        4 * m * a * (Real.log p / p) * ((TT \ TTp p).card : ℝ) := by
      simp only [Finset.mul_sum]
      refine (dsum_le J (TT \ TTp p) _ _
        (fun j hj t ht => hTop j hj t (Finset.mem_sdiff.1 ht).1 p hpP)).trans (le_of_eq ?_)
      rw [hm]; ring
    have hcp0 : 0 ≤ cpF C Sk a p := by
      unfold cpF
      have : 0 ≤ Real.logb p (2 * a) := Real.logb_nonneg (by linarith) (by linarith)
      positivity
    have hpr0 : 0 ≤ prF p₀ Q₁ Q₂ p := by unfold prF; split_ifs <;> assumption
    have hor0 : 0 ≤ orF C lx La a k L₁ p₀ p := by
      unfold orF
      have : 0 ≤ (if p < p₀ then a * (p : ℝ) ^ (-(L₁ p)) else a / (p : ℝ) ^ 2) := by
        split_ifs
        · exact mul_nonneg ha0 (Real.rpow_nonneg hp0.le _)
        · positivity
      positivity
    have hloF0 : 0 ≤ loF C Sk a X' Q₁ Q₂ lx La k L₁ p₀ p := by
      unfold loF; split_ifs <;> linarith
    have hcard : ((TTp p).card : ℝ) ≤ T := by
      rw [← hT]; exact_mod_cast Finset.card_le_card hsub
    have hcard0 : (0 : ℝ) ≤ ((TTp p).card : ℝ) := Nat.cast_nonneg _
    have h2 : m * (TTp p).card * lo p ≤ m * T * loF C Sk a X' Q₁ Q₂ lx La k L₁ p₀ p := by
      calc m * (TTp p).card * lo p ≤ m * (TTp p).card * loF C Sk a X' Q₁ Q₂ lx La k L₁ p₀ p :=
            mul_le_mul_of_nonneg_left (hlo p hpP hc) (by positivity)
        _ ≤ m * T * loF C Sk a X' Q₁ Q₂ lx La k L₁ p₀ p :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hm0) hloF0
    have h3 : m * fl p ≤ m * flF C f N a p := mul_le_mul_of_nonneg_left (hfl p hpP hc) hm0
    unfold servedLoss
    rw [hm]
    have h4 := mul_le_mul_of_nonneg_left (add_le_add h2 h3) (show 0 ≤ 2 * Real.log p by linarith)
    have e1 : 2 * Real.log p * (∑ j ∈ J, ∑ t ∈ TT \ TTp p, vonMangoldtClassSum j t p + m * (TTp p).card * lo p +
        m * fl p) = 2 * Real.log p * ∑ j ∈ J, ∑ t ∈ TT \ TTp p, vonMangoldtClassSum j t p +
        2 * Real.log p * (m * (TTp p).card * lo p + m * fl p) := by ring
    rw [e1]
    have e2 : 2 * Real.log p * (m * T * loF C Sk a X' Q₁ Q₂ lx La k L₁ p₀ p + m * flF C f N a p) =
        2 * Real.log p * (m * T * cpF C Sk a p) +
        (if (p : ℝ) < X' then m * T * (2 * Real.log p * prF p₀ Q₁ Q₂ p) else 0) +
        (if (p : ℝ) < X' then m * T * (2 * Real.log p * orF C lx La a k L₁ p₀ p) else 0) +
        m * (2 * Real.log p * flF C f N a p) := by
      unfold loF
      split_ifs <;> ring
    rw [e2] at h4
    linarith
  have hS1 := Finset.sum_le_sum hServ
  simp only [Finset.sum_add_distrib] at hS1
  rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at hS1
  have hs2 : ∀ p ∈ Ps.filter (fun p => cl p = PClass.served), 2 ≤ p :=
    fun p hp => (hPr p (Finset.mem_filter.1 hp).1).two_le
  have hcardS : ((Ps.filter (fun p => cl p = PClass.served)).card : ℝ) ≤ X'' := by
    have := interval_count 2 X'' (Ps.filter (fun p => cl p = PClass.served)) hX'' (by
      intro p hp
      exact ⟨by exact_mod_cast hs2 p hp,
        hserved p (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hp).2⟩)
    linarith
  have hCp := cp_bucket_bound C Sk a (m * T) X'' _ hC hSk (by linarith) (by positivity) hs2 hcardS
  have hFl := floor_bucket_bound C f N a X'' _ hC hf ha1 hs2 hcardS
  have hPrB := pr_bucket_bound p₀ X' Q₁ Q₂
    ((Ps.filter (fun p => cl p = PClass.served)).filter (fun p : ℕ => (p : ℝ) < X'))
    (by linarith) hQ₁ hQ₂ (by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      exact ⟨hPr p (Finset.mem_filter.1 hp1).1, hp2⟩)
  have hOrB := or_bucket_bound C lx La a k K₀ X' L₁ p₀
    ((Ps.filter (fun p => cl p = PClass.served)).filter (fun p : ℕ => (p : ℝ) < X'))
    hC hlx hLa ha0 hk hK₀ hX' hp₀ (by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      exact ⟨hPr p (Finset.mem_filter.1 hp1).1, hp2⟩) (by
      intro p hp
      exact hL p (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1)
  have hmT : 0 ≤ m * T := by positivity
  have hPr' := mul_le_mul_of_nonneg_left hPrB hmT
  have hOr' := mul_le_mul_of_nonneg_left hOrB hmT
  have hFl' := mul_le_mul_of_nonneg_left hFl hm0
  have hF1 := hS PClass.first
  have hF2 := hS PClass.second
  simp only [← hdT] at hD
  linarith
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
