-- Prove2me | solution 1 for BCFGJPSSV26.Stable.success_prob
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:22:37.495072+00:00
-- url     : https://prove2.me/submissions/e68e732a-4271-4d5c-82cd-539b14466029

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Trial
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch
public import Definitions.Def_BCFGJPSSV26_Stable_Time_Budget
public import Definitions.Def_BCFGJPSSV26_Combine_Analysis
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Main
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_Main
public import Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_trialGood
public import Theorems.Thm_BCFGJPSSV26_Stable_costF_le_bound_of_degenerate
public import Theorems.Thm_BCFGJPSSV26_Stable_isALO_localSearch

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset Sampling

variable {I : Instance}

open Classical in
/-- **The success probability** of the algorithm. -/
theorem success_prob (P : Prm) (hv : I.Valid) (hk : I.k ≤ I.m) {L : ℕ} {β : ℝ} (hβ : 0 < β)
    (hst : I.IsStable β) (hL : 1 / β ≤ L) {T : ℕ} (hT : Par.coinLen P.N I L ≤ T) :
    1 - 1 / (P.N : ℝ) ≤
      coinProb T fun r ↦ I.costF (I.centers (alg P ((I, L), r))) ≤ bound P I := by
  set B := Par.budget P.N I L with hB
  set LS := localSearch P.N (toRaw I) B with hLSdef
  have hN1 := P.N_pos
  have halo : IsALO I (Par.p P.N) (1 / (P.N * I.k)) (I.centers LS) :=
    isALO_localSearch hv hk hN1 (Par.budget_ls₁ hk hN1) (Par.budget_ls₂ hk hN1)
  obtain ⟨hnd, hlen, hm⟩ := localSearch_spec hk P.N B
  have hNpos := P.N_pos'
  have h1N : 0 ≤ 1 - 1 / (P.N : ℝ) := by
    rw [sub_nonneg, div_le_one hNpos]
    exact_mod_cast hN1
  -- the degenerate cases: the local search alone
  by_cases hdeg : I.k = 1 ∨ I.opt I.k = 0
  · have hLS := costF_le_bound_of_degenerate hv hk P.hN halo hdeg
    rw [Combine.coinProb_of_forall fun r ↦ ?_]
    · linarith [div_pos one_pos hNpos]
    have h := cost_alg_le_of_trial (L := L) P hv hk r (t := 0) (by unfold Par.R; positivity)
      (X := LS) List.mem_cons_self
    refine h.trans ((costF_sanitizeK_le hv hnd hm hlen.le).trans hLS)
  -- the standing hypotheses
  rw [not_or] at hdeg
  obtain ⟨O, hO⟩ := Instance.exists_isOpt hv hk
  set X : Ctx := ⟨P, I, β, L, O, I.centers LS⟩ with hX
  have H : Hyp X :=
    { valid := hv
      k_le_m := hk
      two_le_k := by
        change 2 ≤ I.k
        have := hv.one_le_k
        have := hdeg.1
        omega
      opt_pos := lt_of_le_of_ne (Instance.opt_nonneg' hv I.k) (Ne.symm hdeg.2)
      β_pos := hβ
      stable := hst
      L_ge := hL
      isOpt := hO
      alo := halo }
  -- the trials
  set C := Par.Ctr P.N L I.k with hC
  set b := Par.bits P.N (encInstance I).length with hb
  let G : (Fin C → Fin (2 ^ b)) → Prop := fun v ↦ TrialGood P I L LS B (toCh v)
  have hG : P.q L * (Fintype.card (Fin (2 ^ b)) : ℝ) ^ C ≤ (univ.filter G).card := by
    have h := H.card_trialGood (LS := LS) rfl hnd hm (B := B) (Par.pow_s_le_budget hN1)
    simpa using h
  have hrep := card_exists_block_ge G (P.q_nonneg L) (P.q_le_one L) (R := Par.R P.N L) hG
  -- the coins
  let Q : (ℕ → ℕ) → Prop := TrialsGood P I L LS B
  have hQ : ∀ ch ch' : ℕ → ℕ, (∀ i < Par.R P.N L * C, ch i = ch' i) → Q ch → Q ch' := by
    rintro ch ch' h ⟨t, ht, hgood⟩
    refine ⟨t, ht, ?_⟩
    rw [← window_congr (o := t * C) (M := C) fun i hi ↦ h _ ?_]
    · exact hgood
    · calc t * C + i < t * C + C := by omega
        _ = (t + 1) * C := by ring
        _ ≤ Par.R P.N L * C := Nat.mul_le_mul_right _ ht
  have hPQ : ∀ r : List Bool, Q (fun i ↦ chunkVal b r i) →
      I.costF (I.centers (alg P ((I, L), r))) ≤ bound P I := by
    rintro r ⟨t, ht, X', hX', hcost⟩
    exact (cost_alg_le_of_trial P hv hk r ht hX').trans hcost
  have hprob := coinProb_ge_of_chunks (T := T) (M := Par.R P.N L * C) (b := b)
    (by unfold Par.coinLen at hT; exact hT) hQ hPQ
  have hcount : (1 - (1 - P.q L) ^ Par.R P.N L) * ((2 : ℝ) ^ b) ^ (Par.R P.N L * C) ≤
      ((univ.filter fun u : Fin (Par.R P.N L * C) → Fin (2 ^ b) ↦ Q (toCh u)).card : ℝ) := by
    have h1 : (Fintype.card (Fin (2 ^ b)) : ℝ) = (2 : ℝ) ^ b := by simp
    rw [h1] at hrep
    refine hrep.trans ?_
    exact_mod_cast card_le_card fun u hu ↦ by
      simp only [mem_filter, mem_univ, true_and] at hu
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      obtain ⟨t, ht⟩ := hu
      refine ⟨t, t.2, ?_⟩
      rw [window_toCh_block]
      exact ht
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ b) ^ (Par.R P.N L * C) := by positivity
  have hq := P.one_sub_q_pow_le L
  refine le_trans ?_ hprob
  rw [le_div_iff₀ hpos]
  have h2 : (1 - 1 / (P.N : ℝ)) * ((2 : ℝ) ^ b) ^ (Par.R P.N L * C) ≤
      (1 - (1 - P.q L) ^ Par.R P.N L) * ((2 : ℝ) ^ b) ^ (Par.R P.N L * C) :=
    mul_le_mul_of_nonneg_right (by linarith) hpos.le
  exact h2.trans hcount

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.success_prob := @BCFGJPSSV26.Stable.success_prob
