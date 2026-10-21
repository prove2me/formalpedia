-- Prove2me | solution 1 for CloudMWU.Bicriteria.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:08:40.647978+00:00
-- url     : https://prove2.me/submissions/eea21c02-57dd-4591-8462-e42762909a2d

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model
import Theorems.Thm_CloudMWU_Bicriteria_proposition_2_weak_duality
import Theorems.Thm_CloudMWU_Bicriteria_claim_3_1
import Theorems.Thm_CloudMWU_Bicriteria_claim_3_2_block_work

open Finset CloudMWU.Bicriteria

theorem cmw_t3_queue_nonneg (a ℓ : ℕ → ℝ) (u : ℕ) : 0 ≤ queue a ℓ u := by
  cases u with
  | zero => simp [queue]
  | succ u => simp only [queue]; exact le_max_left _ _

set_option maxHeartbeats 1000000 in
theorem solution (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3) (β : Fin N → ℝ)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h)
    (hstar : ℕ → Fin N → ℝ) (hstar_alloc : IsAllocSeq (1 - 4 * ε) hstar) (t : ℕ) :
    totalWork hstar L t - totalWork h L t
      ≤ 8 * (N : ℝ) / (ε ^ 2 * η) * Real.log ((N : ℝ) / ε) + 2 := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hεN : 0 < ε / (N : ℝ) := by positivity
  -- allocations of the algorithm
  have hsimp : ∀ τ, h τ ∈ truncSimplex N ε := by
    intro τ
    cases τ with
    | zero => exact hrun.1
    | succ τ => exact (hrun.2 τ).2.1
  have hpos : ∀ τ i, 0 ≤ h τ i := fun τ i => le_trans hεN.le ((hsimp τ).2 i)
  -- per-step total work
  set Wst : ℕ → ℝ := fun τ => ∑ i, work (fun s => h s i) (fun s => L s i) τ with hWst
  have hW0 : ∀ τ, 0 ≤ Wst τ := by
    intro τ
    apply Finset.sum_nonneg
    intro i _
    exact le_min (hpos τ i) (add_nonneg (hL τ i) (cmw_t3_queue_nonneg _ _ _))
  have hW1 : ∀ τ, Wst τ ≤ 1 := by
    intro τ
    calc Wst τ ≤ ∑ i, h τ i := Finset.sum_le_sum (fun i _ => min_le_left _ _)
      _ = 1 := (hsimp τ).1
  have hWtot : ∀ u, totalWork h L u = ∑ τ ∈ range u, Wst τ := by
    intro u
    unfold totalWork cumWork
    rw [Finset.sum_comm]
  have hWdiff : ∀ u v, u ≤ v → totalWork h L v - totalWork h L u = ∑ τ ∈ Ico u v, Wst τ := by
    intro u v huv
    rw [hWtot, hWtot, Finset.sum_Ico_eq_sub _ huv]
  have hIco_le : ∀ u v, u ≤ v → ∑ τ ∈ Ico u v, Wst τ ≤ ((v : ℝ) - (u : ℝ)) := by
    intro u v huv
    have := Finset.sum_le_card_nsmul (Ico u v) Wst 1 (fun τ _ => hW1 τ)
    rw [Nat.card_Ico, nsmul_eq_mul, mul_one, Nat.cast_sub huv] at this
    exact this
  have hIco_ge : ∀ u v, 0 ≤ ∑ τ ∈ Ico u v, Wst τ := fun u v =>
    Finset.sum_nonneg (fun τ _ => hW0 τ)
  -- the block length
  set st := sTilde N ε η with hst
  have hlog : 1 ≤ Real.log ((N : ℝ) / ε) := by
    have h20 : (20 : ℝ) ≤ (N : ℝ) / ε := by
      rw [le_div_iff₀ hε]; nlinarith
    have he : Real.exp 1 ≤ (N : ℝ) / ε := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) he
  have hst_eq : st = 4 * (N : ℝ) / (ε ^ 2 * η) * Real.log ((N : ℝ) / ε) := by
    rw [hst]; unfold sTilde cLem1; field_simp
  have hst_pos : 0 < st := by rw [hst_eq]; have := hlog; positivity
  set m := ⌈st⌉₊ with hm_def
  have hm1 : st ≤ (m : ℝ) := Nat.le_ceil st
  have hm2 : (m : ℝ) < st + 1 := Nat.ceil_lt_add_one hst_pos.le
  have hmpos : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_of_lt_of_le hst_pos hm1
    exact_mod_cast this
  -- the switching time s*
  let P : ℕ → Prop := fun s => totalLoad L s ≤ totalWork h L (s + m)
  have hP0 : P 0 := by
    show totalLoad L 0 ≤ totalWork h L (0 + m)
    rw [hWtot]
    have : totalLoad L 0 = 0 := by simp [totalLoad, cumLoad]
    rw [this]; exact Finset.sum_nonneg (fun τ _ => hW0 τ)
  set sS := Nat.findGreatest P t with hsS
  have hsS_le : sS ≤ t := Nat.findGreatest_le t
  have hPs : P sS := Nat.findGreatest_spec (Nat.zero_le t) hP0
  have hnotP : ∀ k, sS < k → k ≤ t → ¬ P k := fun k hk hkt =>
    Nat.findGreatest_is_greatest hk hkt
  -- weak duality
  have hdual := proposition_2_weak_duality N (4 * ε) (by linarith) (by linarith) L hL hstar
    hstar_alloc sS t hsS_le
  -- growth after s*
  have hF : ∀ u, sS + 1 ≤ u → u ≤ t →
      totalWork h L (sS + 1) + (1 - 4 * ε) * ((u : ℝ) - ((sS : ℝ) + 1))
        ≤ totalWork h L u + m := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hu1 hut
      by_cases hcase : u < sS + 1 + m
      · have h1 := hWdiff (sS + 1) u hu1
        have h2 := hIco_ge (sS + 1) u
        have h3 : (u : ℝ) - ((sS : ℝ) + 1) ≤ m := by
          have : (u : ℝ) < (sS : ℝ) + 1 + m := by exact_mod_cast hcase
          linarith
        have h4 : 0 ≤ (u : ℝ) - ((sS : ℝ) + 1) := by
          have : ((sS + 1 : ℕ) : ℝ) ≤ u := by exact_mod_cast hu1
          push_cast at this; linarith
        have h5 : (1 - 4 * ε) * ((u : ℝ) - ((sS : ℝ) + 1)) ≤ (u : ℝ) - ((sS : ℝ) + 1) := by
          nlinarith
        linarith
      · push_neg at hcase
        set r := u - m with hr
        have hr1 : sS + 1 ≤ r := by omega
        have hrt : r ≤ t := by omega
        have hru : r + m = u := by omega
        have hrlt : r < u := by omega
        have hfail : totalWork h L (r + m) < totalLoad L r := by
          have := hnotP r (by omega) hrt
          simp only [P, not_le] at this
          exact this
        obtain ⟨i₀, hi₀⟩ := claim_3_1 N hN ε η hε hε' hη hη' β L hL h hrun r m hfail
        have hblock := claim_3_2_block_work N hN ε η hε hε' hη hη' β L hL h hrun r m hm1 i₀ hi₀
        have hd := hWdiff r (r + m) (by omega)
        rw [hru] at hd
        have hIH := ih r hrlt hr1 hrt
        have hcast : (u : ℝ) = (r : ℝ) + (m : ℝ) := by rw [← hru]; push_cast; ring
        have hblock' : (1 - 4 * ε) * (m : ℝ) ≤ totalWork h L u - totalWork h L r := by
          rw [hd]; rw [hru] at hblock; exact hblock
        rw [hcast]
        nlinarith
  -- conclude: W* - W ≤ 2m
  have hmain : totalWork hstar L t - totalWork h L t ≤ 2 * (m : ℝ) := by
    have hPs' : totalLoad L sS ≤ totalWork h L (sS + m) := hPs
    by_cases hts : t = sS
    · have h1 := hWdiff sS (sS + m) (by omega)
      have h2 := hIco_le sS (sS + m) (by omega)
      push_cast at h2
      rw [← hts] at h1 h2 hPs' hdual
      have : (t : ℝ) - (t : ℝ) = 0 := sub_self _
      rw [this, mul_zero, add_zero] at hdual
      have hm0 : (0 : ℝ) ≤ m := by positivity
      linarith
    · have hts' : sS + 1 ≤ t := by omega
      have hFt := hF t hts' le_rfl
      have h1 := hWdiff (sS + 1) (sS + m) (by omega)
      have h2 := hIco_le (sS + 1) (sS + m) (by omega)
      push_cast at h2
      have h3 : (1 - 4 * ε) * ((t : ℝ) - (sS : ℝ))
          = (1 - 4 * ε) * ((t : ℝ) - ((sS : ℝ) + 1)) + (1 - 4 * ε) := by ring
      have h4 : (1 - 4 * ε) ≤ 1 := by linarith
      linarith
  have hfin : 2 * (m : ℝ) ≤ 8 * (N : ℝ) / (ε ^ 2 * η) * Real.log ((N : ℝ) / ε) + 2 := by
    have : 8 * (N : ℝ) / (ε ^ 2 * η) * Real.log ((N : ℝ) / ε) = 2 * st := by
      rw [hst_eq]; ring
    rw [this]; linarith
  linarith
