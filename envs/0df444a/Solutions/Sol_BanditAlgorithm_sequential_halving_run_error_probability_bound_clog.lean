-- Prove2me | solution 1 for BanditAlgorithm.sequential_halving_run_error_probability_bound_clog
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T16:40:31.054551+00:00
-- url     : https://prove2.me/submissions/396e638e-4ce9-4b9a-80fa-dc7b6049acb9

import Theorems.Thm_BanditAlgorithm_sequential_halving_bad_final_probability_bound_clog

open MeasureTheory Finset
open BanditAlgorithm

private lemma seqHalvingCount_mono {k m : ℕ} (hkm : k ≤ m) :
    ∀ ℓ, seqHalvingCount k ℓ ≤ seqHalvingCount m ℓ := by
  intro ℓ
  induction ℓ with
  | zero => simpa [seqHalvingCount]
  | succ ℓ ih =>
      simp only [seqHalvingCount]
      exact Nat.div_le_div_right (Nat.add_le_add_right ih 1)

private lemma seqHalvingCount_two_pow_add (a ℓ : ℕ) :
    seqHalvingCount (2 ^ (a + ℓ)) ℓ = 2 ^ a := by
  induction ℓ generalizing a with
  | zero => simp [seqHalvingCount]
  | succ ℓ ih =>
      rw [seqHalvingCount]
      have hpow : 2 ^ (a + (ℓ + 1)) = 2 ^ ((a + 1) + ℓ) := by
        congr 1
        omega
      rw [hpow, ih (a + 1)]
      simp only [pow_succ]
      omega

private lemma seqHalvingCount_clog_le_one (k : ℕ) :
    seqHalvingCount k (Nat.clog 2 k) ≤ 1 := by
  have hkpow : k ≤ 2 ^ Nat.clog 2 k := Nat.le_pow_clog (by omega) k
  calc
    seqHalvingCount k (Nat.clog 2 k) ≤
        seqHalvingCount (2 ^ Nat.clog 2 k) (Nat.clog 2 k) :=
      seqHalvingCount_mono hkpow _
    _ = 1 := by
      simpa using seqHalvingCount_two_pow_add 0 (Nat.clog 2 k)

private lemma active_card_eq_seqHalvingCount {k n : ℕ}
    {h : BanditHistory k n} {A : ℕ → Finset (Fin k)}
    (hA0 : A 0 = Finset.univ)
    (hA : ∀ ℓ < Nat.clog 2 k,
      A (ℓ + 1) ⊆ A ℓ ∧
      (A (ℓ + 1)).card = ((A ℓ).card + 1) / 2 ∧
      (∀ i ∈ A (ℓ + 1), ∀ j ∈ A ℓ \ A (ℓ + 1),
        seqHalvingPhaseMean h ℓ j ≤ seqHalvingPhaseMean h ℓ i) ∧
      (∀ t ∈ seqHalvingPhase k n ℓ, (h t).1 ∈ A ℓ) ∧
      (∀ i ∈ A ℓ,
        ((seqHalvingPhase k n ℓ).filter (fun t ↦ (h t).1 = i)).card =
          seqHalvingPulls k n ℓ)) :
    ∀ ℓ ≤ Nat.clog 2 k, (A ℓ).card = seqHalvingCount k ℓ := by
  intro ℓ hℓ
  induction ℓ with
  | zero => simp [hA0, seqHalvingCount]
  | succ ℓ ih =>
      have hlt : ℓ < Nat.clog 2 k := by omega
      rw [(hA ℓ hlt).2.1, ih (by omega), seqHalvingCount]

theorem solution {k n : ℕ}
    (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (hsorted : ∀ i j : Fin k, i ≤ j → banditArmMean ν j ≤ banditArmMean ν i)
    (hn : k * Nat.clog 2 k ≤ n) (H₂ : ℝ)
    (hH₂ : ∀ i : Fin k, 0 < banditGap ν i →
      ((i : ℕ) + 1 : ℝ) / banditGap ν i ^ 2 ≤ H₂)
    (π : BanditPolicy k) (rec : BanditHistory k n → Fin k) :
    (banditMeasure ν π n).real
        {h | IsSeqHalvingRun k n h (rec h) ∧ 0 < banditGap ν (rec h)} ≤
      3 * (Nat.clog 2 k : ℝ) *
        Real.exp (-(n / (16 * H₂ * (Nat.clog 2 k : ℝ)))) := by
  let μ := banditMeasure ν π n
  have hsubset :
      {h | IsSeqHalvingRun k n h (rec h) ∧ 0 < banditGap ν (rec h)} ⊆
        {h | IsSeqHalvingBadFinalRun k n ν h} := by
    intro h hh
    rcases hh.1 with ⟨A, hA0, hA, hrec⟩
    have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) (rec h).isLt
    letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
    let i₀ : Fin k := ⟨0, hk⟩
    have hi₀_le (i : Fin k) : i₀ ≤ i := by
      exact Fin.zero_le i
    have hopt : banditOptimalMean ν = banditArmMean ν i₀ := by
      apply le_antisymm
      · rw [banditOptimalMean]
        exact ciSup_le fun i ↦ hsorted i₀ i (hi₀_le i)
      · rw [banditOptimalMean]
        exact le_ciSup (Finite.bddAbove_range fun i : Fin k ↦ banditArmMean ν i) i₀
    have hi₀gap : banditGap ν i₀ = 0 := by
      simp [banditGap, hopt]
    have hcard : (A (Nat.clog 2 k)).card ≤ 1 := by
      rw [active_card_eq_seqHalvingCount hA0 hA _ (by omega)]
      exact seqHalvingCount_clog_le_one k
    have hfinal : ∀ i ∈ A (Nat.clog 2 k), 0 < banditGap ν i := by
      intro i hi
      have heq : i = rec h :=
        Finset.card_le_one.mp hcard i hi (rec h) hrec
      simpa [heq] using hh.2
    exact ⟨A, hA0, hA, ⟨i₀, by simp [hA0], hi₀gap⟩, hfinal⟩
  exact (measureReal_mono hsubset).trans
    (sequential_halving_bad_final_probability_bound_clog
      ν hν hsorted hn H₂ hH₂ π)
