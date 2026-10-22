-- Prove2me | solution 1 for FarmerInfo.Exclusive.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:41:18.490224+00:00
-- url     : https://prove2.me/submissions/b756879c-047f-4322-b708-74556240c098

import Mathlib
import Definitions.Def_FarmerInfo_Exclusive_Setting
import Theorems.Thm_FarmerInfo_Exclusive_proposition_1_existence
import Theorems.Thm_FarmerInfo_Exclusive_proposition_1_uniqueness
import Theorems.Thm_FarmerInfo_Exclusive_lemma_2
import Theorems.Thm_FarmerInfo_Exclusive_proposition_2_after_two
import Theorems.Thm_FarmerInfo_Exclusive_proposition_2_one_gt_two
import Theorems.Thm_FarmerInfo_Exclusive_proposition_2_one_minus_zero

open MeasureTheory Finset FarmerInfo.Exclusive

theorem solution (M : Model) (hM : M.Standing) :
    (∀ I : Finset (Fin M.n), ∃ σ : Fin M.n → Model.Strategy, M.IsBNE I σ) ∧
    (0 < M.V → ∀ I I' : Finset (Fin M.n), I'.card = 1 → I.card ≠ 1 →
      ∀ σ σ' : Fin M.n → Model.Strategy,
        M.IsBNE I σ → M.IsBNE I' σ' → M.welfare I σ < M.welfare I' σ') ∧
    (M.V ≤ 0 → ∀ I : Finset (Fin M.n),
      ∀ σ σ' : Fin M.n → Model.Strategy,
        M.IsBNE I σ → M.IsBNE ∅ σ' → M.welfare I σ ≤ M.welfare ∅ σ') ∧
    (M.V < 0 → ∀ I : Finset (Fin M.n), I.Nonempty →
      ∀ σ σ' : Fin M.n → Model.Strategy,
        M.IsBNE I σ → M.IsBNE ∅ σ' → M.welfare I σ < M.welfare ∅ σ') := by
  obtain ⟨hn, ha, hb, hα, hβ, hγ⟩ := hM
  have hM' : M.Standing := ⟨hn, ha, hb, hα, hβ, hγ⟩
  -- welfare of any equilibrium equals the closed form W(|I|)
  have hwelf : ∀ (I : Finset (Fin M.n)) (σ : Fin M.n → Model.Strategy),
      M.IsBNE I σ → M.welfare I σ = M.W (I.card : ℝ) := by
    intro I σ hσ
    have hu := proposition_1_uniqueness M hM' I σ hσ
    have hall : ∀ᵐ ω ∂M.P, ∀ k : Fin M.n,
        σ k (M.obs I k ω) = M.linProfile I k (M.obs I k ω) := ae_all_iff.2 hu
    have heq : M.welfare I σ = M.welfare I (M.linProfile I) := by
      unfold Model.welfare
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine integral_congr_ae ?_
      filter_upwards [hall] with ω hω
      simp only [Model.profit, hω]
    rw [heq]
    have hL := lemma_2 M hM' I
    unfold Model.welfare
    have hsum : ∀ i ∈ (Finset.univ : Finset (Fin M.n)),
        (∫ ω, M.profit I (M.linProfile I) i ω ∂M.P) =
          if i ∈ I then M.WI (I.card : ℝ) else M.WJ (I.card : ℝ) := by
      intro i _
      split_ifs with h
      · exact hL.1 i h
      · exact hL.2.1 i h
    rw [Finset.sum_congr rfl hsum, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    have h1 : (Finset.univ.filter (fun i : Fin M.n => i ∈ I)) = I := by
      ext i; simp
    have h2 : (Finset.univ.filter (fun i : Fin M.n => i ∉ I)).card = M.n - I.card := by
      have : (Finset.univ.filter (fun i : Fin M.n => i ∉ I)) = Finset.univ \ I := by
        ext i; simp
      rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin]
    have hle : I.card ≤ M.n := by
      simpa using Finset.card_le_univ I
    rw [h1, h2, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub hle]
    unfold Model.W
    ring
  have h10 := proposition_2_one_minus_zero M hM'
  have h12 := proposition_2_one_gt_two M hM'
  have hanti := (proposition_2_after_two M hM').2
  have hD : 0 < M.b * (2 * M.α + M.γ + (M.n : ℝ) * M.γ) ^ 2 *
          (4 * M.α ^ 2 + (1 + (M.n : ℝ)) * M.γ * (M.β + M.γ) +
            2 * M.α * (2 * M.β + (2 + (M.n : ℝ)) * M.γ)) ^ 2 := by positivity
  -- policies above two are dominated by two
  have hbig : ∀ m : ℕ, 2 ≤ m → m ≤ M.n → M.W (m : ℝ) ≤ M.W 2 := by
    intro m h2 hm
    rcases Nat.eq_or_lt_of_le h2 with h | h
    · subst h; norm_num
    · have hm2 : (2 : ℝ) < m := by exact_mod_cast h
      have hmn : (m : ℝ) ≤ M.n := by exact_mod_cast hm
      have h2n : (2 : ℝ) ≤ M.n := le_trans hm2.le hmn
      exact (hanti ⟨le_refl _, h2n⟩ ⟨hm2.le, hmn⟩ hm2).le
  have hcard : ∀ I : Finset (Fin M.n), I.card ≤ M.n := fun I => by
    simpa using Finset.card_le_univ I
  refine ⟨fun I => ⟨M.linProfile I, proposition_1_existence M hM' I⟩, ?_, ?_, ?_⟩
  · intro hV I I' hI' hI σ σ' hσ hσ'
    rw [hwelf I σ hσ, hwelf I' σ' hσ', hI']
    have hpos : 0 < M.W 1 - M.W 0 := by rw [h10]; positivity
    push_cast
    rcases Nat.lt_or_ge I.card 2 with h | h
    · have : I.card = 0 := by omega
      rw [this]; push_cast; linarith
    · have := hbig I.card h (hcard I); linarith
  · intro hV I σ σ' hσ hσ'
    rw [hwelf I σ hσ, hwelf ∅ σ' hσ', Finset.card_empty]
    have hnp : M.W 1 - M.W 0 ≤ 0 := by
      rw [h10]; exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hD.le
    push_cast
    rcases Nat.lt_or_ge I.card 2 with h | h
    · interval_cases hc : I.card
      · simp
      · push_cast; linarith
    · have := hbig I.card h (hcard I); linarith
  · intro hV I hne σ σ' hσ hσ'
    rw [hwelf I σ hσ, hwelf ∅ σ' hσ', Finset.card_empty]
    have hneg : M.W 1 - M.W 0 < 0 := by
      rw [h10]; exact div_neg_of_neg_of_pos (by nlinarith) hD
    have hc1 : 1 ≤ I.card := Finset.card_pos.2 hne
    push_cast
    rcases Nat.lt_or_ge I.card 2 with h | h
    · have : I.card = 1 := by omega
      rw [this]; push_cast; linarith
    · have := hbig I.card h (hcard I); linarith
