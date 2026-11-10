-- Prove2me | solution 1 for ExponomialAssortment.FPTAS.lemma_3
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:14:16.333902+00:00
-- url     : https://prove2.me/submissions/51b19437-8c4d-459c-aef6-f367bf09c399

import Definitions.Def_ExponomialAssortment_FPTAS_DP

open scoped BigOperators
open ExponomialAssortment.FPTAS

def inst3 : Instance 2 where
  outside := 0
  price i := if i = 0 then 0 else 1
  utility i := if i = 0 then 16 else 0

private lemma valid_inst3 : Valid inst3 := by
  refine ⟨?_, ?_, ?_, ⟨1, rfl⟩, ?_⟩
  · intro i
    fin_cases i <;> simp [inst3]
  · simp [inst3]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [inst3] at hij ⊢
  · intro i
    fin_cases i <;> simp [inst3]

private lemma delta_inst3 : delta 2 (1 / 2 : ℝ) = 1 / 8 := by
  unfold delta
  norm_num

private lemma roundedUtility_inst3 (i : Fin 2) :
    roundedUtility inst3 (1 / 2) i = inst3.utility i := by
  unfold roundedUtility
  rw [delta_inst3]
  fin_cases i
  · simp [inst3]; norm_num
  · simp [inst3]

private lemma pmax_inst3 : pmax inst3 = 1 := by
  unfold pmax
  apply le_antisymm
  · refine Finset.sup'_le _ _ ?_
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
    fin_cases i <;> simp [inst3]
  · have hmem : (1 : ℝ) ∈ Finset.univ.image inst3.price :=
      Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
    exact Finset.le_sup' (f := id) hmem

private lemma pmin_inst3 : pmin inst3 = 1 := by
  unfold pmin
  have hpos : positivePrices inst3 = {1} := by
    ext x
    simp only [positivePrices, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨i, rfl⟩, hx⟩
      fin_cases i
      · simp [inst3] at hx
      · rfl
    · rintro rfl
      exact ⟨⟨1, rfl⟩, by norm_num⟩
  have hne : (positivePrices inst3).Nonempty := by
    rw [hpos]
    exact Finset.singleton_nonempty 1
  rw [dif_pos hne]
  apply le_antisymm
  · have hmem : (1 : ℝ) ∈ positivePrices inst3 := by rw [hpos]; exact Finset.mem_singleton_self 1
    exact Finset.inf'_le (f := id) hmem
  · refine Finset.le_inf' _ _ ?_
    intro y hy
    rw [hpos, Finset.mem_singleton] at hy
    rw [hy]
    rfl

private lemma Delta_inst3 : Delta inst3 (1 / 2) = Real.log 16 := by
  unfold Delta
  rw [pmax_inst3, pmin_inst3]
  norm_num

private lemma kIndex_inst3 : kIndex inst3 (1 / 2) 1 = 128 := by
  unfold kIndex
  rw [delta_inst3]
  have hlt : inst3.outside < (1 : Fin 2) := by decide
  rw [if_pos hlt]
  change (⌊(16 : ℝ) / (1 / 8)⌋ - ⌊(0 : ℝ) / (1 / 8)⌋).toNat = 128
  have hfloor : ⌊(16 : ℝ) / (1 / 8)⌋ - ⌊(0 : ℝ) / (1 / 8)⌋ = 128 := by norm_num
  rw [hfloor]
  decide

private lemma bestSingle_inst3 : bestSingle inst3 (1 / 2) 1 := by
  refine ⟨by decide, ?_⟩
  intro j hj
  fin_cases j
  · exact absurd rfl hj
  · exact le_rfl

private lemma profitable_initial_inst3 :
    Profitable inst3 (1 / 2) 1 (initial inst3 (1 / 2) 1) := by
  unfold Profitable stateCoefficient initial stateGap
  have hlt : inst3.outside < (1 : Fin 2) := by decide
  simp only [hlt, ↓reduceDIte, Fin.val_one, Nat.lt_add_one, Nat.cast_one, one_mul,
    roundedUtility_inst3]
  rw [kIndex_inst3, delta_inst3, Delta_inst3]
  change Real.exp (-(128 : ℝ) * (1 / 8) - Real.log 16) ≤
    Real.exp (-((16 : ℝ) - 16) - (16 - 0)) / (1 + 1)
  have h_lhs : (-(128 : ℝ) * (1 / 8) - Real.log 16) = -16 - Real.log 16 := by norm_num
  have h_rhs : -((16 : ℝ) - 16) - (16 - 0) = -16 := by norm_num
  rw [h_lhs, h_rhs, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
  have hexp : 0 ≤ Real.exp (-16) := le_of_lt (Real.exp_pos (-16))
  linarith

theorem solution :
    ¬ (∀ (n : ℕ) (I : Instance n) (_hI : Valid I) (C : ℕ)
      (_hC : 1 ≤ C ∧ C ≤ n) (η : ℝ) (_hη : 0 < η) (_hp : ∃ i, 0 < I.price i)
      (l f : Fin n) (_hl : bestSingle I η l) (_hf : f ≠ I.outside)
      (s : State) (_hr : Reachable I C η l f s) (_hs : Profitable I η l s),
      (kIndex I η l : ℝ) * delta n η - Delta I η ≤ s.utilitySum ∧
      s.utilitySum ≤ (kIndex I η l : ℝ) * delta n η + Delta I η) := by
  intro h
  have hC : 1 ≤ (2 : ℕ) ∧ (2 : ℕ) ≤ 2 := ⟨by decide, by decide⟩
  have hη : (0 : ℝ) < 1 / 2 := by norm_num
  have hp : ∃ i : Fin 2, 0 < inst3.price i := ⟨1, by simp [inst3]⟩
  have hf : (1 : Fin 2) ≠ inst3.outside := by decide
  have hr : Reachable inst3 2 (1 / 2) 1 1 (initial inst3 (1 / 2) 1) :=
    Relation.ReflTransGen.refl
  have hle := (h 2 inst3 valid_inst3 2 hC (1 / 2) hη hp 1 1 bestSingle_inst3 hf
    (initial inst3 (1 / 2) 1) hr profitable_initial_inst3).1
  rw [kIndex_inst3, delta_inst3, Delta_inst3] at hle
  have husum : (initial inst3 (1 / 2) 1).utilitySum = 0 := by
    unfold initial
    have hlt : inst3.outside < (1 : Fin 2) := by decide
    simp [inst3]
  rw [husum] at hle
  have hlog : Real.log 16 ≤ 16 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  linarith
