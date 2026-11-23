-- Prove2me | solution 1 for FlexMargin.eq_5_reduction
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:03:37.044059+00:00
-- url     : https://prove2.me/submissions/11b277b3-ea75-4010-8443-159e2cf4942b

import Mathlib
import Definitions.Def_FlexMargin_InQ
import Definitions.Def_FlexMargin_betaCoef
import Definitions.Def_FlexMargin_dmgi
import Definitions.Def_FlexMargin_dmgi5

set_option autoImplicit false

open Finset FlexMargin

namespace FlexMargin.Eq5Proof

theorem exists_level_fn {α : Type*} [DecidableEq α] :
    ∀ (m : ℕ) (S : Finset α) (cnt : Fin m → ℕ),
      ∑ r, cnt r ≤ S.card →
      ∃ f : α → ℕ, (∀ a ∈ S, f a ≤ m) ∧
        ∀ r : Fin m, (S.filter (fun a => f a = r.val)).card = cnt r
  | 0, S, _, _ => ⟨fun _ => 0, fun _ _ => le_rfl, fun r => Fin.elim0 r⟩
  | m + 1, S, cnt, hsum => by
    rw [Fin.sum_univ_castSucc] at hsum
    have hlast : cnt (Fin.last m) ≤ S.card := by omega
    obtain ⟨A, hAS, hAcard⟩ := Finset.exists_subset_card_eq hlast
    have hsdiff : ∑ r : Fin m, cnt r.castSucc ≤ (S \ A).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAS]
      omega
    obtain ⟨f₀, hf₀_le, hf₀_cnt⟩ := exists_level_fn m (S \ A) (fun r => cnt r.castSucc) hsdiff
    let f : α → ℕ := fun a => if a ∈ A then m else if f₀ a = m then m + 1 else f₀ a
    refine ⟨f, ?_, ?_⟩
    · intro a ha
      simp only [f]
      split_ifs with h1 h2
      · omega
      · omega
      · have : f₀ a ≤ m := hf₀_le a (Finset.mem_sdiff.mpr ⟨ha, h1⟩)
        omega
    · intro r
      rcases Fin.eq_castSucc_or_eq_last r with ⟨r', rfl⟩ | rfl
      · have hr' : r'.val < m := r'.isLt
        have hfilt : S.filter (fun a => f a = r'.val) =
            (S \ A).filter (fun a => f₀ a = r'.val) := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_sdiff, Fin.val_castSucc, f]
          constructor
          · rintro ⟨haS, hfa⟩
            split_ifs at hfa with haA hfm
            · omega
            · omega
            · exact ⟨⟨haS, haA⟩, hfa⟩
          · rintro ⟨⟨haS, haA⟩, hfa⟩
            refine ⟨haS, ?_⟩
            rw [if_neg haA, if_neg (by omega)]
            exact hfa
        rw [Fin.val_castSucc, hfilt, hf₀_cnt r']
      · have hfilt : S.filter (fun a => f a = (Fin.last m).val) = A := by
          ext a
          simp only [Finset.mem_filter, Fin.val_last, f]
          constructor
          · rintro ⟨_, hfa⟩
            split_ifs at hfa with haA hfm
            · exact haA
            · omega
            · exact absurd hfa hfm
          · intro haA
            exact ⟨hAS haA, by rw [if_pos haA]⟩
        rw [hfilt, hAcard]

theorem sum_y_eq {n T : ℕ} (P : Fin T → ℝ) (cat : Fin n → Fin T)
    (K : (t : Fin T) → Fin (t.val + 1) → ℕ)
    (w : Fin n → ℕ) (y : Fin n → ℝ)
    (hw : ∀ i, w i ≤ (cat i).val + 1)
    (hcnt : ∀ (t : Fin T) (r : Fin (t.val + 1)),
      (univ.filter (fun i => cat i = t ∧ w i = r.val)).card = K t r)
    (hy : ∀ i, y i = betaCoef P (cat i) (w i)) :
    ∑ i : Fin n, y i =
      ∑ t : Fin T, ∑ r : Fin (t.val + 1), (K t r : ℝ) * betaCoef P t r.val := by
  have hbeta_top : ∀ t : Fin T, betaCoef P t (t.val + 1) = 0 := by
    intro t
    unfold betaCoef
    have ht : 0 < t.val + 1 ∧ t.val + 1 ≤ T := ⟨by omega, by omega⟩
    rw [dif_pos ht]
    have hidx : (⟨t.val + 1 - 1, by omega⟩ : Fin T) = t := Fin.ext (by simp)
    rw [hidx, sub_self]
  have hy_decomp : ∀ i : Fin n, y i =
      ∑ t : Fin T, ∑ r : Fin (t.val + 1),
        if cat i = t ∧ w i = r.val then betaCoef P t r.val else 0 := by
    intro i
    rw [hy i]
    rw [Finset.sum_eq_single (cat i)]
    · by_cases hlt : w i < (cat i).val + 1
      · rw [Finset.sum_eq_single ⟨w i, hlt⟩]
        · simp
        · intro r _ hne
          have : w i ≠ r.val := fun h => hne (Fin.ext h.symm)
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
      · have hweq : w i = (cat i).val + 1 := by have := hw i; omega
        rw [hweq, hbeta_top (cat i)]
        symm
        apply Finset.sum_eq_zero
        intro r _
        have : (cat i).val + 1 ≠ r.val := by have := r.isLt; omega
        simp [this]
    · intro t _ hne
      apply Finset.sum_eq_zero
      intro r _
      simp [hne.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hy_decomp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  have : (∑ x : Fin n, if cat x = t ∧ w x = r.val then betaCoef P t r.val else 0) =
      ((univ.filter (fun x => cat x = t ∧ w x = r.val)).card : ℝ) * betaCoef P t r.val := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [this, hcnt t r]

end FlexMargin.Eq5Proof

open FlexMargin.Eq5Proof in
theorem solution {m n T : ℕ} (P : Fin T → ℝ) (hP : StrictMono P) (cat : Fin n → Fin T)
    (A : Finset (Fin m × Fin n)) (K : (t : Fin T) → Fin (t.val + 1) → ℕ) (hK : InQ cat K)
    (c : ℝ) :
    dmgi (fun _ => (1 : ℝ)) P cat (fun _ => c) A K =
      c * ∑ t : Fin T, ∑ r : Fin (t.val + 1), (K t r : ℝ) * betaCoef P t r.val +
        dmgi5 P cat A K := by
  set C₀ : ℝ := c * ∑ t : Fin T, ∑ r : Fin (t.val + 1), (K t r : ℝ) * betaCoef P t r.val
  let S₄ : Set ℝ := {v : ℝ | ∃ (w : Fin n → ℕ) (y : Fin n → ℝ) (z : Fin m → ℝ),
    (∀ i, w i ≤ (cat i).val + 1) ∧
    (∀ (t : Fin T) (r : Fin (t.val + 1)),
      (univ.filter (fun i => cat i = t ∧ w i = r.val)).card = K t r) ∧
    (∀ i, y i = betaCoef P (cat i) (w i)) ∧
    (∀ j, 0 ≤ z j) ∧
    (∀ a ∈ A, P (cat a.2) ≤ y a.2 + z a.1) ∧
    v = ∑ i, c * y i + ∑ j, (1 : ℝ) * z j}
  let S₅ : Set ℝ := {v : ℝ | ∃ (w : Fin n → ℕ) (y : Fin n → ℝ) (z : Fin m → ℝ),
    (∀ i, w i ≤ (cat i).val + 1) ∧
    (∀ (t : Fin T) (r : Fin (t.val + 1)),
      (univ.filter (fun i => cat i = t ∧ w i = r.val)).card = K t r) ∧
    (∀ i, y i = betaCoef P (cat i) (w i)) ∧
    (∀ j, 0 ≤ z j) ∧
    (∀ a ∈ A, P (cat a.2) ≤ y a.2 + z a.1) ∧
    v = ∑ j, z j}
  change sInf S₄ = C₀ + sInf S₅
  -- 1. Nonemptiness of S₅ from InQ cat K
  have hS₅_ne : S₅.Nonempty := by
    have hex : ∀ t : Fin T, ∃ ft : Fin n → ℕ,
        (∀ i ∈ univ.filter (fun i => cat i = t), ft i ≤ t.val + 1) ∧
        ∀ r : Fin (t.val + 1),
          ((univ.filter (fun i => cat i = t)).filter (fun i => ft i = r.val)).card = K t r :=
      fun t => exists_level_fn (t.val + 1) (univ.filter (fun i => cat i = t)) (K t) (hK t)
    choose ft hft_le hft_cnt using hex
    let w : Fin n → ℕ := fun i => ft (cat i) i
    let y : Fin n → ℝ := fun i => betaCoef P (cat i) (w i)
    let M : ℝ := ∑ i : Fin n, (|P (cat i)| + |y i|)
    let z : Fin m → ℝ := fun _ => M
    refine ⟨∑ j, z j, w, y, z, ?_, ?_, fun _ => rfl, ?_, ?_, rfl⟩
    · intro i
      exact hft_le (cat i) i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩)
    · intro t r
      have hfilt : univ.filter (fun i => cat i = t ∧ w i = r.val) =
          (univ.filter (fun i => cat i = t)).filter (fun i => ft t i = r.val) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, w]
        constructor
        · rintro ⟨rfl, hw⟩; exact ⟨rfl, hw⟩
        · rintro ⟨rfl, hw⟩; exact ⟨rfl, hw⟩
      rw [hfilt, hft_cnt t r]
    · intro _
      exact Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
    · intro a _
      have hleM : |P (cat a.2)| + |y a.2| ≤ M :=
        Finset.single_le_sum (fun i _ => add_nonneg (abs_nonneg (P (cat i))) (abs_nonneg (y i)))
          (Finset.mem_univ a.2)
      have h1 : P (cat a.2) ≤ |P (cat a.2)| := le_abs_self _
      have h2 : -y a.2 ≤ |y a.2| := neg_le_abs _
      simp only [z]
      linarith
  -- 2. S₅ is bounded below by 0
  have hS₅_bdd : BddBelow S₅ := by
    refine ⟨0, ?_⟩
    rintro _ ⟨_, _, z, -, -, -, hz0, -, rfl⟩
    exact Finset.sum_nonneg fun j _ => hz0 j
  -- 3. S₄ = (C₀ + ·) '' S₅
  have hshift : S₄ = (fun u => C₀ + u) '' S₅ := by
    ext v
    constructor
    · rintro ⟨w, y, z, hw, hcnt, hy, hz0, ha, rfl⟩
      refine ⟨∑ j, z j, ⟨w, y, z, hw, hcnt, hy, hz0, ha, rfl⟩, ?_⟩
      have hcy : ∑ i, c * y i = C₀ := by
        rw [← Finset.mul_sum, sum_y_eq P cat K w y hw hcnt hy]
      have h1z : ∑ j, (1 : ℝ) * z j = ∑ j, z j := by simp
      rw [hcy, h1z]
    · rintro ⟨_, ⟨w, y, z, hw, hcnt, hy, hz0, ha, rfl⟩, rfl⟩
      refine ⟨w, y, z, hw, hcnt, hy, hz0, ha, ?_⟩
      have hcy : ∑ i, c * y i = C₀ := by
        rw [← Finset.mul_sum, sum_y_eq P cat K w y hw hcnt hy]
      have h1z : ∑ j, (1 : ℝ) * z j = ∑ j, z j := by simp
      rw [hcy, h1z]
  rw [hshift]
  have himg_bdd : BddBelow ((fun u => C₀ + u) '' S₅) := by
    obtain ⟨B, hB⟩ := hS₅_bdd
    refine ⟨C₀ + B, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    linarith [hB hu]
  apply le_antisymm
  · have hle : sInf ((fun u => C₀ + u) '' S₅) - C₀ ≤ sInf S₅ := by
      apply le_csInf hS₅_ne
      intro u hu
      have := csInf_le himg_bdd ⟨u, hu, rfl⟩
      linarith
    linarith
  · apply le_csInf (hS₅_ne.image _)
    rintro _ ⟨u, hu, rfl⟩
    linarith [csInf_le hS₅_bdd hu]
