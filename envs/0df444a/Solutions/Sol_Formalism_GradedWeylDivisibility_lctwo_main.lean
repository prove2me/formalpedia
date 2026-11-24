-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lctwo_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:24:59.368188+00:00
-- url     : https://prove2.me/submissions/45b06289-8901-4129-87b0-f2a40f0b69fe

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TwoColumn
import Theorems.Thm_Formalism_GradedWeylDivisibility_lctwo_le_of_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_lctwo_sum_ite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (h1 : PeelDecomp) (h2 : PeelHomog) (h3 : PeelLead) (h4 : PeelDegBound)
    (B : Type) [CommRing B] [IsDomain B] (r n : ℕ) (l j : Fin n) (hlj : l < j) :
    ∀ (d a0 s : ℕ) (ω : Fin r × Fin n →₀ ℕ) (g : MvPolynomial (Fin r × Fin n) B), r - a0 = d →
    g ≠ 0 → IsWeightedHomogeneous (pairW l j) g ω → (∀ b : Fin r, b.val < a0 → ω (b, l) = 0) →
    degreeOf none (colAddGen B l j g) ≤ s → InterlacedAt s l j ((colLex r n).degree g) := by
  intro d
  induction d with
  | zero =>
    intro a0 s ω g hd hg hω h0 _
    unfold InterlacedAt
    intro a
    have hmg := (colLex r n).degree_mem_support hg
    have hz : (∑ b : Fin r with b ≤ a, (colLex r n).degree g (b, j)) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      have hb := b.isLt
      have hle := (lctwo_le_of_mem hlj.ne hω hmg b).2
      rw [h0 b (by omega)] at hle
      omega
    rw [hz]
    exact Nat.zero_le _
  | succ d ih =>
    classical
    intro a0 s ω g hd hg hω h0 hdeg
    have ha0 : a0 < r := by omega
    obtain ⟨A0, hA0⟩ : ∃ A0 : Fin r, A0.val = a0 := ⟨⟨a0, ha0⟩, rfl⟩
    have hmg := (colLex r n).degree_mem_support hg
    have hm_low : ∀ b : Fin r, b.val < a0 → (colLex r n).degree g (b, j) = 0 := by
      intro b hb
      have hle := (lctwo_le_of_mem hlj.ne hω hmg b).2
      rw [h0 b hb] at hle
      omega
    have hlow : ∀ b : Fin r, b < A0 → ω (b, l) = 0 := fun b hb =>
      h0 b (by rw [Fin.lt_def] at hb; omega)
    have hdec := h1 B r n l j hlj.ne A0 ω g hω
    have hvan : ∀ k, ω (A0, l) < k → peel l j A0 k g = 0 := by
      intro k hk
      unfold peel
      apply Finset.sum_eq_zero
      intro m hm
      have hm' := Finset.mem_filter.mp hm
      have hle := (lctwo_le_of_mem hlj.ne hω hm'.1 A0).1
      exfalso
      omega
    have hex : ∃ k ∈ Finset.range (ω (A0, l) + 1), peel l j A0 k g ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hg (hdec.trans (Finset.sum_eq_zero fun k hk => by rw [hne k hk, mul_zero]))
    obtain ⟨k0, hk0, hk00⟩ := hex
    obtain ⟨K, hKT, hKmax⟩ := Finset.exists_max_image
      ((Finset.range (ω (A0, l) + 1)).filter (fun k => peel l j A0 k g ≠ 0)) id
      ⟨k0, Finset.mem_filter.mpr ⟨hk0, hk00⟩⟩
    obtain ⟨hKr, hK0⟩ := Finset.mem_filter.mp hKT
    have hKle : K ≤ ω (A0, l) := by
      have := Finset.mem_range.mp hKr
      omega
    have habove : ∀ k, K < k → peel l j A0 k g = 0 := by
      intro k hk
      by_contra hne
      by_cases hkω : k ≤ ω (A0, l)
      · have hkK := hKmax k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hne⟩)
        exact absurd (show k ≤ K from hkK) (by omega)
      · exact hne (hvan k (by omega))
    have hgK : g = ∑ k ∈ Finset.range (K + 1),
        X (A0, l) ^ k * X (A0, j) ^ (ω (A0, l) - K + (K - k)) * peel l j A0 k g := by
      have hsub : Finset.range (K + 1) ⊆ Finset.range (ω (A0, l) + 1) := by
        intro x hx
        simp only [Finset.mem_range] at hx ⊢
        omega
      calc g = ∑ k ∈ Finset.range (ω (A0, l) + 1),
            X (A0, l) ^ k * X (A0, j) ^ (ω (A0, l) - k) * peel l j A0 k g := hdec
        _ = ∑ k ∈ Finset.range (K + 1),
            X (A0, l) ^ k * X (A0, j) ^ (ω (A0, l) - k) * peel l j A0 k g := by
          symm
          apply Finset.sum_subset hsub
          intro k _ hkK
          simp only [Finset.mem_range, not_lt] at hkK
          rw [habove k (by omega), mul_zero]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k hk
          have := Finset.mem_range.mp hk
          rw [show ω (A0, l) - K + (K - k) = ω (A0, l) - k by omega]
    have hdeg' : degreeOf none (colAddGen B l j (∑ k ∈ Finset.range (K + 1),
        X (A0, l) ^ k * X (A0, j) ^ (ω (A0, l) - K + (K - k)) * peel l j A0 k g)) ≤ s := by
      rw [← hgK]
      exact hdeg
    have hslice_supp : ∀ k, ∀ m ∈ (peel l j A0 k g).support, m (A0, l) = 0 ∧ m (A0, j) = 0 :=
      fun k => (h2 B r n l j hlj.ne A0 ω k g hω).2
    obtain ⟨he, hdegK⟩ := h4 B r n l j hlj.ne A0 K (ω (A0, l) - K) s
      (fun k => peel l j A0 k g) hslice_supp hK0 hdeg'
    have hlead := h3 B r n l j hlj A0 ω g K hω hlow hK0 habove
    have hhomK := (h2 B r n l j hlj.ne A0 ω K g hω).1
    have h0' : ∀ b : Fin r, b.val < a0 + 1 → (ω.erase (A0, l)) (b, l) = 0 := by
      intro b hb
      rw [Finsupp.erase_apply]
      split_ifs with hbA
      · rfl
      · apply h0 b
        have hne : b ≠ A0 := fun h => hbA (by rw [h])
        have hne' : b.val ≠ A0.val := fun h => hne (Fin.ext h)
        omega
    have hIH := ih (a0 + 1) (s - (ω (A0, l) - K) + K) (ω.erase (A0, l)) (peel l j A0 K g)
      (by omega) hK0 hhomK h0' hdegK
    have hmK := (colLex r n).degree_mem_support hK0
    have hm'_low : ∀ b : Fin r, b.val < a0 + 1 →
        (colLex r n).degree (peel l j A0 K g) (b, j) = 0 := by
      intro b hb
      have hle := (lctwo_le_of_mem hlj.ne hhomK hmK b).2
      rw [h0' b hb] at hle
      omega
    have hjx : ∀ b : Fin r, (colLex r n).degree g (b, j) =
        (if A0 = b then ω (A0, l) - K else 0) +
          (colLex r n).degree (peel l j A0 K g) (b, j) := by
      intro b
      rw [hlead]
      by_cases hb : A0 = b <;> simp [hlj.ne', hb]
    have hlx : ∀ b : Fin r, (colLex r n).degree g (b, l) =
        (if A0 = b then K else 0) + (colLex r n).degree (peel l j A0 K g) (b, l) := by
      intro b
      rw [hlead]
      by_cases hb : A0 = b <;> simp [hlj.ne, hb]
    unfold InterlacedAt at hIH ⊢
    intro a
    have hIa := hIH a
    by_cases haA : a.val < a0
    · have hz : (∑ b : Fin r with b ≤ a, (colLex r n).degree g (b, j)) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        have hba := Fin.le_iff_val_le_val.mp (Finset.mem_filter.mp hb).2
        exact hm_low b (by omega)
      rw [hz]
      exact Nat.zero_le _
    · have hsj : (∑ b : Fin r with b ≤ a, (colLex r n).degree g (b, j)) =
          (if A0 ≤ a then ω (A0, l) - K else 0) +
            ∑ b : Fin r with b ≤ a, (colLex r n).degree (peel l j A0 K g) (b, j) := by
        simp only [hjx]
        exact lctwo_sum_ite A0 (ω (A0, l) - K) _ (fun b => b ≤ a)
      have hsl : (∑ b : Fin r with b < a, (colLex r n).degree g (b, l)) =
          (if A0 < a then K else 0) +
            ∑ b : Fin r with b < a, (colLex r n).degree (peel l j A0 K g) (b, l) := by
        simp only [hlx]
        exact lctwo_sum_ite A0 K _ (fun b => b < a)
      have hAa : A0 ≤ a := Fin.le_iff_val_le_val.mpr (by omega)
      rw [hsj, hsl, if_pos hAa]
      by_cases hEq : a.val = a0
      · have hAa' : ¬ A0 < a := by
          rw [Fin.lt_def]
          omega
        have hz : (∑ b : Fin r with b ≤ a,
            (colLex r n).degree (peel l j A0 K g) (b, j)) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          have hba := Fin.le_iff_val_le_val.mp (Finset.mem_filter.mp hb).2
          exact hm'_low b (by omega)
        rw [if_neg hAa', hz]
        omega
      · have hAa' : A0 < a := by
          rw [Fin.lt_def]
          omega
        rw [if_pos hAa']
        omega
end Formalism.GradedWeylDivisibility
