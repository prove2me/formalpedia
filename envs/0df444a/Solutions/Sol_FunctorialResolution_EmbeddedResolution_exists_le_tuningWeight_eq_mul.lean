-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_le_tuningWeight_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:49:13.476894+00:00
-- url     : https://prove2.me/submissions/92daa148-0b21-4012-b38e-0317cae1b6d9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdealPowers
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_sub
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_eq_sum
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_fun_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
private theorem tuningWeight_ite (m j q : ℕ) (hj : j ∈ Finset.range m) :
    tuningWeight m (fun i => if i = j then q else 0) = (m - j) * q := by
  simp only [tuningWeight_eq_sum]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hcon
    exact absurd hj hcon
section
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
end
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (m L r : ℕ) (hL : 0 < L)
    (hdvd : ∀ w : ℕ, 1 ≤ w → w ≤ m → w ∣ L) (c : ℕ → ℕ)
    (hc : r * L + (m - 1) * L ≤ tuningWeight m c) :
    ∃ c' : ℕ → ℕ, (∀ j, c' j ≤ c j) ∧ tuningWeight m c' = r * L := by
  induction r generalizing c with
  | zero =>
      refine ⟨fun _ => 0, fun i => Nat.zero_le _, ?_⟩
      simp [tuningWeight_eq_sum]
  | succ r ih =>
      have hWpos : 0 < tuningWeight m c :=
        lt_of_lt_of_le (mul_pos (Nat.succ_pos r) hL) (le_trans (Nat.le_add_right _ _) hc)
      have hm : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0] at hWpos
          simp [tuningWeight_eq_sum] at hWpos
        · exact h0
      have hlt1 : ∀ a b : ℕ, a < b → a ≤ b - 1 := by
        intro a b h
        omega
      have hex : ∃ j ∈ Finset.range m, L ≤ (m - j) * c j := by
        by_contra hcon
        push Not at hcon
        have h1 : tuningWeight m c ≤ ∑ _x ∈ Finset.range m, (L - 1) := by
          rw [tuningWeight_eq_sum]
          refine Finset.sum_le_sum ?_
          intro i hi
          exact hlt1 _ _ (hcon i hi)
        have h2 : ∑ _x ∈ Finset.range m, (L - 1) = m * (L - 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        rw [h2] at h1
        have hA : m * (L - 1) + m = m * L := by
          have h' : L - 1 + 1 = L := Nat.sub_add_cancel hL
          calc m * (L - 1) + m = m * (L - 1 + 1) := by ring
            _ = m * L := by rw [h']
        have hB : (m - 1) * L + L = m * L := by
          have h' : m - 1 + 1 = m := Nat.sub_add_cancel hm
          calc (m - 1) * L + L = (m - 1 + 1) * L := by ring
            _ = m * L := by rw [h']
        have hC : L ≤ (r + 1) * L := by
          calc L = 1 * L := (one_mul L).symm
            _ ≤ (r + 1) * L := Nat.mul_le_mul (by omega) (le_refl L)
        have key : ∀ X Y Z W mm p : ℕ,
            X + Y ≤ Z → Z + mm = W → Y + p = W → p ≤ X → 1 ≤ mm → False := by
          intro X Y Z W mm p k1 k2 k3 k4 k5
          omega
        exact key ((r + 1) * L) ((m - 1) * L) (m * (L - 1)) (m * L) m L
          (le_trans hc h1) hA hB hC hm
      obtain ⟨j, hjmem, hjL⟩ := hex
      have hjm : j < m := Finset.mem_range.mp hjmem
      have hw0 : 0 < m - j := Nat.sub_pos_of_lt hjm
      have hw1 : 1 ≤ m - j := hw0
      obtain ⟨q, hq⟩ := hdvd (m - j) hw1 (Nat.sub_le m j)
      have hqc : q ≤ c j := by
        refine Nat.le_of_mul_le_mul_left ?_ hw0
        rw [← hq]
        exact hjL
      have hule : ∀ i, (if i = j then q else 0) ≤ c i := by
        intro i
        by_cases hij : i = j
        · rw [if_pos hij, hij]
          exact hqc
        · rw [if_neg hij]
          exact Nat.zero_le _
      have hu : tuningWeight m (fun i => if i = j then q else 0) = L := by
        rw [tuningWeight_ite m j q hjmem]
        exact hq.symm
      have hd : tuningWeight m (fun i => c i - (if i = j then q else 0)) = tuningWeight m c - L := by
        have h := tuningWeight_sub m c (fun i => if i = j then q else 0) hule
        rw [hu] at h
        exact h
      have hc2 : r * L + L + (m - 1) * L ≤ tuningWeight m c := by
        calc r * L + L + (m - 1) * L = (r + 1) * L + (m - 1) * L := by ring
          _ ≤ tuningWeight m c := hc
      have hc' : r * L + (m - 1) * L
          ≤ tuningWeight m (fun i => c i - (if i = j then q else 0)) := by
        rw [hd]
        have h9 : ∀ A B C W : ℕ, A + C + B ≤ W → A + B ≤ W - C := by
          intro A B C W h
          omega
        exact h9 _ _ _ _ hc2
      obtain ⟨e, he1, he2⟩ := ih (fun i => c i - (if i = j then q else 0)) hc'
      refine ⟨fun i => e i + (if i = j then q else 0), ?_, ?_⟩
      · intro i
        have h1 : e i ≤ c i - (if i = j then q else 0) := he1 i
        have h2 : (if i = j then q else 0) ≤ c i := hule i
        show e i + (if i = j then q else 0) ≤ c i
        by_cases hij : i = j
        · rw [if_pos hij] at h1 h2 ⊢
          omega
        · rw [if_neg hij] at h1 h2 ⊢
          omega
      · have hsplit : tuningWeight m (fun i => e i + (if i = j then q else 0))
            = tuningWeight m e + tuningWeight m (fun i => if i = j then q else 0) :=
          tuningWeight_fun_add m e (fun i => if i = j then q else 0)
        rw [hsplit, he2, hu]
        ring
end FunctorialResolution.EmbeddedResolution
