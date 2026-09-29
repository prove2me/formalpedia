-- Prove2me | solution 1 for Erdos20.bell_chueluecha_warnke_bound
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-09-26T15:54:45.162603+00:00
-- url     : https://prove2.me/submissions/aceb1cd0-d66f-4f3d-9f24-03ec7435d978

import Definitions.Def_Erdos20_defs
import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_SunflowerSpread
import Theorems.Thm_Erdos20_spread_disjoint_bound
import Theorems.Thm_Erdos20_exists_spread_link

namespace Erdos20

/-- Passing from a strict finite-family bound to the natural-number threshold in `f`
costs at most a factor of two in the absolute constant. -/
theorem threshold_of_finite_uniform_bound
    (C : ℝ) (hC : 4 ≤ C)
    (hbound : ∀ (n k : ℕ), 2 ≤ n → 2 ≤ k →
      ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
        (∀ A ∈ F, A.card = n) →
        (C * k * Real.log n) ^ n < (F.card : ℝ) →
        ∃ G ⊆ F, G.card = k ∧
          IsSunflower ((fun A : Finset α => (A : Set α)) '' (G : Set (Finset α)))) :
    ∃ D : ℝ, 4 ≤ D ∧ ∀ (n k : ℕ), 2 ≤ n → 2 ≤ k →
      (f n k : ℝ) ≤ (D * k * Real.log n) ^ n := by
  classical
  refine ⟨2 * C, by linarith, ?_⟩
  intro n k hn hk
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : (1 / 2 : ℝ) ≤ Real.log n := by
    have htwo := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    have hmono := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hnR
    norm_num at htwo
    linarith
  have hbase : 1 ≤ C * k * Real.log n := by
    have hCk : (8 : ℝ) ≤ C * k := by nlinarith
    nlinarith
  let B : ℝ := (C * k * Real.log n) ^ n
  have hB : 1 ≤ B := one_le_pow₀ hbase
  let m : ℕ := ⌊B⌋₊ + 1
  have hmpos : 0 < m := by dsimp [m]; omega
  have hBm : B < (m : ℝ) := by
    simpa [m] using Nat.lt_floor_add_one B
  have hfm : f n k ≤ m := by
    apply Nat.sInf_le
    intro α F hF
    have hfin : F.Finite := Set.finite_of_ncard_pos (hmpos.trans_le hF.2)
    have hAfin : ∀ A ∈ F, A.Finite := by
      intro A hA
      apply Set.finite_of_ncard_pos
      rw [hF.1 A hA]
      omega
    let Q : Set (Finset α) := (fun A : Finset α => (A : Set α)) ⁻¹' F
    have hQfin : Q.Finite := Set.Finite.preimage Finset.coe_injective.injOn hfin
    have hQimage : (fun A : Finset α => (A : Set α)) '' Q = F := by
      apply Set.Subset.antisymm
      · rintro _ ⟨A, hA, rfl⟩
        exact hA
      · intro A hA
        refine ⟨(hAfin A hA).toFinset, ?_, ?_⟩
        · simpa [Q] using hA
        · exact (hAfin A hA).coe_toFinset
    have hQcard : hQfin.toFinset.card = F.ncard := by
      rw [← Set.ncard_eq_toFinset_card Q hQfin, ← hQimage]
      exact (Set.ncard_image_of_injective Q Finset.coe_injective).symm
    have hQunif : ∀ A ∈ hQfin.toFinset, A.card = n := by
      intro A hA
      have hAF : (A : Set α) ∈ F := hQfin.mem_toFinset.mp hA
      simpa using hF.1 (A : Set α) hAF
    have hQlarge : (C * k * Real.log n) ^ n < (hQfin.toFinset.card : ℝ) := by
      rw [hQcard]
      exact hBm.trans_le (by exact_mod_cast hF.2)
    obtain ⟨G, hG, hGcard, hGsun⟩ := hbound n k hn hk hQfin.toFinset hQunif hQlarge
    refine ⟨(fun A : Finset α => (A : Set α)) '' (G : Set (Finset α)), ?_, ?_, hGsun⟩
    · rintro _ ⟨A, hA, rfl⟩
      exact hQfin.mem_toFinset.mp (hG hA)
    · rw [Set.ncard_image_of_injective _ Finset.coe_injective, Set.ncard_coe_finset,
        hGcard]
  have hmB : (m : ℝ) ≤ B + 1 := by
    have hfloor := Nat.floor_le (show 0 ≤ B by linarith)
    simpa [m] using add_le_add_right hfloor 1
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ n :=
    le_self_pow₀ (by norm_num) (by omega)
  calc
    (f n k : ℝ) ≤ m := by exact_mod_cast hfm
    _ ≤ B + 1 := hmB
    _ ≤ 2 * B := by linarith
    _ ≤ (2 : ℝ) ^ n * B := mul_le_mul_of_nonneg_right htwo (by linarith)
    _ = (2 * C * k * Real.log n) ^ n := by
      dsimp [B]
      rw [← mul_pow]
      congr 1
      ring

end Erdos20

set_option autoImplicit false

namespace Erdos20

private lemma link_member_properties {α : Type*} [DecidableEq α]
    {F : Finset (Finset α)} {S A : Finset α} (hA : A ∈ link F S) :
    S ∪ A ∈ F ∧ Disjoint S A := by
  rcases Finset.mem_image.mp hA with ⟨B, hB, rfl⟩
  obtain ⟨hBF, hSB⟩ := Finset.mem_filter.mp hB
  constructor
  · simpa [Finset.union_sdiff_of_subset hSB] using hBF
  · exact disjoint_sdiff_self_right

private lemma link_member_rank {α : Type*} [DecidableEq α]
    {F : Finset (Finset α)} {S A : Finset α} {n : ℕ}
    (huni : ∀ B ∈ F, B.card = n) (hS : S.card < n) (hA : A ∈ link F S) :
    A.Nonempty ∧ A.card ≤ n := by
  rcases Finset.mem_image.mp hA with ⟨B, hB, rfl⟩
  obtain ⟨hBF, hSB⟩ := Finset.mem_filter.mp hB
  have hc : (B \ S).card = n - S.card := by
    rw [Finset.card_sdiff_of_subset hSB, huni B hBF]
  constructor
  · apply Finset.card_pos.mp
    rw [hc]
    omega
  · rw [hc]
    omega

/-- Pairwise disjoint members of a link lift to a sunflower in the original family. -/
theorem sunflower_of_disjoint_link {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (S : Finset α) (H : Finset (Finset α))
    (hH : H ⊆ link F S)
    (hdis : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → Disjoint A B) :
    ∃ G ⊆ F, G.card = H.card ∧
      IsSunflower ((fun A : Finset α => (A : Set α)) '' (G : Set (Finset α))) := by
  let G := H.image (fun A => S ∪ A)
  have hinj : Set.InjOn (fun A : Finset α => S ∪ A) (H : Set (Finset α)) := by
    intro A hA B hB hab
    have hSA := (link_member_properties (hH hA)).2
    have hSB := (link_member_properties (hH hB)).2
    apply Finset.ext
    intro x
    have ha : x ∈ A → x ∉ S := fun hx hs => Finset.disjoint_left.mp hSA hs hx
    have hb : x ∈ B → x ∉ S := fun hx hs => Finset.disjoint_left.mp hSB hs hx
    have hm := Finset.ext_iff.mp hab x
    simp only [Finset.mem_union] at hm
    tauto
  refine ⟨G, ?_, ?_, ?_⟩
  · intro B hB
    rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
    exact (link_member_properties (hH hA)).1
  · exact Finset.card_image_of_injOn hinj
  · refine ⟨(S : Set α), ?_⟩
    intro A hA B hB hne
    rcases hA with ⟨A', hA', rfl⟩
    rcases hB with ⟨B', hB', rfl⟩
    rcases Finset.mem_image.mp hA' with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hB' with ⟨b, hb, rfl⟩
    have hab : a ≠ b := by intro he; exact hne (by rw [he])
    have hd := hdis a ha b hb hab
    ext x
    simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_union]
    have hx : ¬(x ∈ a ∧ x ∈ b) := by
      intro h
      exact Finset.disjoint_left.mp hd h.1 h.2
    tauto

/-- The deterministic reduction from disjoint spread families to the BCW threshold. -/
theorem bcw_of_spread_disjoint_bound :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ n k : ℕ, 2 ≤ n → 2 ≤ k →
      (f n k : ℝ) ≤ (C * k * Real.log n) ^ n := by
  obtain ⟨C, hC, hdisjoint⟩ := spread_disjoint_bound
  apply threshold_of_finite_uniform_bound C hC
  intro n k hn hk α inst F huni hlarge
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : (1 / 2 : ℝ) ≤ Real.log n := by
    have htwo := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    have hmono := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hnR
    norm_num at htwo
    linarith
  have hR : 1 < C * k * Real.log n := by
    have hCk : (8 : ℝ) ≤ C * k := by nlinarith
    nlinarith
  obtain ⟨S, hS, hlinkne, hspread⟩ := exists_spread_link F n
    (C * k * Real.log n) hR huni hlarge
  obtain ⟨H, hH, hHcard, hHdis⟩ := hdisjoint n k hn hk (link F S) hlinkne
    (fun A hA => link_member_rank huni hS hA) hspread
  obtain ⟨G, hG, hGcard, hGsun⟩ := sunflower_of_disjoint_link F S H hH hHdis
  exact ⟨G, hG, hGcard.trans hHcard, hGsun⟩

end Erdos20


theorem solution :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ n k : ℕ, 2 ≤ n → 2 ≤ k →
      (Erdos20.f n k : ℝ) ≤ (C * k * Real.log n) ^ n :=
  Erdos20.bcw_of_spread_disjoint_bound
