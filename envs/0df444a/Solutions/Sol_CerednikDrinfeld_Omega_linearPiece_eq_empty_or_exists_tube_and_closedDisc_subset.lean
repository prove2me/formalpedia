-- Prove2me | solution 1 for CerednikDrinfeld.Omega.linearPiece_eq_empty_or_exists_tube_and_closedDisc_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/bd8a3350-eb6b-5560-8e2e-eec058c9d20c

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_linearPiece_eq_empty_or_exists_tube_and_closedDisc_subset

set_option autoImplicit false

open CerednikDrinfeld.Omega

namespace PieceTubeAux

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_sub_comm (a b : K) : Valued.v (a - b) = Valued.v (b - a) := Valuation.map_sub_swap _ a b

theorem v_sub_le_max (a b c : K) : Valued.v (a - c) ≤ max (Valued.v (a - b)) (Valued.v (b - c)) := by
  have : a - c = (a - b) + (b - c) := by ring
  rw [this]; exact Valuation.map_add _ _ _

theorem v_sub_eq_of_lt {a b c : K} (h : Valued.v (a - b) < Valued.v (b - c)) : Valued.v (a - c) = Valued.v (b - c) := by
  have : a - c = (a - b) + (b - c) := by ring
  rw [this]; exact Valuation.map_add_eq_of_lt_right _ h

theorem exists_maxSel (F : K → Finset K) :
    ∃ g : K → K, ∀ h : K, (F h).Nonempty → g h ∈ F h ∧ ∀ x ∈ F h, Valued.v x ≤ Valued.v (g h) := by
  classical
  have : ∀ h : K, ∃ y : K, ((F h).Nonempty → y ∈ F h ∧ ∀ x ∈ F h, Valued.v x ≤ Valued.v y) := by
    intro h
    by_cases hne : (F h).Nonempty
    · obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image (F h) (fun x => Valued.v x) hne
      exact ⟨y, fun _ => ⟨hy, hmax⟩⟩
    · exact ⟨1, fun h' => (hne h').elim⟩
  choose g hg using this
  exact ⟨g, hg⟩

end PieceTubeAux

open PieceTubeAux in
theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hnt : ∃ y : K, y ≠ 0 ∧ Valued.v y < 1)

    (c₀ R₀ : K) (hR₀ : R₀ ≠ 0) (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (P : Set K) (hP : ∀ z : K, z ∈ P ↔ Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h))

    (L M : Finset (K × K)) (hL : ∀ er ∈ L, er.2 ≠ 0) (hM : ∀ er ∈ M, er.2 ≠ 0)
    (Q : Set K) (hQ : ∀ z : K, z ∈ Q ↔ z ∈ P ∧ (∀ er ∈ L, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
      (∀ er ∈ M, Valued.v (z - er.1) ≤ Valued.v er.2)) :
    ((∀ z : K, z ∉ Q) ∨
      ∃ (c₁ R₁ : K) (H₁ : Finset K) (ρ₁ : K → K), R₁ ≠ 0 ∧ (∀ h ∈ H₁, ρ₁ h ≠ 0) ∧
        ∀ z : K, z ∈ Q ↔ Valued.v (z - c₁) ≤ Valued.v R₁ ∧ ∀ h ∈ H₁, Valued.v (ρ₁ h) ≤ Valued.v (z - h)) ∧
    (∀ z ∈ Q, ∃ r : K, r ≠ 0 ∧ ∀ w : K, Valued.v (w - z) ≤ Valued.v r → w ∈ Q) := by
  classical
  obtain ⟨y, hy0, hy1⟩ := hnt
  have hvy : 0 < Valued.v y := (Valuation.pos_iff _).mpr hy0
  refine ⟨?_, ?_⟩
  ·
    by_cases hQe : ∀ z : K, z ∉ Q
    · exact Or.inl hQe
    right
    push_neg at hQe
    obtain ⟨q, hq⟩ := hQe
    obtain ⟨hqP, hqL, hqM⟩ := (hQ q).mp hq
    obtain ⟨hqc, hqH⟩ := (hP q).mp hqP

    let Ds : Finset (K × K) := insert (c₀, R₀) M
    have hDs0 : ∀ d ∈ Ds, d.2 ≠ 0 := by
      intro d hd
      rcases Finset.mem_insert.mp hd with rfl | hd
      · exact hR₀
      · exact hM d hd
    have hqDs : ∀ d ∈ Ds, Valued.v (q - d.1) ≤ Valued.v d.2 := by
      intro d hd
      rcases Finset.mem_insert.mp hd with rfl | hd
      · exact hqc
      · exact hqM d hd
    obtain ⟨d₁, hd₁, hmin⟩ := Finset.exists_min_image Ds (fun d => Valued.v d.2) ⟨(c₀, R₀), Finset.mem_insert_self _ _⟩

    let H₁ : Finset K := H ∪ L.image Prod.fst
    let Rad : K → Finset K := fun h => (H.filter (fun h' => h' = h)).image ρ ∪ (L.filter (fun er => er.1 = h)).image Prod.snd
    obtain ⟨ρ₁, hρ₁⟩ := exists_maxSel (K := K) Rad
    have hRadH : ∀ h ∈ H, ρ h ∈ Rad h := fun h hh =>
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨h, Finset.mem_filter.mpr ⟨hh, rfl⟩, rfl⟩)
    have hRadL : ∀ er ∈ L, er.2 ∈ Rad er.1 := fun er her =>
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨er, Finset.mem_filter.mpr ⟨her, rfl⟩, rfl⟩)
    have hRad_cases : ∀ (h x : K), x ∈ Rad h → (h ∈ H ∧ x = ρ h) ∨ (∃ er ∈ L, er.1 = h ∧ er.2 = x) := by
      intro h x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨h', hh', rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨hh'H, rfl⟩ := Finset.mem_filter.mp hh'
        exact Or.inl ⟨hh'H, rfl⟩
      · obtain ⟨er, her, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨herL, h1⟩ := Finset.mem_filter.mp her
        exact Or.inr ⟨er, herL, h1, rfl⟩
    have hRadne : ∀ h ∈ H₁, (Rad h).Nonempty := by
      intro h hh
      rcases Finset.mem_union.mp hh with hh | hh
      · exact ⟨ρ h, hRadH h hh⟩
      · obtain ⟨er, her, rfl⟩ := Finset.mem_image.mp hh
        exact ⟨er.2, hRadL er her⟩
    refine ⟨d₁.1, d₁.2, H₁, ρ₁, hDs0 d₁ hd₁, ?_, ?_⟩
    · intro h hh
      obtain ⟨hmem, -⟩ := hρ₁ h (hRadne h hh)
      rcases hRad_cases h _ hmem with ⟨hH, e⟩ | ⟨er, her, -, e⟩
      · rw [e]; exact hρ h hH
      · rw [← e]; exact hL er her
    intro z
    constructor
    · intro hz
      obtain ⟨hzP, hzL, hzM⟩ := (hQ z).mp hz
      obtain ⟨hzc, hzH⟩ := (hP z).mp hzP
      refine ⟨?_, fun h hh => ?_⟩
      · rcases Finset.mem_insert.mp hd₁ with e | hd
        · rw [e]; exact hzc
        · exact hzM d₁ hd
      · obtain ⟨hmem, -⟩ := hρ₁ h (hRadne h hh)
        rcases hRad_cases h _ hmem with ⟨hH, e⟩ | ⟨er, her, e1, e⟩
        · rw [e]; exact hzH h hH
        · rw [← e, ← e1]; exact hzL er her
    · rintro ⟨hzc₁, hzH₁⟩

      have hzq : Valued.v (z - q) ≤ Valued.v d₁.2 :=
        (v_sub_le_max z d₁.1 q).trans (max_le hzc₁ (by rw [v_sub_comm]; exact hqDs d₁ hd₁))
      have hzDs : ∀ d ∈ Ds, Valued.v (z - d.1) ≤ Valued.v d.2 := fun d hd =>
        (v_sub_le_max z q d.1).trans (max_le (hzq.trans (hmin d hd)) (hqDs d hd))
      have hlow : ∀ h ∈ H₁, ∀ x ∈ Rad h, Valued.v x ≤ Valued.v (z - h) := fun h hh x hx =>
        ((hρ₁ h (hRadne h hh)).2 x hx).trans (hzH₁ h hh)
      rw [hQ, hP]
      refine ⟨⟨hzDs _ (Finset.mem_insert_self _ _), fun h hh => ?_⟩, fun er her => ?_, fun er her => hzDs er (Finset.mem_insert_of_mem her)⟩
      · exact hlow h (Finset.mem_union_left _ hh) _ (hRadH h hh)
      · exact hlow er.1 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ her)) _ (hRadL er her)
  ·
    intro z hz
    obtain ⟨hzP, hzL, hzM⟩ := (hQ z).mp hz
    obtain ⟨hzc, hzH⟩ := (hP z).mp hzP
    let Gz : Finset K := insert R₀ ((M.image Prod.snd ∪ H.image (fun h => z - h)) ∪ L.image (fun er => z - er.1))
    obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image Gz (fun x => Valued.v x) ⟨R₀, Finset.mem_insert_self _ _⟩
    have hm0 : m ≠ 0 := by
      rcases Finset.mem_insert.mp hm with rfl | hm'
      · exact hR₀
      rcases Finset.mem_union.mp hm' with hm' | hm'
      · rcases Finset.mem_union.mp hm' with hm' | hm'
        · obtain ⟨er, her, rfl⟩ := Finset.mem_image.mp hm'; exact hM er her
        · obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hm'
          intro h0
          have := hzH h hh
          rw [h0, Valuation.map_zero, le_zero_iff] at this
          exact hρ h hh ((Valuation.zero_iff _).mp this)
      · obtain ⟨er, her, rfl⟩ := Finset.mem_image.mp hm'
        intro h0
        have := hzL er her
        rw [h0, Valuation.map_zero, le_zero_iff] at this
        exact hL er her ((Valuation.zero_iff _).mp this)
    have hvm : 0 < Valued.v m := (Valuation.pos_iff _).mpr hm0
    refine ⟨y * m, mul_ne_zero hy0 hm0, fun w hw => ?_⟩
    have hwz : Valued.v (w - z) < Valued.v m := by
      rw [Valuation.map_mul] at hw
      have : Valued.v y * Valued.v m < 1 * Valued.v m := mul_lt_mul_of_pos_right hy1 hvm
      rw [one_mul] at this
      exact lt_of_le_of_lt hw this
    have hwz' : ∀ x ∈ Gz, Valued.v (w - z) < Valued.v x := fun x hx => lt_of_lt_of_le hwz (hmin x hx)
    rw [hQ, hP]
    refine ⟨⟨?_, fun h hh => ?_⟩, fun er her => ?_, fun er her => ?_⟩
    · exact (v_sub_le_max w z c₀).trans (max_le (hwz' R₀ (Finset.mem_insert_self _ _)).le hzc)
    · have : Valued.v (w - z) < Valued.v (z - h) :=
        hwz' _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hh))))
      rw [v_sub_eq_of_lt this]; exact hzH h hh
    · have : Valued.v (w - z) < Valued.v (z - er.1) :=
        hwz' _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ her)))
      rw [v_sub_eq_of_lt this]; exact hzL er her
    · exact (v_sub_le_max w z er.1).trans (max_le
        (hwz' _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ her))))).le
        (hzM er her))

end S_CerednikDrinfeld_Omega_linearPiece_eq_empty_or_exists_tube_and_closedDisc_subset
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_linearPiece_eq_empty_or_exists_tube_and_closedDisc_subset (solution)
