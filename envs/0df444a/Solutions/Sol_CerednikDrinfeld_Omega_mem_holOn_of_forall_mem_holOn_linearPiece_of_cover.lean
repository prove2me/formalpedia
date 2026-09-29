-- Prove2me | solution 1 for CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_linearPiece_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e94e01b6-c688-53c2-a655-4f77ed49ecd7

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Theorems.Thm_CerednikDrinfeld_Omega_mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt
import Theorems.Thm_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_linearPiece_of_cover

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_linearPiece_of_cover.CerednikDrinfeld.Omega"

noncomputable section
open Classical

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt Omega.mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "holOn mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover"
namespace TubeGlue
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

def tube (c₀ R₀ : K) (H : Finset K) (ρ : K → K) (z : K) : Prop :=
  Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h)

def sat (p : Finset (K × K) × Finset (K × K)) (z : K) : Prop :=
  (∀ er ∈ p.1, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧ (∀ er ∈ p.2, Valued.v (z - er.1) ≤ Valued.v er.2)

def weight (s : Finset (Finset (K × K) × Finset (K × K))) : ℕ := s.sum fun p => p.1.card + p.2.card

section Mono
variable (K)

theorem mem_holOn_restrict {S S' : Set K} (hsub : S' ⊆ S) {f : ↥S → K} (hf : f ∈ holOn K S) :
    (fun z : ↥S' => f ⟨(z : K), hsub z.2⟩) ∈ holOn K S' := by
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  refine ⟨r, fun k z hz => hr k z (hsub hz), ⟨b, fun k z => hb k ⟨(z : K), hsub z.2⟩⟩, ?_⟩
  exact hlim.comp (fun z : ↥S' => (⟨(z : K), hsub z.2⟩ : ↥S))

end Mono

section Geometry

theorem v_sub_comm (a b : K) : Valued.v (a - b) = Valued.v (b - a) := by
  rw [← Valuation.map_neg, neg_sub]

theorem v_sub_le_max (a b c : K) : Valued.v (a - c) ≤ max (Valued.v (a - b)) (Valued.v (b - c)) := by
  have : a - c = (a - b) + (b - c) := by ring
  rw [this]; exact Valuation.map_add _ _ _

theorem tube_of_sphere_generic {c₀ R₀ : K} {H : Finset K} {ρ : K → K} {e r : K}
    (hsub : ∀ z : K, Valued.v (z - e) ≤ Valued.v r → Valued.v (z - c₀) ≤ Valued.v R₀)
    {z₀ : K} (hz₀ : tube c₀ R₀ H ρ z₀) (hz₀e : Valued.v (z₀ - e) ≤ Valued.v r)
    {z : K} (hz : Valued.v (z - e) = Valued.v r) (hgen : ∀ h ∈ H, Valued.v r ≤ Valued.v (z - h)) :
    tube c₀ R₀ H ρ z := by
  refine ⟨hsub z hz.le, fun h hh => ?_⟩
  by_contra hlt
  push Not at hlt

  have h1 : Valued.v (e - h) < Valued.v (ρ h) := by
    calc Valued.v (e - h) ≤ max (Valued.v (e - z)) (Valued.v (z - h)) := v_sub_le_max e z h
      _ ≤ Valued.v (z - h) := by rw [v_sub_comm, hz]; exact max_le (hgen h hh) le_rfl
      _ < Valued.v (ρ h) := hlt
  have h2 : Valued.v (z₀ - h) < Valued.v (ρ h) := by
    calc Valued.v (z₀ - h) ≤ max (Valued.v (z₀ - e)) (Valued.v (e - h)) := v_sub_le_max z₀ e h
      _ < Valued.v (ρ h) := max_lt (lt_of_le_of_lt (hz₀e.trans (hgen h hh)) hlt) h1
  exact absurd (hz₀.2 h hh) (not_le.2 h2)

theorem v_sub_le_of_not_sub {c₀ R₀ : K} {H : Finset K} {ρ : K → K} {e r : K}
    (hnot : ¬ ∀ z : K, Valued.v (z - e) ≤ Valued.v r → Valued.v (z - c₀) ≤ Valued.v R₀)
    {z₀ : K} (hz₀ : tube c₀ R₀ H ρ z₀) (hz₀e : Valued.v (z₀ - e) ≤ Valued.v r) :
    Valued.v R₀ < Valued.v r ∧ ∀ z : K, Valued.v (z - c₀) ≤ Valued.v R₀ →
      Valued.v (z - z₀) < Valued.v r := by
  push Not at hnot
  obtain ⟨w, hwe, hwc⟩ := hnot
  have hRr : Valued.v R₀ < Valued.v r := by
    have := v_sub_le_max w z₀ c₀
    have h2 : Valued.v (w - z₀) ≤ Valued.v r :=
      (v_sub_le_max w e z₀).trans (max_le hwe (by rw [v_sub_comm]; exact hz₀e))
    rcases le_max_iff.1 this with h | h
    ·
      by_contra hle; push Not at hle
      exact absurd (hwc.trans_le (h.trans (h2.trans hle))) (lt_irrefl _)
    · exact absurd (hwc.trans_le (h.trans hz₀.1)) (lt_irrefl _)
  refine ⟨hRr, fun z hz => ?_⟩
  calc Valued.v (z - z₀) ≤ max (Valued.v (z - c₀)) (Valued.v (c₀ - z₀)) := v_sub_le_max z c₀ z₀
    _ ≤ Valued.v R₀ := max_le hz (by rw [v_sub_comm]; exact hz₀.1)
    _ < Valued.v r := hRr

end Geometry

section Split
variable {c₀ R₀ e r : K} {H : Finset K} {ρ : K → K}

theorem tube_minus_iff (hDsub : ∀ z : K, Valued.v (z - e) ≤ Valued.v r → Valued.v (z - c₀) ≤ Valued.v R₀) (z : K) :
    tube e r H ρ z ↔ tube c₀ R₀ H ρ z ∧ Valued.v (z - e) ≤ Valued.v r :=
  ⟨fun h => ⟨⟨hDsub z h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩

theorem tube_plus_iff {z₀ : K} (hz₀ : tube c₀ R₀ H ρ z₀) (hz₀e : Valued.v (z₀ - e) ≤ Valued.v r) (z : K) :
    tube c₀ R₀ (insert e H) (Function.update ρ e r) z ↔ tube c₀ R₀ H ρ z ∧ Valued.v r ≤ Valued.v (z - e) := by
  constructor
  · rintro ⟨h0, hh⟩
    have he : Valued.v r ≤ Valued.v (z - e) := by
      have := hh e (Finset.mem_insert_self e H)
      rwa [Function.update_self] at this
    refine ⟨⟨h0, fun h hhH => ?_⟩, he⟩
    by_cases hhe : h = e
    · subst hhe
      exact ((hz₀.2 h hhH).trans hz₀e).trans he
    · have := hh h (Finset.mem_insert_of_mem hhH)
      rwa [Function.update_of_ne hhe] at this
  · rintro ⟨⟨h0, hh⟩, he⟩
    refine ⟨h0, fun h hh' => ?_⟩
    rcases Finset.mem_insert.1 hh' with rfl | hhH
    · rwa [Function.update_self]
    · by_cases hhe : h = e
      · subst hhe; rwa [Function.update_self]
      · rw [Function.update_of_ne hhe]; exact hh h hhH

variable (K) [IsAlgClosed K]

theorem glue_of_split (hr : r ≠ 0)
    (hDsub : ∀ z : K, Valued.v (z - e) ≤ Valued.v r → Valued.v (z - c₀) ≤ Valued.v R₀)
    {z₀ : K} (hz₀ : tube c₀ R₀ H ρ z₀) (hz₀e : Valued.v (z₀ - e) ≤ Valued.v r)
    (F : ↥{z : K | tube c₀ R₀ H ρ z} → K)
    (hminus : (fun z : ↥{z : K | tube e r H ρ z} => F ⟨(z : K), ((tube_minus_iff hDsub (z : K)).1 z.2).1⟩) ∈
      holOn K {z : K | tube e r H ρ z})
    (hplus : (fun z : ↥{z : K | tube c₀ R₀ (insert e H) (Function.update ρ e r) z} =>
        F ⟨(z : K), ((tube_plus_iff hz₀ hz₀e (z : K)).1 z.2).1⟩) ∈
      holOn K {z : K | tube c₀ R₀ (insert e H) (Function.update ρ e r) z}) :
    F ∈ holOn K {z : K | tube c₀ R₀ H ρ z} := by
  set S₁ : Set K := {z : K | tube c₀ R₀ (insert e H) (Function.update ρ e r) z} with hS₁
  set S₂ : Set K := {z : K | tube e r H ρ z} with hS₂
  have hU : ∀ z : K, z ∈ S₁ ∪ S₂ → tube c₀ R₀ H ρ z := fun z hz =>
    hz.elim (fun h => ((tube_plus_iff hz₀ hz₀e z).1 h).1) (fun h => ((tube_minus_iff hDsub z).1 h).1)
  have hglue := CerednikDrinfeld.Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt K S₁ S₂ e r hr H
    (fun z hz => ((tube_plus_iff hz₀ hz₀e z).1 hz).2)
    (fun z hz => by
      rcases le_or_gt (Valued.v r) (Valued.v (z - e)) with h | h
      · exact Or.inl ((tube_plus_iff hz₀ hz₀e z).2 ⟨((tube_minus_iff hDsub z).1 hz).1, h⟩)
      · exact Or.inr h)
    (fun z hz hgen => by
      have ht : tube c₀ R₀ H ρ z := tube_of_sphere_generic hDsub hz₀ hz₀e hz hgen
      exact ⟨(tube_plus_iff hz₀ hz₀e z).2 ⟨ht, hz.ge⟩, (tube_minus_iff hDsub z).2 ⟨ht, hz.le⟩⟩)
    (fun z => F ⟨(z : K), hU z z.2⟩) hplus hminus
  have hsub : {z : K | tube c₀ R₀ H ρ z} ⊆ S₁ ∪ S₂ := fun z hz => by
    rcases le_or_gt (Valued.v r) (Valued.v (z - e)) with h | h
    · exact Or.inl ((tube_plus_iff hz₀ hz₀e z).2 ⟨hz, h⟩)
    · exact Or.inr ((tube_minus_iff hDsub z).2 ⟨hz, h.le⟩)
  exact mem_holOn_restrict K hsub hglue

end Split

section Main

omit Γ₀ in
omit [Field K] in
theorem weight_insert_le (q : Finset (K × K) × Finset (K × K)) (t : Finset (Finset (K × K) × Finset (K × K))) :
    weight (insert q t) ≤ (q.1.card + q.2.card) + weight t := by
  by_cases hq : q ∈ t
  · rw [Finset.insert_eq_of_mem hq]; exact Nat.le_add_left _ _
  · unfold weight; rw [Finset.sum_insert hq]

omit Γ₀ in
omit [Field K] in
theorem weight_erase_add {s : Finset (Finset (K × K) × Finset (K × K))} {p : Finset (K × K) × Finset (K × K)}
    (hp : p ∈ s) : (p.1.card + p.2.card) + weight (s.erase p) = weight s := by
  unfold weight; exact Finset.add_sum_erase s (fun p => p.1.card + p.2.card) hp

omit Γ₀ in
theorem weight_insert_erase_lt {s : Finset (Finset (K × K) × Finset (K × K))} {p q : Finset (K × K) × Finset (K × K)}
    (hp : p ∈ s) (hlt : q.1.card + q.2.card < p.1.card + p.2.card) : weight (insert q (s.erase p)) < weight s := by
  have h1 := weight_insert_le q (s.erase p)
  have h2 := weight_erase_add hp
  omega

omit Γ₀ in
theorem weight_erase_lt {s : Finset (Finset (K × K) × Finset (K × K))} {p : Finset (K × K) × Finset (K × K)}
    (hp : p ∈ s) (hlt : 0 < p.1.card + p.2.card) : weight (s.erase p) < weight s := by
  have h2 := weight_erase_add hp
  omega

variable (K) [IsAlgClosed K]

theorem main (N : ℕ) : ∀ (c₀ R₀ : K) (_hR₀ : R₀ ≠ 0) (H : Finset K) (ρ : K → K) (_hρ : ∀ h ∈ H, ρ h ≠ 0)
    (s : Finset (Finset (K × K) × Finset (K × K))) (_hN : weight s ≤ N)
    (_hrad : ∀ p ∈ s, (∀ er ∈ p.1, er.2 ≠ 0) ∧ (∀ er ∈ p.2, er.2 ≠ 0))
    (_hcov : ∀ z : K, tube c₀ R₀ H ρ z → ∃ p ∈ s, sat p z)
    (F : ↥{z : K | tube c₀ R₀ H ρ z} → K)
    (_hF : ∀ p ∈ s, (fun z : ↥{z : K | tube c₀ R₀ H ρ z ∧ sat p z} => F ⟨(z : K), z.2.1⟩) ∈
      holOn K {z : K | tube c₀ R₀ H ρ z ∧ sat p z}),
    F ∈ holOn K {z : K | tube c₀ R₀ H ρ z} := by
  induction N using Nat.strong_induction_on with
  | _ N ih => ?_
  intro c₀ R₀ hR₀ H ρ hρ s hN hrad hcov F hF

  by_cases h1 : ∃ p ∈ s, p.1 = ∅ ∧ p.2 = ∅
  · obtain ⟨p, hp, hp1, hp2⟩ := h1
    have hsub : {z : K | tube c₀ R₀ H ρ z} ⊆ {z : K | tube c₀ R₀ H ρ z ∧ sat p z} :=
      fun z hz => ⟨hz, by simp [hp1], by simp [hp2]⟩
    exact mem_holOn_restrict K hsub (hF p hp)
  by_cases h3 : ∃ p ∈ s, 2 ≤ p.1.card + p.2.card
  ·
    obtain ⟨p, hp, hp2⟩ := h3
    by_cases hM : p.2.Nonempty
    ·
      obtain ⟨c, hc⟩ := hM
      have hr : c.2 ≠ 0 := (hrad p hp).2 c hc
      by_cases ha : ∀ z : K, tube c₀ R₀ H ρ z → Valued.v c.2 < Valued.v (z - c.1)
      ·
        refine ih (weight (s.erase p)) (lt_of_lt_of_le (weight_erase_lt hp (by omega)) hN) c₀ R₀ hR₀ H ρ hρ
          (s.erase p) le_rfl (fun q hq => hrad q (Finset.mem_of_mem_erase hq)) ?_ F
          (fun q hq => hF q (Finset.mem_of_mem_erase hq))
        intro z hz
        obtain ⟨q, hq, hqz⟩ := hcov z hz
        refine ⟨q, Finset.mem_erase.2 ⟨?_, hq⟩, hqz⟩
        rintro rfl
        exact absurd (hqz.2 c hc) (not_le.2 (ha z hz))
      by_cases hb : ∀ z : K, tube c₀ R₀ H ρ z → Valued.v (z - c.1) ≤ Valued.v c.2
      ·
        set p' : Finset (K × K) × Finset (K × K) := (p.1, p.2.erase c) with hp'
        have hlt : p'.1.card + p'.2.card < p.1.card + p.2.card := by
          simp only [hp', Finset.card_erase_of_mem hc]; have := Finset.card_pos.2 ⟨c, hc⟩; omega
        refine ih (weight (insert p' (s.erase p))) (lt_of_lt_of_le (weight_insert_erase_lt hp hlt) hN) c₀ R₀ hR₀ H ρ hρ
          (insert p' (s.erase p)) le_rfl ?_ ?_ F ?_
        · intro q hq
          rcases Finset.mem_insert.1 hq with rfl | hq
          · exact ⟨(hrad p hp).1, fun er her => (hrad p hp).2 er (Finset.mem_of_mem_erase her)⟩
          · exact hrad q (Finset.mem_of_mem_erase hq)
        · intro z hz
          obtain ⟨q, hq, hqz⟩ := hcov z hz
          by_cases hqp : q = p
          · subst hqp
            exact ⟨p', Finset.mem_insert_self _ _, hqz.1, fun er her => hqz.2 er (Finset.mem_of_mem_erase her)⟩
          · exact ⟨q, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hqp, hq⟩), hqz⟩
        · intro q hq
          rcases Finset.mem_insert.1 hq with rfl | hq
          · have hsub : {z : K | tube c₀ R₀ H ρ z ∧ sat p' z} ⊆ {z : K | tube c₀ R₀ H ρ z ∧ sat p z} := by
              rintro z ⟨hz, hz1, hz2⟩
              refine ⟨hz, hz1, fun er her => ?_⟩
              by_cases hec : er = c
              · subst hec; exact hb z hz
              · exact hz2 er (Finset.mem_erase.2 ⟨hec, her⟩)
            exact mem_holOn_restrict K hsub (hF p hp)
          · exact hF q (Finset.mem_of_mem_erase hq)

      push Not at ha hb
      obtain ⟨z₀, hz₀, hz₀e⟩ := ha
      obtain ⟨z₁, hz₁, hz₁e⟩ := hb
      have hDsub : ∀ z : K, Valued.v (z - c.1) ≤ Valued.v c.2 → Valued.v (z - c₀) ≤ Valued.v R₀ := by
        by_contra hnot
        obtain ⟨-, hall⟩ := v_sub_le_of_not_sub hnot hz₀ hz₀e
        have : Valued.v (z₁ - c.1) ≤ Valued.v c.2 :=
          (v_sub_le_max z₁ z₀ c.1).trans (max_le (hall z₁ hz₁.1).le hz₀e)
        exact absurd hz₁e (not_lt.2 this)

      set p' : Finset (K × K) × Finset (K × K) := (p.1, p.2.erase c) with hp'
      have hlt : p'.1.card + p'.2.card < p.1.card + p.2.card := by
        simp only [hp', Finset.card_erase_of_mem hc]; have := Finset.card_pos.2 ⟨c, hc⟩; omega
      have hminus := ih (weight (insert p' (s.erase p))) (lt_of_lt_of_le (weight_insert_erase_lt hp hlt) hN)
        c.1 c.2 hr H ρ hρ (insert p' (s.erase p)) le_rfl ?_ ?_
        (fun z : ↥{z : K | tube c.1 c.2 H ρ z} => F ⟨(z : K), ((tube_minus_iff hDsub (z : K)).1 z.2).1⟩) ?_
      rotate_left
      · intro q hq
        rcases Finset.mem_insert.1 hq with rfl | hq
        · exact ⟨(hrad p hp).1, fun er her => (hrad p hp).2 er (Finset.mem_of_mem_erase her)⟩
        · exact hrad q (Finset.mem_of_mem_erase hq)
      · intro z hz
        have hz' := (tube_minus_iff hDsub z).1 hz
        obtain ⟨q, hq, hqz⟩ := hcov z hz'.1
        by_cases hqp : q = p
        · subst hqp
          exact ⟨p', Finset.mem_insert_self _ _, hqz.1, fun er her => hqz.2 er (Finset.mem_of_mem_erase her)⟩
        · exact ⟨q, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hqp, hq⟩), hqz⟩
      · intro q hq
        rcases Finset.mem_insert.1 hq with rfl | hq
        · have hsub : {z : K | tube c.1 c.2 H ρ z ∧ sat p' z} ⊆ {z : K | tube c₀ R₀ H ρ z ∧ sat p z} := by
            rintro z ⟨hz, hz1, hz2⟩
            have hz' := (tube_minus_iff hDsub z).1 hz
            refine ⟨hz'.1, hz1, fun er her => ?_⟩
            by_cases hec : er = c
            · subst hec; exact hz'.2
            · exact hz2 er (Finset.mem_erase.2 ⟨hec, her⟩)
          exact mem_holOn_restrict K hsub (hF p hp)
        · have hsub : {z : K | tube c.1 c.2 H ρ z ∧ sat q z} ⊆ {z : K | tube c₀ R₀ H ρ z ∧ sat q z} :=
            fun z hz => ⟨((tube_minus_iff hDsub z).1 hz.1).1, hz.2⟩
          exact mem_holOn_restrict K hsub (hF q (Finset.mem_of_mem_erase hq))

      set pc : Finset (K × K) × Finset (K × K) := (∅, {c}) with hpc
      have hltc : pc.1.card + pc.2.card < p.1.card + p.2.card := by
        simp only [hpc, Finset.card_empty, Finset.card_singleton]; omega
      have hplus := ih (weight (insert pc (s.erase p))) (lt_of_lt_of_le (weight_insert_erase_lt hp hltc) hN)
        c₀ R₀ hR₀ (insert c.1 H) (Function.update ρ c.1 c.2) ?_ (insert pc (s.erase p)) le_rfl ?_ ?_
        (fun z : ↥{z : K | tube c₀ R₀ (insert c.1 H) (Function.update ρ c.1 c.2) z} =>
          F ⟨(z : K), ((tube_plus_iff hz₀ hz₀e (z : K)).1 z.2).1⟩) ?_
      rotate_left
      · intro h hh
        rcases Finset.mem_insert.1 hh with rfl | hhH
        · rwa [Function.update_self]
        · by_cases hhe : h = c.1
          · subst hhe; rwa [Function.update_self]
          · rw [Function.update_of_ne hhe]; exact hρ h hhH
      · intro q hq
        rcases Finset.mem_insert.1 hq with rfl | hq
        · exact ⟨fun er her => absurd her (Finset.notMem_empty _), fun er her => by
            rw [Finset.mem_singleton.1 her]; exact hr⟩
        · exact hrad q (Finset.mem_of_mem_erase hq)
      · intro z hz
        have hz' := (tube_plus_iff hz₀ hz₀e z).1 hz
        obtain ⟨q, hq, hqz⟩ := hcov z hz'.1
        by_cases hqp : q = p
        · subst hqp
          exact ⟨pc, Finset.mem_insert_self _ _, fun er her => absurd her (Finset.notMem_empty _),
            fun er her => by rw [Finset.mem_singleton.1 her]; exact hqz.2 c hc⟩
        · exact ⟨q, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hqp, hq⟩), hqz⟩
      · intro q hq
        rcases Finset.mem_insert.1 hq with rfl | hq
        · have hsub : {z : K | tube c₀ R₀ (insert c.1 H) (Function.update ρ c.1 c.2) z ∧ sat pc z} ⊆
              {z : K | tube c.1 c.2 H ρ z} := by
            rintro z ⟨hz, -, hz2⟩
            have hz' := (tube_plus_iff hz₀ hz₀e z).1 hz
            exact (tube_minus_iff hDsub z).2 ⟨hz'.1, hz2 c (by simp [hpc])⟩
          exact mem_holOn_restrict K hsub hminus
        · have hsub : {z : K | tube c₀ R₀ (insert c.1 H) (Function.update ρ c.1 c.2) z ∧ sat q z} ⊆
              {z : K | tube c₀ R₀ H ρ z ∧ sat q z} :=
            fun z hz => ⟨((tube_plus_iff hz₀ hz₀e z).1 hz.1).1, hz.2⟩
          exact mem_holOn_restrict K hsub (hF q (Finset.mem_of_mem_erase hq))
      exact glue_of_split K hr hDsub hz₀ hz₀e F hminus hplus
    ·
      have hM0 : p.2 = ∅ := Finset.not_nonempty_iff_eq_empty.1 hM
      have hL : p.1.Nonempty := by
        rw [hM0, Finset.card_empty] at hp2; exact Finset.card_pos.1 (by omega)
      obtain ⟨c, hc⟩ := hL
      have hr : c.2 ≠ 0 := (hrad p hp).1 c hc
      by_cases ha : ∀ z : K, tube c₀ R₀ H ρ z → Valued.v (z - c.1) < Valued.v c.2
      ·
        refine ih (weight (s.erase p)) (lt_of_lt_of_le (weight_erase_lt hp (by omega)) hN) c₀ R₀ hR₀ H ρ hρ
          (s.erase p) le_rfl (fun q hq => hrad q (Finset.mem_of_mem_erase hq)) ?_ F
          (fun q hq => hF q (Finset.mem_of_mem_erase hq))
        intro z hz
        obtain ⟨q, hq, hqz⟩ := hcov z hz
        refine ⟨q, Finset.mem_erase.2 ⟨?_, hq⟩, hqz⟩
        rintro rfl
        exact absurd (hqz.1 c hc) (not_le.2 (ha z hz))
      by_cases hb : ∀ z : K, tube c₀ R₀ H ρ z → Valued.v c.2 ≤ Valued.v (z - c.1)
      ·
        set p' : Finset (K × K) × Finset (K × K) := (p.1.erase c, p.2) with hp'
        have hlt : p'.1.card + p'.2.card < p.1.card + p.2.card := by
          simp only [hp', Finset.card_erase_of_mem hc]; have := Finset.card_pos.2 ⟨c, hc⟩; omega
        refine ih (weight (insert p' (s.erase p))) (lt_of_lt_of_le (weight_insert_erase_lt hp hlt) hN) c₀ R₀ hR₀ H ρ hρ
          (insert p' (s.erase p)) le_rfl ?_ ?_ F ?_
        · intro q hq
          rcases Finset.mem_insert.1 hq with rfl | hq
          · exact ⟨fun er her => (hrad p hp).1 er (Finset.mem_of_mem_erase her), (hrad p hp).2⟩
          · exact hrad q (Finset.mem_of_mem_erase hq)
        · intro z hz
          obtain ⟨q, hq, hqz⟩ := hcov z hz
          by_cases hqp : q = p
          · subst hqp
            exact ⟨p', Finset.mem_insert_self _ _, fun er her => hqz.1 er (Finset.mem_of_mem_erase her), hqz.2⟩
          · exact ⟨q, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hqp, hq⟩), hqz⟩
        · intro q hq
          rcases Finset.mem_insert.1 hq with rfl | hq
          · have hsub : {z : K | tube c₀ R₀ H ρ z ∧ sat p' z} ⊆ {z : K | tube c₀ R₀ H ρ z ∧ sat p z} := by
              rintro z ⟨hz, hz1, hz2⟩
              refine ⟨hz, fun er her => ?_, hz2⟩
              by_cases hec : er = c
              · subst hec; exact hb z hz
              · exact hz1 er (Finset.mem_erase.2 ⟨hec, her⟩)
            exact mem_holOn_restrict K hsub (hF p hp)
          · exact hF q (Finset.mem_of_mem_erase hq)

      push Not at ha hb
      obtain ⟨z₁, hz₁, hz₁e⟩ := ha
      obtain ⟨z₀, hz₀, hz₀e⟩ := hb
      have hDsub : ∀ z : K, Valued.v (z - c.1) ≤ Valued.v c.2 → Valued.v (z - c₀) ≤ Valued.v R₀ := by
        by_contra hnot
        obtain ⟨-, hall⟩ := v_sub_le_of_not_sub hnot hz₀ hz₀e.le
        have : Valued.v (z₁ - c.1) < Valued.v c.2 :=
          lt_of_le_of_lt (v_sub_le_max z₁ z₀ c.1) (max_lt (hall z₁ hz₁.1) hz₀e)
        exact absurd hz₁e (not_le.2 this)

      set p' : Finset (K × K) × Finset (K × K) := (p.1.erase c, p.2) with hp'
      have hlt : p'.1.card + p'.2.card < p.1.card + p.2.card := by
        simp only [hp', Finset.card_erase_of_mem hc]; have := Finset.card_pos.2 ⟨c, hc⟩; omega
      have hplus := ih (weight (insert p' (s.erase p))) (lt_of_lt_of_le (weight_insert_erase_lt hp hlt) hN)
        c₀ R₀ hR₀ (insert c.1 H) (Function.update ρ c.1 c.2) ?_ (insert p' (s.erase p)) le_rfl ?_ ?_
        (fun z : ↥{z : K | tube c₀ R₀ (insert c.1 H) (Function.update ρ c.1 c.2) z} =>
          F ⟨(z : K), ((tube_plus_iff hz₀ hz₀e.le (z : K)).1 z.2).1⟩) ?_
      rotate_left
      · intro h hh
        rcases Finset.mem_insert.1 hh with rfl | hhH
        · rwa [Function.update_self]
        · by_cases hhe : h = c.1
          · subst hhe; rwa [Function.update_self]
          · rw [Function.update_of_ne hhe]; exact hρ h hhH
      · intro q hq
        rcases Finset.mem_insert.1 hq with rfl | hq
        · exact ⟨fun er her => (hrad p hp).1 er (Finset.mem_of_mem_erase her), (hrad p hp).2⟩
        · exact hrad q (Finset.mem_of_mem_erase hq)
      · intro z hz
        have hz' := (tube_plus_iff hz₀ hz₀e.le z).1 hz
        obtain ⟨q, hq, hqz⟩ := hcov z hz'.1
        by_cases hqp : q = p
        · subst hqp
          exact ⟨p', Finset.mem_insert_self _ _, fun er her => hqz.1 er (Finset.mem_of_mem_erase her), hqz.2⟩
        · exact ⟨q, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hqp, hq⟩), hqz⟩
      · intro q hq
        rcases Finset.mem_insert.1 hq with rfl | hq
        · have hsub : {z : K | tube c₀ R₀ (insert c.1 H) (Function.update ρ c.1 c.2) z ∧ sat p' z} ⊆
              {z : K | tube c₀ R₀ H ρ z ∧ sat p z} := by
            rintro z ⟨hz, hz1, hz2⟩
            have hz' := (tube_plus_iff hz₀ hz₀e.le z).1 hz
            refine ⟨hz'.1, fun er her => ?_, hz2⟩
            by_cases hec : er = c
            · subst hec; exact hz'.2
            · exact hz1 er (Finset.mem_erase.2 ⟨hec, her⟩)
          exact mem_holOn_restrict K hsub (hF p hp)
        · have hsub : {z : K | tube c₀ R₀ (insert c.1 H) (Function.update ρ c.1 c.2) z ∧ sat q z} ⊆
              {z : K | tube c₀ R₀ H ρ z ∧ sat q z} :=
            fun z hz => ⟨((tube_plus_iff hz₀ hz₀e.le z).1 hz.1).1, hz.2⟩
          exact mem_holOn_restrict K hsub (hF q (Finset.mem_of_mem_erase hq))

      set pc : Finset (K × K) × Finset (K × K) := ({c}, ∅) with hpc
      have hltc : pc.1.card + pc.2.card < p.1.card + p.2.card := by
        simp only [hpc, Finset.card_empty, Finset.card_singleton]; omega
      have hminus := ih (weight (insert pc (s.erase p))) (lt_of_lt_of_le (weight_insert_erase_lt hp hltc) hN)
        c.1 c.2 hr H ρ hρ (insert pc (s.erase p)) le_rfl ?_ ?_
        (fun z : ↥{z : K | tube c.1 c.2 H ρ z} => F ⟨(z : K), ((tube_minus_iff hDsub (z : K)).1 z.2).1⟩) ?_
      rotate_left
      · intro q hq
        rcases Finset.mem_insert.1 hq with rfl | hq
        · exact ⟨fun er her => by rw [Finset.mem_singleton.1 her]; exact hr, fun er her => absurd her (Finset.notMem_empty _)⟩
        · exact hrad q (Finset.mem_of_mem_erase hq)
      · intro z hz
        have hz' := (tube_minus_iff hDsub z).1 hz
        obtain ⟨q, hq, hqz⟩ := hcov z hz'.1
        by_cases hqp : q = p
        · subst hqp
          exact ⟨pc, Finset.mem_insert_self _ _, fun er her => by rw [Finset.mem_singleton.1 her]; exact hqz.1 c hc,
            fun er her => absurd her (Finset.notMem_empty _)⟩
        · exact ⟨q, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hqp, hq⟩), hqz⟩
      · intro q hq
        rcases Finset.mem_insert.1 hq with rfl | hq
        · have hsub : {z : K | tube c.1 c.2 H ρ z ∧ sat pc z} ⊆
              {z : K | tube c₀ R₀ (insert c.1 H) (Function.update ρ c.1 c.2) z} := by
            rintro z ⟨hz, hz1, -⟩
            have hz' := (tube_minus_iff hDsub z).1 hz
            exact (tube_plus_iff hz₀ hz₀e.le z).2 ⟨hz'.1, hz1 c (by simp [hpc])⟩
          exact mem_holOn_restrict K hsub hplus
        · have hsub : {z : K | tube c.1 c.2 H ρ z ∧ sat q z} ⊆ {z : K | tube c₀ R₀ H ρ z ∧ sat q z} :=
            fun z hz => ⟨((tube_minus_iff hDsub z).1 hz.1).1, hz.2⟩
          exact mem_holOn_restrict K hsub (hF q (Finset.mem_of_mem_erase hq))
      exact glue_of_split K hr hDsub hz₀ hz₀e.le F hminus hplus
  ·
    push Not at h1 h3
    have hcard : ∀ p ∈ s, p.1.card + p.2.card = 1 := by
      intro p hp
      have h3' := h3 p hp
      rcases Nat.eq_zero_or_pos (p.1.card + p.2.card) with h0 | hpos
      · exfalso
        have e1 : p.1 = ∅ := Finset.card_eq_zero.1 (by omega)
        have e2 : p.2 = ∅ := Finset.card_eq_zero.1 (by omega)
        have hn := h1 p hp e1
        rw [e2] at hn
        exact Finset.not_nonempty_empty hn
      · omega
    set U : Finset (K × K) := (s.filter fun p => p.1 = ∅).biUnion fun p => p.2 with hU
    set Λ : Finset (K × K) := (s.filter fun p => p.2 = ∅).biUnion fun p => p.1 with hΛ
    refine CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover K c₀ R₀ hR₀ H ρ hρ
      {z : K | tube c₀ R₀ H ρ z} (fun z => Iff.rfl) U Λ ?_ ?_ ?_ F ?_ ?_
    · intro er her
      simp only [hU, Finset.mem_biUnion, Finset.mem_filter] at her
      obtain ⟨p, ⟨hp, -⟩, hep⟩ := her
      exact (hrad p hp).2 er hep
    · intro er her
      simp only [hΛ, Finset.mem_biUnion, Finset.mem_filter] at her
      obtain ⟨p, ⟨hp, -⟩, hep⟩ := her
      exact (hrad p hp).1 er hep
    · intro z hz
      obtain ⟨p, hp, hpz⟩ := hcov z hz
      by_cases hp1 : p.1 = ∅
      · have : p.2.Nonempty := by
          have h' := hcard p hp
          rw [hp1, Finset.card_empty] at h'; exact Finset.card_pos.1 (by omega)
        obtain ⟨er, her⟩ := this
        refine Or.inl ⟨er, ?_, hpz.2 er her⟩
        simp only [hU, Finset.mem_biUnion, Finset.mem_filter]
        exact ⟨p, ⟨hp, hp1⟩, her⟩
      · obtain ⟨er, her⟩ := Finset.nonempty_iff_ne_empty.2 hp1
        have hp2 : p.2 = ∅ := by
          have := hcard p hp
          have : p.2.card = 0 := by have := Finset.card_pos.2 ⟨er, her⟩; omega
          exact Finset.card_eq_zero.1 this
        refine Or.inr ⟨er, ?_, hpz.1 er her⟩
        simp only [hΛ, Finset.mem_biUnion, Finset.mem_filter]
        exact ⟨p, ⟨hp, hp2⟩, her⟩
    · intro er her
      simp only [hU, Finset.mem_biUnion, Finset.mem_filter] at her
      obtain ⟨p, ⟨hp, hp1⟩, hep⟩ := her
      have hp2 : p.2 = {er} := by
        have := hcard p hp
        rw [hp1, Finset.card_empty, zero_add] at this
        obtain ⟨a, ha⟩ := Finset.card_eq_one.1 this
        rw [ha] at hep ⊢; rw [Finset.mem_singleton.1 hep]
      have hsub : {z : K | z ∈ {z : K | tube c₀ R₀ H ρ z} ∧ Valued.v (z - er.1) ≤ Valued.v er.2} ⊆
          {z : K | tube c₀ R₀ H ρ z ∧ sat p z} := by
        rintro z ⟨hz, hze⟩
        refine ⟨hz, by simp [hp1], fun er' her' => ?_⟩
        rw [hp2, Finset.mem_singleton] at her'; subst her'; exact hze
      exact mem_holOn_restrict K hsub (hF p hp)
    · intro er her
      simp only [hΛ, Finset.mem_biUnion, Finset.mem_filter] at her
      obtain ⟨p, ⟨hp, hp2⟩, hep⟩ := her
      have hp1 : p.1 = {er} := by
        have := hcard p hp
        rw [hp2, Finset.card_empty, add_zero] at this
        obtain ⟨a, ha⟩ := Finset.card_eq_one.1 this
        rw [ha] at hep ⊢; rw [Finset.mem_singleton.1 hep]
      have hsub : {z : K | z ∈ {z : K | tube c₀ R₀ H ρ z} ∧ Valued.v er.2 ≤ Valued.v (z - er.1)} ⊆
          {z : K | tube c₀ R₀ H ρ z ∧ sat p z} := by
        rintro z ⟨hz, hze⟩
        refine ⟨hz, fun er' her' => ?_, by simp [hp2]⟩
        rw [hp1, Finset.mem_singleton] at her'; subst her'; exact hze
      exact mem_holOn_restrict K hsub (hF p hp)

end Main

end CerednikDrinfeld.Omega.TubeGlue

open CerednikDrinfeld.Omega.TubeGlue in
theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : K, y ≠ 0 ∧ Valued.v y ≤ ε)

    (c₀ R₀ : K) (hR₀ : R₀ ≠ 0) (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (P : Set K) (hP : ∀ z : K, z ∈ P ↔ Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h))

    {ι : Type} [Fintype ι] (L M : ι → Finset (K × K))
    (hL : ∀ i, ∀ er ∈ L i, er.2 ≠ 0) (hM : ∀ i, ∀ er ∈ M i, er.2 ≠ 0)
    (hcov : ∀ z ∈ P, ∃ i, (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧ (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2))

    (F : ↥P → K)
    (hF : ∀ i, (fun z : ↥{z : K | z ∈ P ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)} => F ⟨(z : K), z.2.1⟩) ∈
        holOn K {z : K | z ∈ P ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)}) :
    F ∈ holOn K P := by
  classical
  have hPeq : P = {z : K | tube c₀ R₀ H ρ z} := Set.ext fun z => hP z
  subst hPeq
  set s : Finset (Finset (K × K) × Finset (K × K)) := Finset.univ.image fun i => (L i, M i) with hs
  refine main K (weight s) c₀ R₀ hR₀ H ρ hρ s le_rfl ?_ ?_ F ?_
  · intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨hL i, hM i⟩
  · intro z hz
    obtain ⟨i, hi⟩ := hcov z hz
    exact ⟨(L i, M i), Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩, hi⟩
  · intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    have hsub : {z : K | tube c₀ R₀ H ρ z ∧ sat (L i, M i) z} ⊆
        {z : K | z ∈ {z : K | tube c₀ R₀ H ρ z} ∧ (∀ er ∈ L i, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧
          (∀ er ∈ M i, Valued.v (z - er.1) ≤ Valued.v er.2)} := fun z hz => hz
    exact mem_holOn_restrict K hsub (hF i)

end

end S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_linearPiece_of_cover
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_linearPiece_of_cover (solution)
