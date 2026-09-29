-- Prove2me | solution 1 for Erdos20.erdos_rado_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:39:01.656694+00:00
-- url     : https://prove2.me/submissions/4b82341c-e332-4b0a-b989-2d3e5cad6a85

import Definitions.Def_Erdos20_defs
import Mathlib

namespace Erdos20

/-- Greedy lemma: if every point lies in at most `d` members of a family of nonempty
`s`-sets and the family has more than `j * s * d` members, it contains `j + 1` pairwise
disjoint members. -/
theorem aux_er_disj {α : Type} [DecidableEq α] (s d : ℕ) (hs : 0 < s) :
    ∀ j : ℕ, ∀ F : Finset (Finset α), (∀ A ∈ F, A.card = s) →
      (∀ x, (F.filter (fun B => x ∈ B)).card ≤ d) → j * s * d < F.card →
      ∃ T ⊆ F, T.card = j + 1 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → A ∩ B = ∅ := by
  intro j
  induction j with
  | zero =>
    intro F _ _ hF
    have : F.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨A, hA⟩ := this
    refine ⟨{A}, by simpa using hA, by simp, ?_⟩
    intro X hX Y hY hXY
    simp only [Finset.mem_singleton] at hX hY
    subst hX; subst hY; exact absurd rfl hXY
  | succ j ih =>
    intro F hcard hdeg hF
    have hne : F.Nonempty := Finset.card_pos.mp (by
      have : 0 ≤ (j+1) * s * d := Nat.zero_le _
      omega)
    obtain ⟨A, hA⟩ := hne
    have hsub : F.filter (fun B => ¬ (A ∩ B = ∅)) ⊆
        A.biUnion (fun x => F.filter (fun B => x ∈ B)) := by
      intro B hB
      simp only [Finset.mem_filter] at hB
      obtain ⟨hBF, hAB⟩ := hB
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hAB
      rw [Finset.mem_inter] at hx
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      exact ⟨x, hx.1, hBF, hx.2⟩
    have hbound : (F.filter (fun B => ¬ (A ∩ B = ∅))).card ≤ s * d := by
      calc (F.filter (fun B => ¬ (A ∩ B = ∅))).card
          ≤ (A.biUnion (fun x => F.filter (fun B => x ∈ B))).card := Finset.card_le_card hsub
        _ ≤ ∑ x ∈ A, (F.filter (fun B => x ∈ B)).card := Finset.card_biUnion_le
        _ ≤ ∑ _x ∈ A, d := Finset.sum_le_sum (fun x _ => hdeg x)
        _ = s * d := by rw [Finset.sum_const, hcard A hA, smul_eq_mul]
    have hsplit := Finset.card_filter_add_card_filter_not (s := F) (fun B => A ∩ B = ∅)
    have hF'card : j * s * d < (F.filter (fun B => A ∩ B = ∅)).card := by
      have : (j+1) * s * d = j * s * d + s * d := by ring
      omega
    obtain ⟨T', hT'sub, hT'card, hT'disj⟩ := ih (F.filter (fun B => A ∩ B = ∅))
      (fun B hB => hcard B (Finset.mem_filter.mp hB).1)
      (fun x => le_trans (Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.filter_subset _ _))) (hdeg x)) hF'card
    have hAT' : A ∉ T' := by
      intro h
      have h2 := (Finset.mem_filter.mp (hT'sub h)).2
      rw [Finset.inter_self] at h2
      have hc := hcard A hA
      rw [h2] at hc
      simp at hc
      omega
    refine ⟨insert A T', ?_, ?_, ?_⟩
    · intro X hX
      rw [Finset.mem_insert] at hX
      rcases hX with rfl | hX
      · exact hA
      · exact (Finset.mem_filter.mp (hT'sub hX)).1
    · rw [Finset.card_insert_of_notMem hAT', hT'card]
    · intro X hX Y hY hXY
      rw [Finset.mem_insert] at hX hY
      rcases hX with rfl | hX <;> rcases hY with rfl | hY
      · exact absurd rfl hXY
      · exact (Finset.mem_filter.mp (hT'sub hY)).2
      · rw [Finset.inter_comm]; exact (Finset.mem_filter.mp (hT'sub hX)).2
      · exact hT'disj X hX Y hY hXY

/-- The Erdős–Rado bound function. -/
def aux_er_G (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => (k - 1) * (n + 1) * aux_er_G k n

/-- Sunflower lemma (Erdős–Rado) for finset families. -/
theorem aux_er_sf {α : Type} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k) :
    ∀ n : ℕ, ∀ F : Finset (Finset α), (∀ A ∈ F, A.card = n) → aux_er_G k n < F.card →
      ∃ S ⊆ F, S.card = k ∧ ∃ K : Finset α, ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = K := by
  intro n
  induction n with
  | zero =>
    intro F hF hc
    exfalso
    have hsub : F ⊆ {∅} := by
      intro A hA
      rw [Finset.mem_singleton]
      exact Finset.card_eq_zero.mp (hF A hA)
    have := Finset.card_le_card hsub
    simp only [aux_er_G, Finset.card_singleton] at hc this
    omega
  | succ n ih =>
    intro F hF hc
    by_cases hx : ∃ x, aux_er_G k n < (F.filter (fun B => x ∈ B)).card
    · obtain ⟨x, hx⟩ := hx
      have hinj : Set.InjOn (fun B => B.erase x)
          ((F.filter (fun B => x ∈ B) : Finset (Finset α)) : Set (Finset α)) := by
        intro B₁ h₁ B₂ h₂ he
        have h₁' := (Finset.mem_filter.mp h₁).2
        have h₂' := (Finset.mem_filter.mp h₂).2
        simp only at he
        rw [← Finset.insert_erase h₁', ← Finset.insert_erase h₂', he]
      obtain ⟨S', hS'sub, hS'card, K, hK⟩ :=
        ih ((F.filter (fun B => x ∈ B)).image (fun B => B.erase x))
        (by
          intro A hA
          rw [Finset.mem_image] at hA
          obtain ⟨B, hB, rfl⟩ := hA
          have hB' := Finset.mem_filter.mp hB
          rw [Finset.card_erase_of_mem hB'.2, hF B hB'.1]
          rfl)
        (by rw [Finset.card_image_of_injOn hinj]; exact hx)
      have hS'x : ∀ B ∈ S', x ∉ B := by
        intro B hB
        obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp (hS'sub hB)
        exact Finset.notMem_erase x C
      have hS'F : ∀ B ∈ S', insert x B ∈ F := by
        intro B hB
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp (hS'sub hB)
        have hC' := Finset.mem_filter.mp hC
        rw [Finset.insert_erase hC'.2]
        exact hC'.1
      have hinj2 : Set.InjOn (fun B => insert x B) (S' : Set (Finset α)) := by
        intro B₁ h₁ B₂ h₂ he
        simp only at he
        rw [← Finset.erase_insert (hS'x B₁ h₁), ← Finset.erase_insert (hS'x B₂ h₂), he]
      refine ⟨S'.image (fun B => insert x B), ?_, ?_, insert x K, ?_⟩
      · intro A hA
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
        exact hS'F B hB
      · rw [Finset.card_image_of_injOn hinj2, hS'card]
      · intro A hA B hB hAB
        obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
        have hne : A' ≠ B' := by rintro rfl; exact hAB rfl
        rw [← Finset.insert_inter_distrib, hK A' hA' B' hB' hne]
    · push Not at hx
      obtain ⟨T, hTsub, hTcard, hTdisj⟩ :=
        aux_er_disj (n+1) (aux_er_G k n) (Nat.succ_pos n) (k-1) F hF hx
        (by simpa [aux_er_G] using hc)
      exact ⟨T, hTsub, by rw [hTcard]; omega, ∅, hTdisj⟩

theorem aux_er_upper (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    (aux_er_G k n + 1) ∈ {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ A ∈ F, A.ncard = n) ∧ m ≤ F.ncard) → ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S} := by
  intro α F ⟨hA, hm⟩
  classical
  have hFfin : F.Finite := Set.finite_of_ncard_pos (by omega)
  have hAfin : ∀ A ∈ F, A.Finite := fun A hA' =>
    Set.finite_of_ncard_pos (by rw [hA A hA']; exact hn)
  have hPfin : ((fun B : Finset α => (B : Set α)) ⁻¹' F).Finite :=
    hFfin.preimage (Finset.coe_injective.injOn)
  have hFimg : (fun B : Finset α => (B : Set α)) '' ((fun B : Finset α => (B : Set α)) ⁻¹' F)
      = F := by
    ext A; constructor
    · rintro ⟨B, hB, rfl⟩; exact hB
    · intro hAF; exact ⟨(hAfin A hAF).toFinset, by simpa using hAF, by simp⟩
  have hFFcard : hPfin.toFinset.card = F.ncard := by
    rw [← Set.ncard_eq_toFinset_card _ hPfin]
    conv_rhs => rw [← hFimg]
    rw [Set.ncard_image_of_injective _ Finset.coe_injective]
  obtain ⟨S, hSsub, hScard, K, hK⟩ := aux_er_sf k (by omega) n hPfin.toFinset
    (by
      intro B hB
      rw [Set.Finite.mem_toFinset] at hB
      have := hA _ hB
      rwa [Set.ncard_coe_finset] at this)
    (by omega)
  refine ⟨(fun B : Finset α => (B : Set α)) '' (S : Set (Finset α)), ?_, ?_, ⟨(K : Set α), ?_⟩⟩
  · rintro _ ⟨B, hB, rfl⟩
    have := hSsub hB
    rw [Set.Finite.mem_toFinset] at this
    exact this
  · rw [Set.ncard_image_of_injective _ Finset.coe_injective, Set.ncard_coe_finset, hScard]
  · rintro _ ⟨A, hA', rfl⟩ _ ⟨B, hB', rfl⟩ hAB
    have hne : A ≠ B := by rintro rfl; exact hAB rfl
    simp only
    rw [← Finset.coe_inter, hK A hA' B hB' hne]

theorem aux_er_lower (n k m : ℕ) (hk : 2 ≤ k)
    (hm : m ∈ {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ A ∈ F, A.ncard = n) ∧ m ≤ F.ncard) → ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}) :
    (k - 1) ^ n < m := by
  by_contra hlt
  push Not at hlt
  let graph : (Fin n → Fin (k-1)) → Set (Fin n × Fin (k-1)) :=
    fun g => Set.range (fun i => (i, g i))
  have hmem : ∀ g i v, ((i, v) ∈ graph g ↔ g i = v) := by
    intro g i v; simp [graph]
  have hginj : Function.Injective graph := by
    intro g h hgh
    funext i
    have : (i, g i) ∈ graph h := by rw [← hgh]; exact (hmem g i (g i)).mpr rfl
    exact ((hmem h i (g i)).mp this).symm
  have hcardA : ∀ g, (graph g).ncard = n := by
    intro g
    simp only [graph]
    rw [Set.ncard_range_of_injective]
    · simp
    · intro i j hij; exact (Prod.mk.inj hij).1
  have hFcard : (Set.range graph).ncard = (k-1)^n := by
    rw [Set.ncard_range_of_injective hginj]
    simp
  obtain ⟨S, hSsub, hScard, K, hK⟩ := hm (Set.range graph)
    ⟨by rintro _ ⟨g, rfl⟩; exact hcardA g, by rw [hFcard]; exact hlt⟩
  have hST : graph '' (graph ⁻¹' S) = S := by
    ext A; constructor
    · rintro ⟨g, hg, rfl⟩; exact hg
    · intro hA; obtain ⟨g, rfl⟩ := hSsub hA; exact ⟨g, hA, rfl⟩
  have hTcard : (graph ⁻¹' S).ncard = k := by
    have h0 := Set.ncard_image_of_injective (graph ⁻¹' S) hginj
    rw [hST, hScard] at h0
    exact h0.symm
  obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff).mp (by omega : 1 < (graph ⁻¹' S).ncard)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
  have hinj : Set.InjOn (fun g => g i) (graph ⁻¹' S) := by
    intro g hg h hh hgh
    by_contra hne
    simp only at hgh
    have h1 : (i, g i) ∈ graph g ∩ graph h :=
      ⟨(hmem g i _).mpr rfl, (hmem h i _).mpr hgh.symm⟩
    rw [hK hg hh (fun e => hne (hginj e))] at h1
    rw [← hK ha hb (fun e => hab (hginj e))] at h1
    exact hi (((hmem a i _).mp h1.1).trans ((hmem b i _).mp h1.2).symm)
  have := Set.ncard_le_ncard_of_injOn (fun g => g i) (fun (g : Fin n → Fin (k-1)) _ => Set.mem_univ (g i)) hinj
    Set.finite_univ
  rw [hTcard, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

end Erdos20

open Erdos20

theorem solution :
    ∀ n k, n > 0 → 2 ≤ k → (k - 1) ^ n < f n k := by
  intro n k hn hk
  unfold f
  exact aux_er_lower n k _ hk (Nat.sInf_mem ⟨_, @aux_er_upper n k hn hk⟩)
