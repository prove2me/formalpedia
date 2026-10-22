-- Prove2me | solution 1 for GagieRIndex.Locate.lemma_3_identity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T16:50:07.698215+00:00
-- url     : https://prove2.me/submissions/5b4f0ceb-9517-48a1-a957-4d797704735e

import Mathlib
import Definitions.Def_GagieRIndex_Locate_Phrases

set_option autoImplicit false

namespace GagieRIndex.Locate.L3Aux
open GagieRIndex.Locate

lemma suffix_cons (n : ℕ) (T : ℕ → ℕ) (i : ℕ) (hi : i ≤ n) :
    suffix n T i = T i :: suffix n T (i + 1) := by
  unfold suffix
  have h : n + 1 - i = (n + 1 - (i + 1)) + 1 := by omega
  rw [h, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [Function.comp, Nat.succ_eq_add_one]
  congr 1
  omega

lemma SA_surj (n : ℕ) (T SA : ℕ → ℕ) (hSA : IsSuffixArray n T SA) (j : ℕ)
    (hj1 : 1 ≤ j) (hjn : j ≤ n) : ∃ p, 1 ≤ p ∧ p ≤ n ∧ SA p = j := by
  have key := Finset.surj_on_of_inj_on_of_card_le (s := Finset.Icc 1 n) (t := Finset.Icc 1 n)
    (fun a _ => SA a)
    (fun a ha => by
      rw [Finset.mem_Icc] at ha ⊢
      exact hSA.1 a ha.1 ha.2)
    (fun a₁ a₂ ha₁ ha₂ h => hSA.2.1 (by simpa using ha₁) (by simpa using ha₂) h)
    le_rfl
  obtain ⟨a, ha, h⟩ := key j (Finset.mem_Icc.2 ⟨hj1, hjn⟩)
  rw [Finset.mem_Icc] at ha
  exact ⟨a, ha.1, ha.2, h.symm⟩

lemma ISA_spec (n : ℕ) (T SA : ℕ → ℕ) (hSA : IsSuffixArray n T SA) (j : ℕ)
    (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    1 ≤ ISA n SA j ∧ ISA n SA j ≤ n ∧ SA (ISA n SA j) = j := by
  obtain ⟨p, hp1, hpn, hpj⟩ := SA_surj n T SA hSA j hj1 hjn
  unfold ISA
  have hsome : ((List.range' 1 n).find? (fun p => SA p == j)).isSome := by
    rw [List.find?_isSome]
    exact ⟨p, List.mem_range'_1.2 ⟨hp1, by omega⟩, by simp [hpj]⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
  rw [hx]
  have hmem := List.mem_of_find?_eq_some hx
  have hpred := List.find?_some hx
  rw [List.mem_range'_1] at hmem
  simp only [beq_iff_eq] at hpred
  simp only [Option.getD_some]
  exact ⟨hmem.1, by omega, hpred⟩

lemma ISA_SA (n : ℕ) (T SA : ℕ → ℕ) (hSA : IsSuffixArray n T SA) (P : ℕ)
    (hP1 : 1 ≤ P) (hPn : P ≤ n) : ISA n SA (SA P) = P := by
  have h := hSA.1 P hP1 hPn
  have hs := ISA_spec n T SA hSA (SA P) h.1 h.2
  exact hSA.2.1 (Set.mem_Icc.2 ⟨hs.1, hs.2.1⟩) (Set.mem_Icc.2 ⟨hP1, hPn⟩) hs.2.2

lemma sorted_lt (n : ℕ) (T SA : ℕ → ℕ) (hSA : IsSuffixArray n T SA) :
    ∀ x y, 1 ≤ x → x < y → y ≤ n → suffix n T (SA x) < suffix n T (SA y) := by
  intro x y hx hxy hyn
  induction y with
  | zero => omega
  | succ y ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hxy with h | h
    · exact lt_trans (ih h (by omega)) (hSA.2.2 y (by omega) (by omega))
    · subst h
      exact hSA.2.2 x hx (by omega)

lemma pos_lt_of_suffix_lt (n : ℕ) (T SA : ℕ → ℕ) (hSA : IsSuffixArray n T SA) (x y : ℕ)
    (hx1 : 1 ≤ x) (hxn : x ≤ n) (hy1 : 1 ≤ y) (hyn : y ≤ n)
    (h : suffix n T (SA x) < suffix n T (SA y)) : x < y := by
  by_contra hc
  rcases lt_or_eq_of_le (not_lt.1 hc) with h' | h'
  · exact lt_asymm h (sorted_lt n T SA hSA y x hy1 h' hxn)
  · subst h'
    exact lt_irrefl _ h

lemma adj (n σ : ℕ) (T SA : ℕ → ℕ) (hT : IsText n σ T) (hSA : IsSuffixArray n T SA)
    (a m j : ℕ) (ha1 : 1 ≤ a) (han : a < n) (hm1 : 1 ≤ m) (hj1 : 1 ≤ j)
    (hma : SA a = m + 1) (hja : SA (a + 1) = j + 1) (hmj : T m = T j) :
    ISA n SA m + 1 = ISA n SA j := by
  have hSAa := hSA.1 a ha1 (by omega)
  have hSAa1 := hSA.1 (a + 1) (by omega) (by omega)
  have hmn : m < n := by omega
  have hjn : j < n := by omega
  obtain ⟨hA1, hAn, hAm⟩ := ISA_spec n T SA hSA m hm1 (by omega)
  obtain ⟨hB1, hBn, hBj⟩ := ISA_spec n T SA hSA j hj1 (by omega)
  have hsm := suffix_cons n T m (by omega)
  have hsj := suffix_cons n T j (by omega)
  have hlt : suffix n T (m + 1) < suffix n T (j + 1) := by
    rw [← hma, ← hja]; exact hSA.2.2 a ha1 han
  have hmj' : suffix n T m < suffix n T j := by
    rw [hsm, hsj, hmj]
    exact List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, hlt⟩)
  have hAB : ISA n SA m < ISA n SA j := by
    apply pos_lt_of_suffix_lt n T SA hSA _ _ hA1 hAn hB1 hBn
    rw [hAm, hBj]; exact hmj'
  by_contra hne
  have hc : ISA n SA m + 1 < ISA n SA j := by omega
  set A := ISA n SA m with hAdef
  set B := ISA n SA j with hBdef
  have hSAc := hSA.1 (A + 1) (by omega) (by omega)
  set s := SA (A + 1) with hsdef
  have h1 : suffix n T m < suffix n T s := by
    rw [← hAm]; exact sorted_lt n T SA hSA A (A + 1) hA1 (by omega) (by omega)
  have h2 : suffix n T s < suffix n T j := by
    rw [← hBj]; exact sorted_lt n T SA hSA (A + 1) B (by omega) hc hBn
  have hss := suffix_cons n T s hSAc.2
  rw [hsm, hss, List.cons_lt_cons_iff] at h1
  rw [hss, hsj, List.cons_lt_cons_iff] at h2
  have hTj : T j ≠ 1 := hT.2.2.2 j hj1 hjn
  have hTn : T n = 1 := hT.2.2.1
  rcases h1 with h1 | ⟨h1e, h1⟩ <;> rcases h2 with h2 | ⟨h2e, h2⟩
  · omega
  · omega
  · omega
  · have hsn : s ≠ n := by
      intro hsn; rw [hsn] at h2e; omega
    have hs1 : 1 ≤ s := hSAc.1
    obtain ⟨hD1, hDn, hDs⟩ := ISA_spec n T SA hSA (s + 1) (by omega) (by omega)
    have e1 : a < ISA n SA (s + 1) := by
      apply pos_lt_of_suffix_lt n T SA hSA _ _ ha1 (by omega) hD1 hDn
      rw [hma, hDs]; exact h1
    have e2 : ISA n SA (s + 1) < a + 1 := by
      apply pos_lt_of_suffix_lt n T SA hSA _ _ hD1 hDn (by omega) (by omega)
      rw [hja, hDs]; exact h2
    omega

lemma mem_sampled_of_runStart (n : ℕ) (T SA : ℕ → ℕ) (P j : ℕ) (hP1 : 1 ≤ P) (hPn : P ≤ n)
    (hPj : SA P = j + 1) (hj1 : 1 ≤ j) (h : IsRunStart n T SA P ∨ IsRunEnd n T SA P) :
    j ∈ sampled n T SA := by
  unfold sampled
  rw [Finset.mem_image]
  refine ⟨P, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hP1, hPn⟩, h⟩, ?_⟩
  unfold textPos
  rw [hPj]
  simp only [Nat.add_eq_right, Nat.add_sub_cancel]
  rw [if_neg (by omega)]

lemma prev_step (n σ : ℕ) (T SA : ℕ → ℕ) (hT : IsText n σ T) (hSA : IsSuffixArray n T SA)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j < n) (hns : j ∉ sampled n T SA) :
    2 ≤ ISA n SA j ∧ SA (ISA n SA j - 1) + 1 = SA (ISA n SA (j + 1) - 1) := by
  obtain ⟨hP1, hPn, hPj⟩ := ISA_spec n T SA hSA (j + 1) (by omega) (by omega)
  set P := ISA n SA (j + 1) with hPdef
  have hnrs : ¬ IsRunStart n T SA P := fun h =>
    hns (mem_sampled_of_runStart n T SA P j hP1 hPn hPj hj1 (Or.inl h))
  unfold IsRunStart at hnrs
  push_neg at hnrs
  obtain ⟨hP1', hbw⟩ := hnrs hP1 hPn
  have hbP : bwt n T SA P = T j := by
    unfold bwt; rw [if_neg (show SA P ≠ 1 by omega), hPj]; rfl
  have hu := hSA.1 (P - 1) (by omega) (by omega)
  have hTj : T j ≠ 1 := hT.2.2.2 j hj1 hjn
  have hTn : T n = 1 := hT.2.2.1
  have hu1 : SA (P - 1) ≠ 1 := by
    intro h1
    have : bwt n T SA (P - 1) = T n := by unfold bwt; rw [if_pos h1]
    rw [hbw, hbP, hTn] at this
    exact hTj this
  have hbu : bwt n T SA (P - 1) = T (SA (P - 1) - 1) := by
    unfold bwt; rw [if_neg hu1]
  have hTm : T (SA (P - 1) - 1) = T j := by rw [← hbu, hbw, hbP]
  have hadj := adj n σ T SA hT hSA (P - 1) (SA (P - 1) - 1) j (by omega) (by omega) (by omega) hj1
    (by omega) (by rw [show P - 1 + 1 = P by omega]; exact hPj) hTm
  obtain ⟨hM1, hMn, hMm⟩ := ISA_spec n T SA hSA (SA (P - 1) - 1) (by omega) (by omega)
  refine ⟨by omega, ?_⟩
  rw [show ISA n SA j - 1 = ISA n SA (SA (P - 1) - 1) by omega, hMm]
  omega

lemma next_step (n σ : ℕ) (T SA : ℕ → ℕ) (hT : IsText n σ T) (hSA : IsSuffixArray n T SA)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j < n) (hns : j ∉ sampled n T SA) :
    ISA n SA j < n ∧ SA (ISA n SA j + 1) + 1 = SA (ISA n SA (j + 1) + 1) := by
  obtain ⟨hP1, hPn, hPj⟩ := ISA_spec n T SA hSA (j + 1) (by omega) (by omega)
  set P := ISA n SA (j + 1) with hPdef
  have hnre : ¬ IsRunEnd n T SA P := fun h =>
    hns (mem_sampled_of_runStart n T SA P j hP1 hPn hPj hj1 (Or.inr h))
  unfold IsRunEnd at hnre
  push_neg at hnre
  obtain ⟨hPn', hbw⟩ := hnre hP1 hPn
  have hbP : bwt n T SA P = T j := by
    unfold bwt; rw [if_neg (show SA P ≠ 1 by omega), hPj]; rfl
  have hu := hSA.1 (P + 1) (by omega) (by omega)
  have hTj : T j ≠ 1 := hT.2.2.2 j hj1 hjn
  have hTn : T n = 1 := hT.2.2.1
  have hu1 : SA (P + 1) ≠ 1 := by
    intro h1
    have : bwt n T SA (P + 1) = T n := by unfold bwt; rw [if_pos h1]
    rw [hbw, hbP, hTn] at this
    exact hTj this
  have hbu : bwt n T SA (P + 1) = T (SA (P + 1) - 1) := by
    unfold bwt; rw [if_neg hu1]
  have hTm : T j = T (SA (P + 1) - 1) := by rw [← hbu, hbw, hbP]
  have hadj := adj n σ T SA hT hSA P j (SA (P + 1) - 1) hP1 (by omega) hj1 (by omega)
    hPj (by omega) hTm
  obtain ⟨hM1, hMn, hMm⟩ := ISA_spec n T SA hSA (SA (P + 1) - 1) (by omega) (by omega)
  refine ⟨by omega, ?_⟩
  rw [hadj, hMm]
  omega

lemma phraseHead_le (n : ℕ) (T SA : ℕ → ℕ) (k : ℕ) : phraseHead n T SA k ≤ k := by
  unfold phraseHead
  apply Finset.sup_le
  intro b hb
  exact (Finset.mem_filter.1 hb).2

lemma not_sampled_of_gt (n : ℕ) (T SA : ℕ → ℕ) (k j : ℕ) (h1 : phraseHead n T SA k < j)
    (h2 : j ≤ k) : j ∉ sampled n T SA := by
  intro hj
  have : j ≤ phraseHead n T SA k := by
    unfold phraseHead
    exact Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hj, h2⟩)
  omega

end GagieRIndex.Locate.L3Aux

open GagieRIndex.Locate in
theorem solution (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : IsText n σ T) (hSA : IsSuffixArray n T SA)
    (p : ℕ) (hp1 : 1 ≤ p) (hpn : p ≤ n) :
    let k := SA p - 1
    let i := phraseHead n T SA k
    let q := ISA n SA (i + 1)
    (2 ≤ p → 2 ≤ q ∧ SA (p - 1) = SA (q - 1) + (k - i)) ∧
    (p < n → q < n ∧ SA (p + 1) = SA (q + 1) + (k - i)) := by
  intro k i q
  have hk : k = SA p - 1 := rfl
  have hi : i = phraseHead n T SA k := rfl
  have hq : q = ISA n SA (i + 1) := rfl
  clear_value q i k
  have hSAp := hSA.1 p hp1 hpn
  have hik : i ≤ k := by rw [hi]; exact L3Aux.phraseHead_le n T SA k
  have hkn : k < n := by omega
  have hp_isa : ISA n SA (k + 1) = p := by
    rw [show k + 1 = SA p by omega]; exact L3Aux.ISA_SA n T SA hSA p hp1 hpn
  have hns : ∀ j, i < j → j ≤ k → j ∉ sampled n T SA := fun j h1 h2 =>
    L3Aux.not_sampled_of_gt n T SA k j (by rw [← hi]; exact h1) h2
  have chainP : ∀ t, i + t ≤ k → SA (ISA n SA (i + 1 + t) - 1) = SA (q - 1) + t := by
    intro t
    induction t with
    | zero => intro _; simp [hq]
    | succ t ih =>
      intro ht
      have hj := L3Aux.prev_step n σ T SA hT hSA (i + 1 + t) (by omega) (by omega)
        (hns _ (by omega) (by omega))
      rw [show i + 1 + (t + 1) = i + 1 + t + 1 by omega, ← hj.2, ih (by omega)]
      ring
  have chainN : ∀ t, i + t ≤ k → SA (ISA n SA (i + 1 + t) + 1) = SA (q + 1) + t := by
    intro t
    induction t with
    | zero => intro _; simp [hq]
    | succ t ih =>
      intro ht
      have hj := L3Aux.next_step n σ T SA hT hSA (i + 1 + t) (by omega) (by omega)
        (hns _ (by omega) (by omega))
      rw [show i + 1 + (t + 1) = i + 1 + t + 1 by omega, ← hj.2, ih (by omega)]
      ring
  refine ⟨fun hp2 => ⟨?_, ?_⟩, fun hpn' => ⟨?_, ?_⟩⟩
  · by_cases hik' : i = k
    · rw [hq, hik', hp_isa]; exact hp2
    · rw [hq]
      exact (L3Aux.prev_step n σ T SA hT hSA (i + 1) (by omega) (by omega)
        (hns _ (by omega) (by omega))).1
  · have h := chainP (k - i) (by omega)
    rw [show i + 1 + (k - i) = k + 1 by omega, hp_isa] at h
    exact h
  · by_cases hik' : i = k
    · rw [hq, hik', hp_isa]; exact hpn'
    · rw [hq]
      exact (L3Aux.next_step n σ T SA hT hSA (i + 1) (by omega) (by omega)
        (hns _ (by omega) (by omega))).1
  · have h := chainN (k - i) (by omega)
    rw [show i + 1 + (k - i) = k + 1 by omega, hp_isa] at h
    exact h
