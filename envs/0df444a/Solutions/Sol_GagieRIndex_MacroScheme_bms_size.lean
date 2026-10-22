-- Prove2me | solution 1 for GagieRIndex.MacroScheme.bms_size
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T20:36:56.117724+00:00
-- url     : https://prove2.me/submissions/78442545-8d32-4a68-9b55-2c72a8417e87

import Mathlib
import Definitions.Def_GagieRIndex_MacroScheme_Arrays
import Definitions.Def_GagieRIndex_MacroScheme_BMS

set_option autoImplicit false

namespace GagieRIndex.MacroScheme.BmsAux
open GagieRIndex.MacroScheme

/-! ## Generic construction of a macro scheme from an explicit set and a source map -/

lemma blockStart_succ (B : List Block) (k : ℕ) (hk : k < B.length) :
    blockStart B (k + 1) = blockStart B k + (B[k]).len := by
  unfold blockStart
  simp only [List.map_take]
  rw [List.take_add_one, List.sum_append, List.getElem?_map, List.getElem?_eq_getElem hk]
  simp [Nat.add_assoc]

lemma blockStart_of_le (B : List Block) (k : ℕ) (h : B.length ≤ k) :
    blockStart B k = 1 + (B.map Block.len).sum := by
  unfold blockStart
  rw [List.take_of_length_le h]

lemma blockStart_le (B : List Block) (k : ℕ) :
    blockStart B k ≤ 1 + (B.map Block.len).sum := by
  unfold blockStart
  rw [List.map_take]
  have := List.sum_take_add_sum_drop (B.map Block.len) k
  omega

lemma blockStart_mono (B : List Block) {a b : ℕ} (h : a ≤ b) :
    blockStart B a ≤ blockStart B b := by
  unfold blockStart
  have h3 : (B.take a).map Block.len = ((B.take b).map Block.len).take a := by
    rw [List.map_take, List.map_take, List.take_take, Nat.min_eq_left h]
  have h2 := List.sum_take_add_sum_drop ((B.take b).map Block.len) a
  rw [h3]
  omega

lemma bs_append (L M : List Block) (k : ℕ) (hk : k ≤ L.length) :
    blockStart (L ++ M) k = blockStart L k := by
  unfold blockStart
  rw [List.take_append_of_le_length hk]

lemma getD_app (L M : List Block) (k : ℕ) (hk : k < L.length) (d : Block) :
    (L ++ M).getD k d = L.getD k d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hk,
    List.getElem_append_left hk]

lemma getD_last (L : List Block) (b d : Block) : (L ++ [b]).getD L.length d = b := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

lemma bs_last (L : List Block) : blockStart L L.length = 1 + (L.map Block.len).sum := by
  unfold blockStart
  simp

def Inv (e : ℕ → Prop) (g : ℕ → ℕ) (L : List Block) (m : ℕ) : Prop :=
  (L.map Block.len).sum = m ∧
  (∀ b ∈ L, 1 ≤ b.len ∧ (b.src = none → b.len = 1)) ∧
  (∀ k, k < L.length → ∀ t, t < (L.getD k ⟨0, none⟩).len →
     ((L.getD k ⟨0, none⟩).src = none → e (blockStart L k + t)) ∧
     (∀ j, (L.getD k ⟨0, none⟩).src = some j →
        ¬ e (blockStart L k + t) ∧ g (blockStart L k + t) = j + t))

def cnt (e : ℕ → Prop) [DecidablePred e] (m : ℕ) : ℕ :=
  ((Finset.range m).filter (fun i => ¬ (¬ e (i + 1) ∧ 2 ≤ i + 1 ∧ ¬ e i))).card

lemma cnt_succ (e : ℕ → Prop) [DecidablePred e] (m : ℕ) :
    cnt e (m + 1) = cnt e m + if (¬ e (m + 1) ∧ 2 ≤ m + 1 ∧ ¬ e m) then 0 else 1 := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : (¬ e (m + 1) ∧ 2 ≤ m + 1 ∧ ¬ e m)
  · rw [if_neg (not_not.2 h), if_pos h]
    simp
  · rw [if_pos h, if_neg h, Finset.card_insert_of_notMem (by simp)]

lemma step (e : ℕ → Prop) [DecidablePred e] (g : ℕ → ℕ) (n : ℕ)
    (hc : ∀ x, 2 ≤ x → x ≤ n → ¬ e x → ¬ e (x - 1) → g x = g (x - 1) + 1)
    (L : List Block) (m : ℕ) (hm : m + 1 ≤ n) (h : Inv e g L m) (hl : L.length ≤ cnt e m) :
    ∃ L', Inv e g L' (m + 1) ∧ L'.length ≤ cnt e (m + 1) := by
  obtain ⟨hsum, hb, hK⟩ := h
  rw [cnt_succ]
  by_cases hmg : (¬ e (m + 1) ∧ 2 ≤ m + 1 ∧ ¬ e m)
  · rw [if_pos hmg]
    rcases List.eq_nil_or_concat L with hL | ⟨L0, b, hL⟩
    · subst hL
      simp at hsum
      omega
    · rw [List.concat_eq_append] at hL
      subst hL
      have hsum' : (L0.map Block.len).sum + b.len = m := by simpa using hsum
      have hb1 : 1 ≤ b.len := (hb b (by simp)).1
      have hlastK := hK L0.length (by simp) (b.len - 1) (by rw [getD_last]; omega)
      rw [getD_last, bs_append _ _ _ le_rfl, bs_last] at hlastK
      have hpos : 1 + (L0.map Block.len).sum + (b.len - 1) = m := by omega
      rw [hpos] at hlastK
      obtain ⟨j, hj⟩ : ∃ j, b.src = some j := by
        cases hs : b.src with
        | none => exact absurd (hlastK.1 hs) hmg.2.2
        | some j => exact ⟨j, rfl⟩
      have hgm := (hlastK.2 j hj).2
      refine ⟨L0 ++ [⟨b.len + 1, b.src⟩], ⟨?_, ?_, ?_⟩, ?_⟩
      · simp
        omega
      · intro b' hb'
        rw [List.mem_append, List.mem_singleton] at hb'
        rcases hb' with hb' | rfl
        · exact hb b' (List.mem_append_left _ hb')
        · refine ⟨by dsimp only; omega, fun h' => ?_⟩
          dsimp only at h'
          rw [hj] at h'
          cases h'
      · intro k hk t ht
        simp only [List.length_append, List.length_singleton] at hk
        rcases Nat.lt_or_ge k L0.length with hk0 | hk0
        · rw [getD_app _ _ _ hk0] at ht ⊢
          rw [bs_append _ _ _ hk0.le]
          have := hK k (by simp; omega) t (by rw [getD_app _ _ _ hk0]; exact ht)
          rw [getD_app _ _ _ hk0, bs_append _ _ _ hk0.le] at this
          exact this
        · have hk' : k = L0.length := by omega
          subst hk'
          rw [getD_last] at ht ⊢
          rw [bs_append _ _ _ le_rfl, bs_last]
          dsimp only at ht ⊢
          rcases Nat.lt_or_ge t b.len with htb | htb
          · have := hK L0.length (by simp) t (by rw [getD_last]; exact htb)
            rw [getD_last, bs_append _ _ _ le_rfl, bs_last] at this
            exact this
          · have ht' : t = b.len := by omega
            subst ht'
            have hpos2 : 1 + (L0.map Block.len).sum + b.len = m + 1 := by omega
            rw [hpos2]
            refine ⟨(fun h' => by rw [hj] at h'; cases h'), fun j' hj' => ?_⟩
            rw [hj] at hj'
            cases hj'
            refine ⟨hmg.1, ?_⟩
            have := hc (m + 1) hmg.2.1 hm hmg.1 (by simpa using hmg.2.2)
            simp only [Nat.add_sub_cancel] at this
            omega
      · simp at hl ⊢
        omega
  · rw [if_neg hmg]
    refine ⟨L ++ [⟨1, if e (m + 1) then none else some (g (m + 1))⟩], ⟨?_, ?_, ?_⟩, ?_⟩
    · simp [hsum]
    · intro b' hb'
      rw [List.mem_append, List.mem_singleton] at hb'
      rcases hb' with hb' | rfl
      · exact hb b' hb'
      · exact ⟨le_rfl, fun _ => rfl⟩
    · intro k hk t ht
      simp only [List.length_append, List.length_singleton] at hk
      rcases Nat.lt_or_ge k L.length with hk0 | hk0
      · rw [getD_app _ _ _ hk0] at ht ⊢
        rw [bs_append _ _ _ hk0.le]
        exact hK k hk0 t ht
      · have hk' : k = L.length := by omega
        subst hk'
        rw [getD_last] at ht ⊢
        dsimp only at ht ⊢
        have ht0 : t = 0 := by omega
        subst ht0
        rw [bs_append _ _ _ le_rfl, bs_last, hsum]
        have h1m : 1 + m + 0 = m + 1 := by omega
        rw [h1m]
        by_cases he : e (m + 1)
        · simp [he]
        · simp [he]
    · simp
      omega

lemma build (e : ℕ → Prop) [DecidablePred e] (g : ℕ → ℕ) (n : ℕ)
    (hc : ∀ x, 2 ≤ x → x ≤ n → ¬ e x → ¬ e (x - 1) → g x = g (x - 1) + 1) :
    ∀ m, m ≤ n → ∃ L, Inv e g L m ∧ L.length ≤ cnt e m := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨[], ⟨by simp, by simp, by simp⟩, by simp⟩
  | succ m ih =>
    intro hm
    obtain ⟨L, hL, hl⟩ := ih (by omega)
    exact step e g n hc L m hm hL hl

lemma locate (B : List Block) (y : ℕ) (h1 : 1 ≤ y) (h2 : y < 1 + (B.map Block.len).sum) :
    ∃ k, ∃ hk : k < B.length, blockStart B k ≤ y ∧ y < blockStart B k + (B[k]).len := by
  have hex : ∃ k, y < blockStart B (k + 1) := ⟨B.length, by
      have := blockStart_of_le B (B.length + 1) (by omega)
      omega⟩
  classical
  have hk1 : y < blockStart B (Nat.find hex + 1) := Nat.find_spec hex
  have hk2 : blockStart B (Nat.find hex) ≤ y := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · rw [h0]
      simp [blockStart]
      omega
    · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      rw [Nat.sub_add_cancel h0] at this
      omega
  have hkl : Nat.find hex < B.length := by
    by_contra hc
    push_neg at hc
    have := blockStart_of_le B (Nat.find hex) hc
    omega
  refine ⟨Nat.find hex, hkl, hk2, ?_⟩
  rw [← blockStart_succ B _ hkl]
  exact hk1

lemma blockOf_eq (B : List Block) (k : ℕ) (hk : k < B.length) (y : ℕ)
    (h1 : blockStart B k ≤ y) (h2 : y < blockStart B k + (B[k]).len) :
    blockOf B y = some k := by
  unfold blockOf
  rw [List.find?_range_eq_some]
  refine ⟨?_, List.mem_range.2 hk, ?_⟩
  · rw [List.getD_eq_getElem _ _ hk]
    simp [h1, h2]
  · intro j hj
    have hjl : j < B.length := by omega
    have e1 := blockStart_succ B j hjl
    have e2 := blockStart_mono B (show j + 1 ≤ k by omega)
    rw [List.getD_eq_getElem _ _ hjl]
    simp only [Bool.not_and, Bool.not_eq_true', decide_eq_false_iff_not, not_le, not_lt,
      Bool.or_eq_true, decide_eq_true_eq]
    right
    omega

def gp (e : ℕ → Prop) [DecidablePred e] (g : ℕ → ℕ) (y : ℕ) : ℕ := if e y then y else g y

theorem gen (n : ℕ) (S : ℕ → ℤ) (e : ℕ → Prop) [DecidablePred e] (g : ℕ → ℕ)
    (hg : ∀ x, 1 ≤ x → x ≤ n → ¬ e x → 1 ≤ g x ∧ g x ≤ n ∧ g x ≠ x ∧ S (g x) = S x)
    (hc : ∀ x, 2 ≤ x → x ≤ n → ¬ e x → ¬ e (x - 1) → g x = g (x - 1) + 1)
    (hreach : ∀ x, 1 ≤ x → x ≤ n → ∃ m, e ((gp e g)^[m] x)) :
    ∃ B : List Block, IsBMS n S B ∧ B.length ≤ cnt e n := by
  obtain ⟨B, ⟨hsum, hb, hK⟩, hlen⟩ := build e g n hc n le_rfl
  have hK' : ∀ k (hk : k < B.length) t, t < (B[k]).len →
      ((B[k]).src = none → e (blockStart B k + t)) ∧
      (∀ j, (B[k]).src = some j → ¬ e (blockStart B k + t) ∧ g (blockStart B k + t) = j + t) := by
    intro k hk t ht
    have := hK k hk t (by rw [List.getD_eq_getElem _ _ hk]; exact ht)
    rw [List.getD_eq_getElem _ _ hk] at this
    exact this
  have hst : ∀ k, 1 ≤ blockStart B k := by
    intro k
    unfold blockStart
    omega
  have hsrc : ∀ y, 1 ≤ y → y ≤ n → srcMap B y = gp e g y := by
    intro y hy1 hyn
    obtain ⟨k, hk, hy1', hy2'⟩ := locate B y hy1 (by omega)
    have hbo := blockOf_eq B k hk y hy1' hy2'
    have := hK' k hk (y - blockStart B k) (by omega)
    rw [show blockStart B k + (y - blockStart B k) = y by omega] at this
    unfold srcMap gp
    rw [hbo]
    dsimp only
    rw [List.getD_eq_getElem _ _ hk]
    cases hs : (B[k]).src with
    | none => simp [this.1 hs]
    | some j =>
      obtain ⟨hne, hgy⟩ := this.2 j hs
      simp only [hne, if_false, hgy]
  have hstay : ∀ y, 1 ≤ y → y ≤ n → 1 ≤ gp e g y ∧ gp e g y ≤ n := by
    intro y hy1 hyn
    unfold gp
    by_cases he : e y
    · rw [if_pos he]; exact ⟨hy1, hyn⟩
    · rw [if_neg he]; exact ⟨(hg y hy1 hyn he).1, (hg y hy1 hyn he).2.1⟩
  have hiter : ∀ m y, 1 ≤ y → y ≤ n →
      (srcMap B)^[m] y = (gp e g)^[m] y ∧ 1 ≤ (gp e g)^[m] y ∧ (gp e g)^[m] y ≤ n := by
    intro m
    induction m with
    | zero => intro y hy1 hyn; simp [hy1, hyn]
    | succ m ih =>
      intro y hy1 hyn
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hsrc y hy1 hyn]
      exact ih _ (hstay y hy1 hyn).1 (hstay y hy1 hyn).2
  refine ⟨B, ⟨hsum, hb, ?_, ?_⟩, hlen⟩
  · intro k hk j hj
    have hlen1 := (hb B[k] (List.getElem_mem hk)).1
    have hend : blockStart B k + (B[k]).len ≤ n + 1 := by
      rw [← blockStart_succ B k hk]
      have := blockStart_le B (k + 1)
      omega
    have hs1 := hst k
    have h0 := (hK' k hk 0 (by omega)).2 j hj
    simp only [Nat.add_zero] at h0
    have hg0 := hg (blockStart B k) hs1 (by omega) h0.1
    have hl := (hK' k hk ((B[k]).len - 1) (by omega)).2 j hj
    have hgl := hg (blockStart B k + ((B[k]).len - 1)) (by omega) (by omega) hl.1
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro t ht
    have ht' := (hK' k hk t ht).2 j hj
    have hgt := hg (blockStart B k + t) (by omega) (by omega) ht'.1
    rw [← ht'.2, hgt.2.2.2]
  · intro x hx1 hxn
    obtain ⟨m, hm⟩ := hreach x hx1 hxn
    obtain ⟨hit, hz1, hzn⟩ := hiter m x hx1 hxn
    obtain ⟨k, hk, hz1', hz2'⟩ := locate B ((gp e g)^[m] x) hz1 (by omega)
    have := hK' k hk ((gp e g)^[m] x - blockStart B k) (by omega)
    rw [show blockStart B k + ((gp e g)^[m] x - blockStart B k) = (gp e g)^[m] x by omega] at this
    have hs : (B[k]).src = none := by
      cases hs : (B[k]).src with
      | none => rfl
      | some j => exact absurd hm (this.2 j hs).1
    have hl1 := (hb B[k] (List.getElem_mem hk)).2 hs
    refine ⟨m, k, hk, hs, ?_⟩
    rw [hit]
    omega

end GagieRIndex.MacroScheme.BmsAux

namespace GagieRIndex.MacroScheme.BmsLoc
open GagieRIndex.Locate GagieRIndex.MacroScheme

/-! ## Suffix-array facts (copied from the sibling proof of `lemma_3_identity`) -/

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

/-! ## The specific explicit set and source map (Lemma 17) -/

def E (n : ℕ) (T SA : ℕ → ℕ) (x : ℕ) : Prop :=
  IsRunStart n T SA x ∨ IsRunStart n T SA (x - 1)

instance (n : ℕ) (T SA : ℕ → ℕ) : DecidablePred (E n T SA) := fun _ => by
  unfold E; infer_instance

/-- The true LF step: the position of the suffix starting one text position earlier. -/
def gf (n : ℕ) (SA : ℕ → ℕ) (x : ℕ) : ℕ := ISA n SA (SA x - 1)

variable {n σ : ℕ} {T SA : ℕ → ℕ}

lemma bwt_ne_one (hT : IsText n σ T) (hSA : IsSuffixArray n T SA) (p : ℕ) (hp1 : 1 ≤ p)
    (hpn : p ≤ n) (h : SA p ≠ 1) : bwt n T SA p ≠ 1 := by
  have := hSA.1 p hp1 hpn
  unfold bwt
  rw [if_neg h]
  exact hT.2.2.2 _ (by omega) (by omega)

lemma not_rs_bwt (p : ℕ) (hp2 : 2 ≤ p) (hpn : p ≤ n) (h : ¬ IsRunStart n T SA p) :
    bwt n T SA (p - 1) = bwt n T SA p := by
  by_contra hne
  exact h ⟨by omega, hpn, Or.inr hne⟩

lemma sa_ne (hT : IsText n σ T) (hSA : IsSuffixArray n T SA) (p : ℕ) (hp2 : 2 ≤ p) (hpn : p ≤ n)
    (h : ¬ IsRunStart n T SA p) : SA p ≠ 1 ∧ SA (p - 1) ≠ 1 := by
  have heq := not_rs_bwt p hp2 hpn h
  have hinj : SA (p - 1) ≠ SA p := by
    intro hh
    have := hSA.2.1 (Set.mem_Icc.2 ⟨(by omega : 1 ≤ p - 1), (by omega : p - 1 ≤ n)⟩)
      (Set.mem_Icc.2 ⟨(by omega : 1 ≤ p), hpn⟩) hh
    omega
  have hTn : T n = 1 := hT.2.2.1
  constructor
  · intro h1
    have hb : bwt n T SA p = 1 := by unfold bwt; rw [if_pos h1]; exact hTn
    by_cases h2 : SA (p - 1) = 1
    · exact hinj (by rw [h1, h2])
    · exact bwt_ne_one hT hSA (p - 1) (by omega) (by omega) h2 (by rw [heq]; exact hb)
  · intro h2
    have hb : bwt n T SA (p - 1) = 1 := by unfold bwt; rw [if_pos h2]; exact hTn
    by_cases h1 : SA p = 1
    · exact hinj (by rw [h1, h2])
    · exact bwt_ne_one hT hSA p (by omega) hpn h1 (by rw [← heq]; exact hb)

lemma gf_spec (hSA : IsSuffixArray n T SA) (x : ℕ) (hx1 : 1 ≤ x) (hxn : x ≤ n)
    (h : SA x ≠ 1) : 1 ≤ gf n SA x ∧ gf n SA x ≤ n ∧ SA (gf n SA x) = SA x - 1 := by
  have := hSA.1 x hx1 hxn
  exact ISA_spec n T SA hSA (SA x - 1) (by omega) (by omega)

lemma gf_succ (hT : IsText n σ T) (hSA : IsSuffixArray n T SA) (p : ℕ) (hp2 : 2 ≤ p)
    (hpn : p ≤ n) (h : ¬ IsRunStart n T SA p) : gf n SA (p - 1) + 1 = gf n SA p := by
  obtain ⟨h1, h2⟩ := sa_ne hT hSA p hp2 hpn h
  have heq := not_rs_bwt p hp2 hpn h
  unfold bwt at heq
  rw [if_neg h2, if_neg h1] at heq
  have s1 := hSA.1 (p - 1) (by omega) (by omega)
  have s2 := hSA.1 p (by omega) hpn
  unfold gf
  refine adj n σ T SA hT hSA (p - 1) (SA (p - 1) - 1) (SA p - 1) (by omega) (by omega)
    (by omega) (by omega) (by omega) ?_ heq
  rw [Nat.sub_add_cancel (by omega : 1 ≤ p)]
  omega

lemma lcp_shift (hT : IsText n σ T) (hSA : IsSuffixArray n T SA) (p : ℕ) (hp2 : 2 ≤ p)
    (hpn : p ≤ n) (h : ¬ IsRunStart n T SA p) :
    LCP n T SA (gf n SA p) = LCP n T SA p + 1 := by
  have hsucc := gf_succ hT hSA p hp2 hpn h
  obtain ⟨h1, h2⟩ := sa_ne hT hSA p hp2 hpn h
  obtain ⟨a1, an, aS⟩ := gf_spec hSA (p - 1) (by omega) (by omega) h2
  obtain ⟨b1, bn, bS⟩ := gf_spec hSA p (by omega) hpn h1
  have heq := not_rs_bwt p hp2 hpn h
  unfold bwt at heq
  rw [if_neg h2, if_neg h1] at heq
  have s1 := hSA.1 (p - 1) (by omega) (by omega)
  have s2 := hSA.1 p (by omega) hpn
  unfold LCP
  rw [if_neg (by omega : ¬ gf n SA p ≤ 1), if_neg (by omega : ¬ p ≤ 1)]
  rw [show gf n SA p - 1 = gf n SA (p - 1) by omega, aS, bS]
  rw [suffix_cons n T (SA (p - 1) - 1) (by omega), suffix_cons n T (SA p - 1) (by omega)]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ SA (p - 1)), Nat.sub_add_cancel (by omega : 1 ≤ SA p),
    heq]
  rw [lcpLen, if_pos rfl]

lemma notE (hT : IsText n σ T) (x : ℕ) (hx1 : 1 ≤ x) (h : ¬ E n T SA x) :
    3 ≤ x ∧ ¬ IsRunStart n T SA x ∧ ¬ IsRunStart n T SA (x - 1) := by
  unfold E at h
  push_neg at h
  have hrs1 : IsRunStart n T SA 1 := ⟨le_rfl, hT.1, Or.inl rfl⟩
  refine ⟨?_, h.1, h.2⟩
  by_contra hc
  rcases (show x = 1 ∨ x = 2 by omega) with hx | hx
  · subst hx; exact h.1 hrs1
  · subst hx; exact h.2 hrs1

lemma dlcp_eq (hT : IsText n σ T) (hSA : IsSuffixArray n T SA) (x : ℕ) (hx1 : 1 ≤ x)
    (hxn : x ≤ n) (h : ¬ E n T SA x) : DLCP n T SA (gf n SA x) = DLCP n T SA x := by
  obtain ⟨hx3, hr0, hr1⟩ := notE hT x hx1 h
  have hsucc := gf_succ hT hSA x (by omega) hxn hr0
  obtain ⟨h1, h2⟩ := sa_ne hT hSA x (by omega) hxn hr0
  obtain ⟨a1, an, aS⟩ := gf_spec hSA (x - 1) (by omega) (by omega) h2
  have l0 := lcp_shift hT hSA x (by omega) hxn hr0
  have l1 := lcp_shift hT hSA (x - 1) (by omega) (by omega) hr1
  unfold DLCP
  rw [if_neg (by omega : ¬ gf n SA x ≤ 1), if_neg (by omega : ¬ x ≤ 1)]
  rw [show gf n SA x - 1 = gf n SA (x - 1) by omega, l0, l1]
  push_cast
  ring

lemma reach (hT : IsText n σ T) (hSA : IsSuffixArray n T SA) :
    ∀ s x, SA x = s → 1 ≤ x → x ≤ n →
      ∃ m, E n T SA ((BmsAux.gp (E n T SA) (gf n SA))^[m] x) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro x hs hx1 hxn
    by_cases he : E n T SA x
    · exact ⟨0, by simpa using he⟩
    · obtain ⟨hx3, hr0, _⟩ := notE hT x hx1 he
      obtain ⟨h1, _⟩ := sa_ne hT hSA x (by omega) hxn hr0
      have s1 := hSA.1 x hx1 hxn
      obtain ⟨g1, gn, gS⟩ := gf_spec hSA x hx1 hxn h1
      obtain ⟨m, hm⟩ := ih (SA (gf n SA x)) (by omega) (gf n SA x) rfl g1 gn
      refine ⟨m + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      have hgp : BmsAux.gp (E n T SA) (gf n SA) x = gf n SA x := by
        unfold BmsAux.gp
        rw [if_neg he]
      rw [hgp]
      exact hm

lemma cnt_bound (hT : IsText n σ T) :
    BmsAux.cnt (E n T SA) n ≤ 4 * runs n T SA + 1 := by
  unfold BmsAux.cnt runs
  set R := (Finset.Icc 1 n).filter (IsRunStart n T SA) with hR
  have hmemR : ∀ p, IsRunStart n T SA p → p ∈ R := by
    intro p hp
    rw [hR, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hp.1, hp.2.1⟩, hp⟩
  have hsub := Finset.card_le_card_of_injOn (fun i => i + 1)
    (s := (Finset.range n).filter (fun i => ¬ (¬ E n T SA (i + 1) ∧ 2 ≤ i + 1 ∧ ¬ E n T SA i)))
    (t := R ∪ R.image (fun p => p + 1) ∪ R.image (fun p => p + 2) ∪ {1})
    (by
      intro a ha
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha
      obtain ⟨_, ha⟩ := ha
      simp only [Finset.coe_union, Finset.coe_image, Finset.coe_singleton, Set.mem_union,
        Set.mem_image, Finset.mem_coe, Set.mem_singleton_iff]
      by_cases h1 : E n T SA (a + 1)
      · unfold E at h1
        rcases h1 with h1 | h1
        · left; left; left; exact hmemR _ h1
        · left; left; right
          refine ⟨a, hmemR _ (by simpa using h1), rfl⟩
      · by_cases h2 : 2 ≤ a + 1
        · have h3 : E n T SA a := by
            by_contra h3
            exact ha ⟨h1, h2, h3⟩
          unfold E at h3
          rcases h3 with h3 | h3
          · left; left; right
            exact ⟨a, hmemR _ h3, rfl⟩
          · left; right
            have := h3.1
            refine ⟨a - 1, hmemR _ h3, by omega⟩
        · right; omega)
    (by
      intro a _ b _ hab
      simp only at hab
      omega)
  have c1 := Finset.card_union_le (R ∪ R.image (fun p => p + 1) ∪ R.image (fun p => p + 2)) {1}
  have c2 := Finset.card_union_le (R ∪ R.image (fun p => p + 1)) (R.image (fun p => p + 2))
  have c3 := Finset.card_union_le R (R.image (fun p => p + 1))
  have c4 := Finset.card_image_le (s := R) (f := fun p => p + 1)
  have c5 := Finset.card_image_le (s := R) (f := fun p => p + 2)
  rw [Finset.card_singleton] at c1
  omega

end GagieRIndex.MacroScheme.BmsLoc

open GagieRIndex.MacroScheme in
theorem solution (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA) :
    ∃ B : List Block, IsBMS n (DLCP n T SA) B ∧ B.length ≤ 4 * GagieRIndex.Locate.runs n T SA + 1 := by
  obtain ⟨B, hB, hl⟩ := BmsAux.gen n (DLCP n T SA) (BmsLoc.E n T SA) (BmsLoc.gf n SA)
    (fun x hx1 hxn he => by
      obtain ⟨hx3, hr0, _⟩ := BmsLoc.notE hT x hx1 he
      obtain ⟨h1, _⟩ := BmsLoc.sa_ne hT hSA x (by omega) hxn hr0
      have s1 := hSA.1 x hx1 hxn
      obtain ⟨g1, gn, gS⟩ := BmsLoc.gf_spec hSA x hx1 hxn h1
      refine ⟨g1, gn, ?_, BmsLoc.dlcp_eq hT hSA x hx1 hxn he⟩
      intro hh
      rw [hh] at gS
      omega)
    (fun x hx2 hxn he _ => by
      obtain ⟨_, hr0, _⟩ := BmsLoc.notE hT x (by omega) he
      exact (BmsLoc.gf_succ hT hSA x hx2 hxn hr0).symm)
    (fun x hx1 hxn => BmsLoc.reach hT hSA (SA x) x rfl hx1 hxn)
  exact ⟨B, hB, le_trans hl (BmsLoc.cnt_bound hT)⟩
