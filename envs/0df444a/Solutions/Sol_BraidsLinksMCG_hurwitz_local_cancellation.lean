-- Prove2me | solution 1 for BraidsLinksMCG.hurwitz_local_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T10:24:50.088587+00:00
-- url     : https://prove2.me/submissions/04938827-9945-4601-9938-d285aa271fc6

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false

open FreeGroup

namespace HurwitzAux

variable {α : Type*} [DecidableEq α]

lemma isReduced_append_iff {L M : List (α × Bool)} :
    FreeGroup.IsReduced (L ++ M) ↔ FreeGroup.IsReduced L ∧ FreeGroup.IsReduced M ∧
      ∀ a ∈ L.getLast?, ∀ b ∈ M.head?, a.1 = b.1 → a.2 = b.2 := by
  unfold FreeGroup.IsReduced; exact List.isChain_append

lemma isReduced_invRev {L : List (α × Bool)} (h : FreeGroup.IsReduced L) : FreeGroup.IsReduced (invRev L) := by
  have := isReduced_toWord (x := (mk L)⁻¹)
  rwa [toWord_inv, toWord_mk, h.reduce_eq] at this

lemma invRev_head? (L : List (α × Bool)) :
    (invRev L).head? = L.getLast?.map (fun x => (x.1, !x.2)) := by
  simp [invRev, List.head?_reverse, List.getLast?_map]

lemma invRev_getLast? (L : List (α × Bool)) :
    (invRev L).getLast? = L.head?.map (fun x => (x.1, !x.2)) := by
  simp [invRev, List.getLast?_reverse, List.head?_map]

/-- A block: conjugator word and generator. -/
abbrev Blk (α : Type*) := List (α × Bool) × α

def Good (b : Blk α) : Prop := FreeGroup.IsReduced b.1 ∧ ∀ a ∈ b.1.getLast?, a.1 ≠ b.2

def cw (b : Blk α) : List (α × Bool) := b.1 ++ [(b.2, true)] ++ invRev b.1

def conj (b : Blk α) : FreeGroup α := mk b.1 * of b.2 * (mk b.1)⁻¹

lemma conj_eq (b : Blk α) : conj b = mk (cw b) := by
  simp only [conj, cw, ← mul_mk, inv_mk]
  rfl

lemma cw_reduced {b : Blk α} (hg : Good b) : FreeGroup.IsReduced (cw b) := by
  unfold cw
  rw [isReduced_append_iff, isReduced_append_iff]
  refine ⟨⟨hg.1, FreeGroup.IsReduced.singleton, ?_⟩, isReduced_invRev hg.1, ?_⟩
  · intro a ha c hc h
    simp at hc; subst hc
    exact absurd h (hg.2 a ha)
  · intro a ha c hc h
    rw [invRev_head?] at hc
    simp only [List.getLast?_append, List.getLast?_singleton] at ha
    simp at ha; subst ha
    simp only [Option.mem_def, Option.map_eq_some_iff] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    exact absurd h.symm (hg.2 d hd)

lemma toWord_conj {b : Blk α} (hg : Good b) : toWord (conj b) = cw b := by
  rw [conj_eq, toWord_mk, (cw_reduced hg).reduce_eq]

lemma cw_length (b : Blk α) : (cw b).length = 2 * b.1.length + 1 := by
  simp [cw, invRev_length]; ring

def Rel (a b : Blk α) : Prop :=
  (¬ ∃ T, b.1 = a.1 ++ (a.2, false) :: T) ∧ (¬ ∃ T, a.1 = b.1 ++ (b.2, true) :: T)

lemma split_prefix (A B : List (α × Bool)) :
    ∃ P A' B', A = P ++ A' ∧ B = P ++ B' ∧ ∀ x ∈ A'.head?, ∀ y ∈ B'.head?, x ≠ y := by
  induction A generalizing B with
  | nil => exact ⟨[], [], B, rfl, rfl, by simp⟩
  | cons a A ih =>
    cases B with
    | nil => exact ⟨[], a :: A, [], rfl, rfl, by simp⟩
    | cons b B =>
      by_cases hab : a = b
      · subst hab
        obtain ⟨P, A', B', h1, h2, h3⟩ := ih B
        exact ⟨a :: P, A', B', by simp [h1], by simp [h2], h3⟩
      · exact ⟨[], a :: A, b :: B, rfl, rfl, by simpa using hab⟩

lemma infix_reduced {L M : List (α × Bool)} (h : FreeGroup.IsReduced M) (hi : L <:+: M) :
    FreeGroup.IsReduced L := h.infix hi

lemma overlap1 {X Y : List (α × Bool)} {c : α × Bool}
    (h1 : FreeGroup.IsReduced (X ++ [c])) (h2 : FreeGroup.IsReduced ([c] ++ Y)) :
    FreeGroup.IsReduced (X ++ [c] ++ Y) :=
  FreeGroup.IsReduced.append_overlap h1 h2 (by simp)

/-- The prepend step. -/
lemma step (a b : Blk α) (ha : Good a) (hb : Good b) (hr : Rel a b) (R : List (α × Bool))
    (hQ : FreeGroup.IsReduced (b.1 ++ [(b.2, true)] ++ R)) :
    ∃ R', toWord (conj a * mk (b.1 ++ [(b.2, true)] ++ R)) = a.1 ++ [(a.2, true)] ++ R' ∧
      FreeGroup.IsReduced (a.1 ++ [(a.2, true)] ++ R') ∧
      R.length + 1 ≤ R'.length ∧
      (a.1 = [] → R'.length = b.1.length + 1 + R.length) := by
  obtain ⟨P, A', B', hA, hB, hd⟩ := split_prefix a.1 b.1
  have hcw := cw_reduced ha
  have S1 : FreeGroup.IsReduced (a.1 ++ [(a.2, true)]) :=
    infix_reduced hcw ⟨[], invRev a.1, by simp [cw]⟩
  have S3 : FreeGroup.IsReduced ([(b.2, true)] ++ R) :=
    infix_reduced hQ ⟨b.1, [], by simp⟩
  have T1 : FreeGroup.IsReduced ([(a.2, true)] ++ invRev A') :=
    infix_reduced hcw ⟨P ++ A', invRev P, by simp [cw, hA, invRev_append]⟩
  have T2 : FreeGroup.IsReduced (B' ++ [(b.2, true)]) :=
    infix_reduced hQ ⟨P, R, by simp [hB]⟩
  have S2 : FreeGroup.IsReduced (([(a.2, true)] ++ invRev A') ++ (B' ++ [(b.2, true)])) := by
    rw [isReduced_append_iff]
    refine ⟨T1, T2, ?_⟩
    intro x hx y hy hxy
    rcases A' with _ | ⟨d, A''⟩ <;> rcases B' with _ | ⟨c, B''⟩
    · simp at hx hy; subst hx hy; rfl
    · simp at hx hy; subst hx hy
      simp at hxy
      by_contra hc2
      have hc2' : c.2 = false := by simpa using hc2
      apply hr.1
      refine ⟨B'', ?_⟩
      rw [hB, hA]; simp
      ext <;> simp [hxy, hc2']
    · rw [List.singleton_append, List.getLast?_cons, invRev_getLast?] at hx
      simp at hx hy
      subst hy
      rw [← hx] at hxy ⊢
      simp at hxy ⊢
      by_contra hd2
      have hd2' : d.2 = true := by simpa using hd2
      apply hr.2
      refine ⟨A'', ?_⟩
      rw [hB, hA]; simp
      ext <;> simp [hxy, hd2']
    · rw [List.singleton_append, List.getLast?_cons, invRev_getLast?] at hx
      simp at hx hy
      subst hy
      rw [← hx] at hxy ⊢
      simp at hxy ⊢
      by_contra hd2
      apply hd d (by simp) c (by simp)
      ext
      · exact hxy
      · cases h1 : d.2 <;> cases h2 : c.2 <;> simp_all
  have S2' : FreeGroup.IsReduced ([(a.2, true)] ++ (invRev A' ++ B') ++ [(b.2, true)]) := by
    have e : [(a.2, true)] ++ (invRev A' ++ B') ++ [(b.2, true)] =
        ([(a.2, true)] ++ invRev A') ++ (B' ++ [(b.2, true)]) := by
      simp only [List.append_assoc]
    rw [e]; exact S2
  have hmid : FreeGroup.IsReduced (a.1 ++ [(a.2, true)] ++ (invRev A' ++ B' ++ [(b.2, true)])) := by
    apply overlap1 S1
    rw [List.append_assoc] at S2'; exact S2'
  have hmid' : FreeGroup.IsReduced ((a.1 ++ [(a.2, true)] ++ (invRev A' ++ B')) ++ [(b.2, true)]) := by
    simpa only [List.append_assoc] using hmid
  have hred0 : FreeGroup.IsReduced ((a.1 ++ [(a.2, true)] ++ (invRev A' ++ B')) ++ [(b.2, true)] ++ R) :=
    overlap1 hmid' S3
  have e2 : a.1 ++ [(a.2, true)] ++ (invRev A' ++ B') ++ [(b.2, true)] ++ R =
      a.1 ++ [(a.2, true)] ++ (invRev A' ++ B' ++ [(b.2, true)] ++ R) := by
    simp only [List.append_assoc]
  have hred : FreeGroup.IsReduced (a.1 ++ [(a.2, true)] ++ (invRev A' ++ B' ++ [(b.2, true)] ++ R)) := by
    rw [← e2]; exact hred0
  refine ⟨invRev A' ++ B' ++ [(b.2, true)] ++ R, ?_, hred, ?_, ?_⟩
  · have hgrp : conj a * mk (b.1 ++ [(b.2, true)] ++ R) =
        mk (a.1 ++ [(a.2, true)] ++ (invRev A' ++ B' ++ [(b.2, true)] ++ R)) := by
      rw [conj_eq]
      simp only [cw, hA, hB, invRev_append, ← mul_mk, inv_mk]
      simp only [mul_assoc, ← inv_mk]
      group
    rw [hgrp, toWord_mk, hred.reduce_eq]
  · simp only [List.length_append, List.length_singleton]; omega
  · intro h0
    rw [h0] at hA
    have hP : P = [] := (List.append_eq_nil_iff.1 hA.symm).1
    have hA' : A' = [] := (List.append_eq_nil_iff.1 hA.symm).2
    subst hP hA'
    simp only [hB, List.nil_append, invRev_empty, List.length_append, List.length_singleton]

lemma main_ind : ∀ (l : List (Blk α)) (b : Blk α), (∀ c ∈ b :: l, Good c) →
    List.IsChain Rel (b :: l) →
    ∃ R, toWord (((b :: l).map conj).prod) = b.1 ++ [(b.2, true)] ++ R ∧
      FreeGroup.IsReduced (b.1 ++ [(b.2, true)] ++ R) ∧ l.length ≤ R.length ∧
      ((∃ c ∈ b :: l, c.1 ≠ []) → l.length + 1 ≤ b.1.length + R.length) := by
  intro l
  induction l with
  | nil =>
    intro b hg _
    have hb := hg b (by simp)
    refine ⟨invRev b.1, ?_, ?_, by simp, ?_⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [toWord_conj hb]; rfl
    · exact cw_reduced hb
    · rintro ⟨c, hc, hne⟩
      simp only [List.mem_singleton] at hc
      subst hc
      have := List.length_pos_of_ne_nil hne
      simp only [List.length_nil, invRev_length]; omega
  | cons c l ih =>
    intro b hg hch
    have hbc : Rel b c := (List.isChain_cons_cons.1 hch).1
    have hch' : List.IsChain Rel (c :: l) := (List.isChain_cons_cons.1 hch).2
    obtain ⟨R, hR1, hR2, hR3, hR4⟩ := ih c (fun d hd => hg d (List.mem_cons_of_mem _ hd)) hch'
    have hprod : ((b :: c :: l).map conj).prod = conj b * mk (c.1 ++ [(c.2, true)] ++ R) := by
      rw [List.map_cons, List.prod_cons, ← hR1, mk_toWord]
    obtain ⟨R', h1, h2, h3, h4⟩ := step b c (hg b (by simp)) (hg c (by simp)) hbc R hR2
    refine ⟨R', by rw [hprod]; exact h1, h2, by simp only [List.length_cons]; omega, ?_⟩
    rintro ⟨d, hd, hne⟩
    by_cases hb0 : b.1 = []
    · have hex : ∃ d ∈ c :: l, d.1 ≠ [] := by
        rcases List.mem_cons.1 hd with rfl | hd'
        · exact absurd hb0 hne
        · exact ⟨d, hd', hne⟩
      have := hR4 hex
      have := h4 hb0
      simp only [List.length_cons, hb0, List.length_nil]; omega
    · have := List.length_pos_of_ne_nil hb0
      simp only [List.length_cons]; omega

lemma chain_ofFn {β : Type*} {r : β → β → Prop} : ∀ {m : ℕ} (f : Fin m → β),
    (∀ i j : Fin m, (j : ℕ) = i + 1 → r (f i) (f j)) → List.IsChain r (List.ofFn f)
  | 0, f, _ => by simp
  | 1, f, _ => by simp
  | m + 2, f, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    apply List.isChain_cons_cons.2
    refine ⟨h 0 1 (by simp), ?_⟩
    have := chain_ofFn (m := m + 1) (fun i => f i.succ) (fun i j hij => h _ _ (by simp [hij]))
    rwa [List.ofFn_succ] at this

lemma norm_prod_le (L : List (FreeGroup α)) (h : ∀ x ∈ L, norm x ≤ 1) :
    norm L.prod ≤ L.length := by
  induction L with
  | nil => simp [FreeGroup.norm_one]
  | cons x L ih =>
    rw [List.prod_cons, List.length_cons]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have := norm_mul_le x L.prod
    omega

lemma norm_conj_le (D : FreeGroup α) (m : α) : norm (D * of m * D⁻¹) ≤ 2 * norm D + 1 := by
  have h1 := norm_mul_le (D * of m) D⁻¹
  have h2 := norm_mul_le D (of m)
  rw [norm_inv_eq, norm_of] at *
  omega

lemma mk_single_conj (m : α) (b : Bool) : mk [(m, b)] * of m * (mk [(m, b)])⁻¹ = of m := by
  cases b
  · have : mk [(m, false)] = (of m)⁻¹ := by rw [of, inv_mk]; rfl
    rw [this]; group
  · have : mk [(m, true)] = of m := rfl
    rw [this]; group

end HurwitzAux

namespace BraidsLinksMCG

open HurwitzAux

theorem _root_.solution (n : ℕ)
    (w : Fin n → FreeGroup (Fin n))
    (mu : Equiv.Perm (Fin n)) (A : Fin n → FreeGroup (Fin n))
    (hw : ∀ i : Fin n, w i = A i * FreeGroup.of (mu i) * (A i)⁻¹)
    (hprod : (List.ofFn w).prod = freeWordProd n)
    (hnotperm : ¬ ∃ nu : Equiv.Perm (Fin n), ∀ i : Fin n, w i = FreeGroup.of (nu i)) :
    ∃ a b : Fin n, (b : ℕ) = (a : ℕ) + 1 ∧
      (FreeGroup.norm (w a * w b * (w a)⁻¹) < FreeGroup.norm (w b) ∨
        FreeGroup.norm ((w b)⁻¹ * w a * w b) < FreeGroup.norm (w a)) := by
  classical
  by_contra H
  push Not at H
  have hex : ∀ i, ∃ k, ∃ C : FreeGroup (Fin n), FreeGroup.norm C = k ∧
      w i = C * FreeGroup.of (mu i) * C⁻¹ := fun i => ⟨_, A i, rfl, hw i⟩
  choose C hCn hC using fun i => Nat.find_spec (hex i)
  -- minimality: the reduced conjugator does not end in the generator
  have hgood : ∀ i, Good ((C i).toWord, mu i) := by
    intro i
    refine ⟨FreeGroup.isReduced_toWord, ?_⟩
    intro a ha heq
    obtain ⟨L, hL⟩ := List.getLast?_eq_some_iff.1 ha
    have hCi : C i = mk L * mk [a] := by
      rw [FreeGroup.mul_mk, ← hL, FreeGroup.mk_toWord]
    have hwi : w i = mk L * FreeGroup.of (mu i) * (mk L)⁻¹ := by
      rw [hC i, hCi]
      have := mk_single_conj (mu i) a.2
      have ha' : a = (mu i, a.2) := by ext <;> simp [heq]
      rw [ha']
      calc mk L * mk [(mu i, a.2)] * FreeGroup.of (mu i) * (mk L * mk [(mu i, a.2)])⁻¹
          = mk L * (mk [(mu i, a.2)] * FreeGroup.of (mu i) * (mk [(mu i, a.2)])⁻¹) * (mk L)⁻¹ := by
            group
        _ = mk L * FreeGroup.of (mu i) * (mk L)⁻¹ := by rw [this]
    have hmin := Nat.find_min' (hex i) ⟨mk L, rfl, hwi⟩
    have h1 : FreeGroup.norm (mk L) ≤ L.length := FreeGroup.norm_mk_le
    have h2 : FreeGroup.norm (C i) = L.length + 1 := by
      unfold FreeGroup.norm; rw [show (C i).toWord = L ++ [a] from hL]; simp
    rw [hCn i] at h2
    omega
  set B : Fin n → Blk (Fin n) := fun i => ((C i).toWord, mu i) with hBdef
  have hconjB : ∀ i, conj (B i) = w i := by
    intro i
    simp only [B, conj, FreeGroup.mk_toWord]
    exact (hC i).symm
  have hnormw : ∀ i, FreeGroup.norm (w i) = 2 * (C i).toWord.length + 1 := by
    intro i
    rw [← hconjB i]
    unfold FreeGroup.norm
    rw [toWord_conj (hgood i), cw_length]
  have hrel : ∀ a b : Fin n, (b : ℕ) = a + 1 → Rel (B a) (B b) := by
    intro a b hab
    obtain ⟨H1, H2⟩ := H a b hab
    constructor
    · rintro ⟨T, hT⟩
      have hCb : C b = C a * (FreeGroup.of (mu a))⁻¹ * mk T := by
        have : C b = mk ((C a).toWord ++ (mu a, false) :: T) := by
          rw [← hT]; simp [B, FreeGroup.mk_toWord]
        have hs : mk [(mu a, false)] = (FreeGroup.of (mu a))⁻¹ := by
          show mk [(mu a, false)] = (mk [(mu a, true)])⁻¹
          rw [FreeGroup.inv_mk]; simp [FreeGroup.invRev]
        rw [this, show (C a).toWord ++ (mu a, false) :: T = (C a).toWord ++ [(mu a, false)] ++ T by simp,
          ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, FreeGroup.mk_toWord, hs]
      have hD : w a * w b * (w a)⁻¹ = (C a * mk T) * FreeGroup.of (mu b) * (C a * mk T)⁻¹ := by
        rw [hC a, hC b, hCb]; group
      have hlen : (C b).toWord.length = (C a).toWord.length + 1 + T.length := by
        have := congrArg List.length hT
        simp [B] at this; omega
      have e1 := norm_conj_le (C a * mk T) (mu b)
      have e2 := FreeGroup.norm_mul_le (C a) (mk T)
      have e3 : FreeGroup.norm (mk T) ≤ T.length := FreeGroup.norm_mk_le
      have e4 : FreeGroup.norm (C a) = (C a).toWord.length := rfl
      rw [← hD] at e1
      rw [hnormw b] at H1
      omega
    · rintro ⟨T, hT⟩
      have hCa : C a = C b * FreeGroup.of (mu b) * mk T := by
        have : C a = mk ((C b).toWord ++ (mu b, true) :: T) := by
          rw [← hT]; simp [B, FreeGroup.mk_toWord]
        have hs : mk [(mu b, true)] = FreeGroup.of (mu b) := rfl
        rw [this, show (C b).toWord ++ (mu b, true) :: T = (C b).toWord ++ [(mu b, true)] ++ T by simp,
          ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, FreeGroup.mk_toWord, hs]
      have hD : (w b)⁻¹ * w a * w b = (C b * mk T) * FreeGroup.of (mu a) * (C b * mk T)⁻¹ := by
        rw [hC a, hC b, hCa]; group
      have hlen : (C a).toWord.length = (C b).toWord.length + 1 + T.length := by
        have := congrArg List.length hT
        simp [B] at this; omega
      have e1 := norm_conj_le (C b * mk T) (mu a)
      have e2 := FreeGroup.norm_mul_le (C b) (mk T)
      have e3 : FreeGroup.norm (mk T) ≤ T.length := FreeGroup.norm_mk_le
      have e4 : FreeGroup.norm (C b) = (C b).toWord.length := rfl
      rw [← hD] at e1
      rw [hnormw a] at H2
      omega
  -- n = 0 is impossible
  cases n with
  | zero => exact hnotperm ⟨1, fun i => i.elim0⟩
  | succ m =>
    have hchain : List.IsChain Rel (List.ofFn B) := chain_ofFn B hrel
    rw [List.ofFn_succ] at hchain
    have hg' : ∀ c ∈ B 0 :: List.ofFn (fun i => B i.succ), Good c := by
      intro c hc
      rw [← List.ofFn_succ, List.mem_ofFn] at hc
      obtain ⟨i, rfl⟩ := hc
      exact hgood i
    obtain ⟨R, hR1, _, _, hR4⟩ := main_ind _ _ hg' hchain
    have hprod' : ((B 0 :: List.ofFn (fun i => B i.succ)).map conj).prod = freeWordProd (m + 1) := by
      rw [← List.ofFn_succ, List.map_ofFn, ← hprod]
      congr 1
      congr 1
      funext i
      exact hconjB i
    have hne : ∃ c ∈ B 0 :: List.ofFn (fun i => B i.succ), c.1 ≠ [] := by
      by_contra hall
      push Not at hall
      apply hnotperm
      refine ⟨mu, fun i => ?_⟩
      have hi : (B i).1 = [] := hall (B i) (by rw [← List.ofFn_succ, List.mem_ofFn]; exact ⟨i, rfl⟩)
      rw [← hconjB i]
      simp only [conj, hi, B] at hi ⊢
      rw [hi]
      change (1 : FreeGroup (Fin (m + 1))) * FreeGroup.of (mu i) * 1 = FreeGroup.of (mu i)
      simp
    have hlen := hR4 hne
    have hup : FreeGroup.norm (freeWordProd (m + 1)) ≤ m + 1 := by
      have := norm_prod_le (List.ofFn fun j : Fin (m + 1) => FreeGroup.of j) (by
        intro x hx
        rw [List.mem_ofFn] at hx
        obtain ⟨j, rfl⟩ := hx
        simp)
      simpa [freeWordProd] using this
    have hlow : FreeGroup.norm (freeWordProd (m + 1)) = (B 0).1.length + 1 + R.length := by
      unfold FreeGroup.norm
      rw [← hprod', hR1]
      simp only [List.length_append, List.length_singleton]
    simp only [List.length_ofFn] at hlen
    omega

end BraidsLinksMCG

#print axioms solution
