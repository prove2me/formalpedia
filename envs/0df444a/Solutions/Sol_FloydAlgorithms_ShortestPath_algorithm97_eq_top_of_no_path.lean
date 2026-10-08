-- Prove2me | solution 1 for FloydAlgorithms.ShortestPath.algorithm97_eq_top_of_no_path
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T14:59:33.862359+00:00
-- url     : https://prove2.me/submissions/b9d44b6c-a3ef-4830-9a66-11abcfe46c3f

import Mathlib
import Definitions.Def_FloydAlgorithms_ShortestPath_Network
import Definitions.Def_FloydAlgorithms_ShortestPath_Algorithm97



namespace FloydAlgorithms.ShortestPath

namespace A97

variable {n : ℕ}

/-! ### Walks as functions `ℕ → Fin n` -/

def wl (w : LengthMatrix n) (f : ℕ → Fin n) (L : ℕ) : WithTop ℝ :=
  ∑ t ∈ Finset.range L, w (f t) (f (t+1))

def SP (f : ℕ → Fin n) (L : ℕ) : Prop :=
  (∀ a b, a < L → b < L → a ≠ b → f a ≠ f b) ∧
  (∀ a b, a < L → b < L → a ≠ b → f (a+1) ≠ f (b+1))

def toP (f : ℕ → Fin n) (L : ℕ) : Fin (L+1) → Fin n := fun x => f x

lemma pathLength_toP (w : LengthMatrix n) (f : ℕ → Fin n) (L : ℕ) :
    pathLength w (toP f L) = wl w f L := by
  unfold pathLength wl toP
  exact Fin.sum_univ_eq_sum_range (fun t => w (f t) (f (t+1))) L

lemma isPath_toP (f : ℕ → Fin n) (L : ℕ) (i j : Fin n) (hL : 1 ≤ L) (h0 : f 0 = i)
    (hL' : f L = j) (hs : SP f L) : IsPath i j L (toP f L) := by
  refine ⟨hL, by simp [toP, h0], by simp [toP, hL'], ?_, ?_⟩
  · intro a b hab
    simp only [toP, Fin.val_castSucc]
    exact hs.1 a b a.2 b.2 (fun h => hab (Fin.ext h))
  · intro a b hab
    simp only [toP, Fin.val_succ]
    exact hs.2 a b a.2 b.2 (fun h => hab (Fin.ext h))

def ofP {L : ℕ} (p : Fin (L+1) → Fin n) : ℕ → Fin n := fun x => p ⟨min x L, by omega⟩

lemma wl_ofP (w : LengthMatrix n) {L : ℕ} (p : Fin (L+1) → Fin n) :
    wl w (ofP p) L = pathLength w p := by
  unfold pathLength wl
  rw [← Fin.sum_univ_eq_sum_range (fun t => w (ofP p t) (ofP p (t+1))) L]
  apply Finset.sum_congr rfl
  intro t _
  simp only [ofP]
  have h1 : (⟨min (t : ℕ) L, by omega⟩ : Fin (L+1)) = t.castSucc := by ext; simp
  have h2 : (⟨min ((t : ℕ) + 1) L, by omega⟩ : Fin (L+1)) = t.succ := by ext; simp <;> omega
  rw [h1, h2]

lemma SP_card (f : ℕ → Fin n) (L : ℕ) (hs : SP f L) : L ≤ n := by
  have := Finset.card_le_card_of_injOn (s := Finset.range L) (t := (Finset.univ : Finset (Fin n)))
    (fun x => f x) (fun a _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (by
      intro a ha b hb hab
      by_contra hne
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      exact hs.1 a b ha hb hne hab)
  simpa using this

/-! ### Shortcutting walks to simple paths -/

theorem walk_simple (w : LengthMatrix n) : ∀ (L : ℕ) (f : ℕ → Fin n), 1 ≤ L →
    ∃ (g : ℕ → Fin n) (L' : ℕ), 1 ≤ L' ∧ g 0 = f 0 ∧ g L' = f L ∧ SP g L' ∧
      (NoNegativeCycle w → wl w g L' ≤ wl w f L) ∧ (wl w f L ≠ ⊤ → wl w g L' ≠ ⊤) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro f hL
  by_cases hs : SP f L
  · exact ⟨f, L, hL, rfl, rfl, hs, fun _ => le_rfl, id⟩
  have hex : ∃ s d r, L = s + d + r ∧ 1 ≤ d ∧ 1 ≤ s + r ∧ f s = f (s + d) := by
    unfold SP at hs
    rw [not_and_or] at hs
    rcases hs with h | h
    · push_neg at h
      obtain ⟨a, b, ha, hb, hab, he⟩ := h
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨a, b - a, L - b, by omega, by omega, by omega, by rw [he]; congr 1; omega⟩
      · exact ⟨b, a - b, L - a, by omega, by omega, by omega, by rw [← he]; congr 1; omega⟩
    · push_neg at h
      obtain ⟨a, b, ha, hb, hab, he⟩ := h
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨a + 1, b - a, L - b - 1, by omega, by omega, by omega, by rw [he]; congr 1; omega⟩
      · exact ⟨b + 1, a - b, L - a - 1, by omega, by omega, by omega, by rw [← he]; congr 1; omega⟩
  obtain ⟨s, d, r, rfl, hd, hsr, hfs⟩ := hex
  -- decomposition of the walk length
  have hsplit : wl w f (s + d + r) = wl w f s + wl w (fun x => f (s + x)) d +
      wl w (fun x => f (s + d + x)) r := by
    unfold wl
    rw [Finset.sum_range_add, Finset.sum_range_add]
    simp only [add_assoc]
  obtain ⟨h, hh⟩ : ∃ h : ℕ → Fin n, h = fun x => if x < s then f x else f (x + d) := ⟨_, rfl⟩
  have hsplit2 : wl w h (s + r) = wl w f s + wl w (fun x => f (s + d + x)) r := by
    unfold wl
    rw [Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_range] at hx
      have h1 : h x = f x := by simp [hh, hx]
      have h2 : h (x + 1) = f (x + 1) := by
        by_cases hx1 : x + 1 < s
        · simp [hh, hx1]
        · have : x + 1 = s := by omega
          simp only [hh, hx1, if_false]
          rw [this, hfs]
      rw [h1, h2]
    · apply Finset.sum_congr rfl
      intro x _
      have h1 : h (s + x) = f (s + d + x) := by
        simp only [hh]; rw [if_neg (by omega)]; congr 1; omega
      have h2 : h (s + x + 1) = f (s + d + x + 1) := by
        simp only [hh]; rw [if_neg (by omega)]; congr 1; omega
      rw [h1, h2]; rfl
  obtain ⟨g, L', hL', hg0, hgL, hgs, hgle, hgtop⟩ := ih (s + r) (by omega) h (by omega)
  have hh0 : h 0 = f 0 := by
    by_cases h0 : 0 < s
    · simp [hh, h0]
    · have : s = 0 := by omega
      subst this
      simp only [hh, lt_irrefl, if_false, zero_add]
      simpa using hfs.symm
  have hhL : h (s + r) = f (s + d + r) := by
    simp only [hh]; rw [if_neg (by omega)]; congr 1; omega
  refine ⟨g, L', hL', by rw [hg0, hh0], by rw [hgL, hhL], hgs, ?_, ?_⟩
  · intro hneg
    obtain ⟨gc, Lc, hLc, hgc0, hgcL, hgcs, hgcle, -⟩ :=
      ih d (by omega) (fun x => f (s + x)) hd
    have hc0 : 0 ≤ wl w (fun x => f (s + x)) d := by
      have hp := isPath_toP gc Lc (f s) (f s) hLc (by rw [hgc0, Nat.add_zero]) (by rw [hgcL, hfs]) hgcs
      have := hneg (f s) Lc (toP gc Lc) hp
      rw [pathLength_toP] at this
      exact this.trans (hgcle hneg)
    calc wl w g L' ≤ wl w h (s + r) := hgle hneg
      _ = wl w f s + 0 + wl w (fun x => f (s + d + x)) r := by rw [hsplit2, add_zero]
      _ ≤ wl w f s + wl w (fun x => f (s + x)) d + wl w (fun x => f (s + d + x)) r := by
          gcongr
      _ = _ := hsplit.symm
  · intro htop
    apply hgtop
    rw [hsplit] at htop
    rw [hsplit2]
    have h1 := (WithTop.add_ne_top.mp htop)
    have h2 := (WithTop.add_ne_top.mp h1.1)
    exact WithTop.add_ne_top.mpr ⟨h2.1, h1.2⟩

/-! ### Soundness invariant -/

def Inv (w : LengthMatrix n) (m : LengthMatrix n) : Prop :=
  (∀ a c, m a c ≤ w a c) ∧
  ∀ a c, m a c ≠ ⊤ → ∃ (f : ℕ → Fin n) (L : ℕ), 1 ≤ L ∧ f 0 = a ∧ f L = c ∧ wl w f L ≤ m a c

lemma concat_walk (w : LengthMatrix n) (f1 f2 : ℕ → Fin n) (L1 L2 : ℕ) (he : f1 L1 = f2 0) :
    ∃ g : ℕ → Fin n, g 0 = (if 0 < L1 then f1 0 else f2 0) ∧ g (L1 + L2) = f2 L2 ∧
      wl w g (L1 + L2) = wl w f1 L1 + wl w f2 L2 := by
  refine ⟨fun x => if x < L1 then f1 x else f2 (x - L1), by simp, by simp, ?_⟩
  unfold wl
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_range] at hx
    simp only [hx, if_true]
    by_cases hx1 : x + 1 < L1
    · simp [hx1]
    · have : x + 1 = L1 := by omega
      simp only [hx1, if_false]
      rw [this, he]; simp
  · apply Finset.sum_congr rfl
    intro x _
    simp only [show ¬ (L1 + x < L1) by omega, show ¬ (L1 + x + 1 < L1) by omega, if_false]
    congr 2 <;> congr 1 <;> omega

lemma inv_update (w : LengthMatrix n) (m : LengthMatrix n) (i j k : Fin n) (hm : Inv w m)
    (hlt : m j i + m i k < m j k) :
    Inv w (Function.update m j (Function.update (m j) k (m j i + m i k))) := by
  have hst : m j i + m i k ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨hji, hik⟩ := WithTop.add_ne_top.mp hst
  constructor
  · intro a c
    by_cases ha : a = j
    · subst ha
      by_cases hc : c = k
      · subst hc; simp only [Function.update_self]; exact hlt.le.trans (hm.1 a c)
      · simp [Function.update_apply, hc, hm.1]
    · simp [Function.update_apply, ha, hm.1]
  · intro a c hac
    by_cases ha : a = j
    · subst ha
      by_cases hc : c = k
      · subst hc
        simp only [Function.update_self] at hac ⊢
        obtain ⟨f1, L1, hL1, hf10, hf1L, hf1le⟩ := hm.2 a i hji
        obtain ⟨f2, L2, hL2, hf20, hf2L, hf2le⟩ := hm.2 i c hik
        obtain ⟨g, hg0, hgL, hgw⟩ := concat_walk w f1 f2 L1 L2 (by rw [hf1L, hf20])
        refine ⟨g, L1 + L2, by omega, by rw [hg0, if_pos (by omega), hf10], by rw [hgL, hf2L], ?_⟩
        rw [hgw]; exact add_le_add hf1le hf2le
      · simp only [Function.update_self, Function.update_apply, hc, if_false] at hac ⊢
        exact hm.2 a c hac
    · simp only [Function.update_apply, ha, if_false] at hac ⊢
      exact hm.2 a c hac

noncomputable def kstep (i j : Fin n) (m : LengthMatrix n) (k : Fin n) : LengthMatrix n :=
  if m i k < ⊤ then
    (if m j i + m i k < m j k then Function.update m j (Function.update (m j) k (m j i + m i k))
     else m)
  else m

lemma rowSweep_def (i j : Fin n) (m : LengthMatrix n) :
    rowSweep i j m = if m j i < ⊤ then (List.finRange n).foldl (kstep i j) m else m := rfl

lemma foldl_inv {α β : Type*} (P : β → Prop) (f : β → α → β) (h : ∀ b a, P b → P (f b a)) :
    ∀ (l : List α) (b : β), P b → P (l.foldl f b) := by
  intro l
  induction l with
  | nil => intro b hb; simpa using hb
  | cons a l ih => intro b hb; rw [List.foldl_cons]; exact ih _ (h b a hb)

lemma inv_kstep (w : LengthMatrix n) (i j : Fin n) (m : LengthMatrix n) (k : Fin n)
    (hm : Inv w m) : Inv w (kstep i j m k) := by
  unfold kstep
  split_ifs with h1 h2
  · exact inv_update w m i j k hm h2
  · exact hm
  · exact hm

lemma inv_rowSweep (w : LengthMatrix n) (i j : Fin n) (m : LengthMatrix n)
    (hm : Inv w m) : Inv w (rowSweep i j m) := by
  rw [rowSweep_def]
  split_ifs
  · exact foldl_inv (Inv w) (kstep i j) (fun b a hb => inv_kstep w i j b a hb) _ _ hm
  · exact hm

noncomputable def pv (i : Fin n) (m : LengthMatrix n) : LengthMatrix n :=
  (List.finRange n).foldl (fun m j => rowSweep i j m) m

lemma alg_def (w : LengthMatrix n) :
    algorithm97 w = (List.finRange n).foldl (fun m i => pv i m) w := rfl

lemma inv_pv (w : LengthMatrix n) (i : Fin n) (m : LengthMatrix n)
    (hm : Inv w m) : Inv w (pv i m) :=
  foldl_inv (Inv w) (fun m j => rowSweep i j m) (fun b a hb => inv_rowSweep w i a b hb) _ _ hm

lemma inv_w (w : LengthMatrix n) : Inv w w := by
  refine ⟨fun a c => le_rfl, ?_⟩
  intro a c _
  refine ⟨fun x => if x = 0 then a else c, 1, le_rfl, by simp, by simp, ?_⟩
  simp [wl]

lemma inv_alg (w : LengthMatrix n) : Inv w (algorithm97 w) := by
  rw [alg_def]
  exact foldl_inv (Inv w) (fun m i => pv i m) (fun b a hb => inv_pv w a b hb) _ _ (inv_w w)

/-! ### Milestone: no path gives `⊤` -/

theorem no_path_core (w : LengthMatrix n) (i j : Fin n)
    (h : ¬ ∃ (L : ℕ) (p : Fin (L + 1) → Fin n),
      IsPath i j L p ∧ pathLength w p ≠ ⊤) :
    algorithm97 w i j = ⊤ := by
  by_contra hne
  obtain ⟨f, L, hL, hf0, hfL, hfle⟩ := (inv_alg w).2 i j hne
  have hft : wl w f L ≠ ⊤ := ne_top_of_le_ne_top hne hfle
  obtain ⟨g, L', hL', hg0, hgL, hgs, -, hgt⟩ := walk_simple w L f hL
  exact h ⟨L', toP g L', isPath_toP g L' i j hL' (by rw [hg0, hf0]) (by rw [hgL, hfL]) hgs,
    by rw [pathLength_toP]; exact hgt hft⟩

end A97

end FloydAlgorithms.ShortestPath

open FloydAlgorithms.ShortestPath


theorem solution {n : ℕ} (w : LengthMatrix n)
    (i j : Fin n)
    (h : ¬ ∃ (L : ℕ) (p : Fin (L + 1) → Fin n),
      IsPath i j L p ∧ pathLength w p ≠ ⊤) :
    algorithm97 w i j = ⊤ := by
  exact A97.no_path_core w i j h
