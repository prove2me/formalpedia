-- Prove2me | solution 1 for FloydAlgorithms.ShortestPath.algorithm97_eq_shortestLength
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T15:01:08.090563+00:00
-- url     : https://prove2.me/submissions/3bdcad30-d739-4352-89e8-fe6634eaa9aa

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


/-! ### Exact pivot formula under nonnegative diagonal -/

def G (m0 : LengthMatrix n) (i j : Fin n) (S : List (Fin n)) : LengthMatrix n :=
  Function.update m0 j (fun k => if k ∈ S then min (m0 j k) (m0 j i + m0 i k) else m0 j k)

lemma min_self_add {x y : WithTop ℝ} (hy : 0 ≤ y) : min x (x + y) = x :=
  min_eq_left (le_add_of_nonneg_right hy)

lemma min_add_self {x y : WithTop ℝ} (hy : 0 ≤ y) : min x (y + x) = x :=
  min_eq_left (le_add_of_nonneg_left hy)

lemma kloop (m0 : LengthMatrix n) (i j : Fin n) (hii : 0 ≤ m0 i i) :
    ∀ (l S : List (Fin n)), l.Nodup → (∀ x ∈ l, x ∉ S) →
      l.foldl (kstep i j) (G m0 i j S) = G m0 i j (l ++ S) := by
  intro l
  induction l with
  | nil => intro S _ _; simp
  | cons k l ih =>
    intro S hnd hdis
    rw [List.foldl_cons]
    have hk : k ∉ S := hdis k (by simp)
    have e1 : G m0 i j S i k = m0 i k := by
      by_cases h : i = j
      · subst h; simp [G, hk]
      · simp [G, Function.update_apply, h]
    have e2 : G m0 i j S j k = m0 j k := by simp [G, hk]
    have e3 : G m0 i j S j i = m0 j i := by
      simp only [G, Function.update_self]
      split_ifs
      · exact min_self_add hii
      · rfl
    have hstep : kstep i j (G m0 i j S) k = G m0 i j (k :: S) := by
      unfold kstep
      rw [e1, e2, e3]
      funext a c
      by_cases ha : a = j
      · subst ha
        by_cases hc : c = k
        · subst hc
          split_ifs with h1 h2
          · simp [G, min_eq_right h2.le]
          · simp [G, hk, min_eq_left (not_lt.mp h2)]
          · have : m0 i c = ⊤ := not_lt_top_iff.mp h1
            simp [G, hk, this]
        · split_ifs <;> simp [G, hc, Function.update_apply]
      · split_ifs <;> simp [G, ha, Function.update_apply]
    rw [hstep, ih (k :: S) (List.nodup_cons.mp hnd).2 ?_]
    · have hm : ∀ x, x ∈ l ++ k :: S ↔ x ∈ k :: l ++ S := by
        intro x; simp only [List.mem_append, List.mem_cons]; tauto
      unfold G; simp only [hm]
    · intro x hx hxS
      rcases List.mem_cons.mp hxS with h | h
      · subst h; exact (List.nodup_cons.mp hnd).1 hx
      · exact hdis x (by simp [hx]) h

lemma rowSweep_eq (i j : Fin n) (m : LengthMatrix n) (hii : 0 ≤ m i i) :
    rowSweep i j m = Function.update m j (fun k => min (m j k) (m j i + m i k)) := by
  rw [rowSweep_def]
  have hG : G m i j [] = m := by
    funext a c; by_cases ha : a = j
    · subst ha; simp [G]
    · simp [G, ha]
  split_ifs with h
  · conv_lhs => rw [← hG]
    rw [kloop m i j hii _ [] (List.nodup_finRange n) (by simp)]
    simp [G]
  · have : m j i = ⊤ := not_lt_top_iff.mp h
    funext a c; by_cases ha : a = j
    · subst ha; simp [this]
    · simp [ha]

def pmin (m : LengthMatrix n) (i : Fin n) : LengthMatrix n :=
  fun a c => min (m a c) (m a i + m i c)

def G2 (m0 : LengthMatrix n) (i : Fin n) (S : List (Fin n)) : LengthMatrix n :=
  fun a c => if a ∈ S then min (m0 a c) (m0 a i + m0 i c) else m0 a c

lemma jloop (m0 : LengthMatrix n) (i : Fin n) (hii : 0 ≤ m0 i i) :
    ∀ (l S : List (Fin n)), l.Nodup → (∀ x ∈ l, x ∉ S) →
      l.foldl (fun m j => rowSweep i j m) (G2 m0 i S) = G2 m0 i (l ++ S) := by
  intro l
  induction l with
  | nil => intro S _ _; simp
  | cons j l ih =>
    intro S hnd hdis
    rw [List.foldl_cons]
    have hj : j ∉ S := hdis j (by simp)
    have hik : ∀ c, G2 m0 i S i c = m0 i c := by
      intro c; unfold G2; split_ifs
      · exact min_add_self hii
      · rfl
    have hii' : 0 ≤ G2 m0 i S i i := by rw [hik]; exact hii
    have hstep : rowSweep i j (G2 m0 i S) = G2 m0 i (j :: S) := by
      rw [rowSweep_eq i j _ hii']
      funext a c
      by_cases ha : a = j
      · subst ha
        simp only [Function.update_self, hik]
        simp [G2, hj]
      · simp [G2, ha, Function.update_apply]
    rw [hstep, ih (j :: S) (List.nodup_cons.mp hnd).2 ?_]
    · have hm : ∀ x, x ∈ l ++ j :: S ↔ x ∈ j :: l ++ S := by
        intro x; simp only [List.mem_append, List.mem_cons]; tauto
      unfold G2; simp only [hm]
    · intro x hx hxS
      rcases List.mem_cons.mp hxS with h | h
      · subst h; exact (List.nodup_cons.mp hnd).1 hx
      · exact hdis x (by simp [hx]) h

lemma pv_eq (i : Fin n) (m : LengthMatrix n) (hii : 0 ≤ m i i) : pv i m = pmin m i := by
  unfold pv
  have h0 : G2 m i [] = m := by funext a c; simp [G2]
  conv_lhs => rw [← h0]
  rw [jloop m i hii _ [] (List.nodup_finRange n) (by simp)]
  funext a c; simp [G2, pmin]

/-! ### Closure -/

def Closed (m : LengthMatrix n) (u : Fin n) : Prop := ∀ a c, m a c ≤ m a u + m u c

lemma pmin_closed_new (m : LengthMatrix n) (v : Fin n) (hv : 0 ≤ m v v) :
    Closed (pmin m v) v := by
  intro a c
  have e1 : pmin m v a v = m a v := min_self_add hv
  have e2 : pmin m v v c = m v c := min_add_self hv
  rw [e1, e2]; exact min_le_right _ _

lemma pmin_closed_old (m : LengthMatrix n) (u v : Fin n) (hv : 0 ≤ m v v) (hu : Closed m u) :
    Closed (pmin m v) u := by
  intro a c
  have hvu : 0 ≤ m v u + m u v := hv.trans (hu v v)
  unfold pmin
  rcases min_choice (m a u) (m a v + m v u) with h1 | h1 <;>
    rcases min_choice (m u c) (m u v + m v c) with h2 | h2 <;> rw [h1, h2]
  · exact (min_le_left _ _).trans (hu a c)
  · refine (min_le_right _ _).trans ?_
    calc m a v + m v c ≤ (m a u + m u v) + m v c := add_le_add (hu a v) le_rfl
      _ = _ := add_assoc _ _ _
  · refine (min_le_right _ _).trans ?_
    calc m a v + m v c ≤ m a v + (m v u + m u c) := add_le_add le_rfl (hu v c)
      _ = _ := (add_assoc _ _ _).symm
  · refine (min_le_right _ _).trans ?_
    calc m a v + m v c = m a v + 0 + m v c := by rw [add_zero]
      _ ≤ m a v + (m v u + m u v) + m v c := by gcongr
      _ = _ := by ac_rfl

lemma diag_nonneg (w : LengthMatrix n) (hneg : NoNegativeCycle w) (m : LengthMatrix n)
    (hm : Inv w m) (v : Fin n) : 0 ≤ m v v := by
  by_cases ht : m v v = ⊤
  · rw [ht]; exact le_top
  obtain ⟨f, L, hL, hf0, hfL, hfle⟩ := hm.2 v v ht
  obtain ⟨g, L', hL', hg0, hgL, hgs, hgle, -⟩ := walk_simple w L f hL
  have hp := isPath_toP g L' v v hL' (by rw [hg0, hf0]) (by rw [hgL, hfL]) hgs
  have := hneg v L' (toP g L') hp
  rw [pathLength_toP] at this
  exact this.trans ((hgle hneg).trans hfle)

lemma main_inv (w : LengthMatrix n) (hneg : NoNegativeCycle w) :
    ∀ (l : List (Fin n)) (m : LengthMatrix n), Inv w m → ∀ u, (Closed m u ∨ u ∈ l) →
      Closed (l.foldl (fun m i => pv i m) m) u := by
  intro l
  induction l with
  | nil => intro m _ u h; simpa using h
  | cons v l ih =>
    intro m hm u h
    rw [List.foldl_cons]
    have hv := diag_nonneg w hneg m hm v
    apply ih _ (inv_pv w v m hm)
    rw [pv_eq v m hv]
    by_cases huv : u = v
    · subst huv; exact Or.inl (pmin_closed_new m u hv)
    · rcases h with h | h
      · exact Or.inl (pmin_closed_old m u v hv h)
      · rcases List.mem_cons.mp h with h | h
        · exact absurd h huv
        · exact Or.inr h

lemma complete (w D : LengthMatrix n) (hle : ∀ a c, D a c ≤ w a c) (hcl : ∀ u, Closed D u) :
    ∀ (L : ℕ) (f : ℕ → Fin n), 1 ≤ L → D (f 0) (f L) ≤ wl w f L := by
  intro L
  induction L with
  | zero => intro f h; omega
  | succ L ih =>
    intro f _
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0; simp [wl, hle]
    · calc D (f 0) (f (L+1)) ≤ D (f 0) (f L) + D (f L) (f (L+1)) := hcl _ _ _
        _ ≤ wl w f L + w (f L) (f (L+1)) := add_le_add (ih f h0) (hle _ _)
        _ = wl w f (L+1) := by simp [wl, Finset.sum_range_succ]

theorem goal_core (w : LengthMatrix n) (hcycle : NoNegativeCycle w) (i j : Fin n) :
    algorithm97 w i j = shortestLength w i j := by
  classical
  have hinv := inv_alg w
  have hcl : ∀ u, Closed (algorithm97 w) u := by
    intro u
    rw [alg_def]
    exact main_inv w hcycle _ w (inv_w w) u (Or.inr (List.mem_finRange u))
  have hcl' := hcl
  apply le_antisymm
  · unfold shortestLength
    apply Finset.le_inf
    intro L _
    apply Finset.le_inf
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hL, hp0, hpL, -, -⟩ := hp.2
    have := complete w (algorithm97 w) hinv.1 hcl' L (ofP p) hL
    rw [wl_ofP] at this
    have e0 : ofP p 0 = i := by rw [← hp0]; simp [ofP]
    have eL : ofP p L = j := by rw [← hpL]; simp [ofP, Fin.last]
    rwa [e0, eL] at this
  · by_cases ht : algorithm97 w i j = ⊤
    · rw [ht]; exact le_top
    obtain ⟨f, L, hL, hf0, hfL, hfle⟩ := hinv.2 i j ht
    obtain ⟨g, L', hL', hg0, hgL, hgs, hgle, -⟩ := walk_simple w L f hL
    have hp := isPath_toP g L' i j hL' (by rw [hg0, hf0]) (by rw [hgL, hfL]) hgs
    have hLn := SP_card g L' hgs
    refine le_trans ?_ ((hgle hcycle).trans hfle)
    rw [← pathLength_toP]
    unfold shortestLength
    refine le_trans (Finset.inf_le (Finset.mem_range.mpr (by omega : L' < n + 1))) ?_
    exact Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)

end A97

end FloydAlgorithms.ShortestPath

open FloydAlgorithms.ShortestPath


theorem solution {n : ℕ} (w : LengthMatrix n)
    (hcycle : NoNegativeCycle w) (i j : Fin n) :
    algorithm97 w i j = shortestLength w i j := by
  exact A97.goal_core w hcycle i j
