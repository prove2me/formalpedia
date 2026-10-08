-- Prove2me | solution 1 for BellmanDP.Fibonacci.discrete_search_corrected
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:29:38.850019+00:00
-- url     : https://prove2.me/submissions/bf32f040-34ed-4747-9a21-0b8e8cfd7818

import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel



namespace BellmanDP.Fibonacci

open SearchTree

lemma bf_ss (n : ℕ) : bookFib (n+2) = bookFib (n+1) + bookFib n := rfl

lemma bf_pos (n : ℕ) : 1 ≤ bookFib n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [bookFib]
    | 1 => simp [bookFib]
    | n+2 => rw [bf_ss]; have := ih (n+1) (by omega); omega

lemma bf_le_succ (n : ℕ) : bookFib n ≤ bookFib (n+1) := by
  cases n with
  | zero => simp [bookFib]
  | succ n => rw [bf_ss]; omega

lemma bf_lt_succ (n : ℕ) (hn : 1 ≤ n) : bookFib n < bookFib (n+1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n-1, by omega⟩
  rw [bf_ss]; have := bf_pos k; omega

lemma bfR_ss (n : ℕ) : (bookFib (n+2) : ℝ) = bookFib (n+1) + bookFib n := by
  rw [bf_ss]; push_cast; ring

lemma bfR_pos (n : ℕ) : (1 : ℝ) ≤ bookFib n := by exact_mod_cast bf_pos n

lemma bfR_le_succ (n : ℕ) : (bookFib n : ℝ) ≤ bookFib (n+1) := by exact_mod_cast bf_le_succ n

lemma bfR_lt_succ (n : ℕ) (hn : 1 ≤ n) : (bookFib n : ℝ) < bookFib (n+1) := by
  exact_mod_cast bf_lt_succ n hn

lemma bfR0 : (bookFib 0 : ℝ) = 1 := by simp [bookFib]
lemma bfR1 : (bookFib 1 : ℝ) = 1 := by simp [bookFib]
lemma bfR2 : (bookFib 2 : ℝ) = 2 := by norm_num [bookFib]


def GoodD (T : SearchTree ℕ ℕ) (N k : ℕ) (g : ℕ → ℝ) : Prop :=
  ∀ m, IsStrictUnimodalOnPoints g N m → T.cost g ≤ k ∧ T.result g = m

lemma goodD_query {x : ℕ} {next : ℝ → SearchTree ℕ ℕ} {N k : ℕ} {g : ℕ → ℝ}
    (hg : GoodD (query x next) N (k+1) g) : GoodD (next (g x)) N k g := by
  intro m hm
  obtain ⟨h1, h2⟩ := hg m hm
  simp only [SearchTree.cost, SearchTree.result] at h1 h2
  exact ⟨by omega, h2⟩

lemma goodD_query_pos {x : ℕ} {next : ℝ → SearchTree ℕ ℕ} {N k : ℕ} {g : ℕ → ℝ} {m : ℕ}
    (hm : IsStrictUnimodalOnPoints g N m) (hg : GoodD (query x next) N k g) : 1 ≤ k := by
  have := (hg m hm).1
  simp only [SearchTree.cost] at this
  omega

lemma zr_le {a b : ℤ} (h : a ≤ b) : (a : ℝ) ≤ b := by exact_mod_cast h
lemma zr_lt {a b : ℤ} (h : a < b) : (a : ℝ) < b := by exact_mod_cast h
lemma nz_lt {a : ℤ} {t : ℕ} (h : a < (t : ℤ)) : (a : ℝ) < (t : ℝ) := by
  have := zr_lt h; push_cast at this; exact this
lemma zn_lt {a : ℤ} {t : ℕ} (h : (t : ℤ) < a) : (t : ℝ) < (a : ℝ) := by
  have := zr_lt h; push_cast at this; exact this
lemma nz_le {a : ℤ} {t : ℕ} (h : a ≤ (t : ℤ)) : (a : ℝ) ≤ (t : ℝ) := by
  have := zr_le h; push_cast at this; exact this
lemma zn_le {a : ℤ} {t : ℕ} (h : (t : ℤ) ≤ a) : (t : ℝ) ≤ (a : ℝ) := by
  have := zr_le h; push_cast at this; exact this

lemma dexists (N : ℕ) (a b : ℤ) (c : ℕ) (V W : ℝ) (h : ℕ → ℝ) (m : ℕ) (hbN : b ≤ N)
    (hm : a < m ∧ (m : ℤ) < b) (hc : a < c ∧ (c : ℤ) < b)
    (hmono : ∀ t1 t2 : ℕ, (t2 : ℤ) ≤ a → t1 < t2 → h t1 < h t2)
    (hanti : ∀ t1 t2 : ℕ, b ≤ (t1 : ℤ) → t1 < t2 → t2 < N → h t2 < h t1)
    (hWl : ∀ t : ℕ, (t : ℤ) ≤ a → h t ≤ W) (hWr : ∀ t : ℕ, b ≤ (t : ℤ) → t < N → h t ≤ W)
    (hWV : W < V) :
    ∃ g : ℕ → ℝ, (∀ t : ℕ, ¬ (a < t ∧ (t : ℤ) < b) → g t = h t) ∧ g c = V ∧
      IsStrictUnimodalOnPoints g N m := by
  have hab : (0 : ℝ) < (b : ℝ) - a := by have := zr_lt (hm.1.trans hm.2); linarith
  set s := (V - W) / (2 * ((b : ℝ) - a)) with hs_def
  have hs : 0 < s := div_pos (by linarith) (by linarith)
  have hsb : s * ((b : ℝ) - a) = (V - W) / 2 := by rw [hs_def]; field_simp
  have hin : ∀ t : ℕ, a < t → (t : ℤ) < b → |(t : ℝ) - m| ≤ (b : ℝ) - a := by
    intro t h1 h2
    have e1 := nz_lt h1; have e2 := zn_lt h2; have e3 := nz_lt hm.1; have e4 := zn_lt hm.2
    rw [abs_le]; constructor <;> linarith
  refine ⟨fun t => if a < t ∧ (t : ℤ) < b then V + s * (|(c : ℝ) - m| - |(t : ℝ) - m|) else h t,
    ?_, ?_, ?_⟩
  · intro t ht; simp only [if_neg ht]
  · simp only [if_pos hc, sub_self, mul_zero, add_zero]
  · refine ⟨by have := hm.2; omega, ?_, ?_⟩
    · intro t1 ht1 t2 ht2 hlt
      simp only [Set.mem_Iic] at ht1 ht2
      simp only
      by_cases h2 : (t2 : ℤ) ≤ a
      · rw [if_neg (show ¬ (a < t1 ∧ (t1 : ℤ) < b) by intro hh; omega),
          if_neg (show ¬ (a < t2 ∧ (t2 : ℤ) < b) by intro hh; omega)]
        exact hmono t1 t2 h2 hlt
      · push_neg at h2
        have h2' : a < t2 ∧ (t2 : ℤ) < b := ⟨h2, by have := hm.2; omega⟩
        rw [if_pos h2']
        by_cases h1 : a < (t1 : ℤ)
        · rw [if_pos (show a < t1 ∧ (t1 : ℤ) < b from ⟨h1, by have := hm.2; omega⟩)]
          have r1 : (t1 : ℝ) < t2 := by exact_mod_cast hlt
          have r2 : (t2 : ℝ) ≤ m := by exact_mod_cast ht2
          have e1 : |(t1 : ℝ) - m| = m - t1 := by rw [abs_of_nonpos (by linarith)]; ring
          have e2 : |(t2 : ℝ) - m| = m - t2 := by rw [abs_of_nonpos (by linarith)]; ring
          rw [e1, e2]
          have : s * (m - t2) < s * (m - t1) := mul_lt_mul_of_pos_left (by linarith) hs
          nlinarith
        · rw [if_neg (show ¬ (a < t1 ∧ (t1 : ℤ) < b) from fun hh => h1 hh.1)]
          push_neg at h1
          have hle := hWl t1 h1
          have habs := hin t2 h2'.1 h2'.2
          have h0 : 0 ≤ s * |(c : ℝ) - m| := mul_nonneg hs.le (abs_nonneg _)
          have hq : s * |(t2 : ℝ) - m| ≤ s * ((b : ℝ) - a) :=
            mul_le_mul_of_nonneg_left habs hs.le
          nlinarith
    · intro t1 ht1 t2 ht2 hlt
      simp only [Set.mem_Ico] at ht1 ht2
      simp only
      by_cases h1 : b ≤ (t1 : ℤ)
      · rw [if_neg (show ¬ (a < t1 ∧ (t1 : ℤ) < b) by intro hh; omega),
          if_neg (show ¬ (a < t2 ∧ (t2 : ℤ) < b) by intro hh; omega)]
        exact hanti t1 t2 h1 hlt ht2.2
      · push_neg at h1
        have h1' : a < t1 ∧ (t1 : ℤ) < b := ⟨by have := hm.1; omega, h1⟩
        rw [if_pos h1']
        by_cases h2 : (t2 : ℤ) < b
        · rw [if_pos (show a < t2 ∧ (t2 : ℤ) < b from ⟨by have := hm.1; omega, h2⟩)]
          have r1 : (t1 : ℝ) < t2 := by exact_mod_cast hlt
          have r2 : (m : ℝ) ≤ t1 := by exact_mod_cast ht1.1
          have e1 : |(t1 : ℝ) - m| = t1 - m := abs_of_nonneg (by linarith)
          have e2 : |(t2 : ℝ) - m| = t2 - m := abs_of_nonneg (by linarith)
          rw [e1, e2]
          have : s * (t1 - m) < s * (t2 - m) := mul_lt_mul_of_pos_left (by linarith) hs
          nlinarith
        · rw [if_neg (show ¬ (a < t2 ∧ (t2 : ℤ) < b) from fun hh => h2 hh.2)]
          push_neg at h2
          have hle := hWr t2 h2 ht2.2
          have habs := hin t1 h1'.1 h1'.2
          have h0 : 0 ≤ s * |(c : ℝ) - m| := mul_nonneg hs.le (abs_nonneg _)
          have hq : s * |(t1 : ℝ) - m| ≤ s * ((b : ℝ) - a) :=
            mul_le_mul_of_nonneg_left habs hs.le
          nlinarith

lemma dstop_len (N k : ℕ) (a b : ℤ) (c : ℕ) (V W : ℝ) (h : ℕ → ℝ) (r : ℕ) (ha : -1 ≤ a)
    (hac : a < c) (hcb : (c : ℤ) < b) (hbN : b ≤ N)
    (hmono : ∀ t1 t2 : ℕ, (t2 : ℤ) ≤ a → t1 < t2 → h t1 < h t2)
    (hanti : ∀ t1 t2 : ℕ, b ≤ (t1 : ℤ) → t1 < t2 → t2 < N → h t2 < h t1)
    (hWl : ∀ t : ℕ, (t : ℤ) ≤ a → h t ≤ W) (hWr : ∀ t : ℕ, b ≤ (t : ℤ) → t < N → h t ≤ W)
    (hWV : W < V)
    (hG : ∀ g : ℕ → ℝ, (∀ t : ℕ, ¬ (a < t ∧ (t : ℤ) < b) → g t = h t) → g c = V →
      GoodD (stop r) N k g) : b - a ≤ 2 := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ m : ℕ, a < m → (m : ℤ) < b → r = m := by
    intro m h1 h2
    obtain ⟨g, hg1, hg2, hg3⟩ :=
      dexists N a b c V W h m hbN ⟨h1, h2⟩ ⟨hac, hcb⟩ hmono hanti hWl hWr hWV
    have := (hG g hg1 hg2 m hg3).2
    simpa [SearchTree.result] using this
  have e1 := key (a + 1).toNat (by omega) (by omega)
  have e2 := key (a + 2).toNat (by omega) (by omega)
  omega

noncomputable def dextL (h : ℕ → ℝ) (a : ℤ) (e : ℕ) (W V : ℝ) : ℕ → ℝ :=
  fun t => if a < t ∧ t ≤ e then W + (V - W) * ((t : ℝ) - a) / ((e : ℝ) - a) else h t

noncomputable def dextR (h : ℕ → ℝ) (e : ℕ) (b : ℤ) (W V : ℝ) : ℕ → ℝ :=
  fun t => if e ≤ t ∧ (t : ℤ) < b then W + (V - W) * ((b : ℝ) - t) / ((b : ℝ) - e) else h t

lemma dextL_off (h : ℕ → ℝ) (a : ℤ) (e : ℕ) (W V : ℝ) (t : ℕ) (ht : ¬ (a < t ∧ t ≤ e)) :
    dextL h a e W V t = h t := by
  unfold dextL; rw [if_neg ht]

lemma dextR_off (h : ℕ → ℝ) (e : ℕ) (b : ℤ) (W V : ℝ) (t : ℕ) (ht : ¬ (e ≤ t ∧ (t : ℤ) < b)) :
    dextR h e b W V t = h t := by
  unfold dextR; rw [if_neg ht]

lemma dextL_val (h : ℕ → ℝ) (a : ℤ) (e : ℕ) (W V : ℝ) (t : ℕ) (ht : a < t ∧ t ≤ e)
    (hWV : W < V) : W < dextL h a e W V t ∧ dextL h a e W V t ≤ V := by
  unfold dextL; rw [if_pos ht]
  have r1 := nz_lt ht.1
  have r2 : (t : ℝ) ≤ e := by exact_mod_cast ht.2
  have hpos : (0 : ℝ) < (e : ℝ) - a := by linarith
  constructor
  · have : 0 < (V - W) * ((t : ℝ) - a) / ((e : ℝ) - a) :=
      div_pos (mul_pos (by linarith) (by linarith)) hpos
    linarith
  · have : (V - W) * ((t : ℝ) - a) / ((e : ℝ) - a) ≤ V - W := by
      rw [div_le_iff₀ hpos]; nlinarith
    linarith

lemma dextR_val (h : ℕ → ℝ) (e : ℕ) (b : ℤ) (W V : ℝ) (t : ℕ) (ht : e ≤ t ∧ (t : ℤ) < b)
    (hWV : W < V) : W < dextR h e b W V t ∧ dextR h e b W V t ≤ V := by
  unfold dextR; rw [if_pos ht]
  have r1 := zn_lt ht.2
  have r2 : (e : ℝ) ≤ t := by exact_mod_cast ht.1
  have hpos : (0 : ℝ) < (b : ℝ) - e := by linarith
  constructor
  · have : 0 < (V - W) * ((b : ℝ) - t) / ((b : ℝ) - e) :=
      div_pos (mul_pos (by linarith) (by linarith)) hpos
    linarith
  · have : (V - W) * ((b : ℝ) - t) / ((b : ℝ) - e) ≤ V - W := by
      rw [div_le_iff₀ hpos]; nlinarith
    linarith

lemma dextL_e (h : ℕ → ℝ) (a : ℤ) (e : ℕ) (W V : ℝ) (hae : a < e) : dextL h a e W V e = V := by
  unfold dextL
  rw [if_pos ⟨hae, le_refl e⟩, mul_div_assoc, div_self (sub_ne_zero.mpr (nz_lt hae).ne'), mul_one]
  ring

lemma dextR_e (h : ℕ → ℝ) (e : ℕ) (b : ℤ) (W V : ℝ) (heb : (e : ℤ) < b) :
    dextR h e b W V e = V := by
  unfold dextR
  rw [if_pos ⟨le_refl e, heb⟩, mul_div_assoc, div_self (sub_ne_zero.mpr (zn_lt heb).ne'),
    mul_one]
  ring

lemma dextL_mono (h : ℕ → ℝ) (a : ℤ) (e : ℕ) (W V : ℝ) (hae : a < e) (hWV : W < V)
    (hmono : ∀ t1 t2 : ℕ, (t2 : ℤ) ≤ a → t1 < t2 → h t1 < h t2)
    (hWl : ∀ t : ℕ, (t : ℤ) ≤ a → h t ≤ W) :
    ∀ t1 t2 : ℕ, (t2 : ℤ) ≤ (e : ℤ) → t1 < t2 → dextL h a e W V t1 < dextL h a e W V t2 := by
  intro t1 t2 ht2 hlt
  by_cases h2 : (t2 : ℤ) ≤ a
  · rw [dextL_off h a e W V t1 (by intro hh; omega), dextL_off h a e W V t2 (by intro hh; omega)]
    exact hmono t1 t2 h2 hlt
  · push_neg at h2
    have hin2 : a < t2 ∧ t2 ≤ e := ⟨h2, by omega⟩
    by_cases h1 : a < (t1 : ℤ)
    · have hin1 : a < t1 ∧ t1 ≤ e := ⟨h1, by omega⟩
      unfold dextL
      rw [if_pos hin1, if_pos hin2]
      have r1 := nz_lt hae
      have r2 : (t1 : ℝ) < t2 := by exact_mod_cast hlt
      have : (V - W) * ((t1 : ℝ) - a) < (V - W) * ((t2 : ℝ) - a) :=
        mul_lt_mul_of_pos_left (by linarith) (by linarith)
      have := div_lt_div_of_pos_right this (by linarith : (0:ℝ) < (e : ℝ) - a)
      linarith
    · push_neg at h1
      rw [dextL_off h a e W V t1 (by intro hh; omega)]
      have := (dextL_val h a e W V t2 hin2 hWV).1
      linarith [hWl t1 h1]

lemma dextL_Wl (h : ℕ → ℝ) (a : ℤ) (e : ℕ) (W V : ℝ) (hWV : W < V)
    (hWl : ∀ t : ℕ, (t : ℤ) ≤ a → h t ≤ W) :
    ∀ t : ℕ, (t : ℤ) ≤ (e : ℤ) → dextL h a e W V t ≤ V := by
  intro t ht
  by_cases h1 : a < (t : ℤ)
  · exact (dextL_val h a e W V t ⟨h1, by omega⟩ hWV).2
  · push_neg at h1
    rw [dextL_off h a e W V t (by intro hh; omega)]
    linarith [hWl t h1]

lemma dextR_anti (N : ℕ) (h : ℕ → ℝ) (e : ℕ) (b : ℤ) (W V : ℝ) (heb : (e : ℤ) < b) (hWV : W < V)
    (hanti : ∀ t1 t2 : ℕ, b ≤ (t1 : ℤ) → t1 < t2 → t2 < N → h t2 < h t1)
    (hWr : ∀ t : ℕ, b ≤ (t : ℤ) → t < N → h t ≤ W) :
    ∀ t1 t2 : ℕ, (e : ℤ) ≤ (t1 : ℤ) → t1 < t2 → t2 < N →
      dextR h e b W V t2 < dextR h e b W V t1 := by
  intro t1 t2 ht1 hlt ht2N
  by_cases h1 : b ≤ (t1 : ℤ)
  · rw [dextR_off h e b W V t1 (by intro hh; omega), dextR_off h e b W V t2 (by intro hh; omega)]
    exact hanti t1 t2 h1 hlt ht2N
  · push_neg at h1
    have hin1 : e ≤ t1 ∧ (t1 : ℤ) < b := ⟨by omega, h1⟩
    by_cases h2 : (t2 : ℤ) < b
    · have hin2 : e ≤ t2 ∧ (t2 : ℤ) < b := ⟨by omega, h2⟩
      unfold dextR
      rw [if_pos hin1, if_pos hin2]
      have r1 := zn_lt heb
      have r2 : (t1 : ℝ) < t2 := by exact_mod_cast hlt
      have : (V - W) * ((b : ℝ) - t2) < (V - W) * ((b : ℝ) - t1) :=
        mul_lt_mul_of_pos_left (by linarith) (by linarith)
      have := div_lt_div_of_pos_right this (by linarith : (0:ℝ) < (b : ℝ) - e)
      linarith
    · push_neg at h2
      rw [dextR_off h e b W V t2 (by intro hh; omega)]
      have := (dextR_val h e b W V t1 hin1 hWV).1
      linarith [hWr t2 h2 ht2N]

lemma dextR_Wr (N : ℕ) (h : ℕ → ℝ) (e : ℕ) (b : ℤ) (W V : ℝ) (hWV : W < V)
    (hWr : ∀ t : ℕ, b ≤ (t : ℤ) → t < N → h t ≤ W) :
    ∀ t : ℕ, (e : ℤ) ≤ (t : ℤ) → t < N → dextR h e b W V t ≤ V := by
  intro t ht htN
  by_cases h1 : (t : ℤ) < b
  · exact (dextR_val h e b W V t ⟨by omega, h1⟩ hWV).2
  · push_neg at h1
    rw [dextR_off h e b W V t (by intro hh; omega)]
    linarith [hWr t h1 htN]

def Pd (k : ℕ) (a b : ℤ) (c : ℕ) : Prop :=
  (c : ℤ) - a ≤ bookFib (k+1) ∧ b - c ≤ bookFib (k+1) ∧ b - a ≤ bookFib (k+2)

lemma bfZ_ss (n : ℕ) : (bookFib (n+2) : ℤ) = bookFib (n+1) + bookFib n := by
  rw [bf_ss]; push_cast; ring

lemma Pd_mono (j : ℕ) (a b : ℤ) (c : ℕ) (P : Pd j a b c) : Pd (j+1) a b c := by
  obtain ⟨p1, p2, p3⟩ := P
  have e1 : (bookFib (j+1+1) : ℤ) = bookFib (j+1) + bookFib j := bfZ_ss j
  have e2 : (bookFib (j+1+2) : ℤ) = bookFib (j+1+1) + bookFib (j+1) := bfZ_ss (j+1)
  have e0 : (bookFib (j+2) : ℤ) = bookFib (j+1+1) := rfl
  have e3 : (1 : ℤ) ≤ bookFib j := by exact_mod_cast bf_pos j
  refine ⟨by omega, by omega, by omega⟩

theorem dadv (N : ℕ) (T : SearchTree ℕ ℕ) : ∀ (k : ℕ) (a b : ℤ) (c : ℕ) (V W : ℝ) (h : ℕ → ℝ),
    -1 ≤ a → a < c → (c : ℤ) < b → b ≤ N →
    (∀ t1 t2 : ℕ, (t2 : ℤ) ≤ a → t1 < t2 → h t1 < h t2) →
    (∀ t1 t2 : ℕ, b ≤ (t1 : ℤ) → t1 < t2 → t2 < N → h t2 < h t1) →
    (∀ t : ℕ, (t : ℤ) ≤ a → h t ≤ W) → (∀ t : ℕ, b ≤ (t : ℤ) → t < N → h t ≤ W) → W < V →
    (∀ g : ℕ → ℝ, (∀ t : ℕ, ¬ (a < t ∧ (t : ℤ) < b) → g t = h t) → g c = V → GoodD T N k g) →
    Pd k a b c := by
  induction T with
  | stop r =>
    intro k a b c V W h ha hac hcb hbN hmono hanti hWl hWr hWV hG
    have key := dstop_len N k a b c V W h r ha hac hcb hbN hmono hanti hWl hWr hWV hG
    have e1 : (1 : ℤ) ≤ bookFib (k+1) := by exact_mod_cast bf_pos (k+1)
    have e2 := bfZ_ss k
    have e3 : (1 : ℤ) ≤ bookFib k := by exact_mod_cast bf_pos k
    refine ⟨by omega, by omega, by omega⟩
  | query x next ih =>
    intro k a b c V W h ha hac hcb hbN hmono hanti hWl hWr hWV hG
    obtain ⟨g0, hg01, hg02, hg03⟩ :=
      dexists N a b c V W h c hbN ⟨hac, hcb⟩ ⟨hac, hcb⟩ hmono hanti hWl hWr hWV
    have hk := goodD_query_pos hg03 (hG g0 hg01 hg02)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have useIH : ∀ (v : ℝ) (a' b' : ℤ) (c' : ℕ) (V' W' : ℝ) (h' : ℕ → ℝ),
        -1 ≤ a' → a' < c' → (c' : ℤ) < b' → b' ≤ N →
        (∀ t1 t2 : ℕ, (t2 : ℤ) ≤ a' → t1 < t2 → h' t1 < h' t2) →
        (∀ t1 t2 : ℕ, b' ≤ (t1 : ℤ) → t1 < t2 → t2 < N → h' t2 < h' t1) →
        (∀ t : ℕ, (t : ℤ) ≤ a' → h' t ≤ W') → (∀ t : ℕ, b' ≤ (t : ℤ) → t < N → h' t ≤ W') →
        W' < V' →
        (∀ g : ℕ → ℝ, (∀ t : ℕ, ¬ (a' < t ∧ (t : ℤ) < b') → g t = h' t) → g c' = V' →
          ((∀ t : ℕ, ¬ (a < t ∧ (t : ℤ) < b) → g t = h t) ∧ g c = V ∧ g x = v)) →
        Pd j a' b' c' := by
      intro v a' b' c' V' W' h' h1 h2 h3 h4 h5 h6 h7 h8 h9 hsub
      refine ih v j a' b' c' V' W' h' h1 h2 h3 h4 h5 h6 h7 h8 h9 ?_
      intro g hg1 hg2
      obtain ⟨e1, e2, e3⟩ := hsub g hg1 hg2
      have := goodD_query (hG g e1 e2)
      rw [e3] at this
      exact this
    have F1 : (bookFib (j+1+1) : ℤ) = bookFib (j+1) + bookFib j := bfZ_ss j
    have F2 : (bookFib (j+1+2) : ℤ) = bookFib (j+1+1) + bookFib (j+1) := bfZ_ss (j+1)
    have F0 : (bookFib (j+2) : ℤ) = bookFib (j+1+1) := rfl
    have F3 : (1 : ℤ) ≤ bookFib j := by exact_mod_cast bf_pos j
    by_cases hout : (x : ℤ) ≤ a ∨ b ≤ (x : ℤ) ∨ x = c
    · rcases hout with hx | hx | hx
      · exact Pd_mono j a b c (useIH (h x) a b c V W h ha hac hcb hbN hmono hanti hWl hWr hWV
          (fun g hg1 hg2 => ⟨hg1, hg2, hg1 x (by intro hh; omega)⟩))
      · exact Pd_mono j a b c (useIH (h x) a b c V W h ha hac hcb hbN hmono hanti hWl hWr hWV
          (fun g hg1 hg2 => ⟨hg1, hg2, hg1 x (by intro hh; omega)⟩))
      · subst hx
        exact Pd_mono j a b x (useIH V a b x V W h ha hac hcb hbN hmono hanti hWl hWr hWV
          (fun g hg1 hg2 => ⟨hg1, hg2, hg2⟩))
    · push_neg at hout
      obtain ⟨hxa, hxb, hxc⟩ := hout
      rcases Nat.lt_or_gt_of_ne hxc with hlt | hlt
      · -- a < x < c
        have hlt' : (x : ℤ) < c := by exact_mod_cast hlt
        -- option 1: f x > V : state (a, c, x), V+1, W' = V, h3 = dextR h c b W V
        have P1 : Pd j a c x := by
          refine useIH (V+1) a c x (V+1) V (dextR h c b W V) ha hxa hlt' (by omega) ?_ ?_ ?_ ?_
            (by linarith) ?_
          · intro t1 t2 ht2 h12
            rw [dextR_off h c b W V t1 (by intro hh; omega),
              dextR_off h c b W V t2 (by intro hh; omega)]
            exact hmono t1 t2 ht2 h12
          · exact dextR_anti N h c b W V hcb hWV hanti hWr
          · intro t ht
            rw [dextR_off h c b W V t (by intro hh; omega)]
            linarith [hWl t ht]
          · exact dextR_Wr N h c b W V hWV hWr
          · intro g hg1 hg2
            refine ⟨fun t ht => ?_, ?_, hg2⟩
            · rw [hg1 t (by intro hh; omega)]
              exact dextR_off h c b W V t (by intro hh; omega)
            · rw [hg1 c (by intro hh; omega), dextR_e h c b W V hcb]
        -- option 2: f x < V : state (x, b, c), V, W' = (V+W)/2, h4 = dextL h a x W ((V+W)/2)
        have P2 : Pd j x b c := by
          refine useIH ((V+W)/2) x b c V ((V+W)/2) (dextL h a x W ((V+W)/2)) (by omega) hlt' hcb
            hbN ?_ ?_ ?_ ?_ (by linarith) ?_
          · exact dextL_mono h a x W _ hxa (by linarith) hmono hWl
          · intro t1 t2 ht1 h12 ht2
            rw [dextL_off h a x W _ t1 (by intro hh; omega),
              dextL_off h a x W _ t2 (by intro hh; omega)]
            exact hanti t1 t2 ht1 h12 ht2
          · exact dextL_Wl h a x W _ (by linarith) hWl
          · intro t ht htN
            rw [dextL_off h a x W _ t (by intro hh; omega)]
            linarith [hWr t ht htN]
          · intro g hg1 hg2
            refine ⟨fun t ht => ?_, hg2, ?_⟩
            · rw [hg1 t (by intro hh; omega)]
              exact dextL_off h a x W _ t (by intro hh; omega)
            · rw [hg1 x (by intro hh; omega), dextL_e h a x W _ hxa]
        obtain ⟨p1, p2, p3⟩ := P1
        obtain ⟨q1, q2, q3⟩ := P2
        refine ⟨by omega, by omega, by omega⟩
      · -- c < x < b
        have hlt' : (c : ℤ) < x := by exact_mod_cast hlt
        -- option 1: f x < V : state (a, x, c), V, W' = (V+W)/2, h1 = dextR h x b W ((V+W)/2)
        have P1 : Pd j a x c := by
          refine useIH ((V+W)/2) a x c V ((V+W)/2) (dextR h x b W ((V+W)/2)) ha hac hlt'
            (by omega) ?_ ?_ ?_ ?_ (by linarith) ?_
          · intro t1 t2 ht2 h12
            rw [dextR_off h x b W _ t1 (by intro hh; omega),
              dextR_off h x b W _ t2 (by intro hh; omega)]
            exact hmono t1 t2 ht2 h12
          · exact dextR_anti N h x b W _ hxb (by linarith) hanti hWr
          · intro t ht
            rw [dextR_off h x b W _ t (by intro hh; omega)]
            linarith [hWl t ht]
          · exact dextR_Wr N h x b W _ (by linarith) hWr
          · intro g hg1 hg2
            refine ⟨fun t ht => ?_, hg2, ?_⟩
            · rw [hg1 t (by intro hh; omega)]
              exact dextR_off h x b W _ t (by intro hh; omega)
            · rw [hg1 x (by intro hh; omega), dextR_e h x b W _ hxb]
        -- option 2: f x > V : state (c, b, x), V+1, W' = V, h2 = dextL h a c W V
        have P2 : Pd j c b x := by
          refine useIH (V+1) c b x (V+1) V (dextL h a c W V) (by omega) hlt' hxb hbN ?_ ?_ ?_ ?_
            (by linarith) ?_
          · exact dextL_mono h a c W V hac hWV hmono hWl
          · intro t1 t2 ht1 h12 ht2
            rw [dextL_off h a c W V t1 (by intro hh; omega),
              dextL_off h a c W V t2 (by intro hh; omega)]
            exact hanti t1 t2 ht1 h12 ht2
          · exact dextL_Wl h a c W V hWV hWl
          · intro t ht htN
            rw [dextL_off h a c W V t (by intro hh; omega)]
            linarith [hWr t ht htN]
          · intro g hg1 hg2
            refine ⟨fun t ht => ?_, ?_, hg2⟩
            · rw [hg1 t (by intro hh; omega)]
              exact dextL_off h a c W V t (by intro hh; omega)
            · rw [hg1 c (by intro hh; omega), dextL_e h a c W V hac]
        obtain ⟨p1, p2, p3⟩ := P1
        obtain ⟨q1, q2, q3⟩ := P2
        refine ⟨by omega, by omega, by omega⟩

theorem dJ (N : ℕ) (hN : 1 ≤ N) (T : SearchTree ℕ ℕ) : ∀ (k : ℕ) (h : ℕ → ℝ),
    (∀ g : ℕ → ℝ, (∀ t : ℕ, N ≤ t → g t = h t) → GoodD T N k g) →
    (k = 0 → N ≤ 1) ∧ (1 ≤ k → N + 1 ≤ bookFib (k+1)) := by
  induction T with
  | stop r =>
    intro k h hG
    have key := dstop_len N k (-1) N 0 1 0 h r le_rfl (by norm_num) (by omega) le_rfl
      (fun t1 t2 ht2 _ => by omega) (fun t1 t2 ht1 h12 ht2 => by omega)
      (fun t ht => by omega) (fun t ht htN => by omega) (by norm_num)
      (fun g hg1 _ => hG g (fun t ht => hg1 t (by omega)))
    refine ⟨fun _ => by omega, fun hk => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have := bf_lt_succ (j+1) (by omega)
    have := bf_pos (j+1)
    omega
  | query x next ih =>
    intro k h hG
    obtain ⟨g0, hg01, _, hg03⟩ :=
      dexists N (-1) N 0 1 0 h 0 le_rfl ⟨by norm_num, by omega⟩ ⟨by norm_num, by omega⟩
        (fun t1 t2 ht2 _ => by omega) (fun t1 t2 ht1 h12 ht2 => by omega)
        (fun t ht => by omega) (fun t ht htN => by omega) (by norm_num)
    have hk := goodD_query_pos hg03 (hG g0 (fun t ht => hg01 t (by omega)))
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    by_cases hx : x < N
    · have P := dadv N (next 1) j (-1) N x 1 0 h le_rfl (by omega) (by omega) le_rfl
        (fun t1 t2 ht2 _ => by omega) (fun t1 t2 ht1 h12 ht2 => by omega)
        (fun t ht => by omega) (fun t ht htN => by omega) (by norm_num) (by
          intro g hg1 hg2
          have := goodD_query (hG g (fun t ht => hg1 t (by omega)))
          rwa [hg2] at this)
      obtain ⟨_, _, p3⟩ := P
      refine ⟨fun hj => by omega, fun _ => ?_⟩
      have e0 : (bookFib (j+2) : ℤ) = bookFib (j+1+1) := rfl
      omega
    · push_neg at hx
      have := ih (h x) j h (by
        intro g hg1
        have := goodD_query (hG g hg1)
        rwa [hg1 x hx] at this)
      obtain ⟨p3, p4⟩ := this
      refine ⟨fun hj => by omega, fun _ => ?_⟩
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        have := p3 rfl
        have e : bookFib (0+1+1) = 2 := rfl
        omega
      · have := p4 hj
        have := bf_le_succ (j+1)
        omega

lemma dcmpL {f : ℕ → ℝ} {N m p q : ℕ} (hf : IsStrictUnimodalOnPoints f N m) (hpq : p < q)
    (hq : q < N) (h : f p < f q) : p < m := by
  by_contra hm
  push_neg at hm
  have := hf.2.2 (show p ∈ Set.Ico m N from ⟨hm, by omega⟩) (show q ∈ Set.Ico m N from
    ⟨by omega, hq⟩) hpq
  linarith

lemma dcmpR {f : ℕ → ℝ} {N m p q : ℕ} (hf : IsStrictUnimodalOnPoints f N m) (hpq : p < q)
    (h : ¬ f p < f q) : m < q := by
  by_contra hm
  push_neg at hm
  exact h (hf.2.1 (show p ∈ Set.Iic m from by simp only [Set.mem_Iic]; omega)
    (show q ∈ Set.Iic m from hm) hpq)

noncomputable def dTree : ℕ → ℤ → ℤ → ℕ → ℝ → SearchTree ℕ ℕ
  | 0, _, _, c, _ => stop c
  | k+1, a, b, c, fc => query (a + b - c).toNat (fun fx =>
      if c ≤ (a + b - c).toNat then
        (if fc < fx then dTree k c b (a + b - c).toNat fx
          else dTree k a ((a + b - c).toNat : ℤ) c fc)
      else
        (if fx < fc then dTree k ((a + b - c).toNat : ℤ) b c fc
          else dTree k a c (a + b - c).toNat fx))

lemma dTree_succ (k : ℕ) (a b : ℤ) (c : ℕ) (fc : ℝ) (x : ℕ) (hx : x = (a + b - c).toNat) :
    dTree (k+1) a b c fc = query x (fun fx =>
      if c ≤ x then (if fc < fx then dTree k c b x fx else dTree k a x c fc)
      else (if fx < fc then dTree k x b c fc else dTree k a c x fx)) := by
  subst hx; rw [dTree]

lemma dTree_correct (N : ℕ) (f : ℕ → ℝ) (m : ℕ) (hf : IsStrictUnimodalOnPoints f N m) :
    ∀ (j : ℕ) (a b : ℤ) (c : ℕ), -1 ≤ a → b ≤ N → a < m → (m : ℤ) < b →
      b - a = bookFib (j+2) → ((c : ℤ) - a = bookFib j ∨ b - c = bookFib j) →
      (dTree j a b c (f c)).cost f ≤ j ∧ (dTree j a b c (f c)).result f = m := by
  intro j
  induction j with
  | zero =>
    intro a b c ha hb hma hmb hlen hc
    have e2 : bookFib (0+2) = 2 := rfl
    have e0 : bookFib 0 = 1 := rfl
    simp only [dTree, SearchTree.cost, SearchTree.result]
    refine ⟨le_rfl, ?_⟩
    rw [e2] at hlen; rw [e0] at hc
    push_cast at hlen hc
    omega
  | succ j ih =>
    intro a b c ha hb hma hmb hlen hc
    have F1 : (bookFib (j+1+1) : ℤ) = bookFib (j+1) + bookFib j := bfZ_ss j
    have F2 : (bookFib (j+1+2) : ℤ) = bookFib (j+1+1) + bookFib (j+1) := bfZ_ss (j+1)
    have F0 : (bookFib (j+2) : ℤ) = bookFib (j+1+1) := rfl
    have F3 : (1 : ℤ) ≤ bookFib j := by exact_mod_cast bf_pos j
    have F4 : (bookFib (j+1+2) : ℤ) = bookFib (j+3) := rfl
    have F5 : (1 : ℤ) ≤ bookFib (j+1) := by exact_mod_cast bf_pos (j+1)
    have hpos : 0 ≤ a + b - c := by rcases hc with hc | hc <;> omega
    obtain ⟨x, hx_def⟩ : ∃ x : ℕ, x = (a + b - c).toNat := ⟨_, rfl⟩
    have hxv : (x : ℤ) = a + b - c := by rw [hx_def]; exact Int.toNat_of_nonneg hpos
    rw [dTree_succ j a b c (f c) x hx_def]
    simp only [SearchTree.cost, SearchTree.result]
    have hmN : m < N := hf.1
    rcases hc with hc | hc
    · have hcx : c < x := by omega
      rw [if_pos hcx.le]
      by_cases hcmp : f c < f x
      · rw [if_pos hcmp]
        have hmc := dcmpL hf hcx (by omega) hcmp
        have := ih c b x (by omega) hb (by exact_mod_cast hmc) hmb (by omega) (Or.inl (by omega))
        exact ⟨by omega, this.2⟩
      · rw [if_neg hcmp]
        have hmc := dcmpR hf hcx hcmp
        have := ih a x c ha (by omega) hma (by exact_mod_cast hmc) (by omega) (Or.inr (by omega))
        exact ⟨by omega, this.2⟩
    · have hcx : x < c := by omega
      rw [if_neg (not_le.mpr hcx)]
      by_cases hcmp : f x < f c
      · rw [if_pos hcmp]
        have hmc := dcmpL hf hcx (by omega) hcmp
        have := ih x b c (by omega) hb (by exact_mod_cast hmc) hmb (by omega) (Or.inl (by omega))
        exact ⟨by omega, this.2⟩
      · rw [if_neg hcmp]
        have hmc := dcmpR hf hcx hcmp
        have := ih a c x ha (by omega) hma (by exact_mod_cast hmc) (by omega) (Or.inr (by omega))
        exact ⟨by omega, this.2⟩

theorem disc_upper (n N : ℕ) (hN : N ∈ identifiableSizes n) :
    (n = 0 → N ≤ 1) ∧ (1 ≤ n → N + 1 ≤ bookFib (n+1)) := by
  obtain ⟨hN1, T, hT⟩ := hN
  exact dJ N hN1 T n (fun _ => 0) (fun g _ m hm => hT g m hm)

theorem disc_mem (n : ℕ) (hn : 1 ≤ n) : bookFib (n+1) - 1 ∈ identifiableSizes n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h2 := bf_lt_succ (k+1) (by omega)
  have h1 := bf_pos (k+1)
  have h0 := bf_pos k
  have hss := bf_ss k
  refine ⟨by omega, query (bookFib k - 1) (fun v => dTree k (-1) (bookFib (k+2) - 1 : ℕ)
    (bookFib k - 1) v), fun f m hf => ?_⟩
  have hmN : m < bookFib (k+1+1) - 1 := hf.1
  have hkk : bookFib (k+1+1) = bookFib (k+2) := rfl
  have := dTree_correct (bookFib (k+1+1) - 1) f m hf k (-1) (bookFib (k+2) - 1 : ℕ)
    (bookFib k - 1) le_rfl le_rfl (by omega) (by omega) (by push_cast; omega)
    (Or.inl (by push_cast; omega))
  simp only [SearchTree.cost, SearchTree.result]
  exact ⟨by omega, this.2⟩

theorem disc_greatest (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest (identifiableSizes n) (bookFib (n+1) - 1) := by
  refine ⟨disc_mem n hn, fun N hN => ?_⟩
  have := (disc_upper n N hN).2 hn
  omega

theorem disc_zero : IsGreatest (identifiableSizes 0) 1 := by
  refine ⟨⟨le_rfl, stop 0, fun f m hf => ?_⟩, fun N hN => (disc_upper 0 N hN).1 rfl⟩
  have : m < 1 := hf.1
  simp only [SearchTree.cost, SearchTree.result]
  omega

theorem discrete_search_corrected_core :
    IsGreatest (identifiableSizes 0) 1 ∧
    IsGreatest (identifiableSizes 1) 1 ∧
    IsGreatest (identifiableSizes 2) 2 ∧
    IsGreatest (identifiableSizes 3) 4 ∧
    ∀ n : ℕ, 3 ≤ n → IsGreatest (identifiableSizes n) (bookFib (n + 1) - 1) := by
  refine ⟨disc_zero, ?_, ?_, ?_, fun n hn => disc_greatest n (by omega)⟩
  · have h := disc_greatest 1 le_rfl
    rwa [show bookFib (1+1) - 1 = 1 from rfl] at h
  · have h := disc_greatest 2 (by norm_num)
    rwa [show bookFib (2+1) - 1 = 2 from rfl] at h
  · have h := disc_greatest 3 (by norm_num)
    rwa [show bookFib (3+1) - 1 = 4 from rfl] at h

end BellmanDP.Fibonacci

open BellmanDP.Fibonacci


theorem solution :
    IsGreatest (identifiableSizes 0) 1 ∧
    IsGreatest (identifiableSizes 1) 1 ∧
    IsGreatest (identifiableSizes 2) 2 ∧
    IsGreatest (identifiableSizes 3) 4 ∧
    ∀ n : ℕ, 3 ≤ n → IsGreatest (identifiableSizes n) (bookFib (n + 1) - 1) := by
  exact discrete_search_corrected_core
