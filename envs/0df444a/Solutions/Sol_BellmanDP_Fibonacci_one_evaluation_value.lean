-- Prove2me | solution 1 for BellmanDP.Fibonacci.one_evaluation_value
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:19:27.501293+00:00
-- url     : https://prove2.me/submissions/f5a074d3-aa35-444f-a591-35f6bed8c7dd

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

/-- the procedure is correct on `g` with budget `k` -/
def Good (T : SearchTree ℝ (ℝ × ℝ)) (L : ℝ) (k : ℕ) (g : ℝ → ℝ) : Prop :=
  ∀ m, IsStrictUnimodalOn g L m → T.cost g ≤ k ∧ (T.result g).2 - (T.result g).1 ≤ 1 ∧
    m ∈ Set.Icc (T.result g).1 (T.result g).2

lemma good_query {x : ℝ} {next : ℝ → SearchTree ℝ (ℝ × ℝ)} {L : ℝ} {k : ℕ} {g : ℝ → ℝ}
    (hg : Good (query x next) L (k+1) g) : Good (next (g x)) L k g := by
  intro m hm
  obtain ⟨h1, h2, h3⟩ := hg m hm
  simp only [SearchTree.cost, SearchTree.result] at h1 h2 h3
  exact ⟨by omega, h2, h3⟩

lemma good_query_pos {x : ℝ} {next : ℝ → SearchTree ℝ (ℝ × ℝ)} {L : ℝ} {k : ℕ} {g : ℝ → ℝ}
    {m : ℝ} (hm : IsStrictUnimodalOn g L m)
    (hg : Good (query x next) L k g) : 1 ≤ k := by
  have := (hg m hm).1
  simp only [SearchTree.cost] at this
  omega

lemma exists_unimodal (L a b c V m : ℝ) (h : ℝ → ℝ) (ha : 0 ≤ a) (hb : b ≤ L)
    (hm : a < m ∧ m < b) (hc : a < c ∧ c < b)
    (hmono : StrictMonoOn h (Set.Icc 0 a)) (hanti : StrictAntiOn h (Set.Icc b L))
    (hVa : h a < V) (hVb : h b < V) :
    ∃ g : ℝ → ℝ, (∀ t, ¬ (a < t ∧ t < b) → g t = h t) ∧ g c = V ∧ IsStrictUnimodalOn g L m := by
  have hab : 0 < b - a := by linarith [hm.1, hm.2]
  set s := min (V - h a) (V - h b) / (2 * (b - a)) with hs_def
  have hmin : 0 < min (V - h a) (V - h b) := lt_min (by linarith) (by linarith)
  have hs : 0 < s := div_pos hmin (by linarith)
  have hsb : s * (b - a) = min (V - h a) (V - h b) / 2 := by
    rw [hs_def]; field_simp
  have hm1 : min (V - h a) (V - h b) ≤ V - h a := min_le_left _ _
  have hm2 : min (V - h a) (V - h b) ≤ V - h b := min_le_right _ _
  refine ⟨fun t => if a < t ∧ t < b then V + s * (|c - m| - |t - m|) else h t, ?_, ?_, ?_⟩
  · intro t ht; simp [ht]
  · simp [hc]
  · refine ⟨⟨by linarith [hm.1], by linarith [hm.2]⟩, ?_, ?_⟩
    · intro t1 ht1 t2 ht2 hlt
      simp only [Set.mem_Icc] at ht1 ht2
      simp only
      by_cases h2 : t2 ≤ a
      · have h1' : ¬ (a < t1 ∧ t1 < b) := by intro h; linarith [h.1]
        have h2' : ¬ (a < t2 ∧ t2 < b) := by intro h; linarith [h.1]
        rw [if_neg h1', if_neg h2']
        exact hmono ⟨ht1.1, by linarith⟩ ⟨ht2.1, h2⟩ hlt
      · push_neg at h2
        have h2' : a < t2 ∧ t2 < b := ⟨h2, by linarith [ht2.2, hm.2]⟩
        rw [if_pos h2']
        by_cases h1 : a < t1
        · rw [if_pos ⟨h1, by linarith [ht1.2, hm.2]⟩]
          have e1 : |t1 - m| = m - t1 := by rw [abs_of_nonpos (by linarith [ht1.2])]; ring
          have e2 : |t2 - m| = m - t2 := by rw [abs_of_nonpos (by linarith [ht2.2])]; ring
          rw [e1, e2]
          have : s * (m - t2) < s * (m - t1) := mul_lt_mul_of_pos_left (by linarith) hs
          nlinarith
        · rw [if_neg (fun h => h1 h.1)]
          push_neg at h1
          have hle : h t1 ≤ h a := hmono.monotoneOn ⟨ht1.1, h1⟩ ⟨ha, le_refl a⟩ h1
          have habs : |t2 - m| ≤ b - a := abs_le.mpr ⟨by linarith [hm.2], by linarith [hm.1]⟩
          have h0 : 0 ≤ s * |c - m| := mul_nonneg hs.le (abs_nonneg _)
          have hq : s * |t2 - m| ≤ s * (b - a) := mul_le_mul_of_nonneg_left habs hs.le
          nlinarith
    · intro t1 ht1 t2 ht2 hlt
      simp only [Set.mem_Icc] at ht1 ht2
      simp only
      by_cases h1 : b ≤ t1
      · have h1' : ¬ (a < t1 ∧ t1 < b) := by intro h; linarith [h.2]
        have h2' : ¬ (a < t2 ∧ t2 < b) := by intro h; linarith [h.2]
        rw [if_neg h1', if_neg h2']
        exact hanti ⟨h1, ht1.2⟩ ⟨by linarith, ht2.2⟩ hlt
      · push_neg at h1
        have h1' : a < t1 ∧ t1 < b := ⟨by linarith [ht1.1, hm.1], h1⟩
        rw [if_pos h1']
        by_cases h2 : t2 < b
        · rw [if_pos ⟨by linarith [ht2.1, hm.1], h2⟩]
          have e1 : |t1 - m| = t1 - m := abs_of_nonneg (by linarith [ht1.1])
          have e2 : |t2 - m| = t2 - m := abs_of_nonneg (by linarith [ht2.1])
          rw [e1, e2]
          have : s * (t1 - m) < s * (t2 - m) := mul_lt_mul_of_pos_left (by linarith) hs
          nlinarith
        · rw [if_neg (fun h => h2 h.2)]
          push_neg at h2
          have hle : h t2 ≤ h b := hanti.antitoneOn ⟨le_refl b, hb⟩ ⟨h2, ht2.2⟩ h2
          have habs : |t1 - m| ≤ b - a := abs_le.mpr ⟨by linarith [hm.2], by linarith [hm.1]⟩
          have h0 : 0 ≤ s * |c - m| := mul_nonneg hs.le (abs_nonneg _)
          have hq : s * |t1 - m| ≤ s * (b - a) := mul_le_mul_of_nonneg_left habs hs.le
          nlinarith

/-- interval-length bound at a stopping node -/
lemma stop_len (L a b c V : ℝ) (h : ℝ → ℝ) (r : ℝ × ℝ) (ha : 0 ≤ a) (hac : a < c) (hcb : c < b)
    (hb : b ≤ L) (hmono : StrictMonoOn h (Set.Icc 0 a)) (hanti : StrictAntiOn h (Set.Icc b L))
    (hVa : h a < V) (hVb : h b < V)
    (hG : ∀ g : ℝ → ℝ, (∀ t, ¬ (a < t ∧ t < b) → g t = h t) → g c = V →
      Good (stop r) L 0 g) : b - a ≤ 1 := by
  have hall : ∀ m, a < m → m < b → (r.1 ≤ m ∧ m ≤ r.2) ∧ r.2 - r.1 ≤ 1 := by
    intro m h1 h2
    obtain ⟨g, hg1, hg2, hg3⟩ :=
      exists_unimodal L a b c V m h ha hb ⟨h1, h2⟩ ⟨hac, hcb⟩ hmono hanti hVa hVb
    have := hG g hg1 hg2 m hg3
    simp only [SearchTree.result] at this
    exact ⟨this.2.2, this.2.1⟩
  have hlen := (hall c hac hcb).2
  have h1 : r.1 ≤ a := by
    apply forall_gt_imp_ge_iff_le_of_dense.mp
    intro m hm
    rcases lt_or_ge m b with h | h
    · exact (hall m hm h).1.1
    · linarith [(hall c hac hcb).1.1]
  have h2 : b ≤ r.2 := by
    apply forall_lt_imp_le_iff_le_of_dense.mp
    intro m hm
    rcases lt_or_ge a m with h | h
    · exact (hall m h hm).1.2
    · linarith [(hall c hac hcb).1.2]
  linarith

noncomputable def extL (h : ℝ → ℝ) (a e W : ℝ) : ℝ → ℝ :=
  fun t => if a < t ∧ t ≤ e then h a + (W - h a) * (t - a) / (e - a) else h t

noncomputable def extR (h : ℝ → ℝ) (e b W : ℝ) : ℝ → ℝ :=
  fun t => if e ≤ t ∧ t < b then h b + (W - h b) * (b - t) / (b - e) else h t

lemma extL_mono (h : ℝ → ℝ) (a e W : ℝ) (ha : 0 ≤ a) (hae : a < e)
    (hmono : StrictMonoOn h (Set.Icc 0 a)) (hW : h a < W) :
    StrictMonoOn (extL h a e W) (Set.Icc 0 e) := by
  intro t1 ht1 t2 ht2 hlt
  simp only [Set.mem_Icc] at ht1 ht2
  unfold extL
  by_cases h2 : t2 ≤ a
  · rw [if_neg (show ¬ (a < t1 ∧ t1 ≤ e) by intro h; linarith [h.1]),
      if_neg (show ¬ (a < t2 ∧ t2 ≤ e) by intro h; linarith [h.1])]
    exact hmono ⟨ht1.1, by linarith⟩ ⟨ht2.1, h2⟩ hlt
  · push_neg at h2
    rw [if_pos (show a < t2 ∧ t2 ≤ e from ⟨h2, ht2.2⟩)]
    by_cases h1 : a < t1
    · rw [if_pos (show a < t1 ∧ t1 ≤ e from ⟨h1, by linarith⟩)]
      have : (W - h a) * (t1 - a) < (W - h a) * (t2 - a) :=
        mul_lt_mul_of_pos_left (by linarith) (by linarith)
      have := div_lt_div_of_pos_right this (by linarith : (0:ℝ) < e - a)
      linarith
    · rw [if_neg (show ¬ (a < t1 ∧ t1 ≤ e) from fun h => h1 h.1)]
      push_neg at h1
      have hle : h t1 ≤ h a := hmono.monotoneOn ⟨ht1.1, h1⟩ ⟨ha, le_refl a⟩ h1
      have : 0 < (W - h a) * (t2 - a) / (e - a) :=
        div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
      linarith

lemma extL_e (h : ℝ → ℝ) (a e W : ℝ) (hae : a < e) : extL h a e W e = W := by
  unfold extL
  rw [if_pos ⟨hae, le_refl e⟩, mul_div_assoc, div_self (sub_ne_zero.mpr hae.ne'), mul_one]
  ring

lemma extL_off (h : ℝ → ℝ) (a e W t : ℝ) (ht : ¬ (a < t ∧ t ≤ e)) : extL h a e W t = h t := by
  unfold extL; rw [if_neg ht]

lemma extR_anti (h : ℝ → ℝ) (e b W L : ℝ) (heb : e < b) (hb : b ≤ L)
    (hanti : StrictAntiOn h (Set.Icc b L)) (hW : h b < W) :
    StrictAntiOn (extR h e b W) (Set.Icc e L) := by
  intro t1 ht1 t2 ht2 hlt
  simp only [Set.mem_Icc] at ht1 ht2
  unfold extR
  by_cases h1 : b ≤ t1
  · rw [if_neg (show ¬ (e ≤ t1 ∧ t1 < b) by intro h; linarith [h.2]),
      if_neg (show ¬ (e ≤ t2 ∧ t2 < b) by intro h; linarith [h.2])]
    exact hanti ⟨h1, ht1.2⟩ ⟨by linarith, ht2.2⟩ hlt
  · push_neg at h1
    rw [if_pos (show e ≤ t1 ∧ t1 < b from ⟨ht1.1, h1⟩)]
    by_cases h2 : t2 < b
    · rw [if_pos (show e ≤ t2 ∧ t2 < b from ⟨by linarith, h2⟩)]
      have : (W - h b) * (b - t2) < (W - h b) * (b - t1) :=
        mul_lt_mul_of_pos_left (by linarith) (by linarith)
      have := div_lt_div_of_pos_right this (by linarith : (0:ℝ) < b - e)
      linarith
    · rw [if_neg (show ¬ (e ≤ t2 ∧ t2 < b) from fun h => h2 h.2)]
      push_neg at h2
      have hle : h t2 ≤ h b := hanti.antitoneOn ⟨le_refl b, hb⟩ ⟨h2, ht2.2⟩ h2
      have : 0 < (W - h b) * (b - t1) / (b - e) :=
        div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
      linarith

lemma extR_e (h : ℝ → ℝ) (e b W : ℝ) (heb : e < b) : extR h e b W e = W := by
  unfold extR
  rw [if_pos ⟨le_refl e, heb⟩, mul_div_assoc, div_self (sub_ne_zero.mpr heb.ne'), mul_one]
  ring

lemma extR_off (h : ℝ → ℝ) (e b W t : ℝ) (ht : ¬ (e ≤ t ∧ t < b)) : extR h e b W t = h t := by
  unfold extR; rw [if_neg ht]

/-- The invariant obtained by the adversary. -/
def Pinv (k : ℕ) (a b c : ℝ) : Prop :=
  c - a ≤ bookFib k ∧ b - c ≤ bookFib k ∧ (k = 0 → b - a ≤ 1) ∧ (1 ≤ k → b - a < bookFib (k+1))

theorem adv (L : ℝ) (T : SearchTree ℝ (ℝ × ℝ)) : ∀ (k : ℕ) (a b c V : ℝ) (h : ℝ → ℝ),
    0 ≤ a → a < c → c < b → b ≤ L → StrictMonoOn h (Set.Icc 0 a) →
    StrictAntiOn h (Set.Icc b L) → h a < V → h b < V →
    (∀ g : ℝ → ℝ, (∀ t, ¬ (a < t ∧ t < b) → g t = h t) → g c = V → Good T L k g) →
    Pinv k a b c := by
  induction T with
  | stop r =>
    intro k a b c V h ha hac hcb hb hmono hanti hVa hVb hG
    have key : b - a ≤ 1 := by
      refine stop_len L a b c V h r ha hac hcb hb hmono hanti hVa hVb ?_
      intro g h1 h2 m hm
      obtain ⟨_, h4, h5⟩ := hG g h1 h2 m hm
      exact ⟨by simp [SearchTree.cost], h4, h5⟩
    refine ⟨by linarith [bfR_pos k], by linarith [bfR_pos k], fun _ => key, fun hk => ?_⟩
    have := bfR_lt_succ k hk
    linarith [bfR_pos k]
  | query x next ih =>
    intro k a b c V h ha hac hcb hb hmono hanti hVa hVb hG
    -- k ≥ 1
    obtain ⟨g0, hg01, hg02, hg03⟩ :=
      exists_unimodal L a b c V c h ha hb ⟨hac, hcb⟩ ⟨hac, hcb⟩ hmono hanti hVa hVb
    have hk := good_query_pos hg03 (hG g0 hg01 hg02)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hF2 := bfR_ss j
    have hF1 := bfR_le_succ j
    have hFp := bfR_pos j
    -- generic use of ih
    have useIH : ∀ (v a' b' c' V' : ℝ) (h' : ℝ → ℝ),
        0 ≤ a' → a' < c' → c' < b' → b' ≤ L → StrictMonoOn h' (Set.Icc 0 a') →
        StrictAntiOn h' (Set.Icc b' L) → h' a' < V' → h' b' < V' →
        (∀ g : ℝ → ℝ, (∀ t, ¬ (a' < t ∧ t < b') → g t = h' t) → g c' = V' →
          ((∀ t, ¬ (a < t ∧ t < b) → g t = h t) ∧ g c = V ∧ g x = v)) →
        Pinv j a' b' c' := by
      intro v a' b' c' V' h' h1 h2 h3 h4 h5 h6 h7 h8 hsub
      refine ih v j a' b' c' V' h' h1 h2 h3 h4 h5 h6 h7 h8 ?_
      intro g hg1 hg2
      obtain ⟨e1, e2, e3⟩ := hsub g hg1 hg2
      have := good_query (hG g e1 e2)
      rw [e3] at this
      exact this
    rcases lt_trichotomy x c with hxc | hxc | hxc
    · by_cases hxa : a < x
      · -- x ∈ (a, c): two options
        -- option 1: f x > V : state (a, c, x), V+1, h3 = extR h c b V
        have P1 : Pinv j a c x := by
          refine useIH (V+1) a c x (V+1) (extR h c b V) ha hxa hxc (by linarith) ?_ ?_ ?_ ?_ ?_
          · intro t1 ht1 t2 ht2 hlt
            rw [extR_off h c b V t1 (by intro hh; linarith [hh.1, ht1.2]),
              extR_off h c b V t2 (by intro hh; linarith [hh.1, ht2.2])]
            exact hmono ht1 ht2 hlt
          · exact extR_anti h c b V L hcb hb hanti hVb
          · rw [extR_off h c b V a (by intro hh; linarith [hh.1])]; linarith
          · rw [extR_e h c b V hcb]; linarith
          · intro g hg1 hg2
            refine ⟨fun t ht => ?_, ?_, hg2⟩
            · rw [hg1 t (by intro hh; exact ht ⟨hh.1, by linarith [hh.2]⟩)]
              exact extR_off h c b V t (by intro hh; exact ht ⟨by linarith [hh.1], hh.2⟩)
            · rw [hg1 c (by intro hh; linarith [hh.2]), extR_e h c b V hcb]
        -- option 2: f x < V : state (x, b, c), V, h4 = extL h a x ((h a + V)/2)
        have P2 : Pinv j x b c := by
          refine useIH (extL h a x ((h a + V)/2) x) x b c V (extL h a x ((h a + V)/2))
            (by linarith) hxc hcb hb ?_ ?_ ?_ ?_ ?_
          · exact extL_mono h a x _ ha hxa hmono (by linarith)
          · intro t1 ht1 t2 ht2 hlt
            rw [extL_off h a x _ t1 (by intro hh; linarith [hh.2, ht1.1]),
              extL_off h a x _ t2 (by intro hh; linarith [hh.2, ht2.1])]
            exact hanti ht1 ht2 hlt
          · rw [extL_e h a x _ hxa]; linarith
          · rw [extL_off h a x _ b (by intro hh; linarith [hh.2])]; exact hVb
          · intro g hg1 hg2
            refine ⟨fun t ht => ?_, hg2, ?_⟩
            · rw [hg1 t (by intro hh; exact ht ⟨by linarith [hh.1], hh.2⟩)]
              exact extL_off h a x _ t (by intro hh; exact ht ⟨hh.1, by linarith [hh.2]⟩)
            · exact hg1 x (by intro hh; linarith [hh.1])
        obtain ⟨p1, p2, p3, p4⟩ := P1
        obtain ⟨q1, q2, q3, q4⟩ := P2
        rcases Nat.eq_zero_or_pos j with hj | hj
        · subst hj
          simp only [zero_add] at *
          rw [bfR0] at p1 p2 q1 q2
          have e1 : (bookFib 1 : ℝ) = 1 := bfR1
          have e2 : (bookFib (1+1) : ℝ) = 2 := bfR2
          have := p3 trivial; have := q3 trivial
          refine ⟨by rw [e1]; linarith, by rw [e1]; linarith, by omega,
            fun _ => by rw [e2]; linarith⟩
        · have := p4 hj; have := q4 hj
          refine ⟨by linarith, by linarith, by omega, fun _ => ?_⟩
          rw [show j + 1 + 1 = j + 2 by ring, hF2]; linarith
      · -- x ≤ a: no information
        push_neg at hxa
        have := useIH (h x) a b c V h ha hac hcb hb hmono hanti hVa hVb
          (fun g hg1 hg2 => ⟨hg1, hg2, hg1 x (by intro hh; linarith [hh.1])⟩)
        obtain ⟨p1, p2, p3, p4⟩ := this
        refine ⟨by linarith, by linarith, by omega, fun _ => ?_⟩
        rcases Nat.eq_zero_or_pos j with hj | hj
        · subst hj; rw [bfR2]; linarith [p3 rfl]
        · rw [show j + 1 + 1 = j + 2 by ring, hF2]; linarith [p4 hj]
    · -- x = c
      subst hxc
      have := useIH V a b x V h ha hac hcb hb hmono hanti hVa hVb
        (fun g hg1 hg2 => ⟨hg1, hg2, hg2⟩)
      obtain ⟨p1, p2, p3, p4⟩ := this
      refine ⟨by linarith, by linarith, by omega, fun _ => ?_⟩
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; rw [bfR2]; linarith [p3 rfl]
      · rw [show j + 1 + 1 = j + 2 by ring, hF2]; linarith [p4 hj]
    · by_cases hxb : x < b
      · -- x ∈ (c, b)
        -- option 1: f x < V : state (a, x, c), V, h1 = extR h x b ((h b + V)/2)
        have P1 : Pinv j a x c := by
          refine useIH (extR h x b ((h b + V)/2) x) a x c V (extR h x b ((h b + V)/2))
            ha hac hxc (by linarith) ?_ ?_ ?_ ?_ ?_
          · intro t1 ht1 t2 ht2 hlt
            rw [extR_off h x b _ t1 (by intro hh; linarith [hh.1, ht1.2]),
              extR_off h x b _ t2 (by intro hh; linarith [hh.1, ht2.2])]
            exact hmono ht1 ht2 hlt
          · exact extR_anti h x b _ L hxb hb hanti (by linarith)
          · rw [extR_off h x b _ a (by intro hh; linarith [hh.1])]; exact hVa
          · rw [extR_e h x b _ hxb]; linarith
          · intro g hg1 hg2
            refine ⟨fun t ht => ?_, hg2, ?_⟩
            · rw [hg1 t (by intro hh; exact ht ⟨hh.1, by linarith [hh.2]⟩)]
              exact extR_off h x b _ t (by intro hh; exact ht ⟨by linarith [hh.1], hh.2⟩)
            · exact hg1 x (by intro hh; linarith [hh.2])
        -- option 2: f x > V : state (c, b, x), V+1, h2 = extL h a c V
        have P2 : Pinv j c b x := by
          refine useIH (V+1) c b x (V+1) (extL h a c V) (by linarith) hxc hxb hb ?_ ?_ ?_ ?_ ?_
          · exact extL_mono h a c V ha hac hmono hVa
          · intro t1 ht1 t2 ht2 hlt
            rw [extL_off h a c V t1 (by intro hh; linarith [hh.2, ht1.1]),
              extL_off h a c V t2 (by intro hh; linarith [hh.2, ht2.1])]
            exact hanti ht1 ht2 hlt
          · rw [extL_e h a c V hac]; linarith
          · rw [extL_off h a c V b (by intro hh; linarith [hh.2])]; linarith
          · intro g hg1 hg2
            refine ⟨fun t ht => ?_, ?_, hg2⟩
            · rw [hg1 t (by intro hh; exact ht ⟨by linarith [hh.1], hh.2⟩)]
              exact extL_off h a c V t (by intro hh; exact ht ⟨hh.1, by linarith [hh.2]⟩)
            · rw [hg1 c (by intro hh; linarith [hh.1]), extL_e h a c V hac]
        obtain ⟨p1, p2, p3, p4⟩ := P1
        obtain ⟨q1, q2, q3, q4⟩ := P2
        rcases Nat.eq_zero_or_pos j with hj | hj
        · subst hj
          simp only [zero_add] at *
          rw [bfR0] at p1 p2 q1 q2
          have e1 : (bookFib 1 : ℝ) = 1 := bfR1
          have e2 : (bookFib (1+1) : ℝ) = 2 := bfR2
          have := p3 trivial; have := q3 trivial
          refine ⟨by rw [e1]; linarith, by rw [e1]; linarith, by omega,
            fun _ => by rw [e2]; linarith⟩
        · have := p4 hj; have := q4 hj
          refine ⟨by linarith, by linarith, by omega, fun _ => ?_⟩
          rw [show j + 1 + 1 = j + 2 by ring, hF2]; linarith
      · push_neg at hxb
        have := useIH (h x) a b c V h ha hac hcb hb hmono hanti hVa hVb
          (fun g hg1 hg2 => ⟨hg1, hg2, hg1 x (by intro hh; linarith [hh.2])⟩)
        obtain ⟨p1, p2, p3, p4⟩ := this
        refine ⟨by linarith, by linarith, by omega, fun _ => ?_⟩
        rcases Nat.eq_zero_or_pos j with hj | hj
        · subst hj; rw [bfR2]; linarith [p3 rfl]
        · rw [show j + 1 + 1 = j + 2 by ring, hF2]; linarith [p4 hj]

theorem advJ (L : ℝ) (hL : 0 < L) (T : SearchTree ℝ (ℝ × ℝ)) : ∀ (k : ℕ) (h : ℝ → ℝ),
    (∀ g : ℝ → ℝ, (∀ t, ¬ (0 < t ∧ t < L) → g t = h t) → Good T L k g) →
    (k ≤ 1 → L ≤ 1) ∧ (2 ≤ k → L < bookFib k) := by
  have hmono0 : ∀ h : ℝ → ℝ, StrictMonoOn h (Set.Icc 0 0) := by
    intro h t1 ht1 t2 ht2 hlt
    simp only [Set.mem_Icc] at ht1 ht2; linarith [ht1.2, ht2.1]
  have hantiL : ∀ h : ℝ → ℝ, StrictAntiOn h (Set.Icc L L) := by
    intro h t1 ht1 t2 ht2 hlt
    simp only [Set.mem_Icc] at ht1 ht2; linarith [ht1.1, ht2.2]
  induction T with
  | stop r =>
    intro k h hG
    have key : L - 0 ≤ 1 := by
      refine stop_len L 0 L (L/2) (max (h 0) (h L) + 1) h r le_rfl (by linarith) (by linarith)
        le_rfl (hmono0 h) (hantiL h) (by linarith [le_max_left (h 0) (h L)])
        (by linarith [le_max_right (h 0) (h L)]) ?_
      intro g h1 _ m hm
      obtain ⟨_, h4, h5⟩ := hG g h1 m hm
      exact ⟨by simp [SearchTree.cost], h4, h5⟩
    refine ⟨fun _ => by linarith, fun hk => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have := bfR_lt_succ j (by omega)
    linarith [bfR_pos j]
  | query x next ih =>
    intro k h hG
    set V0 := max (h 0) (h L) + 1 with hV0
    have hV1 : h 0 < V0 := by linarith [le_max_left (h 0) (h L)]
    have hV2 : h L < V0 := by linarith [le_max_right (h 0) (h L)]
    obtain ⟨g0, hg01, _, hg03⟩ :=
      exists_unimodal L 0 L (L/2) V0 (L/2) h le_rfl le_rfl ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩ (hmono0 h) (hantiL h) hV1 hV2
    have hk := good_query_pos hg03 (hG g0 hg01)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    by_cases hx : 0 < x ∧ x < L
    · have P := adv L (next V0) j 0 L x V0 h le_rfl hx.1 hx.2 le_rfl (hmono0 h) (hantiL h)
        hV1 hV2 (by
          intro g hg1 hg2
          have := good_query (hG g hg1)
          rwa [hg2] at this)
      obtain ⟨_, _, p3, p4⟩ := P
      refine ⟨fun hj => ?_, fun hj => ?_⟩
      · have : j = 0 := by omega
        have := p3 this; linarith
      · have := p4 (by omega); linarith
    · have := ih (h x) j h (by
        intro g hg1
        have := good_query (hG g hg1)
        rwa [hg1 x hx] at this)
      obtain ⟨p3, p4⟩ := this
      refine ⟨fun hj => p3 (by omega), fun hj => ?_⟩
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · have : j = 1 := by omega
        subst this
        have e2 : (bookFib (1+1) : ℝ) = 2 := bfR2
        rw [e2]; linarith [p3 le_rfl]
      · linarith [p4 hj2, bfR_le_succ j]

theorem feasible_lt (n : ℕ) (hn : 2 ≤ n) (L : ℝ) (hL : L ∈ feasibleLengths n) :
    L < bookFib n := by
  obtain ⟨hL0, T, hT⟩ := hL
  refine (advJ L hL0 T n (fun _ => 0) (fun g _ m hm => ?_)).2 hn
  obtain ⟨h1, _, h3, h4⟩ := hT g m hm
  exact ⟨h1, h3, h4⟩

theorem feasible_le_one (n : ℕ) (hn : n ≤ 1) (L : ℝ) (hL : L ∈ feasibleLengths n) :
    L ≤ 1 := by
  obtain ⟨hL0, T, hT⟩ := hL
  refine (advJ L hL0 T n (fun _ => 0) (fun g _ m hm => ?_)).1 hn
  obtain ⟨h1, _, h3, h4⟩ := hT g m hm
  exact ⟨h1, h3, h4⟩

theorem upper_bound_recursion_core (n : ℕ) (hn : 2 ≤ n) (L : ℝ) (hL : L ∈ feasibleLengths n) :
    L < (bookFib (n - 1) : ℝ) + bookFib (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have := feasible_lt (k+2) hn L hL
  rw [bfR_ss] at this
  simpa using this

/-! ## Achievability: Fibonacci search -/

lemma cmp_left {f : ℝ → ℝ} {L m p q : ℝ} (hu : IsStrictUnimodalOn f L m) (hp : 0 ≤ p)
    (hpq : p < q) (hq : q ≤ L) (h : f p < f q) : p < m := by
  by_contra hm
  push_neg at hm
  have := hu.2.2 ⟨hm, by linarith⟩ ⟨by linarith, hq⟩ hpq
  linarith

lemma cmp_right {f : ℝ → ℝ} {L m p q : ℝ} (hu : IsStrictUnimodalOn f L m) (hp : 0 ≤ p)
    (hpq : p < q) (h : ¬ f p < f q) : m < q := by
  by_contra hm
  push_neg at hm
  exact h (hu.2.1 ⟨hp, by linarith⟩ ⟨by linarith, hm⟩ hpq)

noncomputable def fibTree (ε : ℝ) : ℕ → ℝ → ℝ → ℝ → ℝ → SearchTree ℝ (ℝ × ℝ)
  | 0, a, b, _, _ => stop (a, b)
  | k+1, a, b, c, fc =>
    query (if k = 0 then c + ε else a + b - c) (fun fx =>
      if c ≤ (if k = 0 then c + ε else a + b - c) then
        (if fc < fx then fibTree ε k c b (if k = 0 then c + ε else a + b - c) fx
          else fibTree ε k a (if k = 0 then c + ε else a + b - c) c fc)
      else
        (if fx < fc then fibTree ε k (if k = 0 then c + ε else a + b - c) b c fc
          else fibTree ε k a c (if k = 0 then c + ε else a + b - c) fx))

lemma fibTree_succ (ε : ℝ) (k : ℕ) (a b c fc : ℝ) (x : ℝ)
    (hx : x = if k = 0 then c + ε else a + b - c) :
    fibTree ε (k+1) a b c fc = query x (fun fx =>
      if c ≤ x then (if fc < fx then fibTree ε k c b x fx else fibTree ε k a x c fc)
      else (if fx < fc then fibTree ε k x b c fc else fibTree ε k a c x fx)) := by
  subst hx; rw [fibTree]

def LocatesOn (T : SearchTree ℝ (ℝ × ℝ)) (f : ℝ → ℝ) (m δ : ℝ) (n : ℕ) : Prop :=
  T.cost f ≤ n ∧ (T.result f).1 ≤ (T.result f).2 ∧ (T.result f).2 - (T.result f).1 ≤ δ ∧
    m ∈ Set.Icc (T.result f).1 (T.result f).2

lemma fibTree_zero (ε a b c fc δ m : ℝ) (f : ℝ → ℝ) (hab : a ≤ b) (hl : b - a ≤ δ)
    (hm : m ∈ Set.Icc a b) : LocatesOn (fibTree ε 0 a b c fc) f m δ 0 := by
  simp only [LocatesOn, fibTree, SearchTree.cost, SearchTree.result]
  exact ⟨le_rfl, hab, hl, hm⟩

lemma fibTree_correct (L δ u ε : ℝ) (hu : 0 < u) (hε : 0 < ε) (hεu : ε ≤ u)
    (hδ : u + ε ≤ δ) (f : ℝ → ℝ) (m : ℝ) (hf : IsStrictUnimodalOn f L m) :
    ∀ (j : ℕ) (a b c : ℝ), 0 ≤ a → b ≤ L → m ∈ Set.Icc a b →
      b - a = bookFib (j+2) * u → (c - a = bookFib j * u ∨ b - c = bookFib j * u) →
      LocatesOn (fibTree ε (j+1) a b c (f c)) f m δ (j+1) := by
  intro j
  induction j with
  | zero =>
    intro a b c ha hb hm hlen hc
    have hF2 : (bookFib 2 : ℝ) = 2 := bfR2
    have hF0 : (bookFib 0 : ℝ) = 1 := bfR0
    rw [hF2] at hlen
    rw [hF0] at hc
    have hc' : c = a + u := by rcases hc with h | h <;> linarith
    have hx : c ≤ c + ε := by linarith
    rw [fibTree_succ ε 0 a b c (f c) (c + ε) (by simp)]
    simp only [if_pos hx, LocatesOn, SearchTree.cost, SearchTree.result]
    by_cases hcmp : f c < f (c + ε)
    · rw [if_pos hcmp]
      have hmc := cmp_left hf (by linarith) (by linarith : c < c + ε) (by linarith) hcmp
      have := fibTree_zero ε c b (c + ε) (f (c + ε)) δ m f (by linarith) (by linarith)
        ⟨hmc.le, hm.2⟩
      simp only [LocatesOn] at this
      exact ⟨by omega, this.2⟩
    · rw [if_neg hcmp]
      have hmc := cmp_right hf (by linarith) (by linarith : c < c + ε) hcmp
      have := fibTree_zero ε a (c + ε) c (f c) δ m f (by linarith) (by linarith)
        ⟨hm.1, hmc.le⟩
      simp only [LocatesOn] at this
      exact ⟨by omega, this.2⟩
  | succ j ih =>
    intro a b c ha hb hm hlen hc
    have hF := bfR_ss (j+1)
    have hFj := bfR_ss j
    have hFpos := bfR_pos j
    have hlt := bfR_lt_succ (j+1) (by omega)
    have hne : j + 1 ≠ 0 := by omega
    rw [fibTree_succ ε (j+1) a b c (f c) (a + b - c) (by simp)]
    simp only [LocatesOn, SearchTree.cost, SearchTree.result]
    rw [show j + 1 + 2 = (j+1) + 2 from rfl] at hlen
    rw [hF] at hlen
    rcases hc with hc | hc
    · -- c left, x = a + b - c to the right
      have hcx : c < a + b - c := by nlinarith
      rw [if_pos hcx.le]
      by_cases hcmp : f c < f (a + b - c)
      · rw [if_pos hcmp]
        have hmc := cmp_left hf (by nlinarith) hcx (by nlinarith) hcmp
        have := ih c b (a + b - c) (by nlinarith) hb ⟨hmc.le, hm.2⟩ (by rw [hFj]; nlinarith)
          (Or.inl (by rw [hFj] at hlen; nlinarith))
        simp only [LocatesOn] at this
        exact ⟨by omega, this.2⟩
      · rw [if_neg hcmp]
        have hmc := cmp_right hf (by nlinarith) hcx hcmp
        have := ih a (a + b - c) c ha (by nlinarith) ⟨hm.1, hmc.le⟩ (by rw [hFj]; nlinarith)
          (Or.inr (by rw [hFj] at hlen; nlinarith))
        simp only [LocatesOn] at this
        exact ⟨by omega, this.2⟩
    · have hcx : a + b - c < c := by nlinarith
      rw [if_neg (not_le.mpr hcx)]
      by_cases hcmp : f (a + b - c) < f c
      · rw [if_pos hcmp]
        have hmc := cmp_left hf (by nlinarith) hcx (by nlinarith) hcmp
        have := ih (a + b - c) b c (by nlinarith) hb ⟨hmc.le, hm.2⟩ (by rw [hFj]; nlinarith)
          (Or.inl (by rw [hFj] at hlen; nlinarith))
        simp only [LocatesOn] at this
        exact ⟨by omega, this.2⟩
      · rw [if_neg hcmp]
        have hmc := cmp_right hf (by nlinarith) hcx hcmp
        have := ih a c (a + b - c) ha (by nlinarith) ⟨hm.1, hmc.le⟩ (by rw [hFj]; nlinarith)
          (Or.inr (by rw [hFj] at hlen; nlinarith))
        simp only [LocatesOn] at this
        exact ⟨by omega, this.2⟩

theorem achieve (n : ℕ) (hn : 2 ≤ n) (L δ : ℝ) (hL : 0 < L) (hLδ : L < bookFib n * δ) :
    ∃ T : SearchTree ℝ (ℝ × ℝ), Locates T L δ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hFpos : (0 : ℝ) < bookFib (k+2) := by linarith [bfR_pos (k+2)]
  set u := L / bookFib (k+2) with hu_def
  have hu : 0 < u := div_pos hL hFpos
  have hLu : L = bookFib (k+2) * u := by rw [hu_def]; field_simp
  have huδ : u < δ := by
    rw [hLu] at hLδ
    by_contra hh; push_neg at hh
    have := mul_le_mul_of_nonneg_left hh hFpos.le
    linarith
  set ε := min u (δ - u) with hε_def
  have hε : 0 < ε := lt_min hu (by linarith)
  have hεu : ε ≤ u := min_le_left _ _
  have hεδ : u + ε ≤ δ := by linarith [min_le_right u (δ - u)]
  refine ⟨query (bookFib (k+1) * u) (fun v => fibTree ε (k+1) 0 L (bookFib (k+1) * u) v), ?_⟩
  intro f m hf
  have hF := bfR_ss k
  have hFk := bfR_pos k
  have := fibTree_correct L δ u ε hu hε hεu hεδ f m hf k 0 L (bookFib (k+1) * u) le_rfl le_rfl
    hf.1 (by linarith) (Or.inr (by rw [hLu, hF]; ring))
  simp only [LocatesOn] at this
  simp only [SearchTree.cost, SearchTree.result]
  exact ⟨by omega, this.2⟩

theorem achieve_small (n : ℕ) (L δ : ℝ) (hL : 0 < L) (hLδ : L ≤ δ) :
    ∃ T : SearchTree ℝ (ℝ × ℝ), Locates T L δ n := by
  refine ⟨stop (0, L), fun f m hf => ?_⟩
  simp only [SearchTree.cost, SearchTree.result]
  exact ⟨by omega, hL.le, by linarith, hf.1⟩

theorem feas_small (n : ℕ) (hn : n ≤ 1) : feasibleLengths n = Set.Ioc 0 1 := by
  ext L
  constructor
  · intro hL
    exact ⟨hL.1, feasible_le_one n hn L hL⟩
  · intro hL
    exact ⟨hL.1, achieve_small n L 1 hL.1 hL.2⟩

theorem feas_big (n : ℕ) (hn : 2 ≤ n) : feasibleLengths n = Set.Ioo 0 (bookFib n : ℝ) := by
  ext L
  constructor
  · intro hL
    exact ⟨hL.1, feasible_lt n hn L hL⟩
  · intro hL
    exact ⟨hL.1, achieve n hn L 1 hL.1 (by rw [mul_one]; exact hL.2)⟩

theorem lengths_below_attainable_core (n : ℕ) (hn : 2 ≤ n) (L : ℝ) (hL0 : 0 < L)
    (hL : L < (bookFib (n - 1) : ℝ) + bookFib (n - 2)) :
    L ∈ feasibleLengths n := by
  rw [feas_big n hn]
  refine ⟨hL0, ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [bfR_ss]
  simpa using hL

theorem one_evaluation_value_core : IsLUB (feasibleLengths 1) (1 : ℝ) := by
  rw [feas_small 1 le_rfl]
  exact isLUB_Ioc zero_lt_one

theorem two_evaluations_value_core : IsLUB (feasibleLengths 2) (2 : ℝ) := by
  rw [feas_big 2 le_rfl, bfR2]
  exact isLUB_Ioo (by norm_num)

theorem fibonacci_search_optimal_core (n : ℕ) :
    IsLUB (feasibleLengths n) (bookFib n : ℝ) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have h1 : (bookFib n : ℝ) = 1 := by
      interval_cases n
      · exact bfR0
      · exact bfR1
    rw [feas_small n (by omega), h1]
    exact isLUB_Ioc zero_lt_one
  · rw [feas_big n hn]
    exact isLUB_Ioo (by linarith [bfR_pos n])

lemma bf20 : bookFib 20 = 10946 := by decide

theorem twenty_evaluations_core :
    10000 < bookFib 20 ∧
    ∀ L : ℝ, 0 < L → ∃ T : SearchTree ℝ (ℝ × ℝ), Locates T L (L / 10 ^ 4) 20 := by
  refine ⟨by rw [bf20]; norm_num, fun L hL => ?_⟩
  refine achieve 20 (by norm_num) L (L / 10 ^ 4) hL ?_
  have : (bookFib 20 : ℝ) = 10946 := by exact_mod_cast bf20
  rw [this]
  nlinarith

end BellmanDP.Fibonacci

open BellmanDP.Fibonacci


theorem solution :
    IsLUB (feasibleLengths 1) (1 : ℝ) := by
  exact one_evaluation_value_core
