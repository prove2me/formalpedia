-- Prove2me | solution 1 for Freiman.lower_forced_reflections
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-12T21:05:20.010794+00:00
-- url     : https://prove2.me/submissions/a41c3e90-3950-46a5-83aa-60df9914d878

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic
import Definitions.Def_Freiman_lowerCover
import Theorems.Thm_Freiman_prefixEval_difference
import Theorems.Thm_Freiman_continuant_denominator_pos
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_range
import Definitions.Def_Freiman_lowerInitialEntry
open Freiman

attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

private def fr_SmallT : List (List ℕ+) := [[3],[2,1,3]]
private def fr_BigT : List (List ℕ+) := [[1,3],[1,2,1,3]]
private noncomputable def fr_fam (n : ℕ) (u : Bool) : List (List ℕ+) :=
  if (n % 2 = 0) = (!u) then fr_SmallT else fr_BigT

private theorem fr_suffix_mem (w : List ℕ+) (u short : Bool) :
    lowerEndpointSuffix w u short ∈ fr_fam w.length u := by
  unfold lowerEndpointSuffix fr_fam fr_SmallT fr_BigT
  split_ifs <;> simp

private theorem fr_pe_append (a b : List ℕ+) (x : ℝ) :
    prefixEval (a ++ b) x = prefixEval a (prefixEval b x) := by
  induction a with
  | nil => rfl
  | cons h t ih => simp [prefixEval, ih]

private theorem fr_pe_nonneg (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ prefixEval w x := by
  induction w with
  | nil => exact hx
  | cons a t ih =>
    simp only [prefixEval]
    have : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    apply div_nonneg zero_le_one
    linarith

private theorem fr_pe_mono (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x < y) :
    (w.length % 2 = 0 → prefixEval w x < prefixEval w y) ∧
    (w.length % 2 = 1 → prefixEval w y < prefixEval w x) := by
  induction w with
  | nil => exact ⟨fun _ => hxy, fun h => by simp at h⟩
  | cons a t ih =>
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    have px := fr_pe_nonneg t x hx
    have py := fr_pe_nonneg t y hy
    constructor
    · intro he
      have ho : t.length % 2 = 1 := by simp at he; omega
      have := ih.2 ho
      simp only [prefixEval]
      apply one_div_lt_one_div_of_lt <;> linarith
    · intro ho
      have he : t.length % 2 = 0 := by simp at ho; omega
      have := ih.1 he
      simp only [prefixEval]
      apply one_div_lt_one_div_of_lt <;> linarith

private theorem fr_equal_shape (p : LowerPair) (u : Bool) : ∃ t1 t2, lowerEqualWords p u = (p.1 ++ t1, p.2 ++ t2) ∧
    t1 ∈ fr_fam p.1.length u ∧ t2 ∈ fr_fam p.2.length u := by
  unfold lowerEqualWords lowerNormalize
  by_cases hc : lowerWidth p.2 ≤ lowerWidth p.1
  · simp only [hc, ↓reduceIte]
    exact ⟨_, _, rfl, fr_suffix_mem _ _ _, fr_suffix_mem _ _ _⟩
  · simp only [hc, ↓reduceIte]
    exact ⟨_, _, rfl, fr_suffix_mem _ _ _, fr_suffix_mem _ _ _⟩

private theorem fr_natural_shape (p : LowerPair) (u : Bool) : ∃ t1 t2, lowerNaturalWords p u = (p.1 ++ t1, p.2 ++ t2) ∧
    t1 ∈ fr_fam p.1.length u ∧ t2 ∈ fr_fam p.2.length u :=
  ⟨_, _, rfl, fr_suffix_mem _ _ _, fr_suffix_mem _ _ _⟩

private theorem fr_virt_mem (n : ℕ) (u : Bool) (hu : u = decide (n % 2 = 0)) (t : List ℕ+)
    (ht : t ∈ fr_fam (n+1) u) : 1 :: t ∈ fr_fam n u := by
  subst hu
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h' : (n+1) % 2 = 1 := by omega
    simp [fr_fam, fr_SmallT, fr_BigT, h, h'] at ht ⊢
    rcases ht with rfl | rfl <;> simp
  · have h' : (n+1) % 2 = 0 := by omega
    simp [fr_fam, fr_SmallT, fr_BigT, h, h'] at ht ⊢
    rcases ht with rfl | rfl <;> simp

private theorem fr_words_shape (p : LowerPair) (u : Bool) : ∃ t1 t2, lowerEndpointWords p u = (p.1 ++ t1, p.2 ++ t2) ∧
    t1 ∈ fr_fam p.1.length u ∧ t2 ∈ fr_fam p.2.length u := by
  unfold lowerEndpointWords
  by_cases hpar : p.1.length % 2 = p.2.length % 2
  · rw [if_pos hpar]
    exact fr_equal_shape p u
  · rw [if_neg hpar]
    by_cases hlw : lowerWidth p.2 ≤ lowerWidth p.1
    · simp only [hlw, ↓reduceIte]
      by_cases hu : u = decide (p.1.length % 2 = 0)
      · rw [if_pos hu]
        obtain ⟨t1, t2, he, h1, h2⟩ := fr_equal_shape (p.1 ++ [1], p.2) u
        refine ⟨1 :: t1, t2, ?_, ?_, h2⟩
        · rw [he]
          simp
        · exact fr_virt_mem p.1.length u hu t1 (by simpa using h1)
      · rw [if_neg hu]
        exact fr_natural_shape p u
    · simp only [hlw, ↓reduceIte]
      by_cases hu : u = decide (p.2.length % 2 = 0)
      · rw [if_pos hu]
        obtain ⟨t1, t2, he, h1, h2⟩ := fr_equal_shape (p.1, p.2 ++ [1]) u
        refine ⟨t1, 1 :: t2, ?_, h1, ?_⟩
        · rw [he]
          simp
        · exact fr_virt_mem p.2.length u hu t2 (by simpa using h2)
      · rw [if_neg hu]
        exact fr_natural_shape p u

private theorem fr_tails : 0 < lowerAlpha ∧ lowerAlpha < lowerBeta ∧ lowerBeta < 1 ∧
    lowerTau ∈ Set.Icc lowerAlpha lowerBeta ∧
    lowerAlpha*(3+lowerBeta)=1 ∧ lowerBeta*(1+lowerAlpha)=1 := by
  have h21 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 21)
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have n21 := Real.sqrt_nonneg (21:ℝ)
  have n3 := Real.sqrt_nonneg (3:ℝ)
  have s21l : (9/2:ℝ) < Real.sqrt 21 := by nlinarith
  have s21h : Real.sqrt 21 < (5:ℝ) := by nlinarith
  have s3l : (3/2:ℝ) < Real.sqrt 3 := by nlinarith
  have s3h : Real.sqrt 3 < (7/4:ℝ) := by nlinarith
  dsimp [lowerAlpha,lowerBeta,lowerTau,Set.mem_Icc]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · constructor <;> linarith
  constructor <;> nlinarith

private theorem fr_step_invariant (a : ℕ+) (ha : (a:ℕ) ≤ 3) (x : ℝ)
    (hx : x ∈ Set.Icc lowerAlpha lowerBeta) :
    1/((a:ℝ)+x) ∈ Set.Icc lowerAlpha lowerBeta := by
  have ha0 : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast a.pos
  have ha3 : (a:ℝ) ≤ 3 := by exact_mod_cast ha
  have hp : 0 < (a:ℝ)+x := by linarith [fr_tails.1,hx.1]
  constructor
  · apply (le_div_iff₀ hp).mpr
    calc lowerAlpha*((a:ℝ)+x) ≤ lowerAlpha*(3+lowerBeta) :=
          mul_le_mul_of_nonneg_left (by linarith [hx.2]) fr_tails.1.le
      _ = 1 := fr_tails.2.2.2.2.1
  · apply (div_le_iff₀ hp).mpr
    calc 1 = lowerBeta*(1+lowerAlpha) := fr_tails.2.2.2.2.2.symm
      _ ≤ lowerBeta*((a:ℝ)+x) :=
          mul_le_mul_of_nonneg_left (by linarith [hx.1]) (by linarith [fr_tails.1,fr_tails.2.1])

private theorem fr_word_invariant (w : List ℕ+) (hw : ∀ a∈w, (a:ℕ) ≤ 3)
    (x : ℝ) (hx : x ∈ Set.Icc lowerAlpha lowerBeta) :
    prefixEval w x ∈ Set.Icc lowerAlpha lowerBeta := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    apply fr_step_invariant a (hw a (by simp))
    exact ih (by intro b hb; exact hw b (by simp [hb]))

private theorem fr_fam_invariant (w : List ℕ+) (n : ℕ) (u : Bool)
    (hw : w ∈ fr_fam n u) : prefixEval w lowerTau ∈ Set.Icc lowerAlpha lowerBeta := by
  apply fr_word_invariant w _ lowerTau fr_tails.2.2.2.1
  unfold fr_fam fr_SmallT fr_BigT at hw
  split_ifs at hw <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at hw <;>
    rcases hw with rfl | rfl <;> norm_num

private theorem fr_pe_order (w : List ℕ+) (x y : ℝ) (hx : 0≤x) (hy : 0≤y) (hxy : x≤y) :
    (w.length%2=0 → prefixEval w x ≤ prefixEval w y) ∧
    (w.length%2=1 → prefixEval w y ≤ prefixEval w x) := by
  rcases hxy.eq_or_lt with rfl | hxy
  · exact ⟨fun _ => le_rfl,fun _ => le_rfl⟩
  · exact ⟨fun he => ((fr_pe_mono w x y hx hy hxy).1 he).le,
      fun ho => ((fr_pe_mono w x y hx hy hxy).2 ho).le⟩

private noncomputable def fr_lo (w : List ℕ+) := min (prefixEval w lowerAlpha) (prefixEval w lowerBeta)
private noncomputable def fr_hi (w : List ℕ+) := max (prefixEval w lowerAlpha) (prefixEval w lowerBeta)

private theorem fr_pe_bounds (w : List ℕ+) (x : ℝ) (hx : x ∈ Set.Icc lowerAlpha lowerBeta) :
    fr_lo w ≤ prefixEval w x ∧ prefixEval w x ≤ fr_hi w := by
  have ha := fr_pe_order w lowerAlpha x fr_tails.1.le (by linarith [fr_tails.1,hx.1]) hx.1
  have hb := fr_pe_order w x lowerBeta (by linarith [fr_tails.1,hx.1])
    (by linarith [fr_tails.1,fr_tails.2.1]) hx.2
  rcases Nat.mod_two_eq_zero_or_one w.length with h | h
  · exact ⟨le_trans (min_le_left _ _) (ha.1 h),le_trans (hb.1 h) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (hb.2 h),le_trans (ha.2 h) (le_max_left _ _)⟩

private theorem fr_endpoint_bounds (p : LowerPair) (upper : Bool) :
    4+fr_lo p.1+fr_lo p.2 ≤ lowerEndpoint p upper ∧
      lowerEndpoint p upper ≤ 4+fr_hi p.1+fr_hi p.2 := by
  obtain ⟨u,v,he,hu,hv⟩ := fr_words_shape p upper
  have h1 := fr_pe_bounds p.1 _ (fr_fam_invariant u _ _ hu)
  have h2 := fr_pe_bounds p.2 _ (fr_fam_invariant v _ _ hv)
  simp only [lowerEndpoint,he,fr_pe_append]
  constructor <;> linarith

private theorem fr_cover_bounds (p : LowerPair) (x : ℝ) (hx : x∈lowerCover p) :
    4+fr_lo p.1+fr_lo p.2 ≤ x ∧ x ≤ 4+fr_hi p.1+fr_hi p.2 :=
  ⟨le_trans (fr_endpoint_bounds p false).1 hx.1,
    le_trans hx.2 (fr_endpoint_bounds p true).2⟩

private theorem fr_width_hull (w : List ℕ+) : fr_hi w-fr_lo w = lowerWidth w := by
  simp only [fr_hi,fr_lo,lowerWidth,max_sub_min_eq_abs,abs_sub_comm]

private theorem fr_hull_parity (w : List ℕ+) :
    (w.length%2=0 → fr_lo w=prefixEval w lowerAlpha ∧ fr_hi w=prefixEval w lowerBeta) ∧
    (w.length%2=1 → fr_lo w=prefixEval w lowerBeta ∧ fr_hi w=prefixEval w lowerAlpha) := by
  have h := fr_pe_order w lowerAlpha lowerBeta fr_tails.1.le
    (by linarith [fr_tails.1,fr_tails.2.1]) fr_tails.2.1.le
  exact ⟨fun he => ⟨min_eq_left (h.1 he),max_eq_right (h.1 he)⟩,
    fun ho => ⟨min_eq_right (h.2 ho),max_eq_left (h.2 ho)⟩⟩

private theorem fr_gap_order :
    prefixEval [2] lowerAlpha < prefixEval [1] lowerBeta := by
  have ha := fr_tails.1
  have hb := fr_tails.2.2.1
  have hb0 : 0 < lowerBeta := lt_trans ha fr_tails.2.1
  norm_num [prefixEval]
  simpa only [one_div] using one_div_lt_one_div_of_lt
    (show (0:ℝ) < 1+lowerBeta by linarith)
    (show (1:ℝ)+lowerBeta < 2+lowerAlpha by linarith)

private theorem fr_overlap_gap (p : LowerPair) (hg : lowerGood p) :
    |prefixEval (lowerNormalize p).1 (prefixEval [1] lowerBeta) -
      prefixEval (lowerNormalize p).1 (prefixEval [2] lowerAlpha)| ≤
        lowerWidth (lowerNormalize p).2 := by
  rcases hg with ⟨x,hx1,hx2⟩
  have h1 := fr_cover_bounds (lowerChild p ([1],[])) x hx1
  have h2 := fr_cover_bounds (lowerChild p ([2],[])) x hx2
  simp only [lowerChild,List.reverse_cons,List.reverse_nil,List.nil_append,List.append_nil] at h1 h2
  let w := (lowerNormalize p).1
  let v := (lowerNormalize p).2
  change 4+fr_lo (w++[1])+fr_lo v ≤ x ∧ x ≤ 4+fr_hi (w++[1])+fr_hi v at h1
  change 4+fr_lo (w++[2])+fr_lo v ≤ x ∧ x ≤ 4+fr_hi (w++[2])+fr_hi v at h2
  change |prefixEval w (prefixEval [1] lowerBeta) - prefixEval w (prefixEval [2] lowerAlpha)| ≤ lowerWidth v
  rw [← fr_width_hull v]
  have hm := fr_pe_mono w (prefixEval [2] lowerAlpha) (prefixEval [1] lowerBeta)
    (fr_pe_nonneg _ _ fr_tails.1.le)
    (fr_pe_nonneg _ _ (by linarith [fr_tails.1,fr_tails.2.1])) fr_gap_order
  rcases Nat.mod_two_eq_zero_or_one w.length with he | ho
  · have ho1 : (w++[1]).length%2=1 := by simp [Nat.add_mod,he]
    have ho2 : (w++[2]).length%2=1 := by simp [Nat.add_mod,he]
    rw [(fr_hull_parity (w++[1])).2 ho1 |>.1] at h1
    rw [(fr_hull_parity (w++[2])).2 ho2 |>.2] at h2
    simp only [fr_pe_append] at h1 h2
    rw [abs_of_nonneg (sub_nonneg.mpr (hm.1 he).le)]
    linarith [h1.1,h2.2]
  · have he1 : (w++[1]).length%2=0 := by simp [Nat.add_mod,ho]
    have he2 : (w++[2]).length%2=0 := by simp [Nat.add_mod,ho]
    rw [(fr_hull_parity (w++[1])).1 he1 |>.2] at h1
    rw [(fr_hull_parity (w++[2])).1 he2 |>.1] at h2
    simp only [fr_pe_append] at h1 h2
    rw [abs_of_nonpos (sub_nonpos.mpr (hm.2 ho).le)]
    linarith [h1.2,h2.1]



private theorem wg_pe_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

private theorem wg_cd_eq (w : List ℕ+) :
    lowerCD w = (wordContinuantPrevQ w, wordContinuantQ w) := by
  have h : ∀ (v : List ℕ) (m : (ℕ × ℕ) × (ℕ × ℕ)),
      (v.foldl (fun d a => ((d.1.2, (a : ℕ) * d.1.2 + d.1.1),
        (d.2.2, (a : ℕ) * d.2.2 + d.2.1))) m).2 =
      v.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) m.2 := by
    intro v
    induction v with
    | nil => intro m; rfl
    | cons a v ih =>
      intro m
      simp only [List.foldl_cons]
      rw [ih]
      simp only [Nat.add_comm]
  simpa [lowerCD, wordContinuantPrevQ, wordContinuantQ, wordContinuantData]
    using (h (w.flatMap fun a => [(a : ℕ)]) ((1,0),(0,1))).symm

private theorem wg_q_pos (w : List ℕ+) : 0 < ((lowerCD w).2 : ℝ) := by
  rw [wg_cd_eq]
  exact_mod_cast continuant_denominator_pos w

private theorem wg_radical_data :
    let s := Real.sqrt (21 : ℝ)
    s ^ 2 = 21 ∧ 0 ≤ s ∧ 41 / 9 < s ∧ 49 / 11 < s ∧ s < 5 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  dsimp
  refine ⟨hs, hn, ?_, ?_, ?_⟩ <;> nlinarith

private theorem wg_tail_values :
    prefixEval [1] lowerBeta = (Real.sqrt 21 + 1) / 10 ∧
    prefixEval [2] lowerAlpha = (9 - Real.sqrt 21) / 10 ∧
    prefixEval [2] lowerBeta = (Real.sqrt 21 - 1) / 10 := by
  have hs := wg_radical_data.1
  have hlo := wg_radical_data.2.2.2.1
  constructor
  · dsimp [prefixEval, lowerBeta]
    norm_num only [PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat]
    rw [div_eq_iff (by nlinarith : (1 : ℝ) + (Real.sqrt 21 - 3) / 2 ≠ 0)]
    field_simp
    nlinarith
  constructor
  · dsimp [prefixEval, lowerAlpha]
    rw [div_eq_iff (by nlinarith : (2 : ℝ) + (Real.sqrt 21 - 3) / 6 ≠ 0)]
    field_simp
    nlinarith
  · dsimp [prefixEval, lowerBeta]
    rw [div_eq_iff (by nlinarith : (2 : ℝ) + (Real.sqrt 21 - 3) / 2 ≠ 0)]
    field_simp
    nlinarith

private theorem wg_gap_after_two (w : List ℕ+) :
    lowerWidth (w ++ [2]) <
      |prefixEval w (prefixEval [1] lowerBeta) -
        prefixEval w (prefixEval [2] lowerAlpha)| := by
  let s : ℝ := Real.sqrt 21
  let A : ℝ := prefixEval [1] lowerBeta
  let B : ℝ := prefixEval [2] lowerAlpha
  let Y : ℝ := prefixEval [2] lowerBeta
  let P : ℝ := ((lowerCD w).1 : ℝ)
  let Q : ℝ := ((lowerCD w).2 : ℝ)
  let r : ℝ := lowerRatio w
  have hs2 : s ^ 2 = 21 := wg_radical_data.1
  have hs0 : 0 ≤ s := wg_radical_data.2.1
  have hs41 : 41 / 9 < s := wg_radical_data.2.2.1
  have hs49 : 49 / 11 < s := wg_radical_data.2.2.2.1
  have hs5 : s < 5 := wg_radical_data.2.2.2.2
  have hA : A = (s + 1) / 10 := by simpa [A, s] using wg_tail_values.1
  have hB : B = (9 - s) / 10 := by simpa [B, s] using wg_tail_values.2.1
  have hY : Y = (s - 1) / 10 := by simpa [Y, s] using wg_tail_values.2.2
  have hYA : Y < B ∧ B < A := by rw [hA, hB, hY]; constructor <;> linarith
  have hAi : A ∈ Set.Icc (0 : ℝ) 1 := by rw [hA]; constructor <;> linarith
  have hBi : B ∈ Set.Icc (0 : ℝ) 1 := by rw [hB]; constructor <;> linarith
  have hYi : Y ∈ Set.Icc (0 : ℝ) 1 := by rw [hY]; constructor <;> linarith
  have hQ : 0 < Q := by simpa [Q] using wg_q_pos w
  have hP : 0 ≤ P := by simp [P]
  have hrange : 0 ≤ r ∧ r ≤ 1 := by simpa [r] using lowerEarlyTerminal_ratio_range w
  have hPQ : P = r * Q := by
    dsimp [P, Q, r, lowerRatio]
    field_simp [ne_of_gt (wg_q_pos w)]
  have hfacA : 0 < Q + A * P := add_pos_of_pos_of_nonneg hQ (mul_nonneg hAi.1 hP)
  have hfacB : 0 < Q + B * P := add_pos_of_pos_of_nonneg hQ (mul_nonneg hBi.1 hP)
  have hfacY : 0 < Q + Y * P := add_pos_of_pos_of_nonneg hQ (mul_nonneg hYi.1 hP)
  have hbracket :
      0 < (A - B) * (1 + r * Y) - (B - Y) * (1 + r * A) := by
    have heq : (A - B) * (1 + r * Y) - (B - Y) * (1 + r * A) =
        ((11*s - 49) + (1-r)*(9*s-41)) / 50 := by
      rw [hA, hB, hY]
      field_simp
      nlinarith
    rw [heq]
    have h1 : 0 < 11*s - 49 := by linarith
    have h2 : 0 < 9*s - 41 := by linarith
    have h3 : 0 ≤ 1-r := by linarith [hrange.2]
    positivity
  have hcore :
      (B-Y) * (Q+A*P) < (A-B) * (Q+Y*P) := by
    have heq : (A-B)*(Q+Y*P) - (B-Y)*(Q+A*P) =
        Q * ((A-B)*(1+r*Y) - (B-Y)*(1+r*A)) := by
      rw [hPQ]
      ring
    nlinarith [mul_pos hQ hbracket]
  unfold lowerWidth
  rw [wg_pe_append, wg_pe_append]
  change |prefixEval w Y - prefixEval w B| < |prefixEval w A - prefixEval w B|
  rw [prefixEval_difference w Y B hYi hBi,
    prefixEval_difference w A B hAi hBi]
  rw [abs_of_neg (sub_neg.mpr hYA.1), abs_of_pos (sub_pos.mpr hYA.2)]
  have hPrev : (wordContinuantPrevQ w : ℝ) = P := by
    dsimp [P]
    exact_mod_cast (congrArg Prod.fst (wg_cd_eq w)).symm
  have hDen : (wordContinuantQ w : ℝ) = Q := by
    dsimp [Q]
    exact_mod_cast (congrArg Prod.snd (wg_cd_eq w)).symm
  rw [hPrev, hDen]
  rw [show -(Y-B) = B-Y by ring]
  change (B-Y) / ((Q+Y*P)*(Q+B*P)) < (A-B) / ((Q+A*P)*(Q+B*P))
  rw [div_lt_div_iff₀ (mul_pos hfacY hfacB) (mul_pos hfacA hfacB)]
  have hrearr :
      (B-Y)*((Q+A*P)*(Q+B*P)) = (Q+B*P)*((B-Y)*(Q+A*P)) ∧
      (A-B)*((Q+Y*P)*(Q+B*P)) = (Q+B*P)*((A-B)*(Q+Y*P)) := by
    constructor <;> ring
  rw [hrearr.1, hrearr.2]
  exact mul_lt_mul_of_pos_left hcore hfacB



private theorem wt_cd_eq (w : List ℕ+) :
    lowerCD w = (wordContinuantPrevQ w, wordContinuantQ w) := by
  have h : ∀ (v : List ℕ) (m : (ℕ × ℕ) × (ℕ × ℕ)),
      (v.foldl (fun d a => ((d.1.2, (a : ℕ) * d.1.2 + d.1.1),
        (d.2.2, (a : ℕ) * d.2.2 + d.2.1))) m).2 =
      v.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) m.2 := by
    intro v
    induction v with
    | nil => intro m; rfl
    | cons a v ih =>
      intro m
      simp only [List.foldl_cons]
      rw [ih]
      simp only [Nat.add_comm]
  simpa [lowerCD, wordContinuantPrevQ, wordContinuantQ, wordContinuantData]
    using (h (w.flatMap fun a => [(a : ℕ)]) ((1,0),(0,1))).symm

private theorem wt_q_pos (w : List ℕ+) : 0 < ((lowerCD w).2 : ℝ) := by
  rw [wt_cd_eq]
  exact_mod_cast continuant_denominator_pos w

private theorem wt_tails :
    lowerAlpha ∈ Set.Icc (0 : ℝ) 1 ∧
    lowerBeta ∈ Set.Icc (0 : ℝ) 1 ∧ lowerAlpha < lowerBeta := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  have hlo : 3 < Real.sqrt (21 : ℝ) := by nlinarith
  have hhi : Real.sqrt (21 : ℝ) < 5 := by nlinarith
  dsimp [lowerAlpha, lowerBeta, Set.mem_Icc]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  · linarith

private theorem wt_width_formula (w : List ℕ+) :
    lowerWidth w = (lowerBeta - lowerAlpha) /
      ((((lowerCD w).1 : ℝ) * lowerAlpha + (lowerCD w).2) *
       (((lowerCD w).1 : ℝ) * lowerBeta + (lowerCD w).2)) := by
  unfold lowerWidth
  rw [prefixEval_difference w lowerBeta lowerAlpha wt_tails.2.1 wt_tails.1]
  rw [abs_of_pos (sub_pos.mpr wt_tails.2.2), wt_cd_eq]
  ring

private theorem wt_width_pos (w : List ℕ+) : 0 < lowerWidth w := by
  rw [wt_width_formula]
  have hq := wt_q_pos w
  have ha : 0 ≤ lowerAlpha := wt_tails.1.1
  have hb : 0 ≤ lowerBeta := wt_tails.2.1.1
  exact div_pos (sub_pos.mpr wt_tails.2.2) (mul_pos (by positivity) (by positivity))

private theorem fr_width_mono_cd (u v : List ℕ+)
    (hc : ((lowerCD u).1:ℝ) ≤ ((lowerCD v).1:ℝ))
    (hd : ((lowerCD u).2:ℝ) ≤ ((lowerCD v).2:ℝ)) : lowerWidth v ≤ lowerWidth u := by
  rw [wt_width_formula v,wt_width_formula u]
  have ha := fr_tails.1.le
  have hb := (lt_trans fr_tails.1 fr_tails.2.1).le
  have hu := wt_q_pos u
  have hv := wt_q_pos v
  apply div_le_div_of_nonneg_left (sub_nonneg.mpr fr_tails.2.1.le) (by positivity)
  apply mul_le_mul
  · exact add_le_add (mul_le_mul_of_nonneg_right hc ha) hd
  · exact add_le_add (mul_le_mul_of_nonneg_right hc hb) hd
  · positivity
  · positivity

private theorem fr_width_three_le_two (w : List ℕ+) :
    lowerWidth (w++[3]) ≤ lowerWidth (w++[2]) := by
  have h2 : lowerCD (w++[2]) = ((lowerCD w).2,(lowerCD w).1+2*(lowerCD w).2) := by
    simp [lowerCD,List.foldl_append]
  have h3 : lowerCD (w++[3]) = ((lowerCD w).2,(lowerCD w).1+3*(lowerCD w).2) := by
    simp [lowerCD,List.foldl_append]
  apply fr_width_mono_cd
  · rw [h2,h3]
  · rw [h2,h3]
    push_cast
    nlinarith [wt_q_pos w]

private theorem fr_width_eleven_le_two (w : List ℕ+) :
    lowerWidth (w++[1,1]) ≤ lowerWidth (w++[2]) := by
  have h2 : lowerCD (w++[2]) = ((lowerCD w).2,(lowerCD w).1+2*(lowerCD w).2) := by
    simp [lowerCD,List.foldl_append]
  have h11 : lowerCD (w++[1,1]) =
      ((lowerCD w).1+(lowerCD w).2,(lowerCD w).1+2*(lowerCD w).2) := by
    simp [lowerCD,List.foldl_append]
    omega
  apply fr_width_mono_cd
  · rw [h2,h11]
    push_cast
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  · rw [h2,h11]

private theorem fr_one_beta : prefixEval [1] lowerBeta < lowerBeta ∧
    lowerAlpha < prefixEval [1] lowerBeta ∧ prefixEval [1] lowerAlpha = lowerBeta := by
  have ha := fr_tails.1
  have hb := lt_trans fr_tails.1 fr_tails.2.1
  have he : prefixEval [1] lowerAlpha = lowerBeta := by
    calc prefixEval [1] lowerAlpha = 1/(1+lowerAlpha) := by norm_num [prefixEval]
      _ = lowerBeta := (div_eq_iff (by linarith)).mpr fr_tails.2.2.2.2.2.symm
  refine ⟨?_,?_,he⟩
  · exact lt_of_lt_of_eq ((fr_pe_mono [1] lowerAlpha lowerBeta ha.le hb.le
      fr_tails.2.1).2 (by decide)) he
  · calc lowerAlpha = 1/(3+lowerBeta) :=
          ((div_eq_iff (by linarith)).mpr fr_tails.2.2.2.2.1.symm).symm
      _ < 1/(1+lowerBeta) := one_div_lt_one_div_of_lt (by linarith) (by linarith)
      _ = prefixEval [1] lowerBeta := by norm_num [prefixEval]

private theorem fr_width_one_lt (w : List ℕ+) : lowerWidth (w++[1]) < lowerWidth w := by
  have ha := fr_pe_mono w lowerAlpha (prefixEval [1] lowerBeta)
    fr_tails.1.le (by linarith [fr_tails.1,fr_one_beta.2.1]) fr_one_beta.2.1
  have hb := fr_pe_mono w (prefixEval [1] lowerBeta) lowerBeta
    (by linarith [fr_tails.1,fr_one_beta.2.1]) (lt_trans fr_tails.1 fr_tails.2.1).le fr_one_beta.1
  rw [← fr_width_hull w,← fr_width_hull (w++[1])]
  rcases Nat.mod_two_eq_zero_or_one w.length with he | ho
  · have ho1 : (w++[1]).length%2=1 := by simp [Nat.add_mod,he]
    rw [(fr_hull_parity w).1 he |>.1,(fr_hull_parity w).1 he |>.2,
      (fr_hull_parity (w++[1])).2 ho1 |>.1,(fr_hull_parity (w++[1])).2 ho1 |>.2]
    simp only [fr_pe_append,fr_one_beta.2.2]
    linarith [ha.1 he]
  · have he1 : (w++[1]).length%2=0 := by simp [Nat.add_mod,ho]
    rw [(fr_hull_parity w).2 ho |>.1,(fr_hull_parity w).2 ho |>.2,
      (fr_hull_parity (w++[1])).1 he1 |>.1,(fr_hull_parity (w++[1])).1 he1 |>.2]
    simp only [fr_pe_append,fr_one_beta.2.2]
    linarith [ha.2 ho]

private theorem forced_reflections_core (p : LowerPair) (hg : lowerGood p) :
    let q := lowerNormalize p
    lowerWidth (q.1++[2]) < lowerWidth q.2 ∧
    lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
    lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧
    lowerWidth (q.2++[1]) < lowerWidth q.1 := by
  let q := lowerNormalize p
  have hmain := lt_of_lt_of_le (wg_gap_after_two q.1) (fr_overlap_gap p hg)
  have hn : lowerWidth q.2 ≤ lowerWidth q.1 := by
    unfold q lowerNormalize
    split_ifs with h
    · exact h
    · exact (lt_of_not_ge h).le
  exact ⟨hmain,lt_of_le_of_lt (fr_width_three_le_two q.1) hmain,
    lt_of_le_of_lt (fr_width_eleven_le_two q.1) hmain,
    lt_of_lt_of_le (fr_width_one_lt q.2) hn⟩


theorem solution (p : LowerPair) (hg : lowerGood p) (hb : lowerParameterBox p) :
    let q := lowerNormalize p
    lowerWidth (q.1 ++ [2]) < lowerWidth q.2 ∧
    lowerWidth (q.1 ++ [3]) < lowerWidth q.2 ∧
    lowerWidth (q.1 ++ [1,1]) < lowerWidth q.2 ∧
    lowerWidth (q.2 ++ [1]) < lowerWidth q.1 := by
  exact forced_reflections_core p hg

#print axioms solution
