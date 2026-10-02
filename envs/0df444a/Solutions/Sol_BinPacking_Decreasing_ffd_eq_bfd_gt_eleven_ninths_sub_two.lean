-- Prove2me | solution 1 for BinPacking.Decreasing.ffd_eq_bfd_gt_eleven_ninths_sub_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T21:53:27.022929+00:00
-- url     : https://prove2.me/submissions/264818b5-eb42-4d46-b302-a2207276251a

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model

set_option autoImplicit false

namespace P2MDB2494

open BinPacking.Decreasing

/-! ### optBins: packings -/

def Pk' (L : List ℝ) (b : ℕ) : Prop :=
  ∃ g : ℕ → ℕ, (∀ i < L.length, g i < b) ∧
    ∀ j < b, ∑ i ∈ (Finset.range L.length).filter (fun i => g i = j), L.getD i 0 ≤ 1

theorem sum_range_getD (L : List ℝ) : ∑ i ∈ Finset.range L.length, L.getD i 0 = L.sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih, List.sum_cons]
    ring

theorem pk'_cons (B L : List ℝ) (b : ℕ) (hB : B.sum ≤ 1) (h : Pk' L b) :
    Pk' (B ++ L) (b + 1) := by
  obtain ⟨g, hg1, hg2⟩ := h
  refine ⟨fun i => if i < B.length then 0 else g (i - B.length) + 1, ?_, ?_⟩
  · intro i hi
    simp only [List.length_append] at hi
    dsimp only
    split_ifs with h1
    · omega
    · have := hg1 (i - B.length) (by omega); omega
  · intro j hj
    rw [Finset.sum_filter, List.length_append, Finset.sum_range_add]
    have e1 : ∀ x ∈ Finset.range B.length,
        (if (if x < B.length then 0 else g (x - B.length) + 1) = j then (B ++ L).getD x 0 else 0)
          = if 0 = j then B.getD x 0 else 0 := by
      intro x hx
      rw [Finset.mem_range] at hx
      rw [if_pos hx]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hx]
    have e2 : ∀ x ∈ Finset.range L.length,
        (if (if B.length + x < B.length then 0 else g (B.length + x - B.length) + 1) = j
            then (B ++ L).getD (B.length + x) 0 else 0)
          = if g x + 1 = j then L.getD x 0 else 0 := by
      intro x _
      rw [if_neg (show ¬ (B.length + x < B.length) by omega), Nat.add_sub_cancel_left,
        List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
    rcases j with _ | j
    · have h0 : ∀ x, (if g x + 1 = 0 then L.getD x 0 else (0:ℝ)) = 0 :=
        fun x => if_neg (by omega)
      simp only [h0, eq_self_iff_true, if_true, Finset.sum_const_zero, add_zero]
      rw [sum_range_getD]
      exact hB
    · have h2 := hg2 j (by omega)
      rw [Finset.sum_filter] at h2
      have h0 : ∀ x, (if (0:ℕ) = j + 1 then B.getD x 0 else (0:ℝ)) = 0 :=
        fun x => if_neg (by omega)
      simp only [h0, Finset.sum_const_zero, zero_add, Nat.add_right_cancel_iff]
      exact h2

theorem pk'_flatten (Bs : List (List ℝ)) (h : ∀ B ∈ Bs, B.sum ≤ 1) :
    Pk' Bs.flatten Bs.length := by
  induction Bs with
  | nil => exact ⟨fun _ => 0, by simp, by simp⟩
  | cons B Bs ih =>
    rw [List.flatten_cons, List.length_cons]
    exact pk'_cons B _ _ (h B (by simp)) (ih (fun C hC => h C (by simp [hC])))

theorem pk_of_pk' (L : List ℝ) (b : ℕ) (h : Pk' L b) :
    ∃ f : Fin L.length → Fin b, ∀ j : Fin b,
      ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i ≤ 1 := by
  obtain ⟨g, hg1, hg2⟩ := h
  refine ⟨fun i => ⟨g i, hg1 i i.2⟩, fun j => ?_⟩
  have := hg2 j j.2
  rw [Finset.sum_filter] at this ⊢
  rw [← Fin.sum_univ_eq_sum_range] at this
  convert this using 2 with i
  simp [Fin.ext_iff, List.getD_eq_getElem?_getD]

theorem sum_le_of_pk (L : List ℝ) (b : ℕ) (f : Fin L.length → Fin b)
    (hf : ∀ j : Fin b, ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i ≤ 1) :
    L.sum ≤ b := by
  have h1 := Finset.sum_fiberwise (Finset.univ : Finset (Fin L.length)) f (fun i => L.get i)
  have h2 : ∑ i : Fin L.length, L.get i = L.sum := by
    rw [← List.sum_ofFn]; simp
  calc L.sum = ∑ j : Fin b, ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i := by
        rw [← h2, ← h1]
    _ ≤ ∑ _j : Fin b, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hf j)
    _ = b := by simp

theorem optBins_eq (Bs : List (List ℝ)) (h : ∀ B ∈ Bs, B.sum ≤ 1)
    (hs : Bs.flatten.sum = Bs.length) : optBins Bs.flatten = Bs.length := by
  have hP := pk_of_pk' _ _ (pk'_flatten Bs h)
  apply le_antisymm
  · exact Nat.sInf_le hP
  · have hne : ({b : ℕ | ∃ f : Fin Bs.flatten.length → Fin b, ∀ j : Fin b,
        ∑ i ∈ Finset.univ.filter (fun i => f i = j), Bs.flatten.get i ≤ 1}).Nonempty :=
      ⟨_, hP⟩
    obtain ⟨f, hf⟩ := Nat.sInf_mem hne
    have := sum_le_of_pk _ _ f hf
    rw [hs] at this
    exact_mod_cast this

/-! ### runs -/

def Closed (P : List (List ℝ)) (x : ℝ) : Prop := ∀ B ∈ P, 1 < B.sum + x

structure Good (ch : List (List ℝ) → ℝ → ℕ) : Prop where
  new : ∀ bins x, Closed bins x → ch bins x = bins.length
  mid : ∀ (U : List (List ℝ)) (B : List ℝ) (V : List (List ℝ)) (x : ℝ), Closed U x →
    B.sum + x ≤ 1 → (∀ C ∈ V, C.sum + x ≤ 1 → C.sum ≤ B.sum) → ch (U ++ B :: V) x = U.length

theorem good_ff : Good ffChoice := by
  constructor
  · intro bins x h
    unfold ffChoice
    apply List.findIdx_eq_length_of_false
    intro B hB
    simpa using h B hB
  · intro U B V x hU hB _
    unfold ffChoice
    rw [List.findIdx_append]
    have : U.findIdx (fun B => decide (B.sum + x ≤ 1)) = U.length := by
      apply List.findIdx_eq_length_of_false
      intro C hC; simpa using hU C hC
    rw [this, if_neg (lt_irrefl _), List.findIdx_cons]
    simp [hB]

theorem good_bf : Good bfChoice := by
  constructor
  · intro bins x h
    unfold bfChoice
    apply List.findIdx_eq_length_of_false
    intro B hB
    have := h B hB
    simp only [decide_eq_false_iff_not, not_and]
    intro h'; linarith
  · intro U B V x hU hB hV
    unfold bfChoice
    rw [List.findIdx_append]
    have : U.findIdx (fun B' => decide (B'.sum + x ≤ 1 ∧ ∀ B'' ∈ U ++ B :: V,
        B''.sum + x ≤ 1 → B''.sum ≤ B'.sum)) = U.length := by
      apply List.findIdx_eq_length_of_false
      intro C hC
      have := hU C hC
      simp only [decide_eq_false_iff_not, not_and]
      intro h'; linarith
    rw [this, if_neg (lt_irrefl _), List.findIdx_cons]
    have hp : decide (B.sum + x ≤ 1 ∧ ∀ B'' ∈ U ++ B :: V,
        B''.sum + x ≤ 1 → B''.sum ≤ B.sum) = true := by
      rw [decide_eq_true_iff]
      refine ⟨hB, ?_⟩
      intro C hC hCx
      simp only [List.mem_append, List.mem_cons] at hC
      rcases hC with hC | rfl | hC
      · have := hU C hC; linarith
      · exact le_rfl
      · exact hV C hC hCx
    simp [hp]

theorem placeAt_end (bins : List (List ℝ)) (x : ℝ) :
    placeAt bins bins.length x = bins ++ [[x]] := by
  unfold placeAt; simp

theorem placeAt_mid (U V : List (List ℝ)) (B : List ℝ) (x : ℝ) :
    placeAt (U ++ B :: V) U.length x = U ++ (B ++ [x]) :: V := by
  unfold placeAt
  rw [if_pos (by simp)]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_mapIdx]
  rcases lt_trichotomy i U.length with h | h | h
  · rw [if_neg (by omega), List.getElem_append_left h, List.getElem_append_left h]
  · subst h; simp
  · rw [if_neg (by omega)]
    obtain ⟨k, rfl⟩ : ∃ k, i = U.length + (k + 1) := ⟨i - U.length - 1, by omega⟩
    simp [List.getElem_append_right]

section phases

variable (ch : List (List ℝ) → ℝ → ℕ)

theorem fill (hg : Good ch) (P : List (List ℝ)) (x : ℝ) (hP : Closed P x) (hx : 0 ≤ x) :
    ∀ (t s : ℕ), ((s + t : ℕ) : ℝ) * x ≤ 1 →
      (List.replicate t x).foldl (fun bins a => placeAt bins (ch bins a) a)
        (P ++ [List.replicate s x]) = P ++ [List.replicate (s + t) x] := by
  intro t
  induction t with
  | zero => intro s _; simp
  | succ t ih =>
    intro s hst
    rw [List.replicate_succ, List.foldl_cons]
    have hc : ch (P ++ [List.replicate s x]) x = P.length := by
      apply hg.mid P _ [] x hP
      · rw [List.sum_replicate, nsmul_eq_mul]
        have : ((s + 1 : ℕ) : ℝ) * x ≤ ((s + (t + 1) : ℕ) : ℝ) * x :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : s + 1 ≤ s + (t + 1))) hx
        push_cast at this hst; linarith
      · simp
    rw [hc, placeAt_mid P [] _ x, ← List.replicate_succ', ih (s + 1) (by
      rw [show s + 1 + t = s + (t + 1) by omega]; exact hst)]
    congr 3
    omega

theorem group (hg : Good ch) (P : List (List ℝ)) (x : ℝ) (hP : Closed P x) (hx : 0 ≤ x)
    (q : ℕ) (hq : 1 ≤ q) (hqx : (q : ℝ) * x ≤ 1) :
    (List.replicate q x).foldl (fun bins a => placeAt bins (ch bins a) a) P
      = P ++ [List.replicate q x] := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
  rw [List.replicate_succ, List.foldl_cons, hg.new P x hP, placeAt_end]
  have := fill ch hg P x hP hx t 1 (by rw [add_comm]; exact hqx)
  rw [show [[x]] = [List.replicate 1 x] by simp, this, add_comm]
  rfl

theorem groups (hg : Good ch) (x : ℝ) (hx : 0 ≤ x) (q : ℕ) (hq : 1 ≤ q)
    (hqx : (q : ℝ) * x ≤ 1) (hcl : 1 < (q : ℝ) * x + x) :
    ∀ (n : ℕ) (P : List (List ℝ)), Closed P x →
      (List.replicate (n * q) x).foldl (fun bins a => placeAt bins (ch bins a) a) P
        = P ++ List.replicate n (List.replicate q x) := by
  intro n
  induction n with
  | zero => intro P _; simp
  | succ n ih =>
    intro P hP
    rw [show (n + 1) * q = q + n * q by ring, List.replicate_add, List.foldl_append,
      group ch hg P x hP hx q hq hqx]
    have hP' : Closed (P ++ [List.replicate q x]) x := by
      intro B hB
      simp only [List.mem_append, List.mem_singleton] at hB
      rcases hB with hB | rfl
      · exact hP B hB
      · rw [List.sum_replicate, nsmul_eq_mul]; exact hcl
    rw [ih _ hP', List.replicate_succ]
    simp

theorem bphase (hg : Good ch) (a b : ℝ) (hab : a + b ≤ 1) (habb : 1 < a + b + b) :
    ∀ (n i : ℕ) (P : List (List ℝ)), Closed P b →
      (List.replicate n b).foldl (fun bins a => placeAt bins (ch bins a) a)
        (P ++ List.replicate i [a, b] ++ List.replicate n [a])
        = P ++ List.replicate (i + n) [a, b] := by
  intro n
  induction n with
  | zero => intro i P _; simp
  | succ n ih =>
    intro i P hP
    rw [show List.replicate (n + 1) b = b :: List.replicate n b from rfl, List.foldl_cons,
      show List.replicate (n + 1) [a] = [a] :: List.replicate n [a] from rfl]
    have hU : Closed (P ++ List.replicate i [a, b]) b := by
      intro B hB
      simp only [List.mem_append, List.mem_replicate] at hB
      rcases hB with hB | ⟨_, rfl⟩
      · exact hP B hB
      · simp; linarith
    have hc : ch (P ++ List.replicate i [a, b] ++ [a] :: List.replicate n [a]) b
        = (P ++ List.replicate i [a, b]).length := by
      apply hg.mid _ _ _ b hU
      · simpa using hab
      · intro C hC _
        rw [List.mem_replicate] at hC
        rw [hC.2]
    rw [hc, placeAt_mid]
    have := ih (i + 1) P hP
    rw [show i + 1 + n = i + (n + 1) by omega] at this
    rw [← this]
    congr 1
    simp [List.replicate_succ', List.append_assoc]

end phases

/-! ### the instance -/

noncomputable def A : ℝ := 51 / 100
noncomputable def Bv : ℝ := 27 / 100
noncomputable def Cv : ℝ := 26 / 100
noncomputable def Dv : ℝ := 23 / 100

noncomputable def bins0 (r m : ℕ) : List (List ℝ) :=
  List.replicate r [1] ++ List.replicate (6 * m) [A, Cv, Dv] ++
    List.replicate (3 * m) [Bv, Bv, Dv, Dv]

noncomputable def S (r m : ℕ) : List ℝ :=
  List.replicate r 1 ++ List.replicate (6 * m) A ++ List.replicate (6 * m) Bv ++
    List.replicate (6 * m) Cv ++ List.replicate (12 * m) Dv

noncomputable def final (r m : ℕ) : List (List ℝ) :=
  List.replicate r (List.replicate 1 1) ++ List.replicate (6 * m) [A, Bv] ++
    List.replicate (2 * m) (List.replicate 3 Cv) ++ List.replicate (3 * m) (List.replicate 4 Dv)

theorem run_S (ch : List (List ℝ) → ℝ → ℕ) (hg : Good ch) (r m : ℕ) :
    run ch (S r m) = final r m := by
  unfold run S final
  simp only [List.foldl_append]
  have h1 := groups ch hg 1 (by norm_num) 1 le_rfl (by norm_num) (by norm_num) r []
    (by intro B hB; simp at hB)
  rw [mul_one, List.nil_append] at h1
  rw [h1]
  have h2 := groups ch hg A (by norm_num [A]) 1 le_rfl (by norm_num [A]) (by norm_num [A])
    (6 * m) (List.replicate r (List.replicate 1 1)) (by
      intro B hB; rw [List.mem_replicate] at hB; rw [hB.2]; norm_num [A])
  rw [mul_one] at h2
  rw [h2]
  have h3 := bphase ch hg A Bv (by norm_num [A, Bv]) (by norm_num [A, Bv]) (6 * m) 0
    (List.replicate r (List.replicate 1 1)) (by
      intro B hB; rw [List.mem_replicate] at hB; rw [hB.2]; norm_num [Bv])
  simp only [List.replicate_zero, List.append_nil, zero_add] at h3
  rw [show List.replicate (6 * m) (List.replicate 1 A) = List.replicate (6 * m) [A] by simp, h3]
  have h4 := groups ch hg Cv (by norm_num [Cv]) 3 (by norm_num) (by norm_num [Cv])
    (by norm_num [Cv]) (2 * m)
    (List.replicate r (List.replicate 1 1) ++ List.replicate (6 * m) [A, Bv]) (by
      intro B hB
      simp only [List.mem_append, List.mem_replicate] at hB
      rcases hB with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num [A, Bv, Cv])
  rw [show 2 * m * 3 = 6 * m by ring] at h4
  rw [h4]
  have h5 := groups ch hg Dv (by norm_num [Dv]) 4 (by norm_num) (by norm_num [Dv])
    (by norm_num [Dv]) (3 * m)
    (List.replicate r (List.replicate 1 1) ++ List.replicate (6 * m) [A, Bv] ++
      List.replicate (2 * m) (List.replicate 3 Cv)) (by
      intro B hB
      simp only [List.mem_append, List.mem_replicate] at hB
      rcases hB with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> norm_num [A, Bv, Cv, Dv])
  rw [show 3 * m * 4 = 12 * m by ring] at h5
  rw [h5]

theorem final_length (r m : ℕ) : (final r m).length = r + 11 * m := by
  unfold final; simp; ring

theorem perm_S (r m : ℕ) : (bins0 r m).flatten.Perm (S r m) := by
  rw [List.perm_iff_count]
  intro y
  unfold bins0 S
  simp only [List.flatten_append, List.count_append, List.count_flatten, List.map_replicate,
    List.sum_replicate, List.count_replicate, List.count_cons, List.count_nil, smul_eq_mul]
  have hA : A ≠ 1 := by norm_num [A]
  have hB : Bv ≠ 1 := by norm_num [Bv]
  have hC : Cv ≠ 1 := by norm_num [Cv]
  have hD : Dv ≠ 1 := by norm_num [Dv]
  have hAB : A ≠ Bv := by norm_num [A, Bv]
  have hAC : A ≠ Cv := by norm_num [A, Cv]
  have hAD : A ≠ Dv := by norm_num [A, Dv]
  have hBC : Bv ≠ Cv := by norm_num [Bv, Cv]
  have hBD : Bv ≠ Dv := by norm_num [Bv, Dv]
  have hCD : Cv ≠ Dv := by norm_num [Cv, Dv]
  by_cases h1 : y = 1
  · subst h1; simp [hA.symm, hB.symm, hC.symm, hD.symm, hA, hB, hC, hD]
  by_cases h2 : y = A
  · subst h2; simp [hA, hAB, hAC, hAD, hAB.symm, hAC.symm, hAD.symm]
  by_cases h3 : y = Bv
  · subst h3; simp [hB, hAB.symm, hBC, hBD, hAB, hBC.symm, hBD.symm]; ring
  by_cases h4 : y = Cv
  · subst h4; simp [hC, hAC.symm, hBC.symm, hCD, hAC, hBC, hCD.symm]
  by_cases h5 : y = Dv
  · subst h5; simp [hD, hAD.symm, hBD.symm, hCD.symm, hAD, hBD, hCD]; ring
  simp [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, h1, h2, h3, h4, h5]

theorem pw_app (l1 l2 : List ℝ) (t : ℝ) (h1 : l1.Pairwise (· ≥ ·))
    (h2 : l2.Pairwise (· ≥ ·)) (ha : ∀ x ∈ l1, t ≤ x) (hb : ∀ y ∈ l2, y ≤ t) :
    (l1 ++ l2).Pairwise (· ≥ ·) :=
  List.pairwise_append.2 ⟨h1, h2, fun x hx y hy => le_trans (hb y hy) (ha x hx)⟩

theorem pw_rep (n : ℕ) (c : ℝ) : (List.replicate n c).Pairwise (· ≥ ·) :=
  List.pairwise_replicate.2 (Or.inr le_rfl)

theorem sortDesc_eq (r m : ℕ) : sortDesc (bins0 r m).flatten = S r m := by
  unfold sortDesc
  apply List.Perm.eq_of_sortedGE
  · apply List.Pairwise.sortedGE
    have := List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
      (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; linarith)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total b a)
      (bins0 r m).flatten
    exact this.imp (by intro a b h; simpa using h)
  · apply List.Pairwise.sortedGE
    unfold S
    refine pw_app _ _ Dv (pw_app _ _ Cv (pw_app _ _ Bv (pw_app _ _ A (pw_rep _ _) (pw_rep _ _)
      ?_ ?_) (pw_rep _ _) ?_ ?_) (pw_rep _ _) ?_ ?_) (pw_rep _ _) ?_ ?_
    all_goals intro x hx
    all_goals simp only [List.mem_append, List.mem_replicate] at hx
    · rcases hx with ⟨_, rfl⟩; norm_num [A]
    · rcases hx with ⟨_, rfl⟩; norm_num [A]
    · rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num [A, Bv]
    · rcases hx with ⟨_, rfl⟩; norm_num [Bv]
    · rcases hx with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> norm_num [A, Bv, Cv]
    · rcases hx with ⟨_, rfl⟩; norm_num [Cv]
    · rcases hx with ((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> norm_num [A, Bv, Cv, Dv]
    · rcases hx with ⟨_, rfl⟩; norm_num [Dv]
  · exact (List.mergeSort_perm _ _).trans (perm_S r m)

theorem bins0_sum_le (r m : ℕ) : ∀ B ∈ bins0 r m, B.sum ≤ 1 := by
  intro B hB
  unfold bins0 at hB
  simp only [List.mem_append, List.mem_replicate] at hB
  rcases hB with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> norm_num [A, Bv, Cv, Dv]

theorem bins0_length (r m : ℕ) : (bins0 r m).length = r + 9 * m := by
  unfold bins0; simp; ring

theorem bins0_flatten_sum (r m : ℕ) : (bins0 r m).flatten.sum = ((bins0 r m).length : ℝ) := by
  rw [bins0_length]
  unfold bins0
  simp [List.sum_flatten, List.sum_replicate, A, Bv, Cv, Dv]
  ring

theorem isList_bins0 (r m : ℕ) : IsList (bins0 r m).flatten := by
  intro y hy
  unfold bins0 at hy
  simp only [List.mem_flatten, List.mem_append, List.mem_replicate] at hy
  obtain ⟨l, hl, hyl⟩ := hy
  rcases hl with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hyl <;>
    rcases hyl with rfl | rfl | rfl | rfl <;> norm_num [A, Bv, Cv, Dv]

end P2MDB2494

open P2MDB2494 in
open BinPacking.Decreasing in
theorem solution (k : ℕ) (hk : 1 ≤ k) :
    ∃ L : List ℝ, IsList L ∧ optBins L = k ∧ FFD L = BFD L ∧
      (11 / 9 : ℝ) * (optBins L : ℝ) - 2 < (FFD L : ℝ) := by
  set r := k % 9
  set m := k / 9
  have hk9 : k = r + 9 * m := by omega
  have hr : r < 9 := Nat.mod_lt _ (by norm_num)
  have hopt : optBins (bins0 r m).flatten = k := by
    rw [optBins_eq _ (bins0_sum_le r m) (bins0_flatten_sum r m), bins0_length]; omega
  have hffd : FFD (bins0 r m).flatten = r + 11 * m := by
    unfold FFD FF; rw [sortDesc_eq, run_S _ good_ff, final_length]
  have hbfd : BFD (bins0 r m).flatten = r + 11 * m := by
    unfold BFD BF; rw [sortDesc_eq, run_S _ good_bf, final_length]
  refine ⟨(bins0 r m).flatten, isList_bins0 r m, hopt, by rw [hffd, hbfd], ?_⟩
  rw [hopt, hffd, hk9]
  have : (r : ℝ) < 9 := by exact_mod_cast hr
  push_cast
  linarith
