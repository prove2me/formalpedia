-- Prove2me | solution 1 for EditMulticoloring.Code.short_edit_code
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:02:09.995873+00:00
-- url     : https://prove2.me/submissions/2d0737cb-1af7-4df7-8f3e-7a25cb6d51a3

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Theorems.Thm_EditMulticoloring_Code_edit_ball_volume

section
set_option autoImplicit false

namespace EditMulticoloring.Dev.Short
open OAI.EditDistortion EditMulticoloring.Code

/-! ## Edit metric: symmetry and triangle inequality -/

theorem script_trans {Al : Type} {n m : ℕ} {x y z : List Al}
    (h1 : Script true n x y) (h2 : Script true m y z) : Script true (n + m) x z := by
  induction h1 with
  | nil => rw [Nat.zero_add]; exact h2
  | cons first rest ih =>
    rw [Nat.add_right_comm]
    exact Script.cons first (ih h2)

theorem step_symm {Al : Type} {x y : List Al} (h : Step true x y) : Step true y x := by
  cases h with
  | insert p q a => exact Step.delete p q a
  | delete p q a => exact Step.insert p q a
  | substitute hs p q a b => exact Step.substitute hs p q b a

theorem script_symm {Al : Type} {n : ℕ} {x y : List Al}
    (h : Script true n x y) : Script true n y x := by
  induction h with
  | nil => exact Script.nil _
  | cons first rest ih =>
    exact script_trans ih (Script.cons (step_symm first) (Script.nil _))

theorem script_to_nil {Al : Type} (x : List Al) : Script true x.length x [] := by
  induction x with
  | nil => exact Script.nil _
  | cons a x ih =>
    have := Step.delete (substitutions := true) [] x a
    simp only [List.nil_append] at this
    exact Script.cons this ih

theorem script_exists {Al : Type} (x y : List Al) : ∃ n, Script true n x y :=
  ⟨_, script_trans (script_to_nil x) (script_symm (script_to_nil y))⟩

theorem edit_attained {Al : Type} (x y : List Al) :
    Script true (edit x y) x y :=
  Nat.sInf_mem (s := {n | Script true n x y}) (script_exists x y)

theorem edit_le {Al : Type} {n : ℕ} {x y : List Al} (h : Script true n x y) :
    edit x y ≤ n := Nat.sInf_le h

theorem dist_symm {q : ℕ} (x y : Word q) : distance x y = distance y x := by
  unfold distance
  exact le_antisymm (edit_le (script_symm (edit_attained y x)))
    (edit_le (script_symm (edit_attained x y)))

theorem dist_triangle {q : ℕ} (x y z : Word q) :
    distance x z ≤ distance x y + distance y z := by
  unfold distance
  exact edit_le (script_trans (edit_attained x y) (edit_attained y z))

/-! ## Words and value -/

theorem mem_words {q n : ℕ} (w : Word q) : w ∈ words q n ↔ w.length = n := by
  induction n generalizing w with
  | zero => cases w <;> simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons a w => simp [words, ih]

theorem words_length (q n : ℕ) : (words q n).length = q ^ n := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    simp [words, List.length_flatMap, ih, pow_succ, mul_comm]

theorem words_nodup (q n : ℕ) : (words q n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    unfold words
    rw [List.nodup_flatMap]
    refine ⟨fun a _ => ih.map (fun x y h => by simpa using h), ?_⟩
    refine (List.nodup_finRange q).imp ?_
    intro a b hab
    rw [Function.onFun, List.disjoint_left]
    intro w hw hw'
    simp only [List.mem_map] at hw hw'
    obtain ⟨x, _, rfl⟩ := hw
    obtain ⟨y, _, hy⟩ := hw'
    exact hab (List.cons.inj hy).1.symm

theorem value_snoc {q : ℕ} (l : Word q) (a : Fin q) :
    value (l ++ [a]) = q * value l + a.val := by
  simp [value, List.foldl_append]

theorem value_ofFn_succ {q n : ℕ} (u : Fin (n + 1) → Fin q) :
    value (List.ofFn u) = q * value (List.ofFn (fun i : Fin n => u i.castSucc)) + (u (Fin.last n)).val := by
  rw [List.ofFn_succ', List.concat_eq_append, value_snoc]

theorem value_ofFn_lt {q : ℕ} (hq : 0 < q) : ∀ {n : ℕ} (u : Fin n → Fin q),
    value (List.ofFn u) < q ^ n := by
  intro n
  induction n with
  | zero => intro u; simp [value]
  | succ n ih =>
    intro u
    rw [value_ofFn_succ, pow_succ]
    have h1 := ih (fun i : Fin n => u i.castSucc)
    have h2 := (u (Fin.last n)).isLt
    calc _ < q * value (List.ofFn (fun i : Fin n => u i.castSucc)) + q := by omega
      _ = q * (value (List.ofFn (fun i : Fin n => u i.castSucc)) + 1) := by ring
      _ ≤ q * q ^ n := Nat.mul_le_mul_left _ h1
      _ = q ^ n * q := mul_comm _ _

theorem value_ofFn_inj {q : ℕ} (hq : 0 < q) : ∀ {n : ℕ} (u v : Fin n → Fin q),
    value (List.ofFn u) = value (List.ofFn v) → u = v := by
  intro n
  induction n with
  | zero => intro u v _; funext i; exact i.elim0
  | succ n ih =>
    intro u v h
    rw [value_ofFn_succ, value_ofFn_succ] at h
    have hx := (u (Fin.last n)).isLt
    have hy := (v (Fin.last n)).isLt
    set a := value (List.ofFn (fun i : Fin n => u i.castSucc))
    set b := value (List.ofFn (fun i : Fin n => v i.castSucc))
    have d1 : (q * a + (u (Fin.last n)).val) / q = (q * b + (v (Fin.last n)).val) / q := by rw [h]
    have d2 : (q * a + (u (Fin.last n)).val) % q = (q * b + (v (Fin.last n)).val) % q := by rw [h]
    rw [Nat.mul_add_div hq, Nat.mul_add_div hq, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy] at d1
    rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at d2
    have ha : a = b := by omega
    have hpre := ih (fun i : Fin n => u i.castSucc) (fun i : Fin n => v i.castSucc) ha
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Fin.ext d2
    · exact congrFun hpre j

/-! ## Greedy -/

def R {q : ℕ} (t : ℕ) (a b : Word q) : Prop := b ∉ ball (2 * t) a

theorem greedy_aux {q : ℕ} (t : ℕ) (xs ch : List (Word q)) (hp : ch.Pairwise (R t)) :
    (xs.foldl (fun chosen x =>
      if chosen.any (fun z => x ∈ ball (2 * t) z) then chosen else chosen ++ [x]) ch).Pairwise (R t) ∧
    (∀ a ∈ ch, a ∈ xs.foldl (fun chosen x =>
      if chosen.any (fun z => x ∈ ball (2 * t) z) then chosen else chosen ++ [x]) ch) ∧
    (∀ a ∈ xs.foldl (fun chosen x =>
      if chosen.any (fun z => x ∈ ball (2 * t) z) then chosen else chosen ++ [x]) ch,
        a ∈ ch ∨ a ∈ xs) ∧
    (∀ x ∈ xs, x ∈ xs.foldl (fun chosen x =>
      if chosen.any (fun z => x ∈ ball (2 * t) z) then chosen else chosen ++ [x]) ch ∨
      ∃ z ∈ xs.foldl (fun chosen x =>
      if chosen.any (fun z => x ∈ ball (2 * t) z) then chosen else chosen ++ [x]) ch,
        x ∈ ball (2 * t) z) := by
  induction xs generalizing ch with
  | nil => exact ⟨hp, fun a h => h, fun a h => Or.inl h, by simp⟩
  | cons x xs ih =>
    simp only [List.foldl_cons]
    by_cases hany : ch.any (fun z => x ∈ ball (2 * t) z) = true
    · rw [if_pos hany]
      obtain ⟨h1, h2, h3, h4⟩ := ih ch hp
      obtain ⟨z, hz, hzx⟩ := List.any_eq_true.mp hany
      refine ⟨h1, h2, ?_, ?_⟩
      · intro a ha
        rcases h3 a ha with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inr ⟨z, h2 z hz, by simpa using hzx⟩
        · exact h4 y hy
    · rw [if_neg hany]
      have hp' : (ch ++ [x]).Pairwise (R t) := by
        rw [List.pairwise_append]
        refine ⟨hp, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        intro hmem
        apply hany
        exact List.any_eq_true.mpr ⟨a, ha, by simpa using hmem⟩
      obtain ⟨h1, h2, h3, h4⟩ := ih (ch ++ [x]) hp'
      refine ⟨h1, fun a ha => h2 a (List.mem_append_left _ ha), ?_, ?_⟩
      · intro a ha
        rcases h3 a ha with h | h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl h
          · rw [List.mem_singleton] at h; subst h; exact Or.inr (List.mem_cons_self ..)
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inl (h2 y (by simp))
        · exact h4 y hy

theorem pairwise_two {α : Type} {r : α → α → Prop} {l : List α} (hl : l.Pairwise r)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) : r a b ∨ r b a := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
  rw [List.pairwise_iff_getElem] at hl
  have hij : i ≠ j := fun h => hab (by subst h; rfl)
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact Or.inl (hl i j hi hj h)
  · exact Or.inr (hl j i hj hi h)

/-! ## Existence of the short length -/

theorem exists_const (s A : ℕ) : ∃ c : ℕ, s + 1 ≤ c ∧ A * (3 * c) ^ s ≤ 2 ^ c := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt s (by norm_num : (1 : ℝ) < 2)
  have ht2 := ht.const_mul ((A : ℝ) * 3 ^ s)
  rw [mul_zero] at ht2
  have hev := (ht2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).and
    (Filter.eventually_ge_atTop (s + 1))
  obtain ⟨c, hc1, hc2⟩ := hev.exists
  refine ⟨c, hc2, ?_⟩
  have h2 : (0 : ℝ) < 2 ^ c := by positivity
  have : (A : ℝ) * (3 * c) ^ s ≤ 2 ^ c := by
    have := (div_lt_one h2).mp (by
      have e : (A : ℝ) * 3 ^ s * ((c : ℝ) ^ s / 2 ^ c) = A * (3 * c) ^ s / 2 ^ c := by
        rw [mul_pow]; ring
      rw [← e]; exact hc1)
    exact this.le
  exact_mod_cast this

theorem exists_C (q t : ℕ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 1 ≤ h → ∃ k : ℕ,
      q ^ h * radiusBound q (2 * t) (h + k) ≤ q ^ (h + k) ∧ (k : ℝ) ≤ C * Real.log (h + 1 : ℝ) := by
  set s := 2 * t with hs
  obtain ⟨c, hcs, hc⟩ := exists_const s ((s + 1) * (2 * q) ^ s)
  have hc1 : 1 ≤ c := by omega
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 * c / Real.log 2, by positivity, fun h hh => ?_⟩
  set j := Nat.log 2 (h + 1) with hj
  have hj1 : 1 ≤ j := Nat.log_pos (by norm_num) (by omega)
  have hlt : h + 1 < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hle : 2 ^ j ≤ h + 1 := Nat.pow_log_le_self 2 (by omega)
  refine ⟨2 * c * (j + 1), ?_, ?_⟩
  · set k := 2 * c * (j + 1) with hk
    have hjj : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
    have h1 : k + s + 1 ≤ 3 * c * (j + 1) := by
      have : s + 1 ≤ c * (j + 1) := le_trans hcs (Nat.le_mul_of_pos_right _ (by omega))
      rw [hk]; nlinarith
    have h2 : h + k + s + 1 ≤ (h + 1) * (k + s + 1) := by nlinarith
    have h3 : h + k + s + 1 ≤ 2 ^ (2 * j + 1) * (3 * c) := by
      calc h + k + s + 1 ≤ (h + 1) * (k + s + 1) := h2
        _ ≤ 2 ^ (j + 1) * (3 * c * (j + 1)) := Nat.mul_le_mul hlt.le h1
        _ ≤ 2 ^ (j + 1) * (3 * c * 2 ^ j) := by gcongr
        _ = 2 ^ (2 * j + 1) * (3 * c) := by ring
    have h4 : radiusBound q s (h + k) ≤ 2 ^ k := by
      unfold radiusBound
      calc (s + 1) * (2 * q * (h + k + s + 1)) ^ s
          ≤ (s + 1) * (2 * q * (2 ^ (2 * j + 1) * (3 * c))) ^ s := by
            gcongr
        _ = ((s + 1) * (2 * q) ^ s * (3 * c) ^ s) * 2 ^ (s * (2 * j + 1)) := by
            rw [show 2 * q * (2 ^ (2 * j + 1) * (3 * c)) = (2 * q) * (3 * c) * 2 ^ (2 * j + 1) by ring,
              mul_pow, mul_pow, ← pow_mul]; ring
        _ ≤ 2 ^ c * 2 ^ (s * (2 * j + 1)) := by gcongr
        _ = 2 ^ (c + s * (2 * j + 1)) := (pow_add _ _ _).symm
        _ ≤ 2 ^ k := by
          apply Nat.pow_le_pow_right (by norm_num)
          rw [hk]; nlinarith
    calc q ^ h * radiusBound q s (h + k) ≤ q ^ h * 2 ^ k := Nat.mul_le_mul_left _ h4
      _ ≤ q ^ h * q ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq _)
      _ = q ^ (h + k) := (pow_add _ _ _).symm
  · have hlog : (j : ℝ) * Real.log 2 ≤ Real.log (h + 1 : ℝ) := by
      rw [← Real.log_pow]
      apply Real.log_le_log (by positivity)
      exact_mod_cast hle
    have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have : ((2 * c * (j + 1) : ℕ) : ℝ) ≤ 4 * c * j := by
      push_cast; nlinarith [(by exact_mod_cast hc1 : (1 : ℝ) ≤ c)]
    calc _ ≤ 4 * (c : ℝ) * j := this
      _ = 4 * c / Real.log 2 * (j * Real.log 2) := by field_simp
      _ ≤ _ := by gcongr

/-! ## Table -/

theorem ball_iff {q t : ℕ} (hq : 2 ≤ q) (ht : 1 ≤ t) {m : ℕ} (hm : 1 ≤ m) {x : Word q}
    (hx : x.length = m) (y : Word q) : y ∈ ball (2 * t) x ↔ distance x y ≤ 2 * t :=
  (edit_ball_volume q (2 * t) hq (by omega)).1 m hm x hx |>.2.1 y

theorem ball_card {q t : ℕ} (hq : 2 ≤ q) (ht : 1 ≤ t) {m : ℕ} (hm : 1 ≤ m) {x : Word q}
    (hx : x.length = m) : (ball (2 * t) x).card ≤ radiusBound q (2 * t) m :=
  (edit_ball_volume q (2 * t) hq (by omega)).1 m hm x hx |>.2.2

theorem dist_self {q : ℕ} (x : Word q) : distance x x = 0 := by
  unfold distance
  exact Nat.eq_zero_of_le_zero (edit_le (Script.nil x))

theorem radius_pos (q s m : ℕ) (hq : 2 ≤ q) : 0 < radiusBound q s m := by
  unfold radiusBound
  positivity

end EditMulticoloring.Dev.Short

namespace EditMulticoloring.Code
open EditMulticoloring.Dev.Short in
theorem chk_short_edit_code (q t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 1 ≤ h →
      let ρ := shortLength q t h
      (∃ l : ℕ, h ≤ l ∧ q ^ h * radiusBound q (2 * t) l ≤ q ^ l) ∧
      (h ≤ ρ ∧ q ^ h * radiusBound q (2 * t) ρ ≤ q ^ ρ) ∧
      (∀ l : ℕ, h ≤ l → q ^ h * radiusBound q (2 * t) l ≤ q ^ l → ρ ≤ l) ∧
      ((ρ : ℝ) ≤ (h : ℝ) + C * Real.log (h + 1 : ℝ)) ∧
      (shortTable q t h).length = q ^ h ∧
      (∀ u : FixedWord q h, (shortEncode t h (toWord u)).length = ρ) ∧
      Function.Injective (fun u : FixedWord q h => shortEncode t h (toWord u)) ∧
      Corrects t (Set.range (fun u : FixedWord q h => shortEncode t h (toWord u)))
    := by
  obtain ⟨C, hC, hk⟩ := exists_C q t hq
  refine ⟨C, hC, fun h hh => ?_⟩
  obtain ⟨k, hk1, hk2⟩ := hk h hh
  have hne : {l : ℕ | h ≤ l ∧ q ^ h * radiusBound q (2 * t) l ≤ q ^ l}.Nonempty :=
    ⟨h + k, Nat.le_add_right _ _, hk1⟩
  have hmem := Nat.sInf_mem hne
  have hmin : ∀ l : ℕ, h ≤ l → q ^ h * radiusBound q (2 * t) l ≤ q ^ l → shortLength q t h ≤ l :=
    fun l h1 h2 => Nat.sInf_le ⟨h1, h2⟩
  have hmem' : h ≤ shortLength q t h ∧ q ^ h * radiusBound q (2 * t) (shortLength q t h) ≤ q ^ shortLength q t h := hmem
  show _ ∧ _ ∧ _ ∧ ((shortLength q t h : ℕ) : ℝ) ≤ _ ∧ _
  generalize hρ : shortLength q t h = ρ at hmem' hmin ⊢
  have hρ1 : 1 ≤ ρ := le_trans hh hmem'.1
  have hT : shortTable q t h = (greedy t (words q ρ)).take (q ^ h) := by
    unfold shortTable; rw [hρ]
  -- greedy facts
  obtain ⟨g1, -, g3, g4⟩ := greedy_aux t (words q ρ) [] (List.Pairwise.nil)
  change (greedy t (words q ρ)).Pairwise (R t) at g1
  have glen : ∀ a ∈ greedy t (words q ρ), a.length = ρ := by
    intro a ha
    rcases g3 a ha with h | h
    · simp at h
    · exact (mem_words a).mp h
  have hRpos := radius_pos q (2 * t) ρ hq
  -- count
  have hcount : q ^ h ≤ (greedy t (words q ρ)).length := by
    set G := greedy t (words q ρ) with hG
    have hsub : (words q ρ).toFinset ⊆ G.toFinset.biUnion (fun z => ball (2 * t) z) := by
      intro w hw
      rw [List.mem_toFinset] at hw
      rw [Finset.mem_biUnion]
      rcases g4 w hw with h | ⟨z, hz, hzw⟩
      · refine ⟨w, List.mem_toFinset.mpr h, ?_⟩
        rw [ball_iff hq ht hρ1 (glen w h)]
        rw [dist_self]; omega
      · exact ⟨z, List.mem_toFinset.mpr hz, hzw⟩
    have hc1 : (words q ρ).toFinset.card = q ^ ρ := by
      rw [List.toFinset_card_of_nodup (words_nodup q ρ), words_length]
    have hc2 : (G.toFinset.biUnion (fun z => ball (2 * t) z)).card ≤ G.length * radiusBound q (2 * t) ρ := by
      calc _ ≤ ∑ z ∈ G.toFinset, (ball (2 * t) z).card := Finset.card_biUnion_le
        _ ≤ ∑ z ∈ G.toFinset, radiusBound q (2 * t) ρ :=
            Finset.sum_le_sum (fun z hz => ball_card hq ht hρ1 (glen z (List.mem_toFinset.mp hz)))
        _ = G.toFinset.card * radiusBound q (2 * t) ρ := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ (List.toFinset_card_le _)
    have := Finset.card_le_card hsub
    rw [hc1] at this
    have h5 : q ^ h * radiusBound q (2 * t) ρ ≤ G.length * radiusBound q (2 * t) ρ :=
      le_trans hmem'.2 (le_trans this hc2)
    exact Nat.le_of_mul_le_mul_right h5 hRpos
  have hTlen : (shortTable q t h).length = q ^ h := by
    rw [hT, List.length_take]; omega
  have hTpair : (shortTable q t h).Pairwise (R t) := by
    rw [hT]; exact g1.sublist (List.take_sublist _ _)
  have hTlenρ : ∀ a ∈ shortTable q t h, a.length = ρ := fun a ha =>
    glen a (by rw [hT] at ha; exact List.mem_of_mem_take ha)
  have hsep : ∀ a ∈ shortTable q t h, ∀ b ∈ shortTable q t h, a ≠ b → 2 * t < distance a b := by
    intro a ha b hb hab
    rcases pairwise_two hTpair ha hb hab with h1 | h1
    · unfold R at h1
      rw [ball_iff hq ht hρ1 (hTlenρ a ha)] at h1
      omega
    · unfold R at h1
      rw [ball_iff hq ht hρ1 (hTlenρ b hb)] at h1
      rw [dist_symm]; omega
  have hval : ∀ u : FixedWord q h, value (toWord u) < (shortTable q t h).length := by
    intro u; rw [hTlen]; exact value_ofFn_lt (by omega) u
  have henc : ∀ u : FixedWord q h, shortEncode t h (toWord u) = (shortTable q t h)[value (toWord u)]'(hval u) := by
    intro u; unfold shortEncode; simp [List.getElem?_eq_getElem (hval u)]
  have hnodup : (shortTable q t h).Nodup := by
    refine hTpair.imp_of_mem ?_
    intro a b ha _ hab hEq
    apply hab
    subst hEq
    rw [ball_iff hq ht hρ1 (hTlenρ a ha), dist_self]
    omega
  refine ⟨⟨h + k, Nat.le_add_right _ _, hk1⟩, hmem', hmin, ?_, hTlen, ?_, ?_, ?_⟩
  · have := hmin (h + k) (Nat.le_add_right _ _) hk1
    have h6 : (ρ : ℝ) ≤ ((h + k : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h6
    linarith
  · intro u; rw [henc]; exact hTlenρ _ (List.getElem_mem _)
  · intro u v huv
    simp only [henc] at huv
    have := (hnodup.getElem_inj_iff).mp huv
    exact value_ofFn_inj (by omega) u v this
  · rintro x ⟨u, rfl⟩ z ⟨v, rfl⟩ hxz y ⟨h1, h2⟩
    simp only at hxz h1 h2
    have := hsep _ (by rw [henc]; exact List.getElem_mem _) _ (by rw [henc]; exact List.getElem_mem _) hxz
    have h3 := dist_triangle (shortEncode t h (toWord u)) y (shortEncode t h (toWord v))
    rw [dist_symm y] at h3
    omega

end EditMulticoloring.Code
end

theorem solution : type_of% @EditMulticoloring.Code.chk_short_edit_code := @EditMulticoloring.Code.chk_short_edit_code
