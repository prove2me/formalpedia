-- Prove2me | solution 1 for Bartholdi.card_wordBall_le_exp_mul_rpow_alpha0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:09:30.816078+00:00
-- url     : https://prove2.me/submissions/29230203-4f9b-4ee4-9a84-0e3a6a2f78d4

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Theorems.Thm_ErschlerZheng_existsUnique_pos_root_and_alpha0_approx_and_charpoly_matrixM

section
/-!
# Basic facts about sections, `a`, and the generators `b_ω, c_ω, d_ω`

Development helpers for the Grigorchuk part of the Erschler–Zheng mission (not published).
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace GrigBasic

/-! ### Sections -/

theorem nil_smul (g : BinaryTreeAut) : ([] : List Bool) <• g = [] :=
  List.eq_nil_of_length_eq_zero (length_vertex_smul g [])

theorem sec_unique {g h : BinaryTreeAut} {v : List Bool}
    (H : ∀ w : List Bool, (v ++ w) <• g = (v <• g) ++ (w <• h)) : sec g v = h := by
  have key : ∀ w : List Bool, w <• sec g v = w <• h := by
    intro w
    have h1 := append_vertex_smul g v w
    rw [H w] at h1
    exact (List.append_cancel_left h1).symm
  have : (sec g v)⁻¹ = h⁻¹ := Subtype.ext (Equiv.ext fun w => key w)
  exact inv_injective this

theorem sec_mul (g h : BinaryTreeAut) (v : List Bool) :
    sec (g * h) v = sec g v * sec h (v <• g) := by
  apply sec_unique
  intro w
  rw [vertex_smul_mul, vertex_smul_mul, append_vertex_smul, append_vertex_smul,
    vertex_smul_mul]

theorem sec_nil (g : BinaryTreeAut) : sec g [] = g := by
  apply sec_unique
  intro w
  rw [nil_smul]
  rfl

theorem sec_append (g : BinaryTreeAut) (v u : List Bool) :
    sec g (v ++ u) = sec (sec g v) u := by
  apply sec_unique
  intro w
  rw [List.append_assoc, append_vertex_smul, append_vertex_smul, append_vertex_smul]
  simp only [List.append_assoc]

theorem sec_one (v : List Bool) : sec 1 v = 1 := by
  apply sec_unique
  intro w
  rfl

theorem sec_cons (g : BinaryTreeAut) (x : Bool) (u : List Bool) :
    sec g (x :: u) = sec (sec g [x]) u := by
  rw [← sec_append]
  rfl

/-! ### The root swap -/

/-- Whether `g` swaps the two vertices of level 1. -/
def rootSwap (g : BinaryTreeAut) : Bool := decide ([false] <• g = [true])

theorem singleton_smul (g : BinaryTreeAut) (x : Bool) :
    [x] <• g = [xor x (rootSwap g)] := by
  have hlen : ∀ y : Bool, ([y] <• g).length = 1 := fun y => length_vertex_smul g [y]
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp (hlen false)
  obtain ⟨q, hq⟩ := List.length_eq_one_iff.mp (hlen true)
  have hne : p ≠ q := by
    intro e
    have : [false] <• g = [true] <• g := by rw [hp, hq, e]
    have := congrArg (fun v => v <• g⁻¹) this
    simp only [vertex_smul_smul_inv] at this
    simp at this
  unfold rootSwap
  cases x
  · rw [hp]
    cases p <;> simp
  · rw [hq, hp]
    cases p <;> cases q <;> simp_all

theorem cons_smul (g : BinaryTreeAut) (x : Bool) (u : List Bool) :
    (x :: u) <• g = xor x (rootSwap g) :: (u <• sec g [x]) := by
  have := append_vertex_smul g [x] u
  rw [singleton_smul] at this
  exact this

/-- An automorphism is determined by its root swap and its two sections at level 1. -/
theorem ext_of_rootSwap_sec {g h : BinaryTreeAut} (h0 : rootSwap g = rootSwap h)
    (hf : sec g [false] = sec h [false]) (ht : sec g [true] = sec h [true]) : g = h := by
  have key : ∀ v : List Bool, v <• g = v <• h := by
    intro v
    cases v with
    | nil => rw [nil_smul, nil_smul]
    | cons x u =>
      rw [cons_smul, cons_smul, h0]
      cases x
      · rw [hf]
      · rw [ht]
  have : g⁻¹ = h⁻¹ := Subtype.ext (Equiv.ext fun w => key w)
  exact inv_injective this

/-! ### `a` and the generators -/

theorem grigA_mul_self : grigA * grigA = 1 :=
  Subtype.ext (Equiv.ext fun w => grigAFun_involutive w)

/-! ### Words -/

end GrigBasic

end ErschlerZheng
end

section
/-!
# Words in `a, b, c, d` for the first Grigorchuk group and their sections (helpers for K3)

`ev w` is the product of `a, b, c, d` (Garrido's `grigA … grigD`); `secWord w x` is a word for the
section of `ev w` at the first-level vertex `x`, read letter by letter: `b = (a, c)`, `c = (a, d)`,
`d = (1, b)`, `a = (1, 1)ε`. A word in which `a` and the other letters alternate has at least
`k - 1` letters `a` when it has `k` other letters; every word reduces to such a word.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace BartholdiDev

open GrigBasic

/-- The value of a letter. -/
def letter : Gen4 → BinaryTreeAut
  | .a => grigA
  | .b => grigB
  | .c => grigC
  | .d => grigD

/-- The value of a word. -/
def ev (w : List Gen4) : BinaryTreeAut := (w.map letter).prod

theorem ev_cons (l : Gen4) (w : List Gen4) : ev (l :: w) = letter l * ev w := by
  simp [ev]

theorem ev_append (u v : List Gen4) : ev (u ++ v) = ev u * ev v := by
  simp [ev, List.map_append, List.prod_append]

theorem grigB_mul_self : grigB * grigB = 1 :=
  Subtype.ext (Equiv.ext fun w => (grigBCD_involutive w).1)
theorem grigC_mul_self : grigC * grigC = 1 :=
  Subtype.ext (Equiv.ext fun w => (grigBCD_involutive w).2.1)
theorem grigD_mul_self : grigD * grigD = 1 :=
  Subtype.ext (Equiv.ext fun w => (grigBCD_involutive w).2.2)

theorem letter_mul_self (l : Gen4) : letter l * letter l = 1 := by
  cases l
  · exact grigA_mul_self
  · exact grigB_mul_self
  · exact grigC_mul_self
  · exact grigD_mul_self

theorem letter_inv (l : Gen4) : (letter l)⁻¹ = letter l :=
  inv_eq_of_mul_eq_one_right (letter_mul_self l)

/-- The Klein relations among `b, c, d`. -/
theorem bcd_funs (w : List Bool) :
    grigBFun (grigCFun w) = grigDFun w ∧ grigCFun (grigDFun w) = grigBFun w ∧
      grigDFun (grigBFun w) = grigCFun w ∧ grigCFun (grigBFun w) = grigDFun w ∧
      grigDFun (grigCFun w) = grigBFun w ∧ grigBFun (grigDFun w) = grigCFun w := by
  induction w with
  | nil => simp [grigBFun, grigCFun, grigDFun]
  | cons x w ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
    cases x <;> simp [grigBFun, grigCFun, grigDFun, grigAFun_involutive w, h1, h2, h3, h4, h5, h6]

theorem b_mul_c : grigB * grigC = grigD := Subtype.ext (Equiv.ext fun w => (bcd_funs w).1)
theorem c_mul_d : grigC * grigD = grigB := Subtype.ext (Equiv.ext fun w => (bcd_funs w).2.1)
theorem d_mul_b : grigD * grigB = grigC := Subtype.ext (Equiv.ext fun w => (bcd_funs w).2.2.1)
theorem c_mul_b : grigC * grigB = grigD := Subtype.ext (Equiv.ext fun w => (bcd_funs w).2.2.2.1)
theorem d_mul_c : grigD * grigC = grigB := Subtype.ext (Equiv.ext fun w => (bcd_funs w).2.2.2.2.1)
theorem b_mul_d : grigB * grigD = grigC := Subtype.ext (Equiv.ext fun w => (bcd_funs w).2.2.2.2.2)

/-! ### Sections of the letters -/

theorem vertex_smul_letter (l : Gen4) (v : List Bool) :
    v <• letter l = (letter l : Equiv.Perm (List Bool)) v := by
  rw [vertex_smul_def, letter_inv]

/-- Whether the letter swaps the first level. -/
def swapL : Gen4 → Bool
  | .a => true
  | _ => false

/-- The word for the section of a letter at `[x]`. -/
def secL : Gen4 → Bool → List Gen4
  | .a, _ => []
  | .b, false => [.a]
  | .b, true => [.c]
  | .c, false => [.a]
  | .c, true => [.d]
  | .d, false => []
  | .d, true => [.b]

theorem rootSwap_letter (l : Gen4) : rootSwap (letter l) = swapL l := by
  unfold rootSwap
  rw [vertex_smul_letter]
  cases l <;> rfl

theorem sec_letter (l : Gen4) (x : Bool) : sec (letter l) [x] = ev (secL l x) := by
  apply sec_unique
  intro w
  rw [vertex_smul_letter, vertex_smul_letter]
  cases l <;> cases x
  all_goals simp only [secL, ev, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  all_goals rfl

/-- The word for the section of `ev w` at `[x]`. -/
def secWord : List Gen4 → Bool → List Gen4
  | [], _ => []
  | l :: w, x => secL l x ++ secWord w (xor x (swapL l))

theorem ev_secWord (w : List Gen4) (x : Bool) : ev (secWord w x) = sec (ev w) [x] := by
  induction w generalizing x with
  | nil => simp [secWord, ev, sec_one]
  | cons l w ih =>
    rw [secWord, ev_append, ev_cons, sec_mul, ← sec_letter, singleton_smul, rootSwap_letter, ih]

end BartholdiDev

end ErschlerZheng
end

section
/-!
# Bartholdi's weighted contraction for the first Grigorchuk group (helpers for K3)

With `η³ + η² + η = 2`, `D = η + η² - 1` and weights `|a| = 1`, `|b| = η³/D`, `|c| = (1-η²)/D`,
`|d| = (1-η)/D`, every word `w` has words `w₀, w₁` for its two first-level sections with
`|w₀| + |w₁| ⩽ η (|w| + 1)`: reduce `w` to an alternating word (`aa = 1`, `xx = 1`, `xy = z` and
`|z| ⩽ |x| + |y|`), then each non-`a` letter `x` contributes `η(1 + |x|)` to the sections, and an
alternating word has at most one more non-`a` letter than letters `a`.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace BartholdiDev

open GrigBasic

variable (η : ℝ)

/-- `D = η + η² - 1`. -/
noncomputable def Dη : ℝ := η + η ^ 2 - 1

/-- The weights of the letters. -/
noncomputable def wt : Gen4 → ℝ
  | .a => 1
  | .b => η ^ 3 / Dη η
  | .c => (1 - η ^ 2) / Dη η
  | .d => (1 - η) / Dη η

/-- The weight of a word. -/
noncomputable def wtW (w : List Gen4) : ℝ := (w.map (wt η)).sum

theorem wtW_cons (l : Gen4) (w : List Gen4) : wtW η (l :: w) = wt η l + wtW η w := by
  simp [wtW]

theorem wtW_append (u v : List Gen4) : wtW η (u ++ v) = wtW η u + wtW η v := by
  simp [wtW, List.map_append, List.sum_append]

/-- The contribution of a letter to the two first-level sections. -/
noncomputable def nu (l : Gen4) : ℝ := wtW η (secL l false) + wtW η (secL l true)

variable {η}

/-- The standing assumptions on `η`. -/
structure Good (η : ℝ) : Prop where
  pos : 0 < η
  lt_one : η < 1
  cubic : η ^ 3 + η ^ 2 + η = 2

theorem Good.D_pos (h : Good η) : 0 < Dη η := by
  unfold Dη
  have := h.cubic
  nlinarith [h.pos, h.lt_one]

theorem Good.wt_pos (h : Good η) (l : Gen4) : 0 < wt η l := by
  have hD := h.D_pos
  have := h.pos
  have := h.lt_one
  cases l <;> simp only [wt]
  · norm_num
  · exact div_pos (by positivity) hD
  · exact div_pos (by nlinarith) hD
  · exact div_pos (by linarith) hD

theorem Good.wt_ge (h : Good η) (l : Gen4) : wt η .d ≤ wt η l := by
  have hD := h.D_pos
  have h0 := h.pos
  have h1 := h.lt_one
  have hc := h.cubic
  cases l <;> simp only [wt]
  · rw [div_le_iff₀ hD]; unfold Dη; nlinarith
  · apply div_le_div_of_nonneg_right _ hD.le; nlinarith
  · apply div_le_div_of_nonneg_right _ hD.le; nlinarith
  · exact le_rfl

theorem Good.wtW_nonneg (h : Good η) (w : List Gen4) : 0 ≤ wtW η w :=
  List.sum_nonneg fun x hx => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
    exact (h.wt_pos l).le

theorem Good.length_le (h : Good η) (w : List Gen4) : wt η .d * w.length ≤ wtW η w := by
  induction w with
  | nil => simp [wtW]
  | cons l w ih =>
    rw [wtW_cons, List.length_cons, Nat.cast_succ, mul_add, mul_one]
    linarith [h.wt_ge l]

theorem nu_a : nu η .a = 0 := by simp [nu, secL, wtW]

theorem Good.nu_eq (h : Good η) (l : Gen4) (hl : l ≠ .a) : nu η l = η * (1 + wt η l) := by
  have hD := h.D_pos
  have hc := h.cubic
  cases l
  · exact absurd rfl hl
  · simp only [nu, secL, wtW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wt]
    field_simp
    unfold Dη at *
    nlinarith
  · simp only [nu, secL, wtW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wt]
    field_simp
    unfold Dη at *
    nlinarith
  · simp only [nu, secL, wtW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wt]
    field_simp
    unfold Dη
    ring

theorem secWord_wt (w : List Gen4) (x : Bool) :
    wtW η (secWord w x) + wtW η (secWord w (!x)) = (w.map (nu η)).sum := by
  induction w generalizing x with
  | nil => simp [secWord, wtW]
  | cons l w ih =>
    simp only [secWord, wtW_append, List.map_cons, List.sum_cons]
    have := ih (xor x (swapL l))
    rw [show xor (!x) (swapL l) = !(xor x (swapL l)) by cases x <;> cases swapL l <;> rfl]
    cases x
    · simp only [nu, Bool.not_false] at this ⊢; linarith
    · simp only [nu, Bool.not_true] at this ⊢; linarith

/-! ### Alternating words -/

/-- Exactly one of two consecutive letters is `a`. -/
def Alt (x y : Gen4) : Prop := (x = .a) ≠ (y = .a)

theorem count_nonA_le : ∀ (w : List Gen4), List.IsChain Alt w →
    (w.filter (· ≠ .a)).length ≤ w.count .a + 1
  | [], _ => by simp
  | [x], _ => by cases x <;> simp
  | x :: y :: v, hw => by
    have hxy : Alt x y := (List.isChain_cons_cons.mp hw).1
    have hyv : List.IsChain Alt (y :: v) := (List.isChain_cons_cons.mp hw).2
    by_cases hx : x = .a
    · subst hx
      have := count_nonA_le (y :: v) hyv
      simp only [List.filter_cons, List.count_cons] at this ⊢
      simp at this ⊢
      omega
    · have hy : y = .a := by
        unfold Alt at hxy
        by_contra hy
        exact hxy (by simp [hx, hy])
      subst hy
      have hv : List.IsChain Alt v := hyv.tail
      have := count_nonA_le v hv
      simp only [List.filter_cons, List.count_cons] at this ⊢
      simp [hx] at this ⊢
      omega


theorem Good.nu_sum (h : Good η) (w : List Gen4) :
    (w.map (nu η)).sum = η * wtW η w +
      η * (((w.filter (· ≠ .a)).length : ℝ) - (w.count .a : ℝ)) := by
  induction w with
  | nil => simp [wtW]
  | cons l w ih =>
    rw [List.map_cons, List.sum_cons, ih, wtW_cons]
    by_cases hl : l = .a
    · subst hl
      rw [nu_a]
      simp [List.filter_cons, List.count_cons, wt]
      ring
    · rw [h.nu_eq l hl]
      simp [List.filter_cons, List.count_cons, hl]
      ring

theorem Good.nu_sum_le (h : Good η) (w : List Gen4) (hw : List.IsChain Alt w) :
    (w.map (nu η)).sum ≤ η * (wtW η w + 1) := by
  rw [h.nu_sum]
  have := count_nonA_le w hw
  have hc : ((w.filter (· ≠ .a)).length : ℝ) ≤ (w.count .a : ℝ) + 1 := by exact_mod_cast this
  nlinarith [h.pos]

/-- Two consecutive letters that do not alternate reduce. -/
theorem Good.reduce_pair (h : Good η) (x y : Gen4) (hxy : ¬ Alt x y) :
    ∃ r : List Gen4, ev r = letter x * letter y ∧ wtW η r ≤ wt η x + wt η y ∧ r.length < 2 := by
  have hD := h.D_pos
  have h0 := h.pos
  have h1 := h.lt_one
  have hc := h.cubic
  have hpos := h.wt_pos
  cases x <;> cases y <;> simp [Alt] at hxy
  · exact ⟨[], by simp [ev, letter_mul_self], by simp [wtW]; linarith [hpos .a], by simp⟩
  · exact ⟨[], by simp [ev, letter_mul_self], by simp [wtW]; linarith [hpos .b], by simp⟩
  · refine ⟨[.d], by simp [ev, letter, b_mul_c], ?_, by simp⟩
    simp only [wtW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, wt]
    rw [← add_div]; apply div_le_div_of_nonneg_right _ hD.le; nlinarith
  · refine ⟨[.c], by simp [ev, letter, b_mul_d], ?_, by simp⟩
    simp only [wtW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, wt]
    rw [← add_div]; apply div_le_div_of_nonneg_right _ hD.le; nlinarith
  · refine ⟨[.d], by simp [ev, letter, c_mul_b], ?_, by simp⟩
    simp only [wtW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, wt]
    rw [← add_div]; apply div_le_div_of_nonneg_right _ hD.le; nlinarith
  · exact ⟨[], by simp [ev, letter_mul_self], by simp [wtW]; linarith [hpos .c], by simp⟩
  · refine ⟨[.b], by simp [ev, letter, c_mul_d], ?_, by simp⟩
    simp only [wtW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, wt]
    rw [← add_div]; apply div_le_div_of_nonneg_right _ hD.le; nlinarith
  · refine ⟨[.c], by simp [ev, letter, d_mul_b], ?_, by simp⟩
    simp only [wtW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, wt]
    rw [← add_div]; apply div_le_div_of_nonneg_right _ hD.le; nlinarith
  · refine ⟨[.b], by simp [ev, letter, d_mul_c], ?_, by simp⟩
    simp only [wtW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, wt]
    rw [← add_div]; apply div_le_div_of_nonneg_right _ hD.le; nlinarith
  · exact ⟨[], by simp [ev, letter_mul_self], by simp [wtW]; linarith [hpos .d], by simp⟩

theorem split_of_not_chain : ∀ w : List Gen4, ¬ List.IsChain Alt w →
    ∃ u x y v, w = u ++ x :: y :: v ∧ ¬ Alt x y
  | [], hw => absurd List.IsChain.nil hw
  | [x], hw => absurd (List.IsChain.singleton x) hw
  | x :: y :: v, hw => by
    rw [List.isChain_cons_cons] at hw
    by_cases hxy : Alt x y
    · have : ¬ List.IsChain Alt (y :: v) := fun h => hw ⟨hxy, h⟩
      obtain ⟨u, x', y', v', e, h'⟩ := split_of_not_chain (y :: v) this
      exact ⟨x :: u, x', y', v', by rw [e]; rfl, h'⟩
    · exact ⟨[], x, y, v, rfl, hxy⟩

theorem Good.exists_alt (h : Good η) : ∀ (n : ℕ) (w : List Gen4), w.length ≤ n →
    ∃ w', ev w' = ev w ∧ wtW η w' ≤ wtW η w ∧ List.IsChain Alt w' := by
  intro n
  induction n with
  | zero =>
    intro w hw
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hw)]
    exact ⟨[], rfl, le_rfl, List.IsChain.nil⟩
  | succ n ih =>
    intro w hw
    by_cases hc : List.IsChain Alt w
    · exact ⟨w, rfl, le_rfl, hc⟩
    · obtain ⟨u, x, y, v, rfl, hxy⟩ := split_of_not_chain w hc
      obtain ⟨r, hr, hrw, hrl⟩ := h.reduce_pair x y hxy
      obtain ⟨w', h1, h2, h3⟩ := ih (u ++ r ++ v) (by simp at hw ⊢; omega)
      refine ⟨w', ?_, ?_, h3⟩
      · rw [h1, ev_append, ev_append, ev_append, ev_cons, ev_cons, hr]
        simp [mul_assoc]
      · refine h2.trans ?_
        simp only [wtW_append, wtW_cons]
        linarith

/-- Bartholdi's contraction. -/
theorem Good.contraction (h : Good η) (w : List Gen4) :
    ∃ w₀ w₁ : List Gen4, ev w₀ = sec (ev w) [false] ∧ ev w₁ = sec (ev w) [true] ∧
      wtW η w₀ + wtW η w₁ ≤ η * (wtW η w + 1) := by
  obtain ⟨w', hev, hwt, halt⟩ := h.exists_alt w.length w le_rfl
  refine ⟨secWord w' false, secWord w' true, by rw [ev_secWord, hev],
    by rw [ev_secWord, hev], ?_⟩
  have := secWord_wt (η := η) w' false
  simp only [Bool.not_false] at this
  rw [this]
  calc (w'.map (nu η)).sum ≤ η * (wtW η w' + 1) := h.nu_sum_le w' halt
    _ ≤ η * (wtW η w + 1) := by gcongr; exact h.pos.le

end BartholdiDev

end ErschlerZheng
end

section
/-!
# Counting the weighted balls (helpers for K3)

Iterating the contraction `k` times, an element of weight `⩽ r` has words for its `2^k` sections at
level `k` of total weight `⩽ η^k r + 2^k - 1`; it is determined by those sections and by the root
swaps of its sections above level `k`. So `|WB(r)| ⩽ 2^{2^k} · #{families of words of total length
⩽ L}` with `L = (η^k r + 2^k)/|d|`, and a family count of stars-and-bars type,
`#{f : Fin m → words | Σ|f i| ⩽ L} ⩽ 2^m 8^L`, has no logarithmic loss.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace BartholdiDev

open GrigBasic

/-- Level `k + 1` splits into the subtrees of `0` and `1`. -/
def splitEquiv' (k : ℕ) : Bool × List.Vector Bool k ≃ List.Vector Bool (k + 1) where
  toFun p := p.1 ::ᵥ p.2
  invFun v := (v.head, v.tail)
  left_inv p := by simp
  right_inv v := List.Vector.cons_head_tail v

variable {η : ℝ}

/-- Iterated contraction: words for the level-`k` sections. -/
theorem Good.iterate (h : Good η) : ∀ (k : ℕ) (w : List Gen4),
    ∃ f : List.Vector Bool k → List Gen4, (∀ v, ev (f v) = sec (ev w) v.1) ∧
      ∑ v, wtW η (f v) ≤ η ^ k * wtW η w + (2 ^ k - 1) := by
  intro k
  induction k with
  | zero =>
    intro w
    refine ⟨fun _ => w, fun v => ?_, ?_⟩
    · rw [show v.1 = [] from List.eq_nil_of_length_eq_zero v.2, sec_nil]
    · simp
  | succ k ih =>
    intro w
    obtain ⟨w₀, w₁, h₀, h₁, hw⟩ := h.contraction w
    obtain ⟨f₀, hf₀, hs₀⟩ := ih w₀
    obtain ⟨f₁, hf₁, hs₁⟩ := ih w₁
    let f : List.Vector Bool (k + 1) → List Gen4 := fun v =>
      if v.head then f₁ v.tail else f₀ v.tail
    refine ⟨f, fun v => ?_, ?_⟩
    · have hv : v.1 = v.head :: v.tail.1 := by
        conv_lhs => rw [← List.Vector.cons_head_tail v]
        rfl
      rw [hv, sec_cons]
      simp only [f]
      cases hb : v.head
      · simp only [Bool.false_eq_true, if_false]; rw [hf₀, h₀]
      · simp only [if_true]; rw [hf₁, h₁]
    · rw [← Fintype.sum_equiv (splitEquiv' k) (fun p => wtW η (f (p.1 ::ᵥ p.2)))
        (fun v => wtW η (f v)) (fun p => rfl),
        Fintype.sum_prod_type, Fintype.sum_bool]
      simp only [f, List.Vector.head_cons, List.Vector.tail_cons, if_true, Bool.false_eq_true,
        if_false]
      have hη := h.pos.le
      have hη1 := h.lt_one.le
      have hk : η ^ (k + 1) ≤ 1 := pow_le_one₀ hη hη1
      have hk' : (0 : ℝ) ≤ η ^ k := pow_nonneg hη k
      calc ∑ v, wtW η (f₁ v) + ∑ v, wtW η (f₀ v)
          ≤ (η ^ k * wtW η w₁ + (2 ^ k - 1)) + (η ^ k * wtW η w₀ + (2 ^ k - 1)) := by
            linarith
        _ = η ^ k * (wtW η w₀ + wtW η w₁) + (2 * 2 ^ k - 2) := by ring
        _ ≤ η ^ k * (η * (wtW η w + 1)) + (2 * 2 ^ k - 2) := by gcongr
        _ = η ^ (k + 1) * wtW η w + η ^ (k + 1) + (2 * 2 ^ k - 2) := by ring
        _ ≤ η ^ (k + 1) * wtW η w + (2 ^ (k + 1) - 1) := by rw [pow_succ 2 k]; linarith

/-! ### Determination by sections and root swaps -/

/-- Equal root swaps above level `k` and equal sections at level `k` give equal automorphisms. -/
theorem eq_of_sections : ∀ (k : ℕ) (g h : BinaryTreeAut),
    (∀ v : List Bool, v.length < k → rootSwap (sec g v) = rootSwap (sec h v)) →
    (∀ v : List Bool, v.length = k → sec g v = sec h v) → g = h := by
  intro k
  induction k with
  | zero =>
    intro g h _ hs
    have := hs [] rfl
    rwa [sec_nil, sec_nil] at this
  | succ k ih =>
    intro g h hb hs
    have hx : ∀ x : Bool, sec g [x] = sec h [x] := by
      intro x
      apply ih
      · intro v hv
        rw [← sec_cons, ← sec_cons]
        exact hb (x :: v) (by simp; omega)
      · intro v hv
        rw [← sec_cons, ← sec_cons]
        exact hs (x :: v) (by simp; omega)
    have h0 : rootSwap g = rootSwap h := by
      have := hb [] (by simp)
      rwa [sec_nil, sec_nil] at this
    exact ext_of_rootSwap_sec h0 (hx false) (hx true)


/-! ### Counting families of words -/

instance gen4Fintype : Fintype Gen4 :=
  ⟨{.a, .b, .c, .d}, fun x => by cases x <;> simp⟩

theorem card_gen4 : Fintype.card Gen4 = 4 := rfl

/-- The words of length `ℓ`. -/
def wordsOfLength (ℓ : ℕ) : Finset (List Gen4) :=
  (Finset.univ : Finset (List.Vector Gen4 ℓ)).image List.Vector.toList

theorem card_wordsOfLength (ℓ : ℕ) : (wordsOfLength ℓ).card ≤ 4 ^ ℓ := by
  have h : (Finset.univ : Finset (List.Vector Gen4 ℓ)).card = 4 ^ ℓ := by
    rw [Finset.card_univ, card_vector, card_gen4]
  exact (Finset.card_image_le).trans h.le

theorem mem_wordsOfLength (w : List Gen4) : w ∈ wordsOfLength w.length :=
  Finset.mem_image.mpr ⟨(⟨w, rfl⟩ : List.Vector Gen4 w.length), Finset.mem_univ _, rfl⟩

/-- Prepend a word to a family. -/
def consW {m : ℕ} (q : List Gen4 × (Fin m → List Gen4)) : Fin (m + 1) → List Gen4 :=
  Fin.cons q.1 q.2

/-- Families of `m` words of total length `⩽ L`. -/
def famSet : (m : ℕ) → ℕ → Finset (Fin m → List Gen4)
  | 0, _ => {fun i => i.elim0}
  | m + 1, L => (Finset.HasAntidiagonal.antidiagonal L).biUnion fun p =>
      ((wordsOfLength p.1) ×ˢ (famSet m p.2)).image consW

theorem famSet_succ (m L : ℕ) : famSet (m + 1) L =
    (Finset.HasAntidiagonal.antidiagonal L).biUnion fun p =>
      ((wordsOfLength p.1) ×ˢ (famSet m p.2)).image consW := rfl

theorem mem_famSet : ∀ (m L : ℕ) (f : Fin m → List Gen4), ∑ i, (f i).length ≤ L →
    f ∈ famSet m L
  | 0, L, f, _ => by
    simp only [famSet, Finset.mem_singleton]
    funext i; exact i.elim0
  | m + 1, L, f, hf => by
    simp only [famSet_succ, Finset.mem_biUnion, Finset.mem_antidiagonal, Finset.mem_image,
      Finset.mem_product]
    rw [Fin.sum_univ_succ] at hf
    refine ⟨((f 0).length, L - (f 0).length), by simp; omega, ((f 0), Fin.tail f),
      ⟨mem_wordsOfLength _, mem_famSet m _ _ (by simp only [Fin.tail]; omega)⟩, ?_⟩
    exact Fin.cons_self_tail f

theorem sum_antidiagonal_le (L : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal L, 4 ^ p.1 * 8 ^ p.2 ≤ 2 * 8 ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.Nat.sum_antidiagonal_succ]
    have : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal L, 4 ^ (p.1 + 1) * 8 ^ p.2 =
        4 * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal L, 4 ^ p.1 * 8 ^ p.2 := by
      rw [Finset.mul_sum]; congr 1; funext p; ring
    rw [this]
    simp only [pow_zero, one_mul, pow_succ]
    nlinarith

theorem card_famSet : ∀ (m L : ℕ), (famSet m L).card ≤ 2 ^ m * 8 ^ L
  | 0, L => by simp [famSet]; exact Nat.one_le_pow _ _ (by norm_num)
  | m + 1, L => by
    rw [famSet_succ]
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ p ∈ Finset.HasAntidiagonal.antidiagonal L,
          (((wordsOfLength p.1) ×ˢ (famSet m p.2)).image consW).card
        ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal L, 4 ^ p.1 * (2 ^ m * 8 ^ p.2) := by
          refine Finset.sum_le_sum fun p _ => Finset.card_image_le.trans ?_
          rw [Finset.card_product]
          exact Nat.mul_le_mul (card_wordsOfLength _) (card_famSet m p.2)
      _ = 2 ^ m * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal L, 4 ^ p.1 * 8 ^ p.2 := by
          rw [Finset.mul_sum]; congr 1; funext p; ring
      _ ≤ 2 ^ m * (2 * 8 ^ L) := Nat.mul_le_mul_left _ (sum_antidiagonal_le L)
      _ = 2 ^ (m + 1) * 8 ^ L := by ring


/-! ### The weighted balls -/

/-- Elements given by a word of weight `⩽ r`. -/
def WB (η : ℝ) (r : ℝ) : Set BinaryTreeAut := {g | ∃ w : List Gen4, ev w = g ∧ wtW η w ≤ r}

/-- Vertices of length `< k`. -/
abbrev Below (k : ℕ) := (j : Fin k) × List.Vector Bool j

theorem card_below_le (k : ℕ) : Fintype.card (Below k) ≤ 2 ^ k := by
  rw [Fintype.card_sigma]
  simp only [card_vector, Fintype.card_bool]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [pow_succ]
    omega

theorem Good.card_WB_le (h : Good η) (k : ℕ) (r : ℝ) :
    Nat.card (WB η r) ≤ 2 ^ (2 ^ k) * (2 ^ (2 ^ k) * 8 ^ ⌊(η ^ k * r + 2 ^ k) / wt η .d⌋₊) := by
  classical
  set L := ⌊(η ^ k * r + 2 ^ k) / wt η .d⌋₊ with hL
  have hcardV : Fintype.card (List.Vector Bool k) = 2 ^ k := by
    rw [card_vector, Fintype.card_bool]
  let e : List.Vector Bool k ≃ Fin (2 ^ k) := Fintype.equivFinOfCardEq hcardV
  have hδ := h.wt_pos .d
  -- the chosen data of an element of the ball
  have hdata : ∀ g ∈ WB η r, ∃ f : List.Vector Bool k → List Gen4,
      (∀ v, ev (f v) = sec g v.1) ∧ ∑ v, (f v).length ≤ L := by
    rintro g ⟨w, rfl, hw⟩
    obtain ⟨f, hf, hs⟩ := h.iterate k w
    refine ⟨f, hf, ?_⟩
    apply Nat.le_floor
    rw [le_div_iff₀ hδ]
    push_cast
    calc (∑ v, ((f v).length : ℝ)) * wt η .d = ∑ v, wt η .d * (f v).length := by
          rw [Finset.sum_mul]; congr 1; funext v; ring
      _ ≤ ∑ v, wtW η (f v) := Finset.sum_le_sum fun v _ => h.length_le (f v)
      _ ≤ η ^ k * wtW η w + (2 ^ k - 1) := hs
      _ ≤ η ^ k * r + 2 ^ k := by
          have : 0 ≤ η ^ k := pow_nonneg h.pos.le k
          nlinarith
  choose F hF hFL using hdata
  set S : Finset ((Below k → Bool) × (Fin (2 ^ k) → List Gen4)) :=
    (Finset.univ : Finset (Below k → Bool)) ×ˢ famSet (2 ^ k) L with hS
  let Ψ : WB η r → S := fun g =>
    ⟨(fun p => rootSwap (sec (g : BinaryTreeAut) p.2.1), F g g.2 ∘ e.symm), by
      rw [hS, Finset.mem_product]
      refine ⟨Finset.mem_univ _, mem_famSet _ _ _ ?_⟩
      show ∑ i, (F g g.2 (e.symm i)).length ≤ L
      rw [Fintype.sum_equiv e.symm (fun i => (F g g.2 (e.symm i)).length)
        (fun v => (F g g.2 v).length) (fun i => rfl)]
      exact hFL g g.2⟩
  have hΨ : Function.Injective Ψ := by
    intro g g' hgg'
    have h1 := congrArg (fun p : S => p.1.1) hgg'
    have h2 := congrArg (fun p : S => p.1.2) hgg'
    simp only [Ψ] at h1 h2
    apply Subtype.ext
    apply eq_of_sections k
    · intro v hv
      have := congrFun h1 ⟨⟨v.length, hv⟩, ⟨v, rfl⟩⟩
      exact this
    · intro v hv
      have := congrFun h2 (e ⟨v, hv⟩)
      simp only [Function.comp_apply] at this
      have hx : e.symm (e ⟨v, hv⟩) = (⟨v, hv⟩ : List.Vector Bool k) := e.symm_apply_apply _
      rw [hx] at this
      rw [← hF g g.2 ⟨v, hv⟩, ← hF g' g'.2 ⟨v, hv⟩, this]
  have hfin := Nat.card_le_card_of_injective Ψ hΨ
  rw [Nat.card_eq_finsetCard, hS, Finset.card_product, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool] at hfin
  refine hfin.trans (Nat.mul_le_mul ?_ (card_famSet _ _))
  exact Nat.pow_le_pow_right (by norm_num) (card_below_le k)

end BartholdiDev

end ErschlerZheng
end

section
/-!
# The cubic `x³ - x² - 2x - 4`: positive roots exceed 2 and lie in `(2.4675, 2.4676)`
-/

namespace ErschlerZheng

namespace CubicBase

theorem pos_root_gt_two {x : ℝ} (hx : 0 < x) (h : x ^ 3 - x ^ 2 - 2 * x - 4 = 0) : 2 < x := by
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hc), mul_nonneg (mul_nonneg hx.le hx.le)
    (sub_nonneg.mpr hc)]

end CubicBase

end ErschlerZheng
end

section
/-!
# K3: Bartholdi's upper bound `v(n) ⩽ exp(C n^{α_0})` for the first Grigorchuk group

With `η = 2/λ_0` (A19: the real root of `X³ + X² + X - 2`) and Bartholdi's weights, every element
of weight `⩽ r` is determined by the root swaps of its sections above level `k` and by words for its
`2^k` sections at level `k`, of total weight `⩽ η^k r + 2^k` (the contraction
`|g₀| + |g₁| ⩽ η(|g| + 1)`). Taking `λ_0^{k-1} ⩽ r + 1 < λ_0^k`, both are `exp(O(2^k))` and
`2^{k-1} = (λ_0^{k-1})^{α_0} ⩽ (r+1)^{α_0}`, since `λ_0^{α_0} = 2`. A finite generating set has
bounded weights, so its balls sit in weighted balls of proportional radius.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace BartholdiDev

open GrigBasic

variable {η : ℝ}

theorem WB_finite (h : Good η) (r : ℝ) : (WB η r).Finite := by
  have hδ := h.wt_pos .d
  refine ((List.finite_length_le Gen4 ⌊r / wt η .d⌋₊).image ev).subset ?_
  rintro g ⟨w, rfl, hw⟩
  refine ⟨w, ?_, rfl⟩
  show w.length ≤ ⌊r / wt η .d⌋₊
  apply Nat.le_floor
  rw [le_div_iff₀ hδ]
  have := h.length_le w
  linarith

/-- The weighted balls grow like `exp(C (r+1)^{α})` when `λ^α = 2`, `λ = 2/η`. -/
theorem Good.card_WB_le_exp (h : Good η) {α : ℝ} (hα : 0 < α) (hlamα : (2 / η) ^ α = 2) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ r : ℝ, 0 ≤ r → (Nat.card (WB η r) : ℝ) ≤ Real.exp (C₁ * (r + 1) ^ α) := by
  have h0 := h.pos
  have h1 := h.lt_one
  have hδ := h.wt_pos .d
  set lam := 2 / η with hlam
  have hlam1 : 1 < lam := by rw [hlam, lt_div_iff₀ h0]; linarith
  set C₁ := 2 * (2 * Real.log 2 + 2 * Real.log 8 / wt η .d) with hC₁
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    positivity
  refine ⟨C₁, hC₁0, fun r hr => ?_⟩
  classical
  have hex : ∃ k : ℕ, r + 1 < lam ^ k := pow_unbounded_of_one_lt _ hlam1
  set k := Nat.find hex with hk
  have hk1 : r + 1 < lam ^ k := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro e
    rw [e, pow_zero] at hk1
    linarith
  have hkm : lam ^ (k - 1) ≤ r + 1 := by
    have := Nat.find_min hex (show k - 1 < k by omega)
    push Not at this
    exact this
  -- `η^k r ⩽ 2^k`
  have hηk : η ^ k * r ≤ 2 ^ k := by
    have e : η ^ k * lam ^ k = 2 ^ k := by
      rw [← mul_pow, hlam]; congr 1; field_simp
    calc η ^ k * r ≤ η ^ k * (r + 1) := by gcongr; linarith
      _ ≤ η ^ k * lam ^ k := by gcongr
      _ = 2 ^ k := e
  -- `2^k ⩽ 2 (r+1)^α`
  have h2k : (2 : ℝ) ^ k ≤ 2 * (r + 1) ^ α := by
    have e1 : (2 : ℝ) ^ (k - 1) = (lam ^ (k - 1)) ^ α := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith),
        mul_comm, Real.rpow_mul (by linarith), hlamα]
    have e2 : (lam ^ (k - 1)) ^ α ≤ (r + 1) ^ α :=
      Real.rpow_le_rpow (by positivity) hkm hα.le
    calc (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
          rw [← pow_succ']; congr 1; omega
      _ ≤ 2 * (r + 1) ^ α := by rw [e1]; gcongr
  -- the count
  have hc := h.card_WB_le k r
  set L := ⌊(η ^ k * r + 2 ^ k) / wt η .d⌋₊ with hL
  have hLle : (L : ℝ) ≤ 2 * 2 ^ k / wt η .d := by
    calc (L : ℝ) ≤ (η ^ k * r + 2 ^ k) / wt η .d := Nat.floor_le (by positivity)
      _ ≤ 2 * 2 ^ k / wt η .d := by gcongr; linarith
  have hcR : (Nat.card (WB η r) : ℝ) ≤ 2 ^ (2 ^ k) * (2 ^ (2 ^ k) * 8 ^ L) := by exact_mod_cast hc
  calc (Nat.card (WB η r) : ℝ) ≤ 2 ^ (2 ^ k) * (2 ^ (2 ^ k) * 8 ^ L) := hcR
    _ = Real.exp (2 ^ k * (2 * Real.log 2) + L * Real.log 8) := by
        have e2 : ((2 : ℝ)) ^ (2 ^ k) = Real.exp ((2 ^ k : ℕ) * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
        have e8 : ((8 : ℝ)) ^ L = Real.exp (L * Real.log 8) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
        rw [e2, e8, ← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast
        ring
    _ ≤ Real.exp (C₁ * (r + 1) ^ α) := by
        apply Real.exp_le_exp.mpr
        have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have hl8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
        have hLl : (L : ℝ) * Real.log 8 ≤ 2 * 2 ^ k / wt η .d * Real.log 8 :=
          mul_le_mul_of_nonneg_right hLle hl8
        have : (2 : ℝ) ^ k * (2 * Real.log 2) + 2 * 2 ^ k / wt η .d * Real.log 8 =
            2 ^ k * (2 * Real.log 2 + 2 * Real.log 8 / wt η .d) := by ring
        have hpos : 0 ≤ 2 * Real.log 2 + 2 * Real.log 8 / wt η .d := by positivity
        calc (2 : ℝ) ^ k * (2 * Real.log 2) + L * Real.log 8
            ≤ 2 ^ k * (2 * Real.log 2 + 2 * Real.log 8 / wt η .d) := by linarith
          _ ≤ 2 * (r + 1) ^ α * (2 * Real.log 2 + 2 * Real.log 8 / wt η .d) := by gcongr
          _ = C₁ * (r + 1) ^ α := by rw [hC₁]; ring

/-- Every element of the first Grigorchuk group is the value of a word. -/
theorem exists_word (g : BinaryTreeAut) (hg : g ∈ GrigorchukGroup) : ∃ w, ev w = g := by
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨[.a], by simp [ev, letter]⟩
    · exact ⟨[.b], by simp [ev, letter]⟩
    · exact ⟨[.c], by simp [ev, letter]⟩
    · exact ⟨[.d], by simp [ev, letter]⟩
  | one => exact ⟨[], rfl⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨u, rfl⟩ := ihg
    obtain ⟨v, rfl⟩ := ihh
    exact ⟨u ++ v, ev_append u v⟩
  | inv g _ ihg =>
    obtain ⟨u, rfl⟩ := ihg
    exact ⟨u.reverse, ev_reverse u⟩
where
  ev_reverse (u : List Gen4) : ev u.reverse = (ev u)⁻¹ := by
    induction u with
    | nil => simp [ev]
    | cons l u ih =>
      rw [List.reverse_cons, ev_append, ih, ev_cons l u, mul_inv_rev, letter_inv]
      simp [ev]

theorem wtW_reverse (u : List Gen4) : wtW η u.reverse = wtW η u := by
  simp [wtW, List.map_reverse, List.sum_reverse]

end BartholdiDev

end ErschlerZheng

namespace Bartholdi

end Bartholdi
end

section
open scoped RightActions
open Garrido
open Bartholdi
open ErschlerZheng ErschlerZheng.BartholdiDev ErschlerZheng.GrigBasic in
theorem solution (S : Finset Garrido.GrigorchukGroup)
    (_hS : Subgroup.closure (S : Set Garrido.GrigorchukGroup) = ⊤) :
    ∃ C : ℝ, ∀ n : ℕ, (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) n) : ℝ) ≤
      Real.exp (C * (n : ℝ) ^ ErschlerZheng.alpha0) := by
  -- η from A19
  obtain ⟨-, ⟨hl0, hlroot⟩, -, -, -, -, η, hηroot, -, hlη⟩ :=
    existsUnique_pos_root_and_alpha0_approx_and_charpoly_matrixM
  have hl2 : 2 < lambda0 := CubicBase.pos_root_gt_two hl0 hlroot
  have hη0 : 0 < η := by
    by_contra h; push Not at h
    have : 2 / η ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) h
    linarith
  have hgood : Good η := by
    refine ⟨hη0, ?_, by linarith⟩
    have : η = 2 / lambda0 := by rw [hlη]; field_simp
    rw [this, div_lt_one (by linarith)]
    exact hl2
  have hlamα : 2 / η = lambda0 := hlη.symm
  have hlog : 0 < Real.log lambda0 := Real.log_pos (by linarith)
  have hα : 0 < alpha0 := by
    unfold alpha0; exact div_pos (Real.log_pos (by norm_num)) hlog
  have hpow : (2 / η) ^ alpha0 = 2 := by
    rw [hlamα, Real.rpow_def_of_pos (by linarith)]
    unfold alpha0
    rw [mul_div_cancel₀ _ hlog.ne', Real.exp_log (by norm_num)]
  obtain ⟨C₁, hC₁0, hC₁⟩ := hgood.card_WB_le_exp hα hpow
  -- words for the generators
  have hw : ∀ s : Garrido.GrigorchukGroup, ∃ w, ev w = (s : BinaryTreeAut) :=
    fun s => exists_word s s.2
  choose W hW using hw
  set M : ℝ := ∑ s ∈ S, wtW η (W s) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun s _ => hgood.wtW_nonneg _
  have hWle : ∀ s ∈ S, wtW η (W s) ≤ M := fun s hs =>
    Finset.single_le_sum (fun t _ => hgood.wtW_nonneg (W t)) hs
  -- balls sit in weighted balls
  have hsub : ∀ n : ℕ, Subtype.val '' Chou.wordBall (S : Set Garrido.GrigorchukGroup) n ⊆
      WB η (n * M) := by
    intro n
    rintro _ ⟨g, ⟨l, hl, hls, rfl⟩, rfl⟩
    -- a word for each factor
    have : ∀ l : List Garrido.GrigorchukGroup, (∀ x ∈ l, x ∈ (S : Set _) ∨ x⁻¹ ∈ (S : Set _)) →
        ∃ w, ev w = ((l.prod : Garrido.GrigorchukGroup) : BinaryTreeAut) ∧
          wtW η w ≤ l.length * M := by
      intro l hl
      induction l with
      | nil => exact ⟨[], rfl, by simp [wtW]⟩
      | cons x l ih =>
        obtain ⟨w, hw1, hw2⟩ := ih (fun y hy => hl y (by simp [hy]))
        have hx : ∃ u, ev u = (x : BinaryTreeAut) ∧ wtW η u ≤ M := by
          rcases hl x (by simp) with h | h
          · exact ⟨W x, hW x, hWle x h⟩
          · refine ⟨(W x⁻¹).reverse, ?_, by rw [wtW_reverse]; exact hWle _ h⟩
            rw [exists_word.ev_reverse, hW]
            simp
        obtain ⟨u, hu1, hu2⟩ := hx
        refine ⟨u ++ w, ?_, ?_⟩
        · rw [ev_append, hu1, hw1, List.prod_cons, Subgroup.coe_mul]
        · rw [wtW_append, List.length_cons]; push_cast; linarith
    obtain ⟨w, hw1, hw2⟩ := this l hls
    refine ⟨w, hw1, hw2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hM0
  refine ⟨C₁ * (M + 1) ^ alpha0, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : Chou.wordBall (S : Set Garrido.GrigorchukGroup) 0 = {1} := by
      ext g
      constructor
      · rintro ⟨l, hl, -, rfl⟩
        rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)]
        simp
      · rintro rfl
        exact ⟨[], le_rfl, by simp, rfl⟩
    rw [h0, Nat.cast_zero, Real.zero_rpow hα.ne', mul_zero, Real.exp_zero]
    simp
  have hcard : (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) n) : ℝ) ≤
      Nat.card (WB η (n * M)) := by
    rw [← Nat.card_image_of_injective Subtype.val_injective]
    exact_mod_cast Nat.card_mono (WB_finite hgood _) (hsub n)
  refine hcard.trans ((hC₁ _ (by positivity)).trans (Real.exp_le_exp.mpr ?_))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : ((n : ℝ) * M + 1) ^ alpha0 ≤ ((M + 1) * n) ^ alpha0 :=
    Real.rpow_le_rpow (by positivity) (by nlinarith) hα.le
  rw [Real.mul_rpow (by positivity) (by positivity)] at this
  calc C₁ * ((n : ℝ) * M + 1) ^ alpha0 ≤ C₁ * ((M + 1) ^ alpha0 * (n : ℝ) ^ alpha0) :=
        mul_le_mul_of_nonneg_left this hC₁0
    _ = C₁ * (M + 1) ^ alpha0 * (n : ℝ) ^ alpha0 := by ring
end
