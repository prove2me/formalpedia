-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.enumScripts_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:48.116678+00:00
-- url     : https://prove2.me/submissions/04322968-ea0a-4737-bec2-364735525ec4

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_EnumCfg_delPhase
import Theorems.Thm_EditMulticoloring_Dev_Ram_EnumCfg_insPhase
import Theorems.Thm_EditMulticoloring_Dev_Ram_EnumCfg_lev_zero_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_EnumCfg_repPhase
import Theorems.Thm_EditMulticoloring_Dev_Ram_EnumCfg_visitC_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le

section
-- module Solutions.EditMulticoloring.RamEnum
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# The scripts enumerator (q379, Part L)

`enumScripts q s cfg body` runs `body` once per element of `visits s x` (in list order), each
time with the visited word in array `cfg.vis` (offset 0) and its length in register `cfg.VL`.
Main theorem: `enumScripts_spec` (RamEnum3.lean); level induction in RamEnum2.lean.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## The visit list -/

theorem finRange_flatMap {q : ℕ} {β : Type*} (F : Fin q → List β) :
    (List.finRange q).flatMap F = (List.range q).flatMap (finFlat F) := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ_last, List.range_succ, List.flatMap_append, List.flatMap_append,
      List.flatMap_map]
    rw [ih (fun a => F a.castSucc)]
    congr 1
    · apply List.flatMap_congr
      intro a ha
      have ha' : a < n := List.mem_range.mp ha
      simp [finFlat, ha', Nat.lt_succ_of_lt ha']
    · simp [finFlat, Fin.last]

theorem flatMap_filter_eq {α β : Type*} (l : List α) (p : α → Bool) (F : α → List β) :
    (l.filter p).flatMap F = l.flatMap (fun a => if p a then F a else []) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a <;> simp [List.filter_cons, h, ih]

theorem visits_succ {q : ℕ} (s : ℕ) (x : Word q) :
    visits (s + 1) x = x ::
      ((List.range (x.length + 1)).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun a => visits s (insW x i a))) ++
        (List.range x.length).flatMap (fun i => visits s (delW x i)) ++
        (List.range x.length).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun a =>
            if x[i]? = some a then [] else visits s (repW x i a)))) := by
  simp only [visits, scripts, List.map_cons, availableEdits, List.flatMap_append, List.map_append,
    List.map_flatMap]
  congr 1
  congr 1
  congr 1
  · rw [List.flatMap_assoc]
    apply List.flatMap_congr
    intro i hi
    have hi' : i ≤ x.length := Nat.lt_succ_iff.mp (List.mem_range.mp hi)
    rw [List.flatMap_map, ← finRange_flatMap]
    apply List.flatMap_congr
    intro a _
    simp [applyEdit, hi', insW, List.map_map]
  · rw [List.flatMap_map]
    apply List.flatMap_congr
    intro i hi
    have hi' : i < x.length := List.mem_range.mp hi
    simp [applyEdit, hi', delW, List.map_map]
  · rw [List.flatMap_assoc]
    apply List.flatMap_congr
    intro i hi
    have hi' : i < x.length := List.mem_range.mp hi
    rw [List.flatMap_map, flatMap_filter_eq, ← finRange_flatMap]
    apply List.flatMap_congr
    intro a _
    by_cases ha : x[i]? = some a
    · simp [ha]
    · have ha2 : ¬ x[i] = a := fun h => ha (by rw [List.getElem?_eq_getElem hi', h])
      simp [applyEdit, hi', ha, ha2, repW, List.map_map]

/-! ## Configuration -/

namespace EnumCfg
variable (c : EnumCfg)

theorem Agree.setR {s r : ℕ} (hr : c.ownsReg s r) (st : HS) (v : ℕ) : c.Agree s st (st.setR r v) :=
  ⟨fun r' hr' => by
      have : r' ≠ r := fun h => hr' (h ▸ hr)
      simp [Function.update_of_ne this], fun _ _ _ => rfl, rfl, rfl⟩

theorem Fr.agree {s w Y : ℕ} {st st' : HS} (h : c.Fr w Y st st') (hw : c.ownsReg s w)
    (hY : c.ownsArr s Y) : c.Agree s st st' := by
  refine ⟨fun r hr => h.1 r ?_ ?_, fun y i hy => h.2.1 y i ?_, h.2.2.1, h.2.2.2⟩
  · simp only [ownsReg, not_and, not_le] at hr; omega
  · rintro rfl; exact hr hw
  · rintro rfl; exact hy hY

/-! ## Code -/

end EnumCfg

/-! ## Specs of the pieces -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEnum2
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# The scripts enumerator, part 2: the three edit phases (q379, Part L)
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Membership in the visit list -/

/-! ## Positions in the visit list -/

namespace EnumCfg
variable (c : EnumCfg) (inp : ℕ → ℕ) (B : ℕ)

theorem ownsReg_of {s r : ℕ} (h1 : c.r0 ≤ r) (h2 : r ≤ c.r0 + (18 + 3 * s)) : c.ownsReg s r :=
  ⟨h1, h2⟩

theorem ownsArr_of {s y : ℕ} (h1 : c.a0 ≤ y) (h2 : y ≤ c.a0 + 1 + s) : c.ownsArr s y :=
  ⟨h1, h2⟩

section Phases
variable {q : ℕ} {α : Type*} (s L : ℕ) (body : Cmd) (Inv : α → HS → Prop) (f : α → Word q → α)
  (cb : ℕ) (Ok : α → Word q → Prop)

theorem LQ.setR (hstable : ∀ a st st', Inv a st → c.Agree s st st' → Inv a st')
    {k r : ℕ} (hr : c.ownsReg s r) (hr' : r < c.lenR k) {st0 st : HS} {acc : α}
    (h : c.LQ Inv s k st0 acc st) (v : ℕ) : c.LQ Inv s k st0 acc (st.setR r v) := by
  refine ⟨hstable _ _ _ h.1 (Agree.setR c hr st v), fun r' h1 h2 => ?_, fun y i h1 h2 => h.2.2 y i h1 h2⟩
  have : r' ≠ r := by omega
  simp only [HS.setR_regs, Function.update_of_ne this]
  exact h.2.1 r' h1 h2

theorem lev_succ_spec (hstable : ∀ a st st', Inv a st → c.Agree s st st' → Inv a st')
    (hbody : ∀ a st (w : Word q), Inv a st → Ok a w → st.regs c.VL = w.length →
      WordAt st c.vis 0 w →
      Inv (f a w) (body.exec inp st) ∧ c.BodyFrame s st (body.exec inp st) ∧
      body.cost inp B st ≤ cb)
    (k : ℕ) (hk : k + 1 ≤ s) (IH : c.IHk inp B s L body Inv f cb Ok k) :
    c.IHk inp B s L body Inv f cb Ok (k + 1) := by
  intro x a st hxL hok hInv hlen hx
  obtain ⟨v1, v2, v3, v4⟩ := c.visitC_spec inp B (k + 1) x st hlen hx (c.enumM q L s)
    (by simp only [enumM]; omega)
  set st1 := (c.visitC (k + 1)).exec inp st with hst1
  have hInv1 := hstable _ _ _ hInv (Fr.agree c v3 (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
    (c.ownsArr_of (by simp <;> omega) (by simp <;> omega)))
  obtain ⟨b1, b2, b3⟩ := hbody a _ x hInv1
    (by simpa [visits_succ] using hok 0 (by simp [visits_succ])) v1 v2
  set st2 := body.exec inp st1 with hst2
  have Q2 : c.LQ Inv s (k + 1) st (f a x) st2 := by
    refine ⟨b1, fun r h1 h2 => ?_, fun y j h1 h2 => ?_⟩
    · rw [b2.1 r (c.ownsReg_of (by simp at h1 ⊢ <;> omega) (by simp at h2 ⊢ <;> omega))
        (by simp at h1 ⊢ <;> omega)]
      exact v3.1 r (Or.inr (by simp at h1 ⊢ <;> omega)) (by simp at h1 ⊢ <;> omega)
    · rw [b2.2 y j (c.ownsArr_of (by simp at h1 ⊢ <;> omega) (by simp at h2 ⊢ <;> omega))
        (by simp at h1 ⊢ <;> omega)]
      exact v3.2.1 y j (by simp at h1 ⊢ <;> omega)
  have hlenQ : ∀ {acc : α} {st' : HS}, c.LQ Inv s (k + 1) st acc st' →
      st'.regs (c.lenR (k + 1)) = x.length := fun h => (h.2.1 _ le_rfl (by simp <;> omega)).trans hlen
  set st3 := (st2.setR c.one 1).setR c.cnt (x.length + 1) with hst3
  have e3 : (ar .add c.cnt (c.lenR (k + 1)) c.one).exec inp (st2.setR c.one 1) = st3 := by
    simp only [exec_ar, arith_add, HS.setR_regs]
    rw [Function.update_of_ne (by simp <;> omega), Function.update_self, hlenQ Q2]
  have Q3 : c.LQ Inv s (k + 1) st (f a x) st3 :=
    LQ.setR c s Inv hstable (c.ownsReg_of (by simp <;> omega) (by simp <;> omega)) (by simp <;> omega)
      (LQ.setR c s Inv hstable (c.ownsReg_of (by simp <;> omega) (by simp <;> omega)) (by simp <;> omega) Q2 1) _
  obtain ⟨I1, I2⟩ := c.insPhase inp B s L body Inv f cb Ok hstable k hk IH x hxL a hok st hlen hx
    _ st3 [x] (((List.range x.length).flatMap (fun i => visits k (delW x i))) ++ ((List.range x.length).flatMap (fun i =>
        (List.range q).flatMap (finFlat fun b =>
          if x[i]? = some b then [] else visits k (repW x i b)))))
    (by rw [visits_succ]; simp only [List.cons_append, List.nil_append, List.append_assoc])
    (by simp) Q3 (by simp [hst3])
  set st4 := (c.insLoop q body k).exec inp st3 with hst4
  set st5 := st4.setR c.cnt x.length with hst5
  have e5 : (cp c.cnt (c.lenR (k + 1))).exec inp st4 = st5 := by
    simp only [exec_cp]; rw [hlenQ I1]
  have Q5 : c.LQ Inv s (k + 1) st _ st5 := LQ.setR c s Inv hstable (c.ownsReg_of (by simp <;> omega) (by simp <;> omega)) (by simp <;> omega) I1 x.length
  obtain ⟨D1, D2⟩ := c.delPhase inp B s L body Inv f cb Ok hstable k hk IH x hxL a hok st hlen hx
    _ st5 (x :: ((List.range (x.length + 1)).flatMap (fun i =>
        (List.range q).flatMap (finFlat fun b => visits k (insW x i b))))) ((List.range x.length).flatMap (fun i =>
        (List.range q).flatMap (finFlat fun b =>
          if x[i]? = some b then [] else visits k (repW x i b))))
    (by rw [visits_succ]; simp only [List.cons_append, List.append_assoc])
    (by simp [List.foldl_cons]) Q5 (by simp [hst5])
  set st6 := (c.delLoop q body k).exec inp st5 with hst6
  set st7 := st6.setR c.cnt x.length with hst7
  have e7 : (cp c.cnt (c.lenR (k + 1))).exec inp st6 = st7 := by
    simp only [exec_cp]; rw [hlenQ D1]
  have Q7 : c.LQ Inv s (k + 1) st _ st7 := LQ.setR c s Inv hstable (c.ownsReg_of (by simp <;> omega) (by simp <;> omega)) (by simp <;> omega) D1 x.length
  obtain ⟨P1, P2⟩ := c.repPhase inp B s L body Inv f cb Ok hstable k hk IH x hxL a hok st hlen hx
    _ st7 (x :: (((List.range (x.length + 1)).flatMap (fun i =>
        (List.range q).flatMap (finFlat fun b => visits k (insW x i b)))) ++ ((List.range x.length).flatMap (fun i => visits k (delW x i))))) []
    (by rw [visits_succ]; simp only [List.cons_append, List.append_assoc, List.append_nil])
    (by simp [List.foldl_cons, List.foldl_append]) Q7 (by simp [hst7])
  have hex : (c.lev q body (k + 1)).exec inp st = (c.repLoop q body k).exec inp st7 := by
    have : (c.lev q body (k + 1)).exec inp st = (c.repLoop q body k).exec inp
        ((cp c.cnt (c.lenR (k + 1))).exec inp ((c.delLoop q body k).exec inp
        ((cp c.cnt (c.lenR (k + 1))).exec inp ((c.insLoop q body k).exec inp
        ((ar .add c.cnt (c.lenR (k + 1)) c.one).exec inp (st2.setR c.one 1)))))) := rfl
    rw [this, e3, ← hst4, e5, ← hst6, e7]
  have hfold : (visits (k + 1) x).foldl f a =
      (((List.range x.length).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun b =>
            if x[i]? = some b then [] else visits k (repW x i b)))).foldl f
      (((List.range x.length).flatMap (fun i => visits k (delW x i))).foldl f
      (((List.range (x.length + 1)).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun b => visits k (insW x i b)))).foldl f (f a x)))) := by
    rw [visits_succ]; simp only [List.foldl_cons, List.foldl_append]
  rw [hex, hfold]
  refine ⟨P1.1, P1.2, ?_⟩
  have hc : (c.lev q body (k + 1)).cost inp B st =
      (c.visitC (k + 1)).cost inp B st + (body.cost inp B st1 +
      ((lit c.one 1).cost inp B st2 + ((ar .add c.cnt (c.lenR (k + 1)) c.one).cost inp B
        (st2.setR c.one 1) +
      ((c.insLoop q body k).cost inp B st3 + ((cp c.cnt (c.lenR (k + 1))).cost inp B st4 +
      ((c.delLoop q body k).cost inp B st5 + ((cp c.cnt (c.lenR (k + 1))).cost inp B st6 +
      ((c.repLoop q body k).cost inp B st7 + 0)))))))) := by
    have : (c.lev q body (k + 1)).cost inp B st =
      (c.visitC (k + 1)).cost inp B st + (body.cost inp B st1 +
      ((lit c.one 1).cost inp B st2 + ((ar .add c.cnt (c.lenR (k + 1)) c.one).cost inp B
        (st2.setR c.one 1) +
      ((c.insLoop q body k).cost inp B
        ((ar .add c.cnt (c.lenR (k + 1)) c.one).exec inp (st2.setR c.one 1)) +
      ((cp c.cnt (c.lenR (k + 1))).cost inp B ((c.insLoop q body k).exec inp
        ((ar .add c.cnt (c.lenR (k + 1)) c.one).exec inp (st2.setR c.one 1))) +
      ((c.delLoop q body k).cost inp B ((cp c.cnt (c.lenR (k + 1))).exec inp
        ((c.insLoop q body k).exec inp
        ((ar .add c.cnt (c.lenR (k + 1)) c.one).exec inp (st2.setR c.one 1)))) +
      ((cp c.cnt (c.lenR (k + 1))).cost inp B ((c.delLoop q body k).exec inp
        ((cp c.cnt (c.lenR (k + 1))).exec inp ((c.insLoop q body k).exec inp
        ((ar .add c.cnt (c.lenR (k + 1)) c.one).exec inp (st2.setR c.one 1))))) +
      ((c.repLoop q body k).cost inp B
        ((cp c.cnt (c.lenR (k + 1))).exec inp ((c.delLoop q body k).exec inp
        ((cp c.cnt (c.lenR (k + 1))).exec inp ((c.insLoop q body k).exec inp
        ((ar .add c.cnt (c.lenR (k + 1)) c.one).exec inp (st2.setR c.one 1)))))) + 0)))))))) := rfl
    rw [this, e3, ← hst4, e5, ← hst6, e7]
  rw [hc]
  have c1 : (lit c.one 1).cost inp B st2 = kappa B (RAM.bits 1) := rfl
  have c2 : (ar .add c.cnt (c.lenR (k + 1)) c.one).cost inp B (st2.setR c.one 1) =
      kappa B (RAM.bits (x.length + 1)) := by
    simp only [cost_ar, HS.setR_regs]
    rw [Function.update_of_ne (by simp <;> omega), Function.update_self, hlenQ Q2]
  have c3 : (cp c.cnt (c.lenR (k + 1))).cost inp B st4 = kappa B (RAM.bits x.length) := by
    simp only [cost_cp]; rw [hlenQ I1]
  have c4 : (cp c.cnt (c.lenR (k + 1))).cost inp B st6 = kappa B (RAM.bits x.length) := by
    simp only [cost_cp]; rw [hlenQ D1]
  rw [c1, c2, c3, c4]
  have K1 := kappa_bits_le B (a := 1) (M := c.enumM q L s) (by simp only [enumM]; omega)
  have K2 := kappa_bits_le B (a := x.length + 1) (M := c.enumM q L s) (by simp only [enumM]; omega)
  have K3 := kappa_bits_le B (a := x.length) (M := c.enumM q L s) (by simp only [enumM]; omega)
  have hlenv : (visits (k + 1) x).length = 1 +
      ((List.range (x.length + 1)).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun b => visits k (insW x i b)))).length +
      ((List.range x.length).flatMap (fun i => visits k (delW x i))).length +
      ((List.range x.length).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun b =>
            if x[i]? = some b then [] else visits k (repW x i b)))).length := by
    rw [visits_succ]; simp only [List.length_cons, List.length_append]; ring
  rw [hlenv]
  have hW : (7 * x.length + 10) * kappa B (RAM.bits (c.enumM q L s)) + 4 * kappa B (RAM.bits (c.enumM q L s)) + 3 * (20 * (q + 1) * (x.length + 2) ^ 2 * kappa B (RAM.bits (c.enumM q L s))) ≤
      c.enumE B q L s := by
    simp only [enumE]
    have h1 : (x.length + 2) ^ 2 ≤ (L + s + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : (7 * x.length + 10) + 4 + 3 * (20 * (q + 1) * (x.length + 2) ^ 2) ≤
        100 * (q + 1) * (L + s + 2) ^ 2 := by
      nlinarith [Nat.zero_le (q * (x.length + 2) ^ 2), Nat.zero_le (q * (L + s + 2) ^ 2)]
    calc _ = ((7 * x.length + 10) + 4 + 3 * (20 * (q + 1) * (x.length + 2) ^ 2)) * kappa B (RAM.bits (c.enumM q L s)) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ h2
  have hX : (1 + ((List.range (x.length + 1)).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun b => visits k (insW x i b)))).length +
      ((List.range x.length).flatMap (fun i => visits k (delW x i))).length +
      ((List.range x.length).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun b =>
            if x[i]? = some b then [] else visits k (repW x i b)))).length) *
        (cb + c.enumE B q L s) =
      (cb + c.enumE B q L s) + ((List.range (x.length + 1)).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun b => visits k (insW x i b)))).length *
          (cb + c.enumE B q L s) +
      ((List.range x.length).flatMap (fun i => visits k (delW x i))).length *
          (cb + c.enumE B q L s) +
      ((List.range x.length).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun b =>
            if x[i]? = some b then [] else visits k (repW x i b)))).length *
          (cb + c.enumE B q L s) := by ring
  rw [hX]
  omega

/-- The enumerator invariant at every level `k ≤ s`. -/
theorem lev_spec (hstable : ∀ a st st', Inv a st → c.Agree s st st' → Inv a st')
    (hbody : ∀ a st (w : Word q), Inv a st → Ok a w → st.regs c.VL = w.length →
      WordAt st c.vis 0 w →
      Inv (f a w) (body.exec inp st) ∧ c.BodyFrame s st (body.exec inp st) ∧
      body.cost inp B st ≤ cb) :
    ∀ k ≤ s, c.IHk inp B s L body Inv f cb Ok k := by
  intro k hk
  induction k with
  | zero => exact c.lev_zero_spec inp B s L body Inv f cb Ok hstable hbody
  | succ k ih =>
    exact c.lev_succ_spec inp B s L body Inv f cb Ok hstable hbody k hk (ih (by omega))

end Phases

end EnumCfg

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEnum3
/-!
# The scripts enumerator: main theorem, size bound, toy clients (q379, Part L)

* `enumScripts_spec` — the fold specification of `enumScripts q s cfg body`;
* `visits_length_le` — `(visits s x).length ≤ ∑ i ∈ range (s+1), (2q(|x|+s+1))^i`;
* toy clients `countProg` (count the visited words of length `|x|` other than `x`) and
  `listProg` (store them as a 2-D array, word `j` at offsets `j * S`), both proved.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-- **The scripts enumerator.**  Input: `x` in `cfg.buf s` (offset 0), its length in register
`cfg.lenR s`.  `body` runs once per element `w = (visits s x)[j]` in order, with `w` in array
`cfg.vis` (offset 0) and `w.length` in register `cfg.VL`; it may assume the accumulator is the
fold over the earlier visits.  The enumerator only touches resources it owns (`cfg.Agree`), so
the invariant must be stable under such changes (`hstable`); the body must keep every owned
resource except `cfg.VL` and `cfg.vis` (`cfg.BodyFrame`). -/
theorem enumScripts_spec_oai {q : ℕ} {α : Type*} (s : ℕ) (cfg : EnumCfg) (body : Cmd)
    (inp : ℕ → ℕ) (B : ℕ) (Inv : α → HS → Prop) (f : α → Word q → α) (cb : ℕ)
    (x : Word q) (a0 : α)
    (hstable : ∀ a st st', Inv a st → cfg.Agree s st st' → Inv a st')
    (hbody : ∀ a st (w : Word q) (j : ℕ) (hj : j < (visits s x).length),
      w = (visits s x)[j] → a = ((visits s x).take j).foldl f a0 →
      Inv a st → st.regs cfg.VL = w.length → WordAt st cfg.vis 0 w →
      Inv (f a w) (body.exec inp st) ∧ cfg.BodyFrame s st (body.exec inp st) ∧
      body.cost inp B st ≤ cb)
    (st : HS) (hlen : st.regs (cfg.lenR s) = x.length) (hx : WordAt st (cfg.buf s) 0 x)
    (ha : Inv a0 st) :
    Inv ((visits s x).foldl f a0) ((enumScripts q s cfg body).exec inp st) ∧
    ((enumScripts q s cfg body).exec inp st).regs (cfg.lenR s) = x.length ∧
    WordAt ((enumScripts q s cfg body).exec inp st) (cfg.buf s) 0 x ∧
    (enumScripts q s cfg body).cost inp B st ≤
      (visits s x).length * (cb + cfg.enumE B q x.length s) := by
  have := cfg.lev_spec inp B s x.length body Inv f cb
    (fun a w => ∃ j, ∃ hj : j < (visits s x).length, w = (visits s x)[j] ∧
      a = ((visits s x).take j).foldl f a0)
    hstable (fun a st w hInv ⟨j, hj, hw, ha⟩ hVL hvis => hbody a st w j hj hw ha hInv hVL hvis)
    s le_rfl x a0 st (by omega) (fun j hj => ⟨j, hj, rfl, rfl⟩) ha hlen hx
  obtain ⟨h1, h2, h3⟩ := this
  refine ⟨h1, ?_, ?_, h3⟩
  · exact (h2.1 _ le_rfl le_rfl).trans hlen
  · exact hx.congr (fun i _ => h2.2 _ _ le_rfl le_rfl)

/-! ## Size of the visit list -/

/-! ## Toy client (a): counting -/

end EditMulticoloring.Dev.Ram
end

theorem solution.{u_1} : type_of% @EditMulticoloring.Dev.Ram.enumScripts_spec_oai.{u_1} := @EditMulticoloring.Dev.Ram.enumScripts_spec_oai.{u_1}
