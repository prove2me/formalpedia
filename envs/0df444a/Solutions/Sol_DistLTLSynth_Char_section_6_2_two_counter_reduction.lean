-- Prove2me | solution 1 for DistLTLSynth.Char.section_6_2_two_counter_reduction
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T08:07:31.143178+00:00
-- url     : https://prove2.me/submissions/b2a8835f-ff56-46ae-911e-fd8f9b5a0888

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_CounterMachine
import Definitions.Def_DistLTLSynth_Char_CounterFormula

namespace DistLTLSynth.Char.Sec62Aux
open DistLTLSynth.Char

/-! ### Part 1: Ternary Counter Arithmetic and Prefix Sums -/

def wBit (c j : ℕ) : ℕ := (j + 1) / 3 ^ c - j / 3 ^ c

lemma wBit_le_one (c j : ℕ) : wBit c j ≤ 1 := by
  have hd : 0 < 3 ^ c := pow_pos (by decide) c
  have h := Nat.div_le_div_right (show j + 1 ≤ j + 3 ^ c by omega) (c := 3 ^ c)
  rw [Nat.add_div_right _ hd] at h
  unfold wBit
  omega

def wFin (c j : ℕ) : Fin 2 := ⟨wBit c j, by have := wBit_le_one c j; omega⟩

lemma wBit_zero (j : ℕ) : wBit 0 j = 1 := by simp [wBit]

lemma wBit_pos_at_zero (c : ℕ) (hc : 0 < c) : wBit c 0 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  have hp : 0 < 3 ^ k := pow_pos (by decide) k
  unfold wBit
  simp only [zero_add, Nat.zero_div, Nat.sub_zero, pow_succ]
  exact Nat.div_eq_of_lt (by omega)

def carryVal (c m j : ℕ) : ℕ := (m * j) / 3 ^ c - m * (j / 3 ^ c)

lemma carryVal_lt (c m j : ℕ) (hm : 0 < m) : carryVal c m j < m := by
  have hb : 0 < 3 ^ c := pow_pos (by decide) c
  have heq : m * j = m * (j % 3 ^ c) + (m * (j / 3 ^ c)) * 3 ^ c := by
    have h := Nat.mod_add_div j (3 ^ c)
    nlinarith
  have hsplit : (m * j) / 3 ^ c = m * (j / 3 ^ c) + (m * (j % 3 ^ c)) / 3 ^ c := by
    rw [heq, Nat.add_mul_div_right _ _ hb]
    omega
  unfold carryVal
  rw [hsplit, Nat.add_sub_cancel_left]
  exact (Nat.div_lt_iff_lt_mul hb).mpr (Nat.mul_lt_mul_of_pos_left (Nat.mod_lt j hb) hm)

def carryFin (c m j : ℕ) (hm0 : 0 < m) (hm9 : m ≤ 9) : Fin 9 :=
  ⟨carryVal c m j, by have := carryVal_lt c m j hm0; omega⟩

lemma carry_split (c m j : ℕ) : (m * j) / 3 ^ c = m * (j / 3 ^ c) + carryVal c m j := by
  have hb : 0 < 3 ^ c := pow_pos (by decide) c
  have heq : m * j = m * (j % 3 ^ c) + (m * (j / 3 ^ c)) * 3 ^ c := by
    have h := Nat.mod_add_div j (3 ^ c)
    nlinarith
  have hlo : m * (j / 3 ^ c) ≤ (m * j) / 3 ^ c := by
    rw [heq, Nat.add_mul_div_right _ _ hb]
    exact Nat.le_add_left _ _
  unfold carryVal
  exact (Nat.add_sub_of_le hlo).symm

lemma carryVal_at_zero (c m : ℕ) : carryVal c m 0 = 0 := by simp [carryVal]

lemma carryVal_mul_pow (c m k : ℕ) : carryVal c m (3 ^ c * k) = 0 := by
  unfold carryVal
  have hb : 0 < 3 ^ c := pow_pos (by decide) c
  have h1 : m * (3 ^ c * k) = (m * k) * 3 ^ c := by ring
  have h2 : 3 ^ c * k = k * 3 ^ c := by ring
  rw [h1, h2, Nat.mul_div_cancel _ hb, Nat.mul_div_cancel _ hb, Nat.sub_self]

lemma prefix_div_step (c c' m j : ℕ)
    (hstep : (m = 1 ∧ c' = c + 1) ∨ (m = 3 ∧ c' = c) ∨ (m = 9 ∧ 0 < c ∧ c' = c - 1)) :
    (3 * j) / 3 ^ c' = (m * j) / 3 ^ c := by
  rcases hstep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hc, rfl⟩
  · simp only [one_mul, pow_succ]
    rw [Nat.mul_comm (3 ^ c) 3, Nat.mul_div_mul_left _ _ (by decide : 0 < 3)]
  · rfl
  · obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    rw [show 9 * j = 3 * (3 * j) by omega, Nat.mul_comm (3 ^ k) 3,
      Nat.mul_div_mul_left _ _ (by decide : 0 < 3)]

lemma wBit_conservation (c c' m j : ℕ)
    (hstep : (m = 1 ∧ c' = c + 1) ∨ (m = 3 ∧ c' = c) ∨ (m = 9 ∧ 0 < c ∧ c' = c - 1)) :
    wBit c' (3 * j) + wBit c' (3 * j + 1) + wBit c' (3 * j + 2) + carryVal c m j =
      m * wBit c j + carryVal c m (j + 1) := by
  let D := 3 ^ c'
  have h0 := Nat.div_le_div_right (show 3 * j ≤ 3 * j + 1 by omega) (c := D)
  have h1 := Nat.div_le_div_right (show 3 * j + 1 ≤ 3 * j + 2 by omega) (c := D)
  have h2 := Nat.div_le_div_right (show 3 * j + 2 ≤ 3 * j + 3 by omega) (c := D)
  have hp := Nat.div_le_div_right (show j ≤ j + 1 by omega) (c := 3 ^ c)
  have hc0 := carry_split c m j
  have hc1 := carry_split c m (j + 1)
  have hpc0 : (3 * j) / D = (m * j) / 3 ^ c := prefix_div_step c c' m j hstep
  have hpc1 : (3 * j + 3) / D = (m * (j + 1)) / 3 ^ c := by
    simpa [show 3 * (j + 1) = 3 * j + 3 by omega] using prefix_div_step c c' m (j + 1) hstep
  have htel : wBit c' (3 * j) + wBit c' (3 * j + 1) + wBit c' (3 * j + 2) + (3 * j) / D =
      (3 * j + 3) / D := by
    unfold wBit
    change (3 * j + 1) / D - (3 * j) / D + ((3 * j + 2) / D - (3 * j + 1) / D) +
      ((3 * j + 3) / D - (3 * j + 2) / D) + (3 * j) / D = (3 * j + 3) / D
    omega
  have hmul : m * wBit c j + m * (j / 3 ^ c) = m * ((j + 1) / 3 ^ c) := by
    rw [← Nat.mul_add, wBit, Nat.sub_add_cancel hp]
  omega

lemma encoded_zero_iff (W c r : ℕ) (h : W * 3 ^ c = 3 ^ r) : W = 3 ^ r ↔ c = 0 := by
  constructor
  · intro hW
    rw [hW] at h
    cases c with
    | zero => rfl
    | succ k =>
      rw [pow_succ] at h
      have hr : 0 < 3 ^ r := pow_pos (by decide) r
      have hk : 0 < 3 ^ k := pow_pos (by decide) k
      nlinarith
  · intro hc
    simpa [hc] using h

lemma forced_invariant (W : ℕ → ℕ) (z : ℕ → Bool) (m c : ℕ → ℕ)
    (hc0 : c 0 = 0)
    (hW0 : W 0 = 3)
    (hguard : ∀ n, z n = true ↔ W n = 3 ^ (n + 1))
    (hWstep : ∀ n, W (n + 1) = m n * W n)
    (hcstep : ∀ n, (m n = 1 ∧ c (n + 1) = c n + 1) ∨
      (m n = 3 ∧ c (n + 1) = c n) ∨
      (m n = 9 ∧ z n = false ∧ c (n + 1) = c n - 1)) :
    ∀ n, W n * 3 ^ (c n) = 3 ^ (n + 1) ∧ (z n = true ↔ c n = 0) := by
  intro n
  induction n with
  | zero =>
    have hi : W 0 * 3 ^ (c 0) = 3 ^ 1 := by simp [hW0, hc0]
    exact ⟨hi, (hguard 0).trans (encoded_zero_iff _ _ _ hi)⟩
  | succ n ih =>
    have hi : W (n + 1) * 3 ^ (c (n + 1)) = 3 ^ (n + 2) := by
      rw [hWstep n]
      rcases hcstep n with ⟨hm, hc⟩ | ⟨hm, hc⟩ | ⟨hm, hz, hc⟩
      · rw [hm, hc, pow_succ, pow_succ]
        nlinarith [ih.1]
      · rw [hm, hc, pow_succ]
        nlinarith [ih.1]
      · have hcn_ne : c n ≠ 0 := by
          intro h0
          have hzt := ih.2.mpr h0
          simp [hz] at hzt
        obtain ⟨k, hk⟩ : ∃ k, c n = k + 1 := ⟨c n - 1, by omega⟩
        have hck : c (n + 1) = k := by omega
        rw [hm, hck]
        have h1 : W n * (3 ^ k * 3) = 3 ^ (n + 1) := by simpa [hk, pow_succ] using ih.1
        rw [pow_succ _ (n + 1)]
        nlinarith [h1]
    exact ⟨hi, (hguard (n + 1)).trans (encoded_zero_iff _ _ _ hi)⟩

def sumRange : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

lemma sumRange_const_one (L : ℕ) : sumRange L (fun _ => 1) = L := by
  induction L with
  | zero => rfl
  | succ L ih => simp [sumRange, ih]

lemma sumRange_lt_of_zero_head (L : ℕ) (f : ℕ → ℕ) (hL : 0 < L)
    (hf0 : f 0 = 0) (hf : ∀ j < L, f j ≤ 1) : sumRange L f < L := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  induction k with
  | zero => simp [sumRange, hf0]
  | succ k ih =>
    have h1 := ih (by omega) (fun j hj => hf j (by omega))
    have h2 := hf (k + 1) (by omega)
    rw [sumRange]
    omega

lemma sumRange_mul_three (L : ℕ) (f : ℕ → ℕ) :
    sumRange (3 * L) f = sumRange L (fun j => f (3 * j) + f (3 * j + 1) + f (3 * j + 2)) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    have h3 : 3 * (L + 1) = 3 * L + 1 + 1 + 1 := by omega
    rw [h3, sumRange, sumRange, sumRange, sumRange, ih]
    omega

lemma sumRange_telescope (k m : ℕ) (prom wt carryL carryR : ℕ → ℕ)
    (hbal : ∀ j < k + 1, prom j + carryL j = m * wt j + carryR j)
    (hlink : ∀ j, j + 1 < k + 1 → carryR j = carryL (j + 1)) :
    sumRange (k + 1) prom + carryL 0 = m * sumRange (k + 1) wt + carryR k := by
  induction k with
  | zero => simpa [sumRange] using hbal 0 (by omega)
  | succ k ih =>
    have h1 := ih (fun j hj => hbal j (by omega)) (fun j hj => hlink j (by omega))
    have h2 := hbal (k + 1) (by omega)
    have h3 := hlink k (by omega)
    have hL : sumRange (k + 1 + 1) prom = sumRange (k + 1) prom + prom (k + 1) := rfl
    have hR : sumRange (k + 1 + 1) wt = sumRange (k + 1) wt + wt (k + 1) := rfl
    rw [hL, hR, Nat.mul_add]
    omega

/-! ### Part 2: View Geometry on Singleton Inputs (`Fin 1`) -/

abbrev Sig0 : Type := Signal (Fin 1) (Fin 1)

def finZero : Fin 1 := ⟨0, Nat.one_pos⟩

def toSig0 (l : List CommGraph) : List Sig0 :=
  l.map (fun g => (finZero, finZero, g))

@[simp] lemma toSig0_nil : toSig0 [] = [] := rfl
@[simp] lemma toSig0_append (a b : List CommGraph) : toSig0 (a ++ b) = toSig0 a ++ toSig0 b := by
  simp [toSig0]
@[simp] lemma toSig0_length (l : List CommGraph) : (toSig0 l).length = l.length := by
  simp [toSig0]

def vdepth0 : View (Fin 1) (Fin 1) → ℕ
  | .I1 | .I2 => 0
  | .N1 _ u | .C1 _ u _ _ => vdepth0 u + 1
  | .N2 _ v | .C2 _ v _ _ => vdepth0 v + 1

def vcoord0 : View (Fin 1) (Fin 1) → ℕ
  | .I1 => 0
  | .I2 => 1
  | .N1 _ u => 3 * vcoord0 u
  | .N2 _ v => 3 * vcoord0 v
  | .C1 _ u _ v => vcoord0 u + 2 * vcoord0 v
  | .C2 _ v _ u => 2 * vcoord0 u + vcoord0 v

lemma views_append_singleton {X1 X2 : Type} (u : List (Signal X1 X2)) (a : Signal X1 X2) :
    views (u ++ [a]) = viewStep (views u) a := by simp [views]

lemma views_toSig0_snoc (l : List CommGraph) (g : CommGraph) :
    views (toSig0 (l ++ [g])) = viewStep (views (toSig0 l)) (finZero, finZero, g) := by
  have hs : toSig0 (l ++ [g]) = toSig0 l ++ [(finZero, finZero, g)] := by simp [toSig0]
  rw [hs, views_append_singleton]

lemma jIdx_nil : jIdx [] = 0 := rfl

lemma jIdx_append_singleton (h : List CommGraph) (g : CommGraph) :
    jIdx (h ++ [g]) = 3 * jIdx h + if jIdx h % 2 = 0 then delta g else 2 - delta g := by
  unfold jIdx
  rw [List.foldl_append]
  rfl

lemma vdepth_coord_views0 (h : List CommGraph) :
    vdepth0 (view1 (toSig0 h)) = h.length ∧
    vdepth0 (view2 (toSig0 h)) = h.length ∧
    (if jIdx h % 2 = 0 then vcoord0 (view1 (toSig0 h)) else vcoord0 (view2 (toSig0 h))) = jIdx h ∧
    (if jIdx h % 2 = 0 then vcoord0 (view2 (toSig0 h)) else vcoord0 (view1 (toSig0 h))) = jIdx h + 1 := by
  induction h using List.reverseRecOn with
  | nil => simp [view1, view2, views, vdepth0, vcoord0, jIdx_nil]
  | append_singleton h g ih =>
    rcases ih with ⟨hd1, hd2, hcL, hcR⟩
    simp only [view1, view2] at hd1 hd2 hcL hcR ⊢
    rw [views_toSig0_snoc, jIdx_append_singleton]
    rcases hvs : views (toSig0 h) with ⟨u, v⟩
    rw [hvs] at hd1 hd2 hcL hcR
    dsimp only at hd1 hd2 hcL hcR
    rcases (show jIdx h % 2 = 0 ∨ jIdx h % 2 = 1 by omega) with hp | hp
    · simp only [hp, ↓reduceIte] at hcL hcR ⊢
      cases g <;> simp [viewStep, vdepth0, vcoord0, delta, hd1, hd2, hcL, hcR] <;>
        (try split_ifs) <;> omega
    · have hp0 : ¬ (jIdx h % 2 = 0) := by omega
      simp only [hp0, ↓reduceIte] at hcL hcR ⊢
      cases g <;> simp [viewStep, vdepth0, vcoord0, delta, hd1, hd2, hcL, hcR] <;>
        (try split_ifs) <;> omega

lemma vcoord0_mod3_step (uv : View (Fin 1) (Fin 1) × View (Fin 1) (Fin 1)) (g : CommGraph) :
    let uv' := viewStep uv (finZero, finZero, g)
    (Ctr.mod3 (vcoord0 uv'.1), Ctr.mod3 (vcoord0 uv'.2)) =
      Ctr.childPos g (Ctr.mod3 (vcoord0 uv.1)) (Ctr.mod3 (vcoord0 uv.2)) := by
  cases g <;>
  · apply Prod.ext <;> apply Fin.ext <;> simp [viewStep, vcoord0, Ctr.childPos, Ctr.mod3] <;> omega

lemma pre_get {α : Type} (f : ℕ → α) (m k : ℕ) (hk : k < (pre f m).length) :
    (pre f m)[k] = f k := by
  simp only [pre, List.getElem_ofFn]

lemma pre_snoc {α : Type} (s : ℕ → α) (n : ℕ) :
    pre s (n + 1) = pre s n ++ [s n] := by
  apply List.ext_getElem
  · simp [pre]
  · intro i h1 h2
    have hi_lt : i < n + 1 := by simpa [pre] using h1
    by_cases hi : i < n
    · rw [List.getElem_append_left (by simp [pre, hi]), pre_get, pre_get]
    · have heq : i = n := by omega
      subst heq
      rw [List.getElem_append_right (by simp [pre]), pre_get]
      simp [pre]

lemma pre_eq_replicate {α : Type} (f : ℕ → α) (g : α) (r : ℕ) (h : ∀ k < r, f k = g) :
    pre f r = List.replicate r g := by
  apply List.ext_getElem
  · simp [pre]
  · intro i h1 h2
    rw [pre_get, List.getElem_replicate]
    exact h i (by simpa [pre] using h1)

lemma sig0_eq (x : Sig0) : x = (finZero, finZero, x.2.2) := by
  rcases x with ⟨x1, x2, g⟩
  rw [Subsingleton.elim x1 finZero, Subsingleton.elim x2 finZero]

lemma pre_sig0_toSig0 (s : ℕ → Sig0) (r : ℕ) :
    pre s r = toSig0 (pre (graphOf s) r) := by
  apply List.ext_getElem
  · simp [pre, toSig0]
  · intro i h1 h2
    simp only [pre, toSig0, List.getElem_ofFn, List.getElem_map, graphOf]
    exact sig0_eq (s i)

lemma vcoord0_mod3_pre (s : ℕ → Sig0) (n : ℕ) :
    (Ctr.mod3 (vcoord0 (view1 (pre s (n + 1)))), Ctr.mod3 (vcoord0 (view2 (pre s (n + 1))))) =
      if n = 0 then Ctr.childPos (s 0).2.2 0 1
      else Ctr.childPos (s n).2.2
        (Ctr.mod3 (vcoord0 (view1 (pre s n)))) (Ctr.mod3 (vcoord0 (view2 (pre s n)))) := by
  have hpre : pre s (n + 1) = pre s n ++ [(finZero, finZero, (s n).2.2)] := by
    rw [pre_snoc, ← sig0_eq (s n)]
  cases n with
  | zero =>
    simp only [↓reduceIte]
    have hp1 : pre s 1 = [(finZero, finZero, (s 0).2.2)] := by
      rw [hpre]; simp [pre]
    rw [hp1]
    simpa [view1, view2, views, vcoord0, Ctr.mod3] using vcoord0_mod3_step (.I1, .I2) (s 0).2.2
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    rw [hpre]
    simp only [view1, view2, views_append_singleton]
    exact vcoord0_mod3_step (views (pre s (m + 1))) (s (m + 1)).2.2

def stepGraph (even : Bool) (d : ℕ) : CommGraph :=
  if even then
    match d with
    | 0 => .oneToTwo
    | 1 => .both
    | _ => .twoToOne
  else
    match d with
    | 0 => .twoToOne
    | 1 => .both
    | _ => .oneToTwo

lemma dVal_stepGraph (even : Bool) (d : ℕ) (hd : d < 3) :
    Ctr.dVal even (stepGraph even d) = d := by
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl <;>
    cases even <;> rfl

def histOf : ℕ → ℕ → List CommGraph
  | 0, _ => []
  | r + 1, j => histOf r (j / 3) ++ [stepGraph (decide ((j / 3) % 2 = 0)) (j % 3)]

@[simp] lemma histOf_length (r j : ℕ) : (histOf r j).length = r := by
  induction r generalizing j with
  | zero => rfl
  | succ r ih => simp [histOf, ih]

lemma jIdx_histOf (r j : ℕ) (hj : j < 3 ^ r) : jIdx (histOf r j) = j := by
  induction r generalizing j with
  | zero =>
    have hj0 : j = 0 := by simpa using hj
    simp [histOf, jIdx_nil, hj0]
  | succ r ih =>
    have hq : j / 3 < 3 ^ r := by rw [pow_succ] at hj; omega
    have hrem : j % 3 < 3 := Nat.mod_lt j (by decide)
    rw [histOf, jIdx_append_singleton, ih (j / 3) hq]
    have hd := dVal_stepGraph (decide ((j / 3) % 2 = 0)) (j % 3) hrem
    unfold Ctr.dVal at hd
    by_cases hp : (j / 3) % 2 = 0
    · simp only [hp, decide_true, ↓reduceIte] at hd ⊢; omega
    · simp only [hp, decide_false, Bool.false_eq_true, ↓reduceIte] at hd ⊢; omega

lemma histOf_zero (r : ℕ) : histOf r 0 = List.replicate r .oneToTwo := by
  induction r with
  | zero => rfl
  | succ r ih => simp [histOf, ih, stepGraph, List.replicate_succ']

lemma three_pow_sub_one_even (r : ℕ) : (3 ^ r - 1) % 2 = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hp : 1 ≤ 3 ^ r := Nat.one_le_pow r 3 (by decide)
    rw [pow_succ]; omega

lemma histOf_last (r : ℕ) : histOf r (3 ^ r - 1) = List.replicate r .twoToOne := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hp : 1 ≤ 3 ^ r := Nat.one_le_pow r 3 (by decide)
    have hdiv : (3 ^ (r + 1) - 1) / 3 = 3 ^ r - 1 := by rw [pow_succ]; omega
    have hmod : (3 ^ (r + 1) - 1) % 3 = 2 := by rw [pow_succ]; omega
    have hev := three_pow_sub_one_even r
    rw [histOf, hdiv, hmod, ih]
    simp [hev, stepGraph, List.replicate_succ']

lemma histOf_shared_view0 (r : ℕ) :
    ∀ j, j + 1 < 3 ^ r →
      (if j % 2 = 0 then view2 (toSig0 (histOf r j)) else view1 (toSig0 (histOf r j))) =
      (if (j + 1) % 2 = 0 then view1 (toSig0 (histOf r (j + 1))) else view2 (toSig0 (histOf r (j + 1)))) := by
  induction r with
  | zero => intro j hj; simp at hj
  | succ r ih =>
    intro j hj
    rw [pow_succ] at hj
    rcases (show j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 by omega) with hd | hd | hd
    · have hdiv1 : (j + 1) / 3 = j / 3 := by omega
      have hmod1 : (j + 1) % 3 = 1 := by omega
      rcases (show (j / 3) % 2 = 0 ∨ (j / 3) % 2 = 1 by omega) with hp | hp
      · have hj0 : j % 2 = 0 := by omega
        have hj1 : ¬ ((j + 1) % 2 = 0) := by omega
        simp only [hj0, hj1, ↓reduceIte, histOf, hd, hdiv1, hmod1, hp, decide_true,
          stepGraph, view2, views_toSig0_snoc, viewStep]
      · have hj0 : ¬ (j % 2 = 0) := by omega
        have hj1 : (j + 1) % 2 = 0 := by omega
        have hp' : ¬ ((j / 3) % 2 = 0) := by omega
        simp only [hj0, hj1, ↓reduceIte, histOf, hd, hdiv1, hmod1, hp', decide_false,
          Bool.false_eq_true, stepGraph, view1, views_toSig0_snoc, viewStep]
    · have hdiv1 : (j + 1) / 3 = j / 3 := by omega
      have hmod1 : (j + 1) % 3 = 2 := by omega
      rcases (show (j / 3) % 2 = 0 ∨ (j / 3) % 2 = 1 by omega) with hp | hp
      · have hj0 : ¬ (j % 2 = 0) := by omega
        have hj1 : (j + 1) % 2 = 0 := by omega
        simp only [hj0, hj1, ↓reduceIte, histOf, hd, hdiv1, hmod1, hp, decide_true,
          stepGraph, view1, views_toSig0_snoc, viewStep]
      · have hj0 : j % 2 = 0 := by omega
        have hj1 : ¬ ((j + 1) % 2 = 0) := by omega
        have hp' : ¬ ((j / 3) % 2 = 0) := by omega
        simp only [hj0, hj1, ↓reduceIte, histOf, hd, hdiv1, hmod1, hp', decide_false,
          Bool.false_eq_true, stepGraph, view2, views_toSig0_snoc, viewStep]
    · have hdiv1 : (j + 1) / 3 = j / 3 + 1 := by omega
      have hmod1 : (j + 1) % 3 = 0 := by omega
      have hq_lt : j / 3 + 1 < 3 ^ r := by omega
      have hrec := ih (j / 3) hq_lt
      rcases (show (j / 3) % 2 = 0 ∨ (j / 3) % 2 = 1 by omega) with hp | hp
      · have hj0 : j % 2 = 0 := by omega
        have hj1 : ¬ ((j + 1) % 2 = 0) := by omega
        have hp1 : ¬ ((j / 3 + 1) % 2 = 0) := by omega
        simp only [hp, hp1, ↓reduceIte] at hrec
        simp only [hj0, hj1, ↓reduceIte, histOf, hd, hdiv1, hmod1, hp, hp1, decide_true,
          decide_false, Bool.false_eq_true, stepGraph, view2, views_toSig0_snoc, viewStep]
        exact congrArg (View.N2 finZero) hrec
      · have hj0 : ¬ (j % 2 = 0) := by omega
        have hj1 : (j + 1) % 2 = 0 := by omega
        have hp' : ¬ ((j / 3) % 2 = 0) := by omega
        have hp1 : (j / 3 + 1) % 2 = 0 := by omega
        simp only [hp', hp1, ↓reduceIte] at hrec
        simp only [hj0, hj1, ↓reduceIte, histOf, hd, hdiv1, hmod1, hp', hp1, decide_true,
          decide_false, Bool.false_eq_true, stepGraph, view1, views_toSig0_snoc, viewStep]
        exact congrArg (View.N1 finZero) hrec

def extendSig0 (h : List CommGraph) : ℕ → Sig0 :=
  fun n => (finZero, finZero, h.getD n .both)

lemma pre_extendSig0 (h : List CommGraph) (r : ℕ) (hr : r ≤ h.length) :
    pre (extendSig0 h) r = toSig0 (h.take r) := by
  apply List.ext_getElem
  · simp [pre, hr]
  · intro i h1 h2
    simp only [pre, List.length_ofFn] at h1
    have hi : i < h.length := by omega
    simp [pre, extendSig0, toSig0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

lemma pre_const_sig0 (g : CommGraph) (r : ℕ) :
    pre (fun _ : ℕ => (finZero, finZero, g)) r = toSig0 (List.replicate r g) := by
  apply List.ext_getElem <;> simp [pre, toSig0]

lemma pre_graph_extendSig0 (h : List CommGraph) (r : ℕ) (hr : r ≤ h.length) :
    pre (graphOf (extendSig0 h)) r = h.take r := by
  apply List.ext_getElem
  · simp [pre, hr]
  · intro i h1 h2
    simp only [pre, List.length_ofFn] at h1
    have hi : i < h.length := by omega
    simp [pre, graphOf, extendSig0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-! ### Part 3: 2-Counter Payload Coding (Zero-Enumeration Arithmetic Bijection) -/

abbrev Plan2 : Type := Fin 2 × Fin 2 × Fin 2 × Fin 2
abbrev CtrField : Type := Bool × Plan2 × Fin 9
abbrev Payload : Type := CtrField × CtrField × Fin 3

def boolEquivFin2 : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := i.val == 1
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

def plan2Equiv : Plan2 ≃ Fin 16 :=
  ((Equiv.prodCongr (Equiv.refl (Fin 2))
      (Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv)).trans
    (Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv)).trans
    (finProdFinEquiv.trans (finCongr (by norm_num)))

def ctrFieldEquiv : CtrField ≃ Fin 288 :=
  (Equiv.prodCongr boolEquivFin2
    ((Equiv.prodCongr plan2Equiv (Equiv.refl (Fin 9))).trans finProdFinEquiv)).trans
    (finProdFinEquiv.trans (finCongr (by norm_num)))

class PayCode where
  K : ℕ
  hK : 0 < K
  equiv : Payload ≃ Fin K

section Parametric
variable [pc : PayCode]

def K : ℕ := pc.K

lemma K_pos : 0 < K := pc.hK

def payEquiv : Payload ≃ Fin K := pc.equiv

/-- Output alphabet bound `m1 = m2 = (K - 1) + K * s`, so `m1 + 1 = K * (s + 1)` parametrically
without any large numeral in scope. -/
def outM (s : ℕ) : ℕ := (K - 1) + K * s

abbrev OutFin (s : ℕ) : Type := Fin (outM s + 1)

lemma outSize_eq (s : ℕ) : outM s + 1 = K * (s + 1) := by
  have := K_pos
  unfold outM
  rw [Nat.mul_succ]
  omega

def encodeOut (s : ℕ) (q : Fin (s + 1)) (p : Payload) : OutFin s :=
  ⟨(payEquiv p).val + K * q.val, by
    rw [outSize_eq]
    have hq : q.val + 1 ≤ s + 1 := q.isLt
    have hp := (payEquiv p).isLt
    calc (payEquiv p).val + K * q.val
        < K + K * q.val := Nat.add_lt_add_right hp _
      _ = K * (q.val + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      _ ≤ K * (s + 1) := Nat.mul_le_mul_left K hq⟩

def decodeQ (y : ℕ) : ℕ := y / K

def decodePay (y : ℕ) : Payload :=
  payEquiv.symm ⟨y % K, Nat.mod_lt _ K_pos⟩

lemma div_K_encode (q i : ℕ) (hi : i < K) : (i + K * q) / K = q := by
  rw [Nat.add_mul_div_left _ _ K_pos, Nat.div_eq_of_lt hi, zero_add]

lemma mod_K_encode (q i : ℕ) (hi : i < K) : (i + K * q) % K = i := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]

lemma decodeQ_encodeOut (s : ℕ) (q : Fin (s + 1)) (p : Payload) :
    decodeQ (encodeOut s q p).val = q.val :=
  div_K_encode q.val (payEquiv p).val (payEquiv p).isLt

lemma decodePay_encodeOut (s : ℕ) (q : Fin (s + 1)) (p : Payload) :
    decodePay (encodeOut s q p).val = p := by
  unfold decodePay
  have hm := mod_K_encode q.val (payEquiv p).val (payEquiv p).isLt
  have hfin : (⟨(encodeOut s q p).val % K, Nat.mod_lt _ K_pos⟩ : Fin K) = payEquiv p := Fin.ext hm
  rw [hfin, Equiv.symm_apply_apply]

lemma decodeQ_lt (s : ℕ) (y : OutFin s) : decodeQ y.val < s + 1 := by
  unfold decodeQ
  exact Nat.div_lt_of_lt_mul (y.isLt.trans_eq (outSize_eq s))

def pField (r : Fin 2) (p : Payload) : CtrField := if r = 0 then p.1 else p.2.1
def pZero (r : Fin 2) (p : Payload) : Bool := (pField r p).1
def pW (r : Fin 2) (p : Payload) : Fin 2 := (pField r p).2.1.1
def pA (r : Fin 2) (k : Fin 3) (p : Payload) : Fin 2 :=
  match k with
  | 0 => (pField r p).2.1.2.1
  | 1 => (pField r p).2.1.2.2.1
  | 2 => (pField r p).2.1.2.2.2
def pPlanSum (r : Fin 2) (p : Payload) : ℕ :=
  (pA r 0 p).val + (pA r 1 p).val + (pA r 2 p).val
def pCarry (r : Fin 2) (p : Payload) : Fin 9 := (pField r p).2.2
def pPos (p : Payload) : Fin 3 := p.2.2

@[irreducible] def payIndices (P : Payload → Bool) : List ℕ :=
  (List.range K).filter (fun i => if h : i < K then P (payEquiv.symm ⟨i, h⟩) else false)

lemma mem_payIndices (P : Payload → Bool) (i : ℕ) :
    i ∈ payIndices P ↔ i < K ∧ P (decodePay i) = true := by
  unfold payIndices decodePay
  simp only [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hi, hif⟩
    rw [dif_pos hi] at hif
    refine ⟨hi, ?_⟩
    have hfeq : (⟨i % K, Nat.mod_lt _ K_pos⟩ : Fin K) = ⟨i, hi⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hi)
    rwa [hfeq]
  · rintro ⟨hi, hP⟩
    refine ⟨hi, ?_⟩
    rw [dif_pos hi]
    have hfeq : (⟨i % K, Nat.mod_lt _ K_pos⟩ : Fin K) = ⟨i, hi⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hi)
    rwa [← hfeq]

end Parametric

/-! ### Part 4: Prefix-Polish Serializer and Primitive Recursiveness -/

def encFormula : Formula ℕ ℕ ℕ ℕ → List Token
  | .inp1 x => [(0, 1, x)]
  | .inp2 x => [(0, 2, x)]
  | .out1 y => [(1, 1, y)]
  | .out2 y => [(1, 2, y)]
  | .graph .oneToTwo => [(2, 0, 0)]
  | .graph .both => [(2, 1, 0)]
  | .graph .twoToOne => [(2, 2, 0)]
  | .next φ => (3, 0, 0) :: encFormula φ
  | .eventually φ => (4, 0, 0) :: encFormula φ
  | .always φ => (5, 0, 0) :: encFormula φ
  | .untl φ ψ => (6, 0, 0) :: (encFormula φ ++ encFormula ψ)
  | .weakUntil ψ φ => (7, 0, 0) :: (encFormula ψ ++ encFormula φ)
  | .neg φ => (8, 0, 0) :: encFormula φ
  | .or φ ψ => (9, 0, 0) :: (encFormula φ ++ encFormula ψ)
  | .and φ ψ => (10, 0, 0) :: (encFormula φ ++ encFormula ψ)
  | .imp φ ψ => (11, 0, 0) :: (encFormula φ ++ encFormula ψ)
  | .iff φ ψ => (12, 0, 0) :: (encFormula φ ++ encFormula ψ)

lemma parseAux_enc (φ : Formula ℕ ℕ ℕ ℕ) :
    ∀ (rest : List Token) (m : ℕ), (encFormula φ).length ≤ m →
      parseAux m (encFormula φ ++ rest) = some (φ, rest) := by
  induction φ with
  | inp1 x => intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩; rfl
  | inp2 x => intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩; rfl
  | out1 y => intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩; rfl
  | out2 y => intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩; rfl
  | graph g =>
    intro rest m hm
    cases g <;> (obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩; rfl)
  | next φ ih =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp [encFormula, parseAux, ih rest k (by simp [encFormula] at hm; omega)]
  | eventually φ ih =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp [encFormula, parseAux, ih rest k (by simp [encFormula] at hm; omega)]
  | always φ ih =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp [encFormula, parseAux, ih rest k (by simp [encFormula] at hm; omega)]
  | neg φ ih =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp [encFormula, parseAux, ih rest k (by simp [encFormula] at hm; omega)]
  | untl φ ψ ih1 ih2 =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula ψ ++ rest) k (by simp [encFormula] at hm; omega)]; dsimp only
    rw [ih2 rest k (by simp [encFormula] at hm; omega)]
  | weakUntil ψ φ ih1 ih2 =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula φ ++ rest) k (by simp [encFormula] at hm; omega)]; dsimp only
    rw [ih2 rest k (by simp [encFormula] at hm; omega)]
  | or φ ψ ih1 ih2 =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula ψ ++ rest) k (by simp [encFormula] at hm; omega)]; dsimp only
    rw [ih2 rest k (by simp [encFormula] at hm; omega)]
  | and φ ψ ih1 ih2 =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula ψ ++ rest) k (by simp [encFormula] at hm; omega)]; dsimp only
    rw [ih2 rest k (by simp [encFormula] at hm; omega)]
  | imp φ ψ ih1 ih2 =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula ψ ++ rest) k (by simp [encFormula] at hm; omega)]; dsimp only
    rw [ih2 rest k (by simp [encFormula] at hm; omega)]
  | iff φ ψ ih1 ih2 =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula ψ ++ rest) k (by simp [encFormula] at hm; omega)]; dsimp only
    rw [ih2 rest k (by simp [encFormula] at hm; omega)]

lemma parse_encFormula (φ : Formula ℕ ℕ ℕ ℕ) : parse (encFormula φ) = some φ := by
  unfold parse
  have h := parseAux_enc φ [] (encFormula φ).length le_rfl
  rw [List.append_nil] at h
  rw [h]

lemma encFormula_bigAnd (l : List (Formula ℕ ℕ ℕ ℕ)) :
    encFormula (Formula.bigAnd l) =
      (l.map encFormula).foldr (fun t acc => (10, 0, 0) :: (t ++ acc)) (encFormula Formula.tt) := by
  induction l with
  | nil => rfl
  | cons a tl ih => simp [Formula.bigAnd, encFormula, ih]

lemma encFormula_bigOr (l : List (Formula ℕ ℕ ℕ ℕ)) :
    encFormula (Formula.bigOr l) =
      (l.map encFormula).foldr (fun t acc => (9, 0, 0) :: (t ++ acc)) (encFormula Formula.ff) := by
  induction l with
  | nil => rfl
  | cons a tl ih => simp [Formula.bigOr, encFormula, ih]

lemma primrec_fold_tokens (opTag : Token) (init : List Token) :
    Primrec (fun ts : List (List Token) => ts.foldr (fun t acc => opTag :: (t ++ acc)) init) := by
  have h := Primrec.list_foldr Primrec.id (Primrec.const init)
    ((Primrec.list_cons.comp (Primrec.const opTag)
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))).to₂)
  exact h.of_eq (fun _ => rfl)

lemma primrec_enc_out1 {α : Type} [Primcodable α] {f : α → ℕ} (hf : Primrec f) :
    Primrec (fun x => encFormula (.out1 (f x))) :=
  Primrec.list_cons.comp
    (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const 1) hf))
    (Primrec.const [])

lemma primrec_enc_out2 {α : Type} [Primcodable α] {f : α → ℕ} (hf : Primrec f) :
    Primrec (fun x => encFormula (.out2 (f x))) :=
  Primrec.list_cons.comp
    (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const 2) hf))
    (Primrec.const [])

lemma primrec_enc_next {α : Type} [Primcodable α] {F : α → Formula ℕ ℕ ℕ ℕ}
    (hF : Primrec (fun x => encFormula (F x))) :
    Primrec (fun x => encFormula (.next (F x))) :=
  Primrec.list_cons.comp (Primrec.const (3, 0, 0)) hF

lemma primrec_enc_always {α : Type} [Primcodable α] {F : α → Formula ℕ ℕ ℕ ℕ}
    (hF : Primrec (fun x => encFormula (F x))) :
    Primrec (fun x => encFormula (.always (F x))) :=
  Primrec.list_cons.comp (Primrec.const (5, 0, 0)) hF

lemma primrec_enc_neg {α : Type} [Primcodable α] {F : α → Formula ℕ ℕ ℕ ℕ}
    (hF : Primrec (fun x => encFormula (F x))) :
    Primrec (fun x => encFormula (.neg (F x))) :=
  Primrec.list_cons.comp (Primrec.const (8, 0, 0)) hF

lemma primrec_enc_weakUntil {α : Type} [Primcodable α] {F G : α → Formula ℕ ℕ ℕ ℕ}
    (hF : Primrec (fun x => encFormula (F x))) (hG : Primrec (fun x => encFormula (G x))) :
    Primrec (fun x => encFormula (.weakUntil (F x) (G x))) :=
  Primrec.list_cons.comp (Primrec.const (7, 0, 0)) (Primrec.list_append.comp hF hG)

lemma primrec_enc_or {α : Type} [Primcodable α] {F G : α → Formula ℕ ℕ ℕ ℕ}
    (hF : Primrec (fun x => encFormula (F x))) (hG : Primrec (fun x => encFormula (G x))) :
    Primrec (fun x => encFormula (.or (F x) (G x))) :=
  Primrec.list_cons.comp (Primrec.const (9, 0, 0)) (Primrec.list_append.comp hF hG)

lemma primrec_enc_and {α : Type} [Primcodable α] {F G : α → Formula ℕ ℕ ℕ ℕ}
    (hF : Primrec (fun x => encFormula (F x))) (hG : Primrec (fun x => encFormula (G x))) :
    Primrec (fun x => encFormula (.and (F x) (G x))) :=
  Primrec.list_cons.comp (Primrec.const (10, 0, 0)) (Primrec.list_append.comp hF hG)

lemma primrec_enc_imp {α : Type} [Primcodable α] {F G : α → Formula ℕ ℕ ℕ ℕ}
    (hF : Primrec (fun x => encFormula (F x))) (hG : Primrec (fun x => encFormula (G x))) :
    Primrec (fun x => encFormula (.imp (F x) (G x))) :=
  Primrec.list_cons.comp (Primrec.const (11, 0, 0)) (Primrec.list_append.comp hF hG)

lemma primrec_enc_bigAnd_map {α β : Type} [Primcodable α] [Primcodable β]
    {L : α → List β} {F : α → β → Formula ℕ ℕ ℕ ℕ}
    (hL : Primrec L) (hF : Primrec (fun p : α × β => encFormula (F p.1 p.2))) :
    Primrec (fun x => encFormula (Formula.bigAnd ((L x).map (F x)))) := by
  have hm : Primrec (fun x => (L x).map (fun b => encFormula (F x b))) :=
    Primrec.list_map hL hF.to₂
  exact ((primrec_fold_tokens (10, 0, 0) (encFormula Formula.tt)).comp hm).of_eq fun x => by
    rw [encFormula_bigAnd, List.map_map]; rfl

lemma primrec_enc_bigOr_map {α β : Type} [Primcodable α] [Primcodable β]
    {L : α → List β} {F : α → β → Formula ℕ ℕ ℕ ℕ}
    (hL : Primrec L) (hF : Primrec (fun p : α × β => encFormula (F p.1 p.2))) :
    Primrec (fun x => encFormula (Formula.bigOr ((L x).map (F x)))) := by
  have hm : Primrec (fun x => (L x).map (fun b => encFormula (F x b))) :=
    Primrec.list_map hL hF.to₂
  exact ((primrec_fold_tokens (9, 0, 0) (encFormula Formula.ff)).comp hm).of_eq fun x => by
    rw [encFormula_bigOr, List.map_map]; rfl

lemma primrec_enc_bigAnd_const {α γ : Type} [Primcodable α] (xs : List γ)
    (F : α → γ → Formula ℕ ℕ ℕ ℕ)
    (hF : ∀ g ∈ xs, Primrec (fun x => encFormula (F x g))) :
    Primrec (fun x => encFormula (Formula.bigAnd (xs.map (F x)))) := by
  induction xs with
  | nil => exact Primrec.const _
  | cons a tl ih =>
    exact primrec_enc_and (hF a (by simp)) (ih (fun g hg => hF g (by simp [hg])))

lemma primrec_enc_bigOr_const {α γ : Type} [Primcodable α] (xs : List γ)
    (F : α → γ → Formula ℕ ℕ ℕ ℕ)
    (hF : ∀ g ∈ xs, Primrec (fun x => encFormula (F x g))) :
    Primrec (fun x => encFormula (Formula.bigOr (xs.map (F x)))) := by
  induction xs with
  | nil => exact Primrec.const _
  | cons a tl ih =>
    exact primrec_enc_or (hF a (by simp)) (ih (fun g hg => hF g (by simp [hg])))

/-! ### Part 5: 2-Counter Reduction Formula and `Primrec` Proof -/

section Parametric
variable [PayCode]

def atomQ1 (q : ℕ) : Formula ℕ ℕ ℕ ℕ :=
  Formula.bigOr ((List.range K).map fun i => Formula.out1 (i + K * q))

def atomQ2 (q : ℕ) : Formula ℕ ℕ ℕ ℕ :=
  Formula.bigOr ((List.range K).map fun i => Formula.out2 (i + K * q))

def atomPay1 (s : ℕ) (P : Payload → Bool) : Formula ℕ ℕ ℕ ℕ :=
  Formula.bigOr (((List.range (s + 1)).flatMap fun q => (payIndices P).map fun i => i + K * q).map
    Formula.out1)

def atomPay2 (s : ℕ) (P : Payload → Bool) : Formula ℕ ℕ ℕ ℕ :=
  Formula.bigOr (((List.range (s + 1)).flatMap fun q => (payIndices P).map fun i => i + K * q).map
    Formula.out2)

lemma primrec_atomQ1 : Primrec (fun q : ℕ => encFormula (atomQ1 q)) := by
  unfold atomQ1
  apply primrec_enc_bigOr_map (Primrec.const (List.range K))
  exact primrec_enc_out1 (Primrec.nat_add.comp Primrec.snd
    (Primrec.nat_mul.comp (Primrec.const K) Primrec.fst))

lemma primrec_atomQ2 : Primrec (fun q : ℕ => encFormula (atomQ2 q)) := by
  unfold atomQ2
  apply primrec_enc_bigOr_map (Primrec.const (List.range K))
  exact primrec_enc_out2 (Primrec.nat_add.comp Primrec.snd
    (Primrec.nat_mul.comp (Primrec.const K) Primrec.fst))

lemma primrec_payList (P : Payload → Bool) :
    Primrec (fun s : ℕ => (List.range (s + 1)).flatMap fun q => (payIndices P).map fun i => i + K * q) := by
  apply Primrec.list_flatMap (Primrec.list_range.comp Primrec.succ)
  unfold Primrec₂
  apply Primrec.list_map (Primrec.const (payIndices P))
  unfold Primrec₂
  exact Primrec.nat_add.comp Primrec.snd
    (Primrec.nat_mul.comp (Primrec.const K) (Primrec.snd.comp Primrec.fst))

lemma primrec_atomPay1 (P : Payload → Bool) : Primrec (fun s : ℕ => encFormula (atomPay1 s P)) :=
  primrec_enc_bigOr_map (primrec_payList P) (primrec_enc_out1 Primrec.snd)

lemma primrec_atomPay2 (P : Payload → Bool) : Primrec (fun s : ℕ => encFormula (atomPay2 s P)) :=
  primrec_enc_bigOr_map (primrec_payList P) (primrec_enc_out2 Primrec.snd)

def fPosEq (s : ℕ) (uv : Fin 3 × Fin 3) : Formula ℕ ℕ ℕ ℕ :=
  .and (atomPay1 s (fun p => pPos p == uv.1)) (atomPay2 s (fun p => pPos p == uv.2))

def fPhiPos (s : ℕ) (u v : Fin 3) (g : CommGraph) : Formula ℕ ℕ ℕ ℕ :=
  .imp (fPosEq s (u, v)) (.next (.imp (.graph g) (fPosEq s (Ctr.childPos g u v))))

def fPosOrd (s : ℕ) : Formula ℕ ℕ ℕ ℕ :=
  .and (Formula.bigAnd (Ctr.graphs.map fun g => .imp (.graph g) (fPosEq s (Ctr.childPos g 0 1))))
    (.always (Formula.bigAnd ((List.finRange 3).map fun u =>
      Formula.bigAnd ((List.finRange 3).map fun v =>
        Formula.bigAnd (Ctr.graphs.map fun g => fPhiPos s u v g)))))

def fOneIsLeft (s : ℕ) : Formula ℕ ℕ ℕ ℕ :=
  Formula.bigOr ((List.finRange 3).map fun u =>
    .and (atomPay1 s (fun p => pPos p == u)) (atomPay2 s (fun p => pPos p == Ctr.mod3 (u.val + 1))))

def fPathAgr (s : ℕ) : Formula ℕ ℕ ℕ ℕ :=
  .always (.and
    (Formula.bigOr ((List.range (s + 1)).map fun q => .and (atomQ1 q) (atomQ2 q)))
    (.and
      (Formula.bigOr (Ctr.bools.map fun z =>
        .and (atomPay1 s (fun p => pZero 0 p == z)) (atomPay2 s (fun p => pZero 0 p == z))))
      (Formula.bigOr (Ctr.bools.map fun z =>
        .and (atomPay1 s (fun p => pZero 1 p == z)) (atomPay2 s (fun p => pZero 1 p == z))))))

def codeEntry (c : CMCode) (q : ℕ) : Bool × ℕ × ℕ × ℕ :=
  (c.2.2.2[q]?).getD (false, 0, 0, 0)

def codeMult (c : CMCode) (r : Fin 2) (q : ℕ) (z0 z1 : Bool) : ℕ :=
  let ent := codeEntry c q
  if ent.2.1 % 2 = r.val then
    if ent.1 then (if (if r = 0 then z0 else z1) then 3 else 9) else 1
  else 3

def codeNextQ (c : CMCode) (q : ℕ) (z0 z1 : Bool) : ℕ :=
  let ent := codeEntry c q
  if ent.1 then
    if (if ent.2.1 % 2 = 0 then z0 else z1) then ent.2.2.1 % (c.1 + 1) else ent.2.2.2 % (c.1 + 1)
  else ent.2.2.1 % (c.1 + 1)

def fBal1 (s : ℕ) (r : Fin 2) (m : ℕ) : Formula ℕ ℕ ℕ ℕ :=
  Formula.bigOr ((List.finRange 9).map fun c2 =>
    .and (atomPay1 s (fun p => decide (pPlanSum r p + (pCarry r p).val = m * (pW r p).val + c2.val)))
      (atomPay2 s (fun p => pCarry r p == c2)))

def fBal2 (s : ℕ) (r : Fin 2) (m : ℕ) : Formula ℕ ℕ ℕ ℕ :=
  Formula.bigOr ((List.finRange 9).map fun c1 =>
    .and (atomPay2 s (fun p => decide (pPlanSum r p + (pCarry r p).val = m * (pW r p).val + c1.val)))
      (atomPay1 s (fun p => pCarry r p == c1)))

def fBalSel1 (s : ℕ) (r : Fin 2) (m : ℕ) : Formula ℕ ℕ ℕ ℕ :=
  if m = 1 then fBal1 s r 1 else if m = 3 then fBal1 s r 3 else fBal1 s r 9

def fBalSel2 (s : ℕ) (r : Fin 2) (m : ℕ) : Formula ℕ ℕ ℕ ℕ :=
  if m = 1 then fBal2 s r 1 else if m = 3 then fBal2 s r 3 else fBal2 s r 9

def fPsi1 (c : CMCode) (q : ℕ) (z0 z1 : Bool) : Formula ℕ ℕ ℕ ℕ :=
  .imp (.and (atomQ1 q) (.and (atomPay1 c.1 (fun p => pZero 0 p == z0))
      (atomPay1 c.1 (fun p => pZero 1 p == z1))))
    (.and (fBalSel1 c.1 0 (codeMult c 0 q z0 z1)) (fBalSel1 c.1 1 (codeMult c 1 q z0 z1)))

def fPsi2 (c : CMCode) (q : ℕ) (z0 z1 : Bool) : Formula ℕ ℕ ℕ ℕ :=
  .imp (.and (atomQ2 q) (.and (atomPay2 c.1 (fun p => pZero 0 p == z0))
      (atomPay2 c.1 (fun p => pZero 1 p == z1))))
    (.and (fBalSel2 c.1 0 (codeMult c 0 q z0 z1)) (fBalSel2 c.1 1 (codeMult c 1 q z0 z1)))

def fLocalSum (c : CMCode) : Formula ℕ ℕ ℕ ℕ :=
  .always (Formula.bigAnd ((List.range (c.1 + 1)).map fun q =>
    Formula.bigAnd (Ctr.bools.map fun z0 =>
      Formula.bigAnd (Ctr.bools.map fun z1 =>
        .and (.imp (fOneIsLeft c.1) (fPsi1 c q z0 z1))
          (.imp (.neg (fOneIsLeft c.1)) (fPsi2 c q z0 z1))))))

def fZeroIndR (s : ℕ) (r : Fin 2) : Formula ℕ ℕ ℕ ℕ :=
  .always (.or
    (.and (fOneIsLeft s) (.imp (atomPay1 s (fun p => pZero r p == true))
      (atomPay1 s (fun p => pW r p == 1))))
    (.and (.neg (fOneIsLeft s)) (.imp (atomPay2 s (fun p => pZero r p == true))
      (atomPay2 s (fun p => pW r p == 1)))))

def fLeftMostR (s : ℕ) (r : Fin 2) : Formula ℕ ℕ ℕ ℕ :=
  .weakUntil
    (.and (atomPay1 s (fun p => pCarry r p == 0))
      (.imp (atomPay1 s (fun p => pZero r p == false)) (atomPay1 s (fun p => pW r p == 0))))
    (.neg (.graph CommGraph.oneToTwo))

def fRightMostR (s : ℕ) (r : Fin 2) : Formula ℕ ℕ ℕ ℕ :=
  .weakUntil (atomPay2 s (fun p => pCarry r p == 0)) (.neg (.graph CommGraph.twoToOne))

def fZeroCheck (s : ℕ) : Formula ℕ ℕ ℕ ℕ :=
  .and (.and (fZeroIndR s 0) (fZeroIndR s 1))
    (.and (.and (fLeftMostR s 0) (fLeftMostR s 1)) (.and (fRightMostR s 0) (fRightMostR s 1)))

def fInitCheck (c : CMCode) : Formula ℕ ℕ ℕ ℕ :=
  .and (atomQ1 (c.2.1 % (c.1 + 1)))
    (.and (atomPay1 c.1 (fun p => pZero 0 p == true)) (atomPay1 c.1 (fun p => pZero 1 p == true)))

def fStateTrans (c : CMCode) : Formula ℕ ℕ ℕ ℕ :=
  Formula.bigAnd ((List.range (c.1 + 1)).map fun q =>
    Formula.bigAnd (Ctr.bools.map fun z0 =>
      Formula.bigAnd (Ctr.bools.map fun z1 =>
        .imp (.and (atomQ1 q) (.and (atomPay1 c.1 (fun p => pZero 0 p == z0))
            (atomPay1 c.1 (fun p => pZero 1 p == z1))))
          (.next (atomQ1 (codeNextQ c q z0 z1))))))

def fDK (s : ℕ) (k : Fin 3) (g : CommGraph) : Formula ℕ ℕ ℕ ℕ :=
  .or (.and (fOneIsLeft s) (if Ctr.dVal true g = k.val then Formula.tt else Formula.ff))
    (.and (.neg (fOneIsLeft s)) (if Ctr.dVal false g = k.val then Formula.tt else Formula.ff))

def fPlanL (s : ℕ) (sel : Payload → Fin 2) (b : Fin 2) : Formula ℕ ℕ ℕ ℕ :=
  .or (.and (fOneIsLeft s) (atomPay1 s (fun p => sel p == b)))
    (.and (.neg (fOneIsLeft s)) (atomPay2 s (fun p => sel p == b)))

def fWeightTransR (s : ℕ) (r : Fin 2) : Formula ℕ ℕ ℕ ℕ :=
  Formula.bigAnd ((List.finRange 3).map fun k =>
    Formula.bigAnd ((List.finRange 2).map fun b =>
      Formula.bigAnd (Ctr.graphs.map fun g =>
        .imp (.and (.next (.graph g)) (.and (fDK s k g) (fPlanL s (pA r k) b)))
          (.next (fPlanL s (pW r) b)))))

def fPropTrans (c : CMCode) : Formula ℕ ℕ ℕ ℕ :=
  .always (.and (fStateTrans c) (.and (fWeightTransR c.1 0) (fWeightTransR c.1 1)))

def fNoHalt (c : CMCode) : Formula ℕ ℕ ℕ ℕ :=
  .always (Formula.bigAnd (c.2.2.1.map fun q => .neg (atomQ1 q)))

def instFormula (c : CMCode) : Formula ℕ ℕ ℕ ℕ :=
  .and (fPosOrd c.1) (.and (fPathAgr c.1) (.and (fLocalSum c) (.and (fZeroCheck c.1)
    (.and (fInitCheck c) (.and (fPropTrans c) (fNoHalt c))))))

def red (c : CMCode) : Instance :=
  ⟨0, 0, outM c.1, outM c.1, encFormula (instFormula c)⟩

end Parametric

lemma primrec_codeEntry : Primrec (fun p : CMCode × ℕ => codeEntry p.1 p.2) :=
  Primrec.option_getD.comp
    (Primrec.list_getElem?.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)
    (Primrec.const (false, 0, 0, 0))

lemma primrec_codeMult (r : Fin 2) (z0 z1 : Bool) :
    Primrec (fun p : CMCode × ℕ => codeMult p.1 r p.2 z0 z1) := by
  have hent := primrec_codeEntry
  have hi_mod : Primrec (fun p : CMCode × ℕ => (codeEntry p.1 p.2).2.1 % 2) :=
    Primrec.nat_mod.comp (Primrec.fst.comp (Primrec.snd.comp hent)) (Primrec.const 2)
  have hisDec : Primrec (fun p : CMCode × ℕ => (codeEntry p.1 p.2).1) :=
    Primrec.fst.comp hent
  let hdecBranch : ℕ := if (if r = 0 then z0 else z1) then 3 else 9
  have hinner : Primrec (fun p : CMCode × ℕ => cond (codeEntry p.1 p.2).1 hdecBranch 1) :=
    Primrec.cond hisDec (Primrec.const hdecBranch) (Primrec.const 1)
  exact (Primrec.ite (Primrec.eq.comp hi_mod (Primrec.const r.val)) hinner (Primrec.const 3)).of_eq
    fun p => by
      unfold codeMult
      by_cases hm : (codeEntry p.1 p.2).2.1 % 2 = r.val <;>
        cases hd : (codeEntry p.1 p.2).1 <;> simp [hm, hd, hdecBranch]

lemma primrec_codeNextQ (z0 z1 : Bool) :
    Primrec (fun p : CMCode × ℕ => codeNextQ p.1 p.2 z0 z1) := by
  have hent := primrec_codeEntry
  have hs1 : Primrec (fun p : CMCode × ℕ => p.1.1 + 1) :=
    Primrec.succ.comp (Primrec.fst.comp Primrec.fst)
  have ha : Primrec (fun p : CMCode × ℕ => (codeEntry p.1 p.2).2.2.1 % (p.1.1 + 1)) :=
    Primrec.nat_mod.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hent))) hs1
  have hb : Primrec (fun p : CMCode × ℕ => (codeEntry p.1 p.2).2.2.2 % (p.1.1 + 1)) :=
    Primrec.nat_mod.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hent))) hs1
  have hi0 : Primrec (fun p : CMCode × ℕ => decide ((codeEntry p.1 p.2).2.1 % 2 = 0)) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.fst.comp (Primrec.snd.comp hent)) (Primrec.const 2))
      (Primrec.const 0)).decide
  have hzi : Primrec (fun p : CMCode × ℕ => if (codeEntry p.1 p.2).2.1 % 2 = 0 then z0 else z1) :=
    (Primrec.cond hi0 (Primrec.const z0) (Primrec.const z1)).of_eq fun p => by
      by_cases h : (codeEntry p.1 p.2).2.1 % 2 = 0 <;> simp [h]
  have hdec : Primrec (fun p : CMCode × ℕ =>
      cond (if (codeEntry p.1 p.2).2.1 % 2 = 0 then z0 else z1)
        ((codeEntry p.1 p.2).2.2.1 % (p.1.1 + 1))
        ((codeEntry p.1 p.2).2.2.2 % (p.1.1 + 1))) :=
    Primrec.cond hzi ha hb
  exact (Primrec.cond (Primrec.fst.comp hent) hdec ha).of_eq fun p => by
    unfold codeNextQ
    cases hd : (codeEntry p.1 p.2).1 <;>
      cases hz : (if (codeEntry p.1 p.2).2.1 % 2 = 0 then z0 else z1) <;> simp [hd, hz]

section Parametric
variable [PayCode]

lemma primrec_fOneIsLeft : Primrec (fun s : ℕ => encFormula (fOneIsLeft s)) :=
  primrec_enc_bigOr_const (List.finRange 3) _ fun _ _ =>
    primrec_enc_and (primrec_atomPay1 _) (primrec_atomPay2 _)

lemma primrec_fPosOrd : Primrec (fun s : ℕ => encFormula (fPosOrd s)) := by
  have hposEq : ∀ uv : Fin 3 × Fin 3, Primrec (fun s : ℕ => encFormula (fPosEq s uv)) :=
    fun uv => primrec_enc_and (primrec_atomPay1 _) (primrec_atomPay2 _)
  exact primrec_enc_and
    (primrec_enc_bigAnd_const Ctr.graphs _ fun g _ =>
      primrec_enc_imp (Primrec.const _) (hposEq _))
    (primrec_enc_always (primrec_enc_bigAnd_const (List.finRange 3) _ fun u _ =>
      primrec_enc_bigAnd_const (List.finRange 3) _ fun v _ =>
        primrec_enc_bigAnd_const Ctr.graphs _ fun g _ =>
          primrec_enc_imp (hposEq _) (primrec_enc_next (primrec_enc_imp (Primrec.const _) (hposEq _)))))

lemma primrec_fPathAgr : Primrec (fun s : ℕ => encFormula (fPathAgr s)) :=
  primrec_enc_always (primrec_enc_and
    (primrec_enc_bigOr_map (Primrec.list_range.comp Primrec.succ)
      (primrec_enc_and (primrec_atomQ1.comp Primrec.snd) (primrec_atomQ2.comp Primrec.snd)))
    (primrec_enc_and
      (primrec_enc_bigOr_const Ctr.bools _ fun _ _ =>
        primrec_enc_and (primrec_atomPay1 _) (primrec_atomPay2 _))
      (primrec_enc_bigOr_const Ctr.bools _ fun _ _ =>
        primrec_enc_and (primrec_atomPay1 _) (primrec_atomPay2 _))))

lemma primrec_fBal1 (r : Fin 2) (m : ℕ) : Primrec (fun s : ℕ => encFormula (fBal1 s r m)) :=
  primrec_enc_bigOr_const (List.finRange 9) _ fun _ _ =>
    primrec_enc_and (primrec_atomPay1 _) (primrec_atomPay2 _)

lemma primrec_fBal2 (r : Fin 2) (m : ℕ) : Primrec (fun s : ℕ => encFormula (fBal2 s r m)) :=
  primrec_enc_bigOr_const (List.finRange 9) _ fun _ _ =>
    primrec_enc_and (primrec_atomPay2 _) (primrec_atomPay1 _)

lemma primrec_fBalSel1 (r : Fin 2) (z0 z1 : Bool) :
    Primrec (fun p : CMCode × ℕ => encFormula (fBalSel1 p.1.1 r (codeMult p.1 r p.2 z0 z1))) := by
  have hm := primrec_codeMult r z0 z1
  have hs : Primrec (fun p : CMCode × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  exact (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1)) ((primrec_fBal1 r 1).comp hs)
    (Primrec.ite (Primrec.eq.comp hm (Primrec.const 3)) ((primrec_fBal1 r 3).comp hs)
      ((primrec_fBal1 r 9).comp hs))).of_eq fun p => by
    unfold fBalSel1
    split_ifs <;> rfl

lemma primrec_fBalSel2 (r : Fin 2) (z0 z1 : Bool) :
    Primrec (fun p : CMCode × ℕ => encFormula (fBalSel2 p.1.1 r (codeMult p.1 r p.2 z0 z1))) := by
  have hm := primrec_codeMult r z0 z1
  have hs : Primrec (fun p : CMCode × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  exact (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1)) ((primrec_fBal2 r 1).comp hs)
    (Primrec.ite (Primrec.eq.comp hm (Primrec.const 3)) ((primrec_fBal2 r 3).comp hs)
      ((primrec_fBal2 r 9).comp hs))).of_eq fun p => by
    unfold fBalSel2
    split_ifs <;> rfl

lemma primrec_fLocalSum : Primrec (fun c : CMCode => encFormula (fLocalSum c)) := by
  apply primrec_enc_always
  apply primrec_enc_bigAnd_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
  apply primrec_enc_bigAnd_const Ctr.bools _ fun z0 _ => ?_
  apply primrec_enc_bigAnd_const Ctr.bools _ fun z1 _ => ?_
  have hs : Primrec (fun p : CMCode × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hoil := primrec_fOneIsLeft.comp hs
  exact primrec_enc_and
    (primrec_enc_imp hoil
      (primrec_enc_imp
        (primrec_enc_and (primrec_atomQ1.comp Primrec.snd)
          (primrec_enc_and ((primrec_atomPay1 _).comp hs) ((primrec_atomPay1 _).comp hs)))
        (primrec_enc_and (primrec_fBalSel1 0 z0 z1) (primrec_fBalSel1 1 z0 z1))))
    (primrec_enc_imp (primrec_enc_neg hoil)
      (primrec_enc_imp
        (primrec_enc_and (primrec_atomQ2.comp Primrec.snd)
          (primrec_enc_and ((primrec_atomPay2 _).comp hs) ((primrec_atomPay2 _).comp hs)))
        (primrec_enc_and (primrec_fBalSel2 0 z0 z1) (primrec_fBalSel2 1 z0 z1))))

lemma primrec_fZeroCheck : Primrec (fun s : ℕ => encFormula (fZeroCheck s)) := by
  have hzi : ∀ r : Fin 2, Primrec (fun s : ℕ => encFormula (fZeroIndR s r)) := fun r =>
    primrec_enc_always (primrec_enc_or
      (primrec_enc_and primrec_fOneIsLeft (primrec_enc_imp (primrec_atomPay1 _) (primrec_atomPay1 _)))
      (primrec_enc_and (primrec_enc_neg primrec_fOneIsLeft)
        (primrec_enc_imp (primrec_atomPay2 _) (primrec_atomPay2 _))))
  have hlm : ∀ r : Fin 2, Primrec (fun s : ℕ => encFormula (fLeftMostR s r)) := fun r =>
    primrec_enc_weakUntil
      (primrec_enc_and (primrec_atomPay1 _) (primrec_enc_imp (primrec_atomPay1 _) (primrec_atomPay1 _)))
      (Primrec.const _)
  have hrm : ∀ r : Fin 2, Primrec (fun s : ℕ => encFormula (fRightMostR s r)) := fun r =>
    primrec_enc_weakUntil (primrec_atomPay2 _) (Primrec.const _)
  exact primrec_enc_and (primrec_enc_and (hzi 0) (hzi 1))
    (primrec_enc_and (primrec_enc_and (hlm 0) (hlm 1)) (primrec_enc_and (hrm 0) (hrm 1)))

lemma primrec_fInitCheck : Primrec (fun c : CMCode => encFormula (fInitCheck c)) :=
  primrec_enc_and
    (primrec_atomQ1.comp (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.succ.comp Primrec.fst)))
    (primrec_enc_and ((primrec_atomPay1 _).comp Primrec.fst) ((primrec_atomPay1 _).comp Primrec.fst))

lemma primrec_fPropTrans : Primrec (fun c : CMCode => encFormula (fPropTrans c)) := by
  have hs : Primrec (fun p : CMCode × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hst : Primrec (fun c : CMCode => encFormula (fStateTrans c)) :=
    primrec_enc_bigAnd_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
      (primrec_enc_bigAnd_const Ctr.bools _ fun z0 _ =>
        primrec_enc_bigAnd_const Ctr.bools _ fun z1 _ =>
          primrec_enc_imp
            (primrec_enc_and (primrec_atomQ1.comp Primrec.snd)
              (primrec_enc_and ((primrec_atomPay1 _).comp hs) ((primrec_atomPay1 _).comp hs)))
            (primrec_enc_next (primrec_atomQ1.comp (primrec_codeNextQ z0 z1))))
  have hwt : ∀ r : Fin 2, Primrec (fun s : ℕ => encFormula (fWeightTransR s r)) := fun r =>
    primrec_enc_bigAnd_const (List.finRange 3) _ fun k _ =>
      primrec_enc_bigAnd_const (List.finRange 2) _ fun b _ =>
        primrec_enc_bigAnd_const Ctr.graphs _ fun g _ =>
          primrec_enc_imp
            (primrec_enc_and (Primrec.const _)
              (primrec_enc_and
                (primrec_enc_or
                  (primrec_enc_and primrec_fOneIsLeft (Primrec.const _))
                  (primrec_enc_and (primrec_enc_neg primrec_fOneIsLeft) (Primrec.const _)))
                (primrec_enc_or
                  (primrec_enc_and primrec_fOneIsLeft (primrec_atomPay1 _))
                  (primrec_enc_and (primrec_enc_neg primrec_fOneIsLeft) (primrec_atomPay2 _)))))
            (primrec_enc_next (primrec_enc_or
              (primrec_enc_and primrec_fOneIsLeft (primrec_atomPay1 _))
              (primrec_enc_and (primrec_enc_neg primrec_fOneIsLeft) (primrec_atomPay2 _))))
  exact primrec_enc_always (primrec_enc_and hst
    (primrec_enc_and ((hwt 0).comp Primrec.fst) ((hwt 1).comp Primrec.fst)))

lemma primrec_fNoHalt : Primrec (fun c : CMCode => encFormula (fNoHalt c)) :=
  primrec_enc_always (primrec_enc_bigAnd_map
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (primrec_enc_neg (primrec_atomQ1.comp Primrec.snd)))

lemma primrec_instFormula : Primrec (fun c : CMCode => encFormula (instFormula c)) :=
  primrec_enc_and (primrec_fPosOrd.comp Primrec.fst)
    (primrec_enc_and (primrec_fPathAgr.comp Primrec.fst)
      (primrec_enc_and primrec_fLocalSum
        (primrec_enc_and (primrec_fZeroCheck.comp Primrec.fst)
          (primrec_enc_and primrec_fInitCheck
            (primrec_enc_and primrec_fPropTrans primrec_fNoHalt)))))

lemma computable_red : Computable red := by
  have hm : Primrec (fun c : CMCode => outM c.1) :=
    Primrec.nat_add.comp (Primrec.const (K - 1))
      (Primrec.nat_mul.comp (Primrec.const K) Primrec.fst)
  have htup : Primrec (fun c : CMCode =>
      (0, 0, outM c.1, outM c.1, encFormula (instFormula c))) :=
    Primrec.pair (Primrec.const 0)
      (Primrec.pair (Primrec.const 0)
        (Primrec.pair hm (Primrec.pair hm primrec_instFormula)))
  have hdec : Primrec Instance.equiv.invFun := Primrec.of_equiv_symm
  exact (hdec.comp htup).to_comp

end Parametric

/-! ### Part 6: Structural Safety Proof for `red c` -/

def horizon {X1 X2 Y1 Y2 : Type} : Formula X1 X2 Y1 Y2 → Option ℕ
  | .inp1 _ | .inp2 _ | .out1 _ | .out2 _ | .graph _ => some 1
  | .neg φ => horizon φ
  | .and φ ψ | .or φ ψ | .imp φ ψ | .iff φ ψ => Option.map₂ max (horizon φ) (horizon ψ)
  | .next φ => (horizon φ).map (· + 1)
  | .eventually _ | .always _ | .untl _ _ | .weakUntil _ _ => none

lemma sat_congr_of_horizon {X1 X2 Y1 Y2 : Type} (φ : Formula X1 X2 Y1 Y2) :
    ∀ (d : ℕ), horizon φ = some d →
      ∀ (e1 e2 : ℕ → Signal X1 X2 × (Y1 × Y2)),
        (∀ k < d, e1 k = e2 k) → (φ.Sat e1 ↔ φ.Sat e2) := by
  induction φ with
  | inp1 x => intro d hd e1 e2 heq; simp [horizon] at hd; subst hd; simp [Formula.Sat, heq 0 (by omega)]
  | inp2 x => intro d hd e1 e2 heq; simp [horizon] at hd; subst hd; simp [Formula.Sat, heq 0 (by omega)]
  | out1 y => intro d hd e1 e2 heq; simp [horizon] at hd; subst hd; simp [Formula.Sat, heq 0 (by omega)]
  | out2 y => intro d hd e1 e2 heq; simp [horizon] at hd; subst hd; simp [Formula.Sat, heq 0 (by omega)]
  | graph g => intro d hd e1 e2 heq; simp [horizon] at hd; subst hd; simp [Formula.Sat, heq 0 (by omega)]
  | neg φ ih =>
    intro d hd e1 e2 heq
    simp only [Formula.Sat]
    exact not_congr (ih d hd e1 e2 heq)
  | next φ ih =>
    intro d hd e1 e2 heq
    simp only [horizon, Option.map_eq_some_iff] at hd
    rcases hd with ⟨d0, hd0, rfl⟩
    exact ih d0 hd0 (shift e1 1) (shift e2 1) (fun k hk => heq (k + 1) (by omega))
  | and φ ψ ih1 ih2 =>
    intro d hd e1 e2 heq
    simp only [horizon, Option.map₂_eq_some_iff] at hd
    rcases hd with ⟨d1, d2, h1, h2, rfl⟩
    exact and_congr (ih1 d1 h1 e1 e2 (fun k hk => heq k (by omega)))
      (ih2 d2 h2 e1 e2 (fun k hk => heq k (by omega)))
  | or φ ψ ih1 ih2 =>
    intro d hd e1 e2 heq
    simp only [horizon, Option.map₂_eq_some_iff] at hd
    rcases hd with ⟨d1, d2, h1, h2, rfl⟩
    exact or_congr (ih1 d1 h1 e1 e2 (fun k hk => heq k (by omega)))
      (ih2 d2 h2 e1 e2 (fun k hk => heq k (by omega)))
  | imp φ ψ ih1 ih2 =>
    intro d hd e1 e2 heq
    simp only [horizon, Option.map₂_eq_some_iff] at hd
    rcases hd with ⟨d1, d2, h1, h2, rfl⟩
    exact imp_congr (ih1 d1 h1 e1 e2 (fun k hk => heq k (by omega)))
      (ih2 d2 h2 e1 e2 (fun k hk => heq k (by omega)))
  | iff φ ψ ih1 ih2 =>
    intro d hd e1 e2 heq
    simp only [horizon, Option.map₂_eq_some_iff] at hd
    rcases hd with ⟨d1, d2, h1, h2, rfl⟩
    exact iff_congr (ih1 d1 h1 e1 e2 (fun k hk => heq k (by omega)))
      (ih2 d2 h2 e1 e2 (fun k hk => heq k (by omega)))
  | eventually _ => intro d hd; simp [horizon] at hd
  | always _ => intro d hd; simp [horizon] at hd
  | untl _ _ => intro d hd; simp [horizon] at hd
  | weakUntil _ _ => intro d hd; simp [horizon] at hd

lemma append_pre_lt {α : Type} (t u : ℕ → α) (i k : ℕ) (hk : k < i) :
    append (pre t i) u k = t k := by
  unfold append
  have hlt : k < (pre t i).length := by simp [pre, hk]
  rw [dif_pos hlt, pre_get]

lemma isSafety_of_horizon {X1 X2 Y1 Y2 : Type} {φ : Formula X1 X2 Y1 Y2}
    (h : (horizon φ).isSome) : φ.IsSafety := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
  intro t ht
  refine ⟨d, fun u hu => ht ?_⟩
  exact (sat_congr_of_horizon φ d hd (append (pre t d) u) t (append_pre_lt t u d)).mp hu

lemma isSafety_and {X1 X2 Y1 Y2 : Type} {φ ψ : Formula X1 X2 Y1 Y2}
    (hφ : φ.IsSafety) (hψ : ψ.IsSafety) : (Formula.and φ ψ).IsSafety := by
  intro t ht
  change ¬ (φ.Sat t ∧ ψ.Sat t) at ht
  rw [not_and_or] at ht
  rcases ht with ht1 | ht2
  · obtain ⟨i, hi⟩ := hφ t ht1
    exact ⟨i, fun u hu => hi u hu.1⟩
  · obtain ⟨i, hi⟩ := hψ t ht2
    exact ⟨i, fun u hu => hi u hu.2⟩

lemma isSafety_always_of_horizon {X1 X2 Y1 Y2 : Type} {φ : Formula X1 X2 Y1 Y2}
    (h : (horizon φ).isSome) : (Formula.always φ).IsSafety := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
  intro t ht
  change ¬ (∀ r, φ.Sat (shift t r)) at ht
  rw [not_forall] at ht
  rcases ht with ⟨r, hr⟩
  refine ⟨r + d, fun u hu => hr ?_⟩
  have hur : φ.Sat (shift (append (pre t (r + d)) u) r) := hu r
  exact (sat_congr_of_horizon φ d hd _ (shift t r) (fun k hk => by
    simp only [shift]
    exact append_pre_lt t u (r + d) (k + r) (by omega))).mp hur

lemma isSafety_weakUntil_not_graph {X1 X2 Y1 Y2 : Type} {ψ : Formula X1 X2 Y1 Y2}
    (h : horizon ψ = some 1) (g : CommGraph) :
    (Formula.weakUntil ψ (.neg (.graph g))).IsSafety := by
  intro t ht
  change ¬ (Formula.weakUntil ψ (.neg (.graph g))).Sat t at ht
  have hiff : ∀ e, (Formula.weakUntil ψ (.neg (.graph g))).Sat e ↔
      ∀ r, (∀ k ≤ r, (e k).1.2.2 = g) → ψ.Sat (shift e r) := by
    intro e
    simp only [Formula.Sat, shift]
    constructor
    · rintro (hall | ⟨r0, hneq, hbefore⟩) r hstay
      · exact hall r
      · by_cases hr : r < r0
        · exact hbefore r hr
        · exact False.elim (hneq (by simpa using hstay r0 (by omega)))
    · intro hh
      by_cases hall : ∀ k, (e k).1.2.2 = g
      · exact Or.inl (fun r => hh r (fun k _ => hall k))
      · classical
        push Not at hall
        let r0 := Nat.find hall
        refine Or.inr ⟨r0, by simpa using Nat.find_spec hall, fun r' hr' => hh r' (fun k hk => ?_)⟩
        have hmin := Nat.find_min hall (Nat.lt_of_le_of_lt hk hr')
        push Not at hmin
        exact hmin
  rw [hiff] at ht
  push Not at ht
  rcases ht with ⟨r, hstay, hbad⟩
  refine ⟨r + 1, fun u hu => hbad ?_⟩
  have hu' := (hiff _).mp hu r (fun k hk => by
    rw [append_pre_lt t u (r + 1) k (by omega)]
    exact hstay k hk)
  exact (sat_congr_of_horizon ψ 1 h _ (shift t r) (fun k hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [shift, zero_add]
    exact append_pre_lt t u (r + 1) r (by omega))).mp hu'

lemma horizon_bigAnd {X1 X2 Y1 Y2 : Type} (l : List (Formula X1 X2 Y1 Y2))
    (hl : ∀ φ ∈ l, (horizon φ).isSome) : (horizon (Formula.bigAnd l)).isSome := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    obtain ⟨d1, h1⟩ := Option.isSome_iff_exists.mp (hl a (by simp))
    obtain ⟨d2, h2⟩ := Option.isSome_iff_exists.mp (ih (fun φ hφ => hl φ (by simp [hφ])))
    simp [Formula.bigAnd, horizon, h1, h2]

lemma horizon_bigOr_one {X1 X2 Y1 Y2 : Type} (l : List (Formula X1 X2 Y1 Y2))
    (hl : ∀ φ ∈ l, horizon φ = some 1) : horizon (Formula.bigOr l) = some 1 := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    simp [Formula.bigOr, horizon, hl a (by simp), ih (fun φ hφ => hl φ (by simp [hφ]))]

section Parametric
variable [PayCode]

lemma horizon_atomQ1 (q : ℕ) : horizon (atomQ1 q) = some 1 := by
  apply horizon_bigOr_one; simp only [List.mem_map]; rintro _ ⟨i, _, rfl⟩; rfl

lemma horizon_atomQ2 (q : ℕ) : horizon (atomQ2 q) = some 1 := by
  apply horizon_bigOr_one; simp only [List.mem_map]; rintro _ ⟨i, _, rfl⟩; rfl

lemma horizon_atomPay1 (s : ℕ) (P : Payload → Bool) : horizon (atomPay1 s P) = some 1 := by
  apply horizon_bigOr_one; simp only [List.mem_map]; rintro _ ⟨i, _, rfl⟩; rfl

lemma horizon_atomPay2 (s : ℕ) (P : Payload → Bool) : horizon (atomPay2 s P) = some 1 := by
  apply horizon_bigOr_one; simp only [List.mem_map]; rintro _ ⟨i, _, rfl⟩; rfl

lemma horizon_fOneIsLeft (s : ℕ) : horizon (fOneIsLeft s) = some 1 := by
  apply horizon_bigOr_one; simp only [List.mem_map]; rintro _ ⟨u, _, rfl⟩
  simp [horizon, horizon_atomPay1, horizon_atomPay2]

lemma horizon_fBalSel1 (s : ℕ) (r : Fin 2) (m : ℕ) : horizon (fBalSel1 s r m) = some 1 := by
  have hb : ∀ k, horizon (fBal1 s r k) = some 1 := fun k => by
    apply horizon_bigOr_one; simp only [List.mem_map]; rintro _ ⟨c2, _, rfl⟩
    simp [horizon, horizon_atomPay1, horizon_atomPay2]
  unfold fBalSel1; split_ifs <;> exact hb _

lemma horizon_fBalSel2 (s : ℕ) (r : Fin 2) (m : ℕ) : horizon (fBalSel2 s r m) = some 1 := by
  have hb : ∀ k, horizon (fBal2 s r k) = some 1 := fun k => by
    apply horizon_bigOr_one; simp only [List.mem_map]; rintro _ ⟨c1, _, rfl⟩
    simp [horizon, horizon_atomPay1, horizon_atomPay2]
  unfold fBalSel2; split_ifs <;> exact hb _

lemma instFormula_isSafety (c : CMCode) : (instFormula c).IsSafety := by
  have hposEq : ∀ uv, (horizon (fPosEq c.1 uv)).isSome := fun uv => by
    simp [fPosEq, horizon, horizon_atomPay1, horizon_atomPay2]
  have hPosOrd : (fPosOrd c.1).IsSafety := by
    apply isSafety_and
    · apply isSafety_of_horizon
      apply horizon_bigAnd; simp only [List.mem_map]; rintro _ ⟨g, _, rfl⟩
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hposEq (Ctr.childPos g 0 1))
      simp [horizon, hd]
    · apply isSafety_always_of_horizon
      apply horizon_bigAnd; simp only [List.mem_map]; rintro _ ⟨u, _, rfl⟩
      apply horizon_bigAnd; simp only [List.mem_map]; rintro _ ⟨v, _, rfl⟩
      apply horizon_bigAnd; simp only [List.mem_map]; rintro _ ⟨g, _, rfl⟩
      obtain ⟨d1, hd1⟩ := Option.isSome_iff_exists.mp (hposEq (u, v))
      obtain ⟨d2, hd2⟩ := Option.isSome_iff_exists.mp (hposEq (Ctr.childPos g u v))
      simp [fPhiPos, horizon, hd1, hd2]
  have hPathAgr : (fPathAgr c.1).IsSafety := by
    apply isSafety_always_of_horizon
    have hq : horizon (Formula.bigOr ((List.range (c.1 + 1)).map fun q => .and (atomQ1 q) (atomQ2 q))) = some 1 := by
      apply horizon_bigOr_one; simp only [List.mem_map]; rintro _ ⟨q, _, rfl⟩
      simp [horizon, horizon_atomQ1, horizon_atomQ2]
    have hz : ∀ r : Fin 2, horizon (Formula.bigOr (Ctr.bools.map fun z =>
        .and (atomPay1 c.1 (fun p => pZero r p == z)) (atomPay2 c.1 (fun p => pZero r p == z)))) = some 1 := fun r => by
      apply horizon_bigOr_one; simp only [List.mem_map]; rintro _ ⟨z, _, rfl⟩
      simp [horizon, horizon_atomPay1, horizon_atomPay2]
    simp [horizon, hq, hz 0, hz 1]
  have hLocalSum : (fLocalSum c).IsSafety := by
    apply isSafety_always_of_horizon
    apply horizon_bigAnd; simp only [List.mem_map]; rintro _ ⟨q, _, rfl⟩
    apply horizon_bigAnd; simp only [List.mem_map]; rintro _ ⟨z0, _, rfl⟩
    apply horizon_bigAnd; simp only [List.mem_map]; rintro _ ⟨z1, _, rfl⟩
    simp [fPsi1, fPsi2, horizon, horizon_fOneIsLeft, horizon_atomQ1, horizon_atomQ2,
      horizon_atomPay1, horizon_atomPay2, horizon_fBalSel1, horizon_fBalSel2]
  have hZeroCheck : (fZeroCheck c.1).IsSafety := by
    have hzi : ∀ r : Fin 2, (fZeroIndR c.1 r).IsSafety := fun r => by
      apply isSafety_always_of_horizon
      simp [horizon, horizon_fOneIsLeft, horizon_atomPay1, horizon_atomPay2]
    have hlm : ∀ r : Fin 2, (fLeftMostR c.1 r).IsSafety := fun r =>
      isSafety_weakUntil_not_graph (by simp [horizon, horizon_atomPay1]) _
    have hrm : ∀ r : Fin 2, (fRightMostR c.1 r).IsSafety := fun r =>
      isSafety_weakUntil_not_graph (horizon_atomPay2 c.1 _) _
    exact isSafety_and (isSafety_and (hzi 0) (hzi 1))
      (isSafety_and (isSafety_and (hlm 0) (hlm 1)) (isSafety_and (hrm 0) (hrm 1)))
  have hInitCheck : (fInitCheck c).IsSafety :=
    isSafety_of_horizon (by simp [fInitCheck, horizon, horizon_atomQ1, horizon_atomPay1])
  have hPropTrans : (fPropTrans c).IsSafety := by
    apply isSafety_always_of_horizon
    have hst : (horizon (fStateTrans c)).isSome := by
      apply horizon_bigAnd; simp only [List.mem_map]; rintro _ ⟨q, _, rfl⟩
      apply horizon_bigAnd; simp only [List.mem_map]; rintro _ ⟨z0, _, rfl⟩
      apply horizon_bigAnd; simp only [List.mem_map]; rintro _ ⟨z1, _, rfl⟩
      simp [horizon, horizon_atomQ1, horizon_atomPay1]
    have hwt : ∀ r : Fin 2, (horizon (fWeightTransR c.1 r)).isSome := fun r => by
      apply horizon_bigAnd; simp only [List.mem_map]; rintro _ ⟨k, _, rfl⟩
      apply horizon_bigAnd; simp only [List.mem_map]; rintro _ ⟨b, _, rfl⟩
      apply horizon_bigAnd; simp only [List.mem_map]; rintro _ ⟨g, _, rfl⟩
      have hd1 : horizon (if Ctr.dVal true g = k.val then (Formula.tt : Formula ℕ ℕ ℕ ℕ) else Formula.ff) = some 1 := by
        split_ifs <;> rfl
      have hd2 : horizon (if Ctr.dVal false g = k.val then (Formula.tt : Formula ℕ ℕ ℕ ℕ) else Formula.ff) = some 1 := by
        split_ifs <;> rfl
      simp [fDK, fPlanL, horizon, horizon_fOneIsLeft, horizon_atomPay1, horizon_atomPay2, hd1, hd2]
    obtain ⟨ds, hds⟩ := Option.isSome_iff_exists.mp hst
    obtain ⟨dw0, hdw0⟩ := Option.isSome_iff_exists.mp (hwt 0)
    obtain ⟨dw1, hdw1⟩ := Option.isSome_iff_exists.mp (hwt 1)
    simp [horizon, hds, hdw0, hdw1]
  have hNoHalt : (fNoHalt c).IsSafety := by
    apply isSafety_always_of_horizon
    apply horizon_bigAnd; simp only [List.mem_map]; rintro _ ⟨q, _, rfl⟩
    simp [horizon, horizon_atomQ1]
  exact isSafety_and hPosOrd (isSafety_and hPathAgr (isSafety_and hLocalSum
    (isSafety_and hZeroCheck (isSafety_and hInitCheck (isSafety_and hPropTrans hNoHalt)))))

end Parametric

lemma append_pre_ge {α : Type} (t u : ℕ → α) (i n : ℕ) (hn : ¬ n < i) :
    append (pre t i) u n = u (n - i) := by
  have hl : (pre t i).length = i := by simp [pre]
  unfold append
  rw [dif_neg (by omega), hl]

lemma valExec_append_pre {a b d1 d2 : ℕ}
    (t u : ℕ → Signal (Fin a) (Fin b) × (Fin d1 × Fin d2)) (i : ℕ) :
    valExec (append (pre t i) u) = append (pre (valExec t) i) (valExec u) := by
  funext n
  by_cases hn : n < i
  · rw [append_pre_lt (valExec t) (valExec u) i n hn]
    unfold valExec
    rw [append_pre_lt t u i n hn]
  · rw [append_pre_ge (valExec t) (valExec u) i n hn]
    unfold valExec
    rw [append_pre_ge t u i n hn]

lemma instance_tokens_mk (k1 k2 m1 m2 : ℕ) (ts : List Token) :
    (Instance.mk k1 k2 m1 m2 ts).tokens = ts := rfl

lemma parse_mk_tokens (k1 k2 m1 m2 : ℕ) (φ : Formula ℕ ℕ ℕ ℕ) :
    parse (Instance.mk k1 k2 m1 m2 (encFormula φ)).tokens = some φ := by
  rw [instance_tokens_mk]
  exact parse_encFormula φ

lemma mk_isSafety (m1 m2 : ℕ) (φ : Formula ℕ ℕ ℕ ℕ) (hsaf : φ.IsSafety) :
    (Instance.mk 0 0 m1 m2 (encFormula φ)).IsSafety := by
  refine ⟨φ, parse_mk_tokens 0 0 m1 m2 φ, ?_⟩
  intro t ht
  have ht' : valExec t ∉ φ.Lang := ht
  obtain ⟨i, hi⟩ := hsaf (valExec t) ht'
  refine ⟨i, fun u hu => hi (valExec u) ?_⟩
  change φ.Sat (append (pre (valExec t) i) (valExec u))
  rw [← valExec_append_pre t u i]
  exact hu

lemma mk_realizable_iff (m1 m2 : ℕ) (φ : Formula ℕ ℕ ℕ ℕ) :
    (Instance.mk 0 0 m1 m2 (encFormula φ)).Realizable Set.univ ↔
      ∃ f : Algorithm (Fin 1) (Fin 1) (Fin (m1 + 1)) (Fin (m2 + 1)),
        ∀ sig : ℕ → Signal (Fin 1) (Fin 1), φ.Sat (valExec (exec f sig)) := by
  constructor
  · rintro ⟨ψ, hparse, f, hf⟩
    have hψ : ψ = φ := Option.some.inj (hparse.symm.trans (parse_mk_tokens 0 0 m1 m2 φ))
    subst hψ
    exact ⟨f, fun sig => hf sig (Set.mem_univ _)⟩
  · rintro ⟨f, hf⟩
    exact ⟨φ, parse_mk_tokens 0 0 m1 m2 φ, f, fun sig _ => hf sig⟩

lemma red_isSafety [PayCode] (c : CMCode) : (red c).IsSafety :=
  mk_isSafety (outM c.1) (outM c.1) (instFormula c) (instFormula_isSafety c)

/-! ### Part 7: Formula Satisfaction & 2-Counter Realizability Equivalence -/

lemma sat_tt {X1 X2 Y1 Y2 : Type} (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    (Formula.tt : Formula X1 X2 Y1 Y2).Sat e := by
  simp only [Formula.tt, Formula.Sat]; exact em _

lemma sat_ff {X1 X2 Y1 Y2 : Type} (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    ¬ (Formula.ff : Formula X1 X2 Y1 Y2).Sat e := by
  simp only [Formula.ff, Formula.Sat]; exact not_not_intro (sat_tt e)

lemma sat_bigAnd {X1 X2 Y1 Y2 : Type} (l : List (Formula X1 X2 Y1 Y2))
    (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    (Formula.bigAnd l).Sat e ↔ ∀ ψ ∈ l, ψ.Sat e := by
  induction l with
  | nil => simp [Formula.bigAnd, sat_tt]
  | cons a tl ih => simp only [Formula.bigAnd, Formula.Sat, ih, List.mem_cons, forall_eq_or_imp]

lemma sat_bigOr {X1 X2 Y1 Y2 : Type} (l : List (Formula X1 X2 Y1 Y2))
    (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    (Formula.bigOr l).Sat e ↔ ∃ ψ ∈ l, ψ.Sat e := by
  induction l with
  | nil => simp [Formula.bigOr, sat_ff]
  | cons a tl ih => simp only [Formula.bigOr, Formula.Sat, ih, List.mem_cons, exists_eq_or_imp]

lemma shift_shift {α : Type} (e : ℕ → α) (a b : ℕ) :
    shift (shift e a) b = shift e (a + b) := by
  funext n; simp only [shift]; congr 1; omega

lemma shift_valExec {a b c d : ℕ} (e : ℕ → Signal (Fin a) (Fin b) × (Fin c × Fin d)) (r : ℕ) :
    shift (valExec e) r = valExec (shift e r) := rfl

lemma sat_weakUntil_not_graph {X1 X2 Y1 Y2 : Type}
    (ψ : Formula X1 X2 Y1 Y2) (g : CommGraph)
    (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    (Formula.weakUntil ψ (.neg (.graph g))).Sat e ↔
      ∀ r, (∀ k ≤ r, (e k).1.2.2 = g) → ψ.Sat (shift e r) := by
  simp only [Formula.Sat, shift]
  constructor
  · rintro (hall | ⟨r0, hneq, hbefore⟩) r hstay
    · exact hall r
    · by_cases hr : r < r0
      · exact hbefore r hr
      · exact False.elim (hneq (by simpa using hstay r0 (by omega)))
  · intro hh
    by_cases hall : ∀ k, (e k).1.2.2 = g
    · exact Or.inl (fun r => hh r (fun k _ => hall k))
    · classical
      push Not at hall
      let r0 := Nat.find hall
      refine Or.inr ⟨r0, by simpa using Nat.find_spec hall, fun r' hr' => hh r' (fun k hk => ?_)⟩
      have hmin := Nat.find_min hall (Nat.lt_of_le_of_lt hk hr')
      push Not at hmin
      exact hmin

lemma mem_graphs (g : CommGraph) : g ∈ Ctr.graphs := by cases g <;> simp [Ctr.graphs]
lemma mem_bools (z : Bool) : z ∈ Ctr.bools := by cases z <;> simp [Ctr.bools]
lemma codeMult_mem (c : CMCode) (r : Fin 2) (q : ℕ) (z0 z1 : Bool) :
    codeMult c r q z0 z1 = 1 ∨ codeMult c r q z0 z1 = 3 ∨ codeMult c r q z0 z1 = 9 := by
  dsimp only [codeMult]
  split_ifs <;> simp

section Parametric
variable [PayCode]

lemma sat_atomQ1 {a b : ℕ} (s q : ℕ)
    (e : ℕ → Signal (Fin a) (Fin b) × (OutFin s × OutFin s)) :
    (atomQ1 q).Sat (valExec e) ↔ decodeQ (e 0).2.1.val = q := by
  unfold atomQ1 decodeQ
  rw [sat_bigOr]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, heq⟩
    change (e 0).2.1.val = i + K * q at heq
    rw [heq]
    exact div_K_encode q i hi
  · intro hdiv
    refine ⟨Formula.out1 ((e 0).2.1.val % K + K * q), ⟨(e 0).2.1.val % K, Nat.mod_lt _ K_pos, rfl⟩, ?_⟩
    change (e 0).2.1.val = (e 0).2.1.val % K + K * q
    have hdm := Nat.mod_add_div (e 0).2.1.val K
    rw [← hdiv]
    exact hdm.symm

lemma sat_atomQ2 {a b : ℕ} (s q : ℕ)
    (e : ℕ → Signal (Fin a) (Fin b) × (OutFin s × OutFin s)) :
    (atomQ2 q).Sat (valExec e) ↔ decodeQ (e 0).2.2.val = q := by
  unfold atomQ2 decodeQ
  rw [sat_bigOr]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, heq⟩
    change (e 0).2.2.val = i + K * q at heq
    rw [heq]
    exact div_K_encode q i hi
  · intro hdiv
    refine ⟨Formula.out2 ((e 0).2.2.val % K + K * q), ⟨(e 0).2.2.val % K, Nat.mod_lt _ K_pos, rfl⟩, ?_⟩
    change (e 0).2.2.val = (e 0).2.2.val % K + K * q
    have hdm := Nat.mod_add_div (e 0).2.2.val K
    rw [← hdiv]
    exact hdm.symm

lemma sat_atomPay1 {a b : ℕ} (s : ℕ) (P : Payload → Bool)
    (e : ℕ → Signal (Fin a) (Fin b) × (OutFin s × OutFin s)) :
    (atomPay1 s P).Sat (valExec e) ↔ P (decodePay (e 0).2.1.val) = true := by
  unfold atomPay1
  rw [sat_bigOr]
  simp only [List.mem_map, List.mem_flatMap, List.mem_range, mem_payIndices]
  constructor
  · rintro ⟨_, ⟨y, ⟨q, _, i, ⟨hi, hP⟩, rfl⟩, rfl⟩, heq⟩
    change (e 0).2.1.val = i + K * q at heq
    have hmod : (e 0).2.1.val % K = i % K := by
      rw [heq, mod_K_encode q i hi, Nat.mod_eq_of_lt hi]
    unfold decodePay at hP ⊢
    have hfin : (⟨(e 0).2.1.val % K, Nat.mod_lt _ K_pos⟩ : Fin K) = ⟨i % K, Nat.mod_lt _ K_pos⟩ :=
      Fin.ext hmod
    rwa [hfin]
  · intro hP
    let q := (e 0).2.1.val / K
    let i := (e 0).2.1.val % K
    have hq_lt : q < s + 1 := decodeQ_lt s (e 0).2.1
    have hi_lt : i < K := Nat.mod_lt _ K_pos
    have hPi : P (decodePay i) = true := by
      unfold decodePay at hP ⊢
      have hfin : (⟨i % K, Nat.mod_lt _ K_pos⟩ : Fin K) = ⟨(e 0).2.1.val % K, Nat.mod_lt _ K_pos⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hi_lt)
      rwa [hfin]
    have heq : (e 0).2.1.val = i + K * q := (Nat.mod_add_div (e 0).2.1.val K).symm
    exact ⟨Formula.out1 (i + K * q), ⟨i + K * q, ⟨q, hq_lt, i, ⟨hi_lt, hPi⟩, rfl⟩, rfl⟩, heq⟩

lemma sat_atomPay2 {a b : ℕ} (s : ℕ) (P : Payload → Bool)
    (e : ℕ → Signal (Fin a) (Fin b) × (OutFin s × OutFin s)) :
    (atomPay2 s P).Sat (valExec e) ↔ P (decodePay (e 0).2.2.val) = true := by
  unfold atomPay2
  rw [sat_bigOr]
  simp only [List.mem_map, List.mem_flatMap, List.mem_range, mem_payIndices]
  constructor
  · rintro ⟨_, ⟨y, ⟨q, _, i, ⟨hi, hP⟩, rfl⟩, rfl⟩, heq⟩
    change (e 0).2.2.val = i + K * q at heq
    have hmod : (e 0).2.2.val % K = i % K := by
      rw [heq, mod_K_encode q i hi, Nat.mod_eq_of_lt hi]
    unfold decodePay at hP ⊢
    have hfin : (⟨(e 0).2.2.val % K, Nat.mod_lt _ K_pos⟩ : Fin K) = ⟨i % K, Nat.mod_lt _ K_pos⟩ :=
      Fin.ext hmod
    rwa [hfin]
  · intro hP
    let q := (e 0).2.2.val / K
    let i := (e 0).2.2.val % K
    have hq_lt : q < s + 1 := decodeQ_lt s (e 0).2.2
    have hi_lt : i < K := Nat.mod_lt _ K_pos
    have hPi : P (decodePay i) = true := by
      unfold decodePay at hP ⊢
      have hfin : (⟨i % K, Nat.mod_lt _ K_pos⟩ : Fin K) = ⟨(e 0).2.2.val % K, Nat.mod_lt _ K_pos⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hi_lt)
      rwa [hfin]
    have heq : (e 0).2.2.val = i + K * q := (Nat.mod_add_div (e 0).2.2.val K).symm
    exact ⟨Formula.out2 (i + K * q), ⟨i + K * q, ⟨q, hq_lt, i, ⟨hi_lt, hPi⟩, rfl⟩, rfl⟩, heq⟩

lemma sat_fOneIsLeft {a b : ℕ} (s : ℕ)
    (e : ℕ → Signal (Fin a) (Fin b) × (OutFin s × OutFin s)) :
    (fOneIsLeft s).Sat (valExec e) ↔
      (pPos (decodePay (e 0).2.2.val)).val = ((pPos (decodePay (e 0).2.1.val)).val + 1) % 3 := by
  unfold fOneIsLeft
  rw [sat_bigOr]
  simp only [List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, h1, h2⟩
    rw [sat_atomPay1] at h1
    rw [sat_atomPay2] at h2
    have hu1 : pPos (decodePay (e 0).2.1.val) = u := of_decide_eq_true h1
    have hu2 : pPos (decodePay (e 0).2.2.val) = Ctr.mod3 (u.val + 1) := of_decide_eq_true h2
    rw [hu1, hu2]
    rfl
  · intro heq
    let u := pPos (decodePay (e 0).2.1.val)
    refine ⟨_, ⟨u, rfl⟩, ?_, ?_⟩
    · rw [sat_atomPay1, beq_iff_eq]
    · rw [sat_atomPay2, beq_iff_eq]; exact Fin.ext heq

lemma sat_fPosOrd {a b : ℕ} (s : ℕ)
    (e : ℕ → Signal (Fin a) (Fin b) × (OutFin s × OutFin s)) :
    (fPosOrd s).Sat (valExec e) ↔
      ((pPos (decodePay (e 0).2.1.val), pPos (decodePay (e 0).2.2.val)) =
          Ctr.childPos (e 0).1.2.2 0 1 ∧
        ∀ n, (pPos (decodePay (e (n + 1)).2.1.val), pPos (decodePay (e (n + 1)).2.2.val)) =
          Ctr.childPos (e (n + 1)).1.2.2
            (pPos (decodePay (e n).2.1.val)) (pPos (decodePay (e n).2.2.val))) := by
  unfold fPosOrd fPhiPos fPosEq
  constructor
  · rintro ⟨h0, hstep⟩
    rw [sat_bigAnd] at h0
    refine ⟨?_, fun n => ?_⟩
    · have hg := h0 _ (List.mem_map.mpr ⟨(e 0).1.2.2, mem_graphs _, rfl⟩) rfl
      simp only [Formula.Sat, sat_atomPay1, sat_atomPay2, beq_iff_eq] at hg
      exact Prod.ext hg.1 hg.2
    · have hn := hstep n
      rw [shift_valExec, sat_bigAnd] at hn
      let u := pPos (decodePay (e n).2.1.val)
      let v := pPos (decodePay (e n).2.2.val)
      let g := (e (n + 1)).1.2.2
      have h1 := hn _ (List.mem_map.mpr ⟨u, List.mem_finRange u, rfl⟩)
      rw [sat_bigAnd] at h1
      have h2 := h1 _ (List.mem_map.mpr ⟨v, List.mem_finRange v, rfl⟩)
      rw [sat_bigAnd] at h2
      have h3 := h2 _ (List.mem_map.mpr ⟨g, mem_graphs g, rfl⟩)
      simp only [Formula.Sat, shift_valExec, shift_shift, sat_atomPay1,
        sat_atomPay2, beq_iff_eq] at h3
      have hs0 : shift e n 0 = e n := by simp [shift]
      have hs1 : shift e (n + 1) 0 = e (n + 1) := by simp [shift]
      rw [hs0, hs1] at h3
      have hres := h3 ⟨rfl, rfl⟩ (by simp [valExec, shift, g])
      exact Prod.ext hres.1 hres.2
  · rintro ⟨h0, hstep⟩
    refine ⟨?_, fun n => ?_⟩
    · rw [sat_bigAnd]
      simp only [List.mem_map]
      rintro _ ⟨g, _, rfl⟩ hg
      change (e 0).1.2.2 = g at hg
      simp only [Formula.Sat, sat_atomPay1, sat_atomPay2, beq_iff_eq, ← hg]
      exact ⟨congrArg Prod.fst h0, congrArg Prod.snd h0⟩
    · rw [shift_valExec, sat_bigAnd]; simp only [List.mem_map]; rintro _ ⟨u, _, rfl⟩
      rw [sat_bigAnd]; simp only [List.mem_map]; rintro _ ⟨v, _, rfl⟩
      rw [sat_bigAnd]; simp only [List.mem_map]; rintro _ ⟨g, _, rfl⟩
      simp only [Formula.Sat, shift_valExec, shift_shift, sat_atomPay1,
        sat_atomPay2, beq_iff_eq]
      rintro ⟨hu, hv⟩ hg
      have hs0 : shift e n 0 = e n := by simp [shift]
      have hs1 : shift e (n + 1) 0 = e (n + 1) := by simp [shift]
      rw [hs0] at hu hv
      have hg' : (e (n + 1)).1.2.2 = g := by simpa [valExec, shift] using hg
      rw [hs1]
      have hsn := hstep n
      rw [hu, hv, hg'] at hsn
      exact ⟨congrArg Prod.fst hsn, congrArg Prod.snd hsn⟩

lemma fPosOrd_exec_coords (s : ℕ)
    (f : Algorithm (Fin 1) (Fin 1) (OutFin s) (OutFin s))
    (sig : ℕ → Sig0) (hpos : (fPosOrd s).Sat (valExec (exec f sig))) (n : ℕ) :
    (pPos (decodePay (exec f sig n).2.1.val), pPos (decodePay (exec f sig n).2.2.val)) =
      (Ctr.mod3 (vcoord0 (view1 (pre sig (n + 1)))), Ctr.mod3 (vcoord0 (view2 (pre sig (n + 1))))) := by
  obtain ⟨h0, hstep⟩ := (sat_fPosOrd s (exec f sig)).mp hpos
  induction n with
  | zero =>
    rw [vcoord0_mod3_pre sig 0]
    simpa [exec] using h0
  | succ n ih =>
    rw [vcoord0_mod3_pre sig (n + 1)]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    have ih1 : pPos (decodePay (exec f sig n).2.1.val) = Ctr.mod3 (vcoord0 (view1 (pre sig (n + 1)))) :=
      congrArg Prod.fst ih
    have ih2 : pPos (decodePay (exec f sig n).2.2.val) = Ctr.mod3 (vcoord0 (view2 (pre sig (n + 1)))) :=
      congrArg Prod.snd ih
    rw [hstep n, ih1, ih2]
    rfl

lemma fOneIsLeft_iff_even (s : ℕ)
    (f : Algorithm (Fin 1) (Fin 1) (OutFin s) (OutFin s))
    (sig : ℕ → Sig0) (hpos : (fPosOrd s).Sat (valExec (exec f sig))) (n : ℕ) :
    (fOneIsLeft s).Sat (shift (valExec (exec f sig)) n) ↔
      jIdx (pre (graphOf sig) (n + 1)) % 2 = 0 := by
  rw [shift_valExec, sat_fOneIsLeft]
  have hsh : shift (exec f sig) n 0 = exec f sig n := by simp [shift]
  rw [hsh]
  have hc := fPosOrd_exec_coords s f sig hpos n
  rw [pre_sig0_toSig0] at hc
  have hvc := vdepth_coord_views0 (pre (graphOf sig) (n + 1))
  have hc1 := congrArg Prod.fst hc
  have hc2 := congrArg Prod.snd hc
  dsimp only at hc1 hc2
  rw [hc1, hc2]
  set j := jIdx (pre (graphOf sig) (n + 1))
  rcases (show j % 2 = 0 ∨ j % 2 = 1 by omega) with hp | hp
  · simp only [hp, ↓reduceIte] at hvc ⊢
    simp [Ctr.mod3, hvc.2.2.1, hvc.2.2.2]
  · have hp0 : ¬ (j % 2 = 0) := by omega
    simp only [hp0, ↓reduceIte, iff_false] at hvc ⊢
    simp [Ctr.mod3, hvc.2.2.1, hvc.2.2.2]
    omega

lemma fBalSel1_eq (s : ℕ) (r : Fin 2) (m : ℕ) (hm : m = 1 ∨ m = 3 ∨ m = 9) :
    fBalSel1 s r m = fBal1 s r m := by
  rcases hm with rfl | rfl | rfl <;> rfl

lemma fBalSel2_eq (s : ℕ) (r : Fin 2) (m : ℕ) (hm : m = 1 ∨ m = 3 ∨ m = 9) :
    fBalSel2 s r m = fBal2 s r m := by
  rcases hm with rfl | rfl | rfl <;> rfl

lemma sat_fBal1 {a b : ℕ} (s : ℕ) (r : Fin 2) (m : ℕ)
    (e : ℕ → Signal (Fin a) (Fin b) × (OutFin s × OutFin s)) :
    (fBal1 s r m).Sat (valExec e) ↔
      pPlanSum r (decodePay (e 0).2.1.val) + (pCarry r (decodePay (e 0).2.1.val)).val =
        m * (pW r (decodePay (e 0).2.1.val)).val + (pCarry r (decodePay (e 0).2.2.val)).val := by
  unfold fBal1
  rw [sat_bigOr]
  simp only [List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨_, ⟨c2, rfl⟩, h1, h2⟩
    rw [sat_atomPay1, decide_eq_true_eq] at h1
    rw [sat_atomPay2, beq_iff_eq] at h2
    rwa [← h2] at h1
  · intro heq
    refine ⟨_, ⟨pCarry r (decodePay (e 0).2.2.val), rfl⟩, ?_, ?_⟩
    · rw [sat_atomPay1, decide_eq_true_eq]; exact heq
    · rw [sat_atomPay2, beq_iff_eq]

lemma sat_fBal2 {a b : ℕ} (s : ℕ) (r : Fin 2) (m : ℕ)
    (e : ℕ → Signal (Fin a) (Fin b) × (OutFin s × OutFin s)) :
    (fBal2 s r m).Sat (valExec e) ↔
      pPlanSum r (decodePay (e 0).2.2.val) + (pCarry r (decodePay (e 0).2.2.val)).val =
        m * (pW r (decodePay (e 0).2.2.val)).val + (pCarry r (decodePay (e 0).2.1.val)).val := by
  unfold fBal2
  rw [sat_bigOr]
  simp only [List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨_, ⟨c1, rfl⟩, h1, h2⟩
    rw [sat_atomPay2, decide_eq_true_eq] at h1
    rw [sat_atomPay1, beq_iff_eq] at h2
    rwa [← h2] at h1
  · intro heq
    refine ⟨_, ⟨pCarry r (decodePay (e 0).2.1.val), rfl⟩, ?_, ?_⟩
    · rw [sat_atomPay2, decide_eq_true_eq]; exact heq
    · rw [sat_atomPay1, beq_iff_eq]

end Parametric

lemma cm2_step_props (c : CMCode) (cfg : Config (Fin (c.1 + 1)) 2) :
    let M := c.toMachine 2 (by norm_num)
    let q := cfg.state.val
    let z0 := decide (cfg.counters 0 = 0)
    let z1 := decide (cfg.counters 1 = 0)
    let cfg' := M.step cfg
    cfg'.state.val = codeNextQ c q z0 z1 ∧
      ∀ r : Fin 2,
        let m := codeMult c r q z0 z1
        0 < m ∧ m ≤ 9 ∧
        ((m = 1 ∧ cfg'.counters r = cfg.counters r + 1) ∨
          (m = 3 ∧ cfg'.counters r = cfg.counters r) ∨
          (m = 9 ∧ 0 < cfg.counters r ∧ cfg'.counters r = cfg.counters r - 1)) := by
  unfold CounterMachine.step CMCode.toMachine codeNextQ codeMult codeEntry
  dsimp only
  rw [← List.getD_eq_getElem?_getD]
  rcases hent : c.2.2.2.getD cfg.state.val (false, 0, 0, 0) with ⟨isDec, idx, a, b⟩
  cases isDec
  · -- inc
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨trivial, fun r => ?_⟩
    fin_cases r
    · by_cases hi : idx % 2 = 0
      · simp [hi, Function.update_self]
      · simp [hi]
    · by_cases hi : idx % 2 = 1
      · simp [hi, Function.update_self]
      · simp [hi]
  · -- dec
    simp only [↓reduceIte]
    rcases (show idx % 2 = 0 ∨ idx % 2 = 1 by omega) with hi | hi
    · have hfin : (⟨idx % 2, Nat.mod_lt idx (by norm_num)⟩ : Fin 2) = 0 := Fin.ext hi
      rw [hfin]
      by_cases hc0 : cfg.counters 0 = 0
      · simp only [hi, hc0, decide_true, ↓reduceIte]
        refine ⟨trivial, fun r => ?_⟩
        fin_cases r <;> simp
      · have hpos : 0 < cfg.counters 0 := Nat.pos_of_ne_zero hc0
        simp only [hi, hc0, decide_false, Bool.false_eq_true, ↓reduceIte]
        refine ⟨trivial, fun r => ?_⟩
        fin_cases r
        · simp [hpos, Function.update_self]
        · simp
    · have hfin : (⟨idx % 2, Nat.mod_lt idx (by norm_num)⟩ : Fin 2) = 1 := Fin.ext hi
      rw [hfin]
      have hi0 : ¬ (idx % 2 = 0) := by omega
      by_cases hc1 : cfg.counters 1 = 0
      · simp only [hi0, hc1, decide_true, ↓reduceIte]
        refine ⟨trivial, fun r => ?_⟩
        fin_cases r <;> simp [hi]
      · have hpos : 0 < cfg.counters 1 := Nat.pos_of_ne_zero hc1
        simp only [hi0, hc1, decide_false, Bool.false_eq_true, ↓reduceIte]
        refine ⟨trivial, fun r => ?_⟩
        fin_cases r
        · simp [hi0]
        · simp [hi, hpos, Function.update_self]

lemma cm2_counter_le_step (c : CMCode) (n : ℕ) (r : Fin 2) :
    ((c.toMachine 2 (by norm_num)).run n).counters r ≤ n := by
  induction n with
  | zero => simp [CounterMachine.run]
  | succ n ih =>
    have hs := ((cm2_step_props c ((c.toMachine 2 (by norm_num)).run n)).2 r).2.2
    change ((c.toMachine 2 (by norm_num)).step ((c.toMachine 2 (by norm_num)).run n)).counters r ≤ n + 1
    rcases hs with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;> omega

/-! ### Part 8: Completeness & Soundness for `red c` -/

section Parametric
variable [PayCode]

def nodePay2 (c : CMCode) (t i : ℕ) : Fin (c.1 + 1) × Payload :=
  let M := c.toMachine 2 (by norm_num)
  let cfg := M.run t
  let cfg' := M.run (t + 1)
  let q := cfg.state
  let c0 := cfg.counters 0
  let c1 := cfg.counters 1
  let c0' := cfg'.counters 0
  let c1' := cfg'.counters 1
  let z0 := decide (c0 = 0)
  let z1 := decide (c1 = 0)
  let m0 := codeMult c 0 q.val z0 z1
  let m1 := codeMult c 1 q.val z0 z1
  have hm0 := (cm2_step_props c cfg).2 0
  have hm1 := (cm2_step_props c cfg).2 1
  let f0 : CtrField := (z0, (wFin c0 i, wFin c0' (3 * i), wFin c0' (3 * i + 1), wFin c0' (3 * i + 2)),
    carryFin c0 m0 i hm0.1 hm0.2.1)
  let f1 : CtrField := (z1, (wFin c1 i, wFin c1' (3 * i), wFin c1' (3 * i + 1), wFin c1' (3 * i + 2)),
    carryFin c1 m1 i hm1.1 hm1.2.1)
  (q, (f0, f1, Ctr.mod3 i))

def nodeOut2 (c : CMCode) (t i : ℕ) : OutFin c.1 :=
  encodeOut c.1 (nodePay2 c t i).1 (nodePay2 c t i).2

def completeAlg2 (c : CMCode) : Algorithm (Fin 1) (Fin 1) (OutFin c.1) (OutFin c.1) where
  f1 v := nodeOut2 c (vdepth0 v - 1) (vcoord0 v)
  f2 v := nodeOut2 c (vdepth0 v - 1) (vcoord0 v)

lemma completeness2_aux (c : CMCode) (hnh : ¬ (c.toMachine 2 (by norm_num)).Halts)
    (sig : ℕ → Sig0) :
    (instFormula c).Sat (valExec (exec (completeAlg2 c) sig)) := by
  let M := c.toMachine 2 (by norm_num)
  let e := exec (completeAlg2 c) sig
  change (instFormula c).Sat (valExec e)
  have hviews : ∀ n,
      (e n).2.1 = nodeOut2 c n (vcoord0 (view1 (toSig0 (pre (graphOf sig) (n + 1))))) ∧
      (e n).2.2 = nodeOut2 c n (vcoord0 (view2 (toSig0 (pre (graphOf sig) (n + 1))))) := by
    intro n
    have hp := pre_sig0_toSig0 sig (n + 1)
    have hvc := vdepth_coord_views0 (pre (graphOf sig) (n + 1))
    have hlen : (pre (graphOf sig) (n + 1)).length = n + 1 := by simp [pre]
    dsimp only [e, exec, completeAlg2]
    rw [hp, hvc.1, hvc.2.1, hlen, Nat.add_sub_cancel]
    exact ⟨rfl, rfl⟩
  have hq_node : ∀ n i, decodeQ (nodeOut2 c n i).val = ((M.run n).state).val :=
    fun n i => decodeQ_encodeOut c.1 _ _
  have hp_node : ∀ n i, decodePay (nodeOut2 c n i).val = (nodePay2 c n i).2 :=
    fun n i => decodePay_encodeOut c.1 _ _
  have hpos : (fPosOrd c.1).Sat (valExec e) := by
    rw [sat_fPosOrd]
    have hopos : ∀ n, (pPos (decodePay (e n).2.1.val), pPos (decodePay (e n).2.2.val)) =
        (Ctr.mod3 (vcoord0 (view1 (pre sig (n + 1)))), Ctr.mod3 (vcoord0 (view2 (pre sig (n + 1))))) := by
      intro n
      rw [(hviews n).1, (hviews n).2, hp_node, hp_node, pre_sig0_toSig0]
      rfl
    refine ⟨?_, fun n => ?_⟩
    · rw [hopos 0, vcoord0_mod3_pre sig 0]; rfl
    · rw [hopos (n + 1), vcoord0_mod3_pre sig (n + 1)]
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      have h1 : Ctr.mod3 (vcoord0 (view1 (pre sig (n + 1)))) = pPos (decodePay (e n).2.1.val) :=
        (congrArg Prod.fst (hopos n)).symm
      have h2 : Ctr.mod3 (vcoord0 (view2 (pre sig (n + 1)))) = pPos (decodePay (e n).2.2.val) :=
        (congrArg Prod.snd (hopos n)).symm
      rw [h1, h2]
      rfl
  have hoil : ∀ n, (fOneIsLeft c.1).Sat (shift (valExec e) n) ↔
      jIdx (pre (graphOf sig) (n + 1)) % 2 = 0 :=
    fOneIsLeft_iff_even c.1 (completeAlg2 c) sig hpos
  have hLR1 : ∀ n,
      (if jIdx (pre (graphOf sig) (n + 1)) % 2 = 0 then (e n).2.1 else (e n).2.2) =
        nodeOut2 c n (jIdx (pre (graphOf sig) (n + 1))) := by
    intro n
    have hvc := vdepth_coord_views0 (pre (graphOf sig) (n + 1))
    by_cases hp : jIdx (pre (graphOf sig) (n + 1)) % 2 = 0
    · simp only [hp, ↓reduceIte] at hvc ⊢
      rw [(hviews n).1, hvc.2.2.1]
    · simp only [hp, ↓reduceIte] at hvc ⊢
      rw [(hviews n).2, hvc.2.2.1]
  have hLR2 : ∀ n,
      (if jIdx (pre (graphOf sig) (n + 1)) % 2 = 0 then (e n).2.2 else (e n).2.1) =
        nodeOut2 c n (jIdx (pre (graphOf sig) (n + 1)) + 1) := by
    intro n
    have hvc := vdepth_coord_views0 (pre (graphOf sig) (n + 1))
    by_cases hp : jIdx (pre (graphOf sig) (n + 1)) % 2 = 0
    · simp only [hp, ↓reduceIte] at hvc ⊢
      rw [(hviews n).2, hvc.2.2.2]
    · simp only [hp, ↓reduceIte] at hvc ⊢
      rw [(hviews n).1, hvc.2.2.2]
  unfold instFormula
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- PathAgr
    unfold fPathAgr
    intro n
    rw [shift_valExec]
    have hsh : shift e n 0 = e n := by simp [shift]
    refine ⟨?_, ?_, ?_⟩
    · rw [sat_bigOr]
      simp only [List.mem_map, List.mem_range]
      refine ⟨_, ⟨(M.run n).state.val, (M.run n).state.isLt, rfl⟩, ?_, ?_⟩
      · rw [sat_atomQ1, hsh, (hviews n).1, hq_node]
      · rw [sat_atomQ2, hsh, (hviews n).2, hq_node]
    · rw [sat_bigOr]
      simp only [List.mem_map]
      refine ⟨_, ⟨pZero 0 (nodePay2 c n 0).2, mem_bools _, rfl⟩, ?_, ?_⟩
      · rw [sat_atomPay1, beq_iff_eq, hsh, (hviews n).1, hp_node]; rfl
      · rw [sat_atomPay2, beq_iff_eq, hsh, (hviews n).2, hp_node]; rfl
    · rw [sat_bigOr]
      simp only [List.mem_map]
      refine ⟨_, ⟨pZero 1 (nodePay2 c n 0).2, mem_bools _, rfl⟩, ?_, ?_⟩
      · rw [sat_atomPay1, beq_iff_eq, hsh, (hviews n).1, hp_node]; rfl
      · rw [sat_atomPay2, beq_iff_eq, hsh, (hviews n).2, hp_node]; rfl
  · -- LocalSum
    unfold fLocalSum
    intro n
    rw [shift_valExec, sat_bigAnd]; simp only [List.mem_map]; rintro _ ⟨q, _, rfl⟩
    rw [sat_bigAnd]; simp only [List.mem_map]; rintro _ ⟨z0, _, rfl⟩
    rw [sat_bigAnd]; simp only [List.mem_map]; rintro _ ⟨z1, _, rfl⟩
    have hsh : shift e n 0 = e n := by simp [shift]
    let j := jIdx (pre (graphOf sig) (n + 1))
    have hl1 : (if j % 2 = 0 then (e n).2.1 else (e n).2.2) = nodeOut2 c n j := hLR1 n
    have hl2 : (if j % 2 = 0 then (e n).2.2 else (e n).2.1) = nodeOut2 c n (j + 1) := hLR2 n
    refine ⟨?_, ?_⟩
    · intro hl
      have hj : j % 2 = 0 := (hoil n).mp (by rwa [shift_valExec])
      unfold fPsi1
      simp only [Formula.Sat, sat_atomQ1, sat_atomPay1, beq_iff_eq, hsh]
      rintro ⟨hq, hz0, hz1⟩
      have he1 : (e n).2.1 = nodeOut2 c n j := by simpa [hj] using hl1
      have he2 : (e n).2.2 = nodeOut2 c n (j + 1) := by simpa [hj] using hl2
      rw [he1, hq_node] at hq
      rw [he1, hp_node] at hz0 hz1
      subst hq hz0 hz1
      rw [fBalSel1_eq _ _ _ (codeMult_mem _ _ _ _ _), fBalSel1_eq _ _ _ (codeMult_mem _ _ _ _ _),
        sat_fBal1, sat_fBal1, hsh, he1, he2, hp_node, hp_node]
      have hsp0 := ((cm2_step_props c (M.run n)).2 0).2.2
      have hsp1 := ((cm2_step_props c (M.run n)).2 1).2.2
      refine ⟨?_, ?_⟩
      · simpa [nodePay2, pPlanSum, pA, pW, pCarry, pZero, pField, wFin, carryFin,
          CounterMachine.run] using
          wBit_conservation ((M.run n).counters 0) ((M.run (n + 1)).counters 0) _ j hsp0
      · simpa [nodePay2, pPlanSum, pA, pW, pCarry, pZero, pField, wFin, carryFin,
          CounterMachine.run] using
          wBit_conservation ((M.run n).counters 1) ((M.run (n + 1)).counters 1) _ j hsp1
    · intro hnl
      have hj : ¬ (j % 2 = 0) := fun h => hnl (by rw [← shift_valExec]; exact (hoil n).mpr h)
      unfold fPsi2
      simp only [Formula.Sat, sat_atomQ2, sat_atomPay2, beq_iff_eq, hsh]
      rintro ⟨hq, hz0, hz1⟩
      have he2 : (e n).2.2 = nodeOut2 c n j := by simpa [hj] using hl1
      have he1 : (e n).2.1 = nodeOut2 c n (j + 1) := by simpa [hj] using hl2
      rw [he2, hq_node] at hq
      rw [he2, hp_node] at hz0 hz1
      subst hq hz0 hz1
      rw [fBalSel2_eq _ _ _ (codeMult_mem _ _ _ _ _), fBalSel2_eq _ _ _ (codeMult_mem _ _ _ _ _),
        sat_fBal2, sat_fBal2, hsh, he1, he2, hp_node, hp_node]
      have hsp0 := ((cm2_step_props c (M.run n)).2 0).2.2
      have hsp1 := ((cm2_step_props c (M.run n)).2 1).2.2
      refine ⟨?_, ?_⟩
      · simpa [nodePay2, pPlanSum, pA, pW, pCarry, pZero, pField, wFin, carryFin,
          CounterMachine.run] using
          wBit_conservation ((M.run n).counters 0) ((M.run (n + 1)).counters 0) _ j hsp0
      · simpa [nodePay2, pPlanSum, pA, pW, pCarry, pZero, pField, wFin, carryFin,
          CounterMachine.run] using
          wBit_conservation ((M.run n).counters 1) ((M.run (n + 1)).counters 1) _ j hsp1
  · -- ZeroCheck
    have hzi : ∀ r : Fin 2, (fZeroIndR c.1 r).Sat (valExec e) := by
      intro r n
      rw [shift_valExec]
      have hsh : shift e n 0 = e n := by simp [shift]
      let j := jIdx (pre (graphOf sig) (n + 1))
      have hl1 : (if j % 2 = 0 then (e n).2.1 else (e n).2.2) = nodeOut2 c n j := hLR1 n
      by_cases hj : j % 2 = 0
      · refine Or.inl ⟨by rw [← shift_valExec]; exact (hoil n).mpr hj, ?_⟩
        simp only [Formula.Sat, sat_atomPay1, beq_iff_eq, hsh]
        have he1 : (e n).2.1 = nodeOut2 c n j := by simpa [hj] using hl1
        rw [he1, hp_node]
        intro hz
        fin_cases r <;>
        · have hc0 := of_decide_eq_true hz
          apply Fin.ext
          simp [nodePay2, pW, pField, wFin, hc0, wBit_zero]
      · refine Or.inr ⟨fun h => hj ((hoil n).mp (by rwa [shift_valExec])), ?_⟩
        simp only [Formula.Sat, sat_atomPay2, beq_iff_eq, hsh]
        have he2 : (e n).2.2 = nodeOut2 c n j := by simpa [hj] using hl1
        rw [he2, hp_node]
        intro hz
        fin_cases r <;>
        · have hc0 := of_decide_eq_true hz
          apply Fin.ext
          simp [nodePay2, pW, pField, wFin, hc0, wBit_zero]
    have hlm : ∀ r : Fin 2, (fLeftMostR c.1 r).Sat (valExec e) := by
      intro r
      unfold fLeftMostR
      rw [sat_weakUntil_not_graph]
      intro n hstay
      rw [shift_valExec]
      have hpre : pre (graphOf sig) (n + 1) = histOf (n + 1) 0 := by
        rw [histOf_zero]
        exact pre_eq_replicate (graphOf sig) .oneToTwo (n + 1)
          (fun k hk => by simpa [graphOf, valExec, e, exec] using hstay k (by omega))
      have hj0 : jIdx (pre (graphOf sig) (n + 1)) = 0 := by
        rw [hpre, jIdx_histOf (n + 1) 0 (pow_pos (by decide) _)]
      have he1 : (e n).2.1 = nodeOut2 c n 0 := by
        have h := hLR1 n
        simpa [hj0] using h
      have hsh : shift e n 0 = e n := by simp [shift]
      simp only [Formula.Sat, sat_atomPay1, beq_iff_eq, hsh, he1, hp_node]
      fin_cases r <;>
      · refine ⟨?_, fun hz => ?_⟩
        · apply Fin.ext; simp [nodePay2, pCarry, pField, carryFin, carryVal_at_zero]
        · have hc_ne := of_decide_eq_false hz
          apply Fin.ext
          simp [nodePay2, pW, pField, wFin, wBit_pos_at_zero _ (Nat.pos_of_ne_zero hc_ne)]
    have hrm : ∀ r : Fin 2, (fRightMostR c.1 r).Sat (valExec e) := by
      intro r
      unfold fRightMostR
      rw [sat_weakUntil_not_graph]
      intro n hstay
      rw [shift_valExec]
      have hpre : pre (graphOf sig) (n + 1) = histOf (n + 1) (3 ^ (n + 1) - 1) := by
        rw [histOf_last]
        exact pre_eq_replicate (graphOf sig) .twoToOne (n + 1)
          (fun k hk => by simpa [graphOf, valExec, e, exec] using hstay k (by omega))
      have hp : 1 ≤ 3 ^ (n + 1) := Nat.one_le_pow (n + 1) 3 (by decide)
      have hj : jIdx (pre (graphOf sig) (n + 1)) = 3 ^ (n + 1) - 1 := by
        rw [hpre, jIdx_histOf (n + 1) (3 ^ (n + 1) - 1) (by omega)]
      have hev := three_pow_sub_one_even (n + 1)
      have he2 : (e n).2.2 = nodeOut2 c n (3 ^ (n + 1)) := by
        have h := hLR2 n
        rw [hj] at h
        simpa [hev, Nat.sub_add_cancel hp] using h
      have hsh : shift e n 0 = e n := by simp [shift]
      simp only [sat_atomPay2, beq_iff_eq, hsh, he2, hp_node]
      have hle : ((c.toMachine 2 (by norm_num)).run n).counters r ≤ n + 1 :=
        (cm2_counter_le_step c n r).trans (Nat.le_succ n)
      have hpow : 3 ^ (n + 1) =
          3 ^ (((c.toMachine 2 (by norm_num)).run n).counters r) *
            3 ^ (n + 1 - ((c.toMachine 2 (by norm_num)).run n).counters r) := by
        rw [← pow_add, Nat.add_sub_of_le hle]
      fin_cases r <;>
      · apply Fin.ext
        simp only [nodePay2, pCarry, pField, carryFin, Fin.val_zero]
        rw [hpow]
        exact carryVal_mul_pow _ _ _
    exact ⟨⟨hzi 0, hzi 1⟩, ⟨hlm 0, hlm 1⟩, ⟨hrm 0, hrm 1⟩⟩
  · -- InitCheck
    unfold fInitCheck
    simp only [Formula.Sat, sat_atomQ1, sat_atomPay1, beq_iff_eq, (hviews 0).1, hq_node, hp_node]
    exact ⟨rfl, rfl, rfl⟩
  · -- PropTrans
    unfold fPropTrans
    intro n
    rw [shift_valExec]
    have hsh0 : shift e n 0 = e n := by simp [shift]
    have hsh1 : shift (shift e n) 1 0 = e (n + 1) := by simp [shift, Nat.add_comm]
    have hst : (fStateTrans c).Sat (valExec (shift e n)) := by
      unfold fStateTrans
      rw [sat_bigAnd]; simp only [List.mem_map]; rintro _ ⟨q, _, rfl⟩
      rw [sat_bigAnd]; simp only [List.mem_map]; rintro _ ⟨z0, _, rfl⟩
      rw [sat_bigAnd]; simp only [List.mem_map]; rintro _ ⟨z1, _, rfl⟩
      simp only [Formula.Sat, shift_valExec, sat_atomQ1, sat_atomPay1, beq_iff_eq, hsh0, hsh1,
        (hviews n).1, (hviews (n + 1)).1, hq_node, hp_node]
      rintro ⟨hq, hz0, hz1⟩
      subst hq hz0 hz1
      exact (cm2_step_props c (M.run n)).1
    have hwt : ∀ r : Fin 2, (fWeightTransR c.1 r).Sat (valExec (shift e n)) := by
      intro r
      unfold fWeightTransR
      rw [sat_bigAnd]; simp only [List.mem_map]; rintro _ ⟨k, _, rfl⟩
      rw [sat_bigAnd]; simp only [List.mem_map]; rintro _ ⟨b, _, rfl⟩
      rw [sat_bigAnd]; simp only [List.mem_map]; rintro _ ⟨g, _, rfl⟩
      simp only [Formula.Sat, shift_valExec]
      rintro ⟨hg, hdk, hplan⟩
      change (e (1 + n)).1.2.2 = g at hg
      rw [Nat.add_comm 1 n] at hg
      have hgs : graphOf sig (n + 1) = g := hg
      have hpre_succ : pre (graphOf sig) (n + 2) = pre (graphOf sig) (n + 1) ++ [g] := by
        rw [show n + 2 = (n + 1) + 1 from rfl, pre_snoc, hgs]
      let j := jIdx (pre (graphOf sig) (n + 1))
      let j' := jIdx (pre (graphOf sig) (n + 2))
      have hl1 : (if j % 2 = 0 then (e n).2.1 else (e n).2.2) = nodeOut2 c n j := hLR1 n
      have hl1' : (if j' % 2 = 0 then (e (n + 1)).2.1 else (e (n + 1)).2.2) =
          nodeOut2 c (n + 1) j' := hLR1 (n + 1)
      have hk_eq : Ctr.dVal (decide (j % 2 = 0)) g = k.val := by
        unfold fDK at hdk
        rcases hdk with ⟨hl, hc⟩ | ⟨hnl, hc⟩
        · have hj : j % 2 = 0 := (hoil n).mp (by rwa [shift_valExec])
          simp only [hj, decide_true]
          by_cases hd : Ctr.dVal true g = k.val
          · exact hd
          · simp only [hd, ↓reduceIte] at hc; exact False.elim (sat_ff _ hc)
        · have hj : ¬ (j % 2 = 0) := fun h => hnl (by rw [← shift_valExec]; exact (hoil n).mpr h)
          simp only [hj, decide_false]
          by_cases hd : Ctr.dVal false g = k.val
          · exact hd
          · simp only [hd, ↓reduceIte] at hc; exact False.elim (sat_ff _ hc)
      have hj'_eq : j' = 3 * j + k.val := by
        rw [← hk_eq]
        dsimp only [j', j]
        rw [hpre_succ, jIdx_append_singleton]
        by_cases hj : jIdx (pre (graphOf sig) (n + 1)) % 2 = 0 <;> simp [Ctr.dVal, hj]
      have hb_eq : pA r k (nodePay2 c n j).2 = b := by
        unfold fPlanL at hplan
        rcases hplan with ⟨hl, ha⟩ | ⟨hnl, ha⟩
        · have hj : j % 2 = 0 := (hoil n).mp (by rwa [shift_valExec])
          rw [sat_atomPay1, beq_iff_eq, hsh0] at ha
          have he1 : (e n).2.1 = nodeOut2 c n j := by simpa [hj] using hl1
          rwa [he1, hp_node] at ha
        · have hj : ¬ (j % 2 = 0) := fun h => hnl (by rw [← shift_valExec]; exact (hoil n).mpr h)
          rw [sat_atomPay2, beq_iff_eq, hsh0] at ha
          have he2 : (e n).2.2 = nodeOut2 c n j := by simpa [hj] using hl1
          rwa [he2, hp_node] at ha
      have how_eq : pW r (nodePay2 c (n + 1) j').2 = b := by
        rw [← hb_eq, hj'_eq]
        fin_cases r <;> fin_cases k <;> rfl
      have hsh_next : shift (shift e n) 1 = shift e (n + 1) := by rw [shift_shift, Nat.add_comm]
      rw [hsh_next]
      unfold fPlanL
      by_cases hj' : j' % 2 = 0
      · refine Or.inl ⟨by rw [← shift_valExec]; exact (hoil (n + 1)).mpr hj', ?_⟩
        rw [sat_atomPay1, beq_iff_eq]
        have he1' : (shift e (n + 1) 0).2.1 = nodeOut2 c (n + 1) j' := by
          simp only [shift, zero_add]
          simpa [hj'] using hl1'
        rwa [he1', hp_node]
      · refine Or.inr ⟨fun h => hj' ((hoil (n + 1)).mp (by rwa [shift_valExec])), ?_⟩
        rw [sat_atomPay2, beq_iff_eq]
        have he2' : (shift e (n + 1) 0).2.2 = nodeOut2 c (n + 1) j' := by
          simp only [shift, zero_add]
          simpa [hj'] using hl1'
        rwa [he2', hp_node]
    exact ⟨hst, hwt 0, hwt 1⟩
  · -- NoHalt
    unfold fNoHalt
    intro n
    rw [shift_valExec, sat_bigAnd]; simp only [List.mem_map]
    rintro _ ⟨q, hqF, rfl⟩ hsat
    rw [sat_atomQ1] at hsat
    have hsh0 : shift e n 0 = e n := by simp [shift]
    rw [hsh0, (hviews n).1, hq_node] at hsat
    exact hnh ⟨n, by change ((M.run n).state).val ∈ c.2.2.1; rwa [hsat]⟩

lemma completeness2 (c : CMCode) (hnh : ¬ (c.toMachine 2 (by norm_num)).Halts) :
    (red c).Realizable Set.univ :=
  (mk_realizable_iff (outM c.1) (outM c.1) (instFormula c)).mpr
    ⟨completeAlg2 c, completeness2_aux c hnh⟩

def simCnt2 (c : CMCode) (r : Fin 2) (rowQ : ℕ → ℕ) (rowZ : Fin 2 → ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      let m := codeMult c r (rowQ n) (rowZ 0 n) (rowZ 1 n)
      if m = 1 then simCnt2 c r rowQ rowZ n + 1
      else if m = 3 then simCnt2 c r rowQ rowZ n
      else simCnt2 c r rowQ rowZ n - 1

lemma soundness2_aux (c : CMCode)
    (f : Algorithm (Fin 1) (Fin 1) (OutFin c.1) (OutFin c.1))
    (hsat_all : ∀ sig : ℕ → Sig0, (instFormula c).Sat (valExec (exec f sig))) :
    ¬ (c.toMachine 2 (by norm_num)).Halts := by
  let M := c.toMachine 2 (by norm_num)
  let hAt (n j : ℕ) : List CommGraph := histOf (n + 1) j
  let y1At (n j : ℕ) := f.f1 (view1 (toSig0 (hAt n j)))
  let y2At (n j : ℕ) := f.f2 (view2 (toSig0 (hAt n j)))
  let yL (n j : ℕ) := if j % 2 = 0 then y1At n j else y2At n j
  let yR (n j : ℕ) := if j % 2 = 0 then y2At n j else y1At n j
  have hlink : ∀ n j, j + 1 < 3 ^ (n + 1) → yR n j = yL n (j + 1) := by
    intro n j hj
    have hsv := histOf_shared_view0 (n + 1) j hj
    rcases (show j % 2 = 0 ∨ j % 2 = 1 by omega) with hp | hp
    · have hp1 : ¬ ((j + 1) % 2 = 0) := by omega
      simp only [yR, yL, y1At, y2At, hAt, hp, hp1, ↓reduceIte] at hsv ⊢
      exact congrArg f.f2 hsv
    · have hp0 : ¬ (j % 2 = 0) := by omega
      have hp1 : (j + 1) % 2 = 0 := by omega
      simp only [yR, yL, y1At, y2At, hAt, hp0, hp1, ↓reduceIte] at hsv ⊢
      exact congrArg f.f1 hsv
  have hexec_at : ∀ (h : List CommGraph) (n : ℕ), h.length = n + 1 →
      (exec f (extendSig0 h) n).2 = (f.f1 (view1 (toSig0 h)), f.f2 (view2 (toSig0 h))) := by
    intro h n hlen
    have hp := pre_extendSig0 h (n + 1) (by omega)
    have ht : h.take (n + 1) = h := List.take_of_length_le (by omega)
    rw [ht] at hp
    simp only [exec, hp]
  have hpre_hAt : ∀ n j, pre (graphOf (extendSig0 (hAt n j))) (n + 1) = hAt n j := by
    intro n j
    rw [pre_graph_extendSig0 (hAt n j) (n + 1) (by simp [hAt])]
    simp [hAt]
  have hoil_ext : ∀ (sig : ℕ → Sig0) (n : ℕ),
      (fOneIsLeft c.1).Sat (shift (valExec (exec f sig)) n) ↔
        jIdx (pre (graphOf sig) (n + 1)) % 2 = 0 :=
    fun sig n => fOneIsLeft_iff_even c.1 f sig (hsat_all sig).1 n
  let rowQ (n : ℕ) : ℕ := decodeQ (y1At n 0).val
  let rowZ (r : Fin 2) (n : ℕ) : Bool := pZero r (decodePay (y1At n 0).val)
  have hpair_agr : ∀ n j, j < 3 ^ (n + 1) →
      decodeQ (y1At n j).val = decodeQ (y2At n j).val ∧
      pZero 0 (decodePay (y1At n j).val) = pZero 0 (decodePay (y2At n j).val) ∧
      pZero 1 (decodePay (y1At n j).val) = pZero 1 (decodePay (y2At n j).val) := by
    intro n j _
    let sig := extendSig0 (hAt n j)
    have hpa := (hsat_all sig).2.1 n
    rw [shift_valExec] at hpa
    have hsh : shift (exec f sig) n 0 = exec f sig n := by simp [shift]
    have hex := hexec_at (hAt n j) n (histOf_length (n + 1) j)
    have hex1 : (exec f sig n).2.1 = y1At n j := congrArg Prod.fst hex
    have hex2 : (exec f sig n).2.2 = y2At n j := congrArg Prod.snd hex
    rcases hpa with ⟨hq, hz0, hz1⟩
    rw [sat_bigOr] at hq hz0 hz1
    refine ⟨?_, ?_, ?_⟩
    · rcases hq with ⟨_, hmem, hsub⟩
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hmem
      rcases hsub with ⟨h1, h2⟩
      rw [sat_atomQ1, hsh, hex1] at h1
      rw [sat_atomQ2, hsh, hex2] at h2
      exact h1.trans h2.symm
    · rcases hz0 with ⟨_, hmem, hsub⟩
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hmem
      rcases hsub with ⟨h1, h2⟩
      rw [sat_atomPay1, beq_iff_eq, hsh, hex1] at h1
      rw [sat_atomPay2, beq_iff_eq, hsh, hex2] at h2
      exact h1.trans h2.symm
    · rcases hz1 with ⟨_, hmem, hsub⟩
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hmem
      rcases hsub with ⟨h1, h2⟩
      rw [sat_atomPay1, beq_iff_eq, hsh, hex1] at h1
      rw [sat_atomPay2, beq_iff_eq, hsh, hex2] at h2
      exact h1.trans h2.symm
  have huniform : ∀ n j, j < 3 ^ (n + 1) →
      decodeQ (yL n j).val = rowQ n ∧ decodeQ (yR n j).val = rowQ n ∧
      ∀ r : Fin 2, pZero r (decodePay (yL n j).val) = rowZ r n ∧
        pZero r (decodePay (yR n j).val) = rowZ r n := by
    intro n j hj
    induction j with
    | zero =>
      obtain ⟨hq, hz0, hz1⟩ := hpair_agr n 0 hj
      refine ⟨rfl, hq.symm, fun r => ?_⟩
      fin_cases r
      · exact ⟨rfl, hz0.symm⟩
      · exact ⟨rfl, hz1.symm⟩
    | succ j ih =>
      obtain ⟨_, hqR, hzR⟩ := ih (by omega)
      have hl := hlink n j hj
      obtain ⟨hpq, hpz0, hpz1⟩ := hpair_agr n (j + 1) hj
      have hqL : decodeQ (yL n (j + 1)).val = rowQ n := by rw [← hl]; exact hqR
      have hqR' : decodeQ (yR n (j + 1)).val = rowQ n := by
        by_cases hev : (j + 1) % 2 = 0 <;> simp only [yL, yR, hev, ↓reduceIte] at hqL ⊢
        · exact hpq.symm.trans hqL
        · exact hpq.trans hqL
      refine ⟨hqL, hqR', fun r => ?_⟩
      have hzL : pZero r (decodePay (yL n (j + 1)).val) = rowZ r n := by
        rw [← hl]; exact (hzR r).2
      refine ⟨hzL, ?_⟩
      fin_cases r
      · by_cases hev : (j + 1) % 2 = 0 <;> simp only [yL, yR, hev, ↓reduceIte] at hzL ⊢
        · exact hpz0.symm.trans hzL
        · exact hpz0.trans hzL
      · by_cases hev : (j + 1) % 2 = 0 <;> simp only [yL, yR, hev, ↓reduceIte] at hzL ⊢
        · exact hpz1.symm.trans hzL
        · exact hpz1.trans hzL
  have hrowQ_lt : ∀ n, rowQ n < c.1 + 1 := fun n => decodeQ_lt c.1 (y1At n 0)
  have hbal_edge : ∀ (r : Fin 2) n j, j < 3 ^ (n + 1) →
      pPlanSum r (decodePay (yL n j).val) + (pCarry r (decodePay (yL n j).val)).val =
        codeMult c r (rowQ n) (rowZ 0 n) (rowZ 1 n) * (pW r (decodePay (yL n j).val)).val +
          (pCarry r (decodePay (yR n j).val)).val := by
    intro r n j hj
    let sig := extendSig0 (hAt n j)
    have hls := (hsat_all sig).2.2.1 n
    rw [shift_valExec, sat_bigAnd] at hls
    have h1 := hls _ (List.mem_map.mpr ⟨rowQ n, List.mem_range.mpr (hrowQ_lt n), rfl⟩)
    rw [sat_bigAnd] at h1
    have h2 := h1 _ (List.mem_map.mpr ⟨rowZ 0 n, mem_bools _, rfl⟩)
    rw [sat_bigAnd] at h2
    have hinst := h2 _ (List.mem_map.mpr ⟨rowZ 1 n, mem_bools _, rfl⟩)
    have hj_eq : jIdx (pre (graphOf sig) (n + 1)) = j := by
      change jIdx (pre (graphOf (extendSig0 (hAt n j))) (n + 1)) = j
      rw [hpre_hAt n j, jIdx_histOf (n + 1) j hj]
    have hoil := hoil_ext sig n
    rw [hj_eq] at hoil
    have hsh : shift (exec f sig) n 0 = exec f sig n := by simp [shift]
    have hex := hexec_at (hAt n j) n (histOf_length (n + 1) j)
    have hex1 : (exec f sig n).2.1 = y1At n j := congrArg Prod.fst hex
    have hex2 : (exec f sig n).2.2 = y2At n j := congrArg Prod.snd hex
    obtain ⟨hqL, _, hzLR⟩ := huniform n j hj
    have hzL0 := (hzLR 0).1
    have hzL1 := (hzLR 1).1
    by_cases hev : j % 2 = 0
    · have hp1 := hinst.1 (by rw [← shift_valExec]; exact hoil.mpr hev)
      unfold fPsi1 at hp1
      simp only [Formula.Sat, sat_atomQ1, sat_atomPay1, beq_iff_eq, hsh, hex1] at hp1
      simp only [yL, yR, hev, ↓reduceIte] at hqL hzL0 hzL1 ⊢
      have hboth := hp1 ⟨hqL, hzL0, hzL1⟩
      rw [fBalSel1_eq _ _ _ (codeMult_mem _ _ _ _ _), fBalSel1_eq _ _ _ (codeMult_mem _ _ _ _ _),
        sat_fBal1, sat_fBal1, hsh, hex1, hex2] at hboth
      fin_cases r
      · exact hboth.1
      · exact hboth.2
    · have hp2 := hinst.2 (fun h => hev (hoil.mp (by rwa [shift_valExec])))
      unfold fPsi2 at hp2
      simp only [Formula.Sat, sat_atomQ2, sat_atomPay2, beq_iff_eq, hsh, hex2] at hp2
      simp only [yL, yR, hev, ↓reduceIte] at hqL hzL0 hzL1 ⊢
      have hboth := hp2 ⟨hqL, hzL0, hzL1⟩
      rw [fBalSel2_eq _ _ _ (codeMult_mem _ _ _ _ _), fBalSel2_eq _ _ _ (codeMult_mem _ _ _ _ _),
        sat_fBal2, sat_fBal2, hsh, hex1, hex2] at hboth
      fin_cases r
      · exact hboth.1
      · exact hboth.2
  have hleft_ray : ∀ (r : Fin 2) n,
      (pCarry r (decodePay (yL n 0).val)).val = 0 ∧
      (rowZ r n = false → (pW r (decodePay (yL n 0).val)).val = 0) := by
    intro r n
    let sig : ℕ → Sig0 := fun _ => (finZero, finZero, .oneToTwo)
    have hzc := (hsat_all sig).2.2.2.1.2.1
    have hlm : (fLeftMostR c.1 r).Sat (valExec (exec f sig)) := by
      fin_cases r
      · exact hzc.1
      · exact hzc.2
    unfold fLeftMostR at hlm
    rw [sat_weakUntil_not_graph] at hlm
    have hn := hlm n (fun _ _ => rfl)
    rw [shift_valExec] at hn
    have hsh : shift (exec f sig) n 0 = exec f sig n := by simp [shift]
    have hp : pre sig (n + 1) = toSig0 (hAt n 0) := by rw [pre_const_sig0, ← histOf_zero]
    simp only [Formula.Sat, sat_atomPay1, beq_iff_eq, hsh, exec, hp, yL, y1At, Nat.zero_mod,
      ↓reduceIte, rowZ] at hn ⊢
    exact ⟨congrArg Fin.val hn.1, fun hz => congrArg Fin.val (hn.2 hz)⟩
  have hright_ray : ∀ (r : Fin 2) n,
      (pCarry r (decodePay (yR n (3 ^ (n + 1) - 1)).val)).val = 0 := by
    intro r n
    let sig : ℕ → Sig0 := fun _ => (finZero, finZero, .twoToOne)
    have hzc := (hsat_all sig).2.2.2.1.2.2
    have hrm : (fRightMostR c.1 r).Sat (valExec (exec f sig)) := by
      fin_cases r
      · exact hzc.1
      · exact hzc.2
    unfold fRightMostR at hrm
    rw [sat_weakUntil_not_graph] at hrm
    have hn := hrm n (fun _ _ => rfl)
    rw [shift_valExec] at hn
    have hsh : shift (exec f sig) n 0 = exec f sig n := by simp [shift]
    have hp : pre sig (n + 1) = toSig0 (hAt n (3 ^ (n + 1) - 1)) := by
      rw [pre_const_sig0, ← histOf_last]
    have hev := three_pow_sub_one_even (n + 1)
    simp only [sat_atomPay2, beq_iff_eq, hsh, exec, hp, yR, y2At, hev, ↓reduceIte] at hn ⊢
    exact congrArg Fin.val hn
  have hchild_wt : ∀ (r : Fin 2) n j (k : Fin 3), j < 3 ^ (n + 1) →
      pW r (decodePay (yL (n + 1) (3 * j + k.val)).val) = pA r k (decodePay (yL n j).val) := by
    intro r n j k hj
    let g := stepGraph (decide (j % 2 = 0)) k.val
    have hchild_hist : hAt (n + 1) (3 * j + k.val) = hAt n j ++ [g] := by
      have hk := k.isLt
      have hdiv : (3 * j + k.val) / 3 = j := by omega
      have hmod : (3 * j + k.val) % 3 = k.val := by omega
      simp [hAt, histOf, hdiv, hmod, g]
    let sig := extendSig0 (hAt (n + 1) (3 * j + k.val))
    have hpt := ((hsat_all sig).2.2.2.2.2.1 n)
    rw [shift_valExec] at hpt
    have hwt : (fWeightTransR c.1 r).Sat (valExec (shift (exec f sig) n)) := by
      fin_cases r
      · exact hpt.2.1
      · exact hpt.2.2
    unfold fWeightTransR at hwt
    rw [sat_bigAnd] at hwt
    have h1 := hwt _ (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩)
    rw [sat_bigAnd] at h1
    set b := pA r k (decodePay (yL n j).val)
    have h2 := h1 _ (List.mem_map.mpr ⟨b, List.mem_finRange b, rfl⟩)
    rw [sat_bigAnd] at h2
    have hinst := h2 _ (List.mem_map.mpr ⟨g, mem_graphs g, rfl⟩)
    have hpre1 : pre (graphOf sig) (n + 1) = hAt n j := by
      change pre (graphOf (extendSig0 (hAt (n + 1) (3 * j + k.val)))) (n + 1) = hAt n j
      have hp := pre_graph_extendSig0 (hAt (n + 1) (3 * j + k.val)) (n + 1) (by simp [hAt])
      rw [hp, hchild_hist, List.take_left' (histOf_length (n + 1) j)]
    have hpre2 : pre (graphOf sig) (n + 2) = hAt (n + 1) (3 * j + k.val) :=
      hpre_hAt (n + 1) (3 * j + k.val)
    have hj1 : jIdx (pre (graphOf sig) (n + 1)) = j := by
      rw [hpre1, jIdx_histOf (n + 1) j hj]
    have hj2 : jIdx (pre (graphOf sig) (n + 2)) = 3 * j + k.val := by
      have hlt2 : 3 * j + k.val < 3 ^ (n + 2) := by have := k.isLt; rw [pow_succ]; omega
      rw [hpre2, jIdx_histOf (n + 2) (3 * j + k.val) hlt2]
    have hg_at : (Formula.next (.graph g)).Sat (valExec (shift (exec f sig) n)) := by
      change (exec f sig (1 + n)).1.2.2 = g
      rw [Nat.add_comm 1 n]
      simp only [exec, sig, extendSig0, hchild_hist]
      have hlen : (hAt n j).length = n + 1 := histOf_length (n + 1) j
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp [hlen]
    have hdk_at : (fDK c.1 k g).Sat (valExec (shift (exec f sig) n)) := by
      unfold fDK
      have hd := dVal_stepGraph (decide (j % 2 = 0)) k.val k.isLt
      have hoil1 := hoil_ext sig n
      rw [hj1] at hoil1
      by_cases hev : j % 2 = 0
      · simp only [g, hev, decide_true] at hd ⊢
        exact Or.inl ⟨by rw [← shift_valExec]; exact hoil1.mpr hev,
          by rw [if_pos hd]; exact sat_tt _⟩
      · simp only [g, hev, decide_false] at hd ⊢
        exact Or.inr ⟨fun h => hev (hoil1.mp (by rwa [shift_valExec])),
          by rw [if_pos hd]; exact sat_tt _⟩
    have hex1 : (exec f sig n).2 = (y1At n j, y2At n j) := by
      have hp : pre sig (n + 1) = toSig0 (hAt n j) := by rw [pre_sig0_toSig0, hpre1]
      simp [exec, hp, y1At, y2At]
    have hex2 : (exec f sig (n + 1)).2 =
        (y1At (n + 1) (3 * j + k.val), y2At (n + 1) (3 * j + k.val)) := by
      have hp : pre sig (n + 2) = toSig0 (hAt (n + 1) (3 * j + k.val)) := by
        rw [pre_sig0_toSig0, hpre2]
      simp [exec, hp, y1At, y2At]
    have hplan_at : (fPlanL c.1 (pA r k) b).Sat (valExec (shift (exec f sig) n)) := by
      unfold fPlanL
      have hoil1 := hoil_ext sig n
      rw [hj1] at hoil1
      have hsh0 : shift (exec f sig) n 0 = exec f sig n := by simp [shift]
      by_cases hev : j % 2 = 0
      · refine Or.inl ⟨by rw [← shift_valExec]; exact hoil1.mpr hev, ?_⟩
        rw [sat_atomPay1, beq_iff_eq, hsh0, congrArg Prod.fst hex1]
        simp [b, yL, hev]
      · refine Or.inr ⟨fun h => hev (hoil1.mp (by rwa [shift_valExec])), ?_⟩
        rw [sat_atomPay2, beq_iff_eq, hsh0, congrArg Prod.snd hex1]
        simp [b, yL, hev]
    have hnext := hinst ⟨hg_at, hdk_at, hplan_at⟩
    change (fPlanL c.1 (pW r) b).Sat (shift (valExec (shift (exec f sig) n)) 1) at hnext
    rw [shift_valExec, shift_shift, Nat.add_comm n 1, Nat.add_comm 1 n] at hnext
    unfold fPlanL at hnext
    have hoil2 := hoil_ext sig (n + 1)
    rw [hj2] at hoil2
    have hsh2 : shift (exec f sig) (n + 1) 0 = exec f sig (n + 1) := by simp [shift]
    rcases hnext with ⟨hl, ha⟩ | ⟨hnl, ha⟩
    · have hev2 : (3 * j + k.val) % 2 = 0 := hoil2.mp (by rwa [shift_valExec])
      rw [sat_atomPay1, beq_iff_eq, hsh2, congrArg Prod.fst hex2] at ha
      simpa [yL, hev2] using ha
    · have hev2 : ¬ ((3 * j + k.val) % 2 = 0) := fun h => hnl (by rw [← shift_valExec]; exact hoil2.mpr h)
      rw [sat_atomPay2, beq_iff_eq, hsh2, congrArg Prod.snd hex2] at ha
      simpa [yL, hev2] using ha
  let W (r : Fin 2) (n : ℕ) : ℕ := sumRange (3 ^ (n + 1)) (fun j => (pW r (decodePay (yL n j).val)).val)
  have hW_step : ∀ (r : Fin 2) n,
      W r (n + 1) = codeMult c r (rowQ n) (rowZ 0 n) (rowZ 1 n) * W r n := by
    intro r n
    have hp : 1 ≤ 3 ^ (n + 1) := Nat.one_le_pow (n + 1) 3 (by decide)
    have htel := sumRange_telescope (3 ^ (n + 1) - 1) (codeMult c r (rowQ n) (rowZ 0 n) (rowZ 1 n))
      (fun j => pPlanSum r (decodePay (yL n j).val))
      (fun j => (pW r (decodePay (yL n j).val)).val)
      (fun j => (pCarry r (decodePay (yL n j).val)).val)
      (fun j => (pCarry r (decodePay (yR n j).val)).val)
      (fun j hj => hbal_edge r n j (by omega))
      (fun j hj => congrArg (fun y => (pCarry r (decodePay y.val)).val) (hlink n j (by omega)))
    rw [Nat.sub_add_cancel hp, (hleft_ray r n).1, hright_ray r n, add_zero, add_zero] at htel
    have hsum_child : W r (n + 1) = sumRange (3 ^ (n + 1)) (fun j => pPlanSum r (decodePay (yL n j).val)) := by
      dsimp only [W]
      rw [pow_succ', sumRange_mul_three]
      have hcongr : ∀ L, L ≤ 3 ^ (n + 1) →
          sumRange L (fun j => (pW r (decodePay (yL (n + 1) (3 * j)).val)).val +
            (pW r (decodePay (yL (n + 1) (3 * j + 1)).val)).val +
            (pW r (decodePay (yL (n + 1) (3 * j + 2)).val)).val) =
          sumRange L (fun j => pPlanSum r (decodePay (yL n j).val)) := by
        intro L hL
        induction L with
        | zero => rfl
        | succ L ih =>
          simp only [sumRange, ih (by omega)]
          have h0 := hchild_wt r n L 0 (by omega)
          have h1 := hchild_wt r n L 1 (by omega)
          have h2 := hchild_wt r n L 2 (by omega)
          simp only [Fin.val_zero, add_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
          simp [pPlanSum, h0, h1, h2]
      exact hcongr (3 ^ (n + 1)) le_rfl
    rw [hsum_child, htel]
  have hzero_guard : ∀ (r : Fin 2) n, rowZ r n = true ↔ W r n = 3 ^ (n + 1) := by
    intro r n
    constructor
    · intro hz
      have hall : ∀ j < 3 ^ (n + 1), (pW r (decodePay (yL n j).val)).val = 1 := by
        intro j hj
        let sig := extendSig0 (hAt n j)
        have hzc := (hsat_all sig).2.2.2.1.1
        have hzi : (fZeroIndR c.1 r).Sat (valExec (exec f sig)) := by
          fin_cases r
          · exact hzc.1
          · exact hzc.2
        have hzin := hzi n
        rw [shift_valExec] at hzin
        have hj_eq : jIdx (pre (graphOf sig) (n + 1)) = j := by
          change jIdx (pre (graphOf (extendSig0 (hAt n j))) (n + 1)) = j
          rw [hpre_hAt n j, jIdx_histOf (n + 1) j hj]
        have hoil := hoil_ext sig n
        rw [hj_eq] at hoil
        have hsh : shift (exec f sig) n 0 = exec f sig n := by simp [shift]
        have hex := hexec_at (hAt n j) n (histOf_length (n + 1) j)
        have hex1 : (exec f sig n).2.1 = y1At n j := congrArg Prod.fst hex
        have hex2 : (exec f sig n).2.2 = y2At n j := congrArg Prod.snd hex
        have hzL : pZero r (decodePay (yL n j).val) = true := ((huniform n j hj).2.2 r).1.trans hz
        rcases hzin with ⟨hl, h1⟩ | ⟨hnl, h2⟩
        · have hev : j % 2 = 0 := hoil.mp (by rwa [shift_valExec])
          simp only [Formula.Sat, sat_atomPay1, beq_iff_eq, hsh, hex1] at h1
          simp only [yL, hev, ↓reduceIte] at hzL ⊢
          exact congrArg Fin.val (h1 hzL)
        · have hev : ¬ (j % 2 = 0) := fun h => hnl (by rw [← shift_valExec]; exact hoil.mpr h)
          simp only [Formula.Sat, sat_atomPay2, beq_iff_eq, hsh, hex2] at h2
          simp only [yL, hev, ↓reduceIte] at hzL ⊢
          exact congrArg Fin.val (h2 hzL)
      have hcongr : ∀ L, L ≤ 3 ^ (n + 1) →
          sumRange L (fun j => (pW r (decodePay (yL n j).val)).val) = sumRange L (fun _ => 1) := by
        intro L hL
        induction L with
        | zero => rfl
        | succ L ih => simp [sumRange, ih (by omega), hall L (by omega)]
      dsimp only [W]
      rw [hcongr (3 ^ (n + 1)) le_rfl, sumRange_const_one]
    · intro hW
      cases hzn : rowZ r n with
      | true => rfl
      | false =>
        have hw0 : (pW r (decodePay (yL n 0).val)).val = 0 := (hleft_ray r n).2 hzn
        have hlt := sumRange_lt_of_zero_head (3 ^ (n + 1))
          (fun j => (pW r (decodePay (yL n j).val)).val) (pow_pos (by decide) _) hw0
          (fun j _ => by have := (pW r (decodePay (yL n j).val)).isLt; omega)
        dsimp only [W] at hW
        omega
  have hinit : rowQ 0 = c.2.1 % (c.1 + 1) ∧ rowZ 0 0 = true ∧ rowZ 1 0 = true := by
    let sig : ℕ → Sig0 := fun _ => (finZero, finZero, .oneToTwo)
    have hic := (hsat_all sig).2.2.2.2.1
    have hp : pre sig 1 = toSig0 (hAt 0 0) := by rw [pre_const_sig0, ← histOf_zero]
    unfold fInitCheck at hic
    simpa [Formula.Sat, sat_atomQ1, sat_atomPay1, beq_iff_eq, exec, hp, rowQ, rowZ, y1At] using hic
  have hQ_step : ∀ n, rowQ (n + 1) = codeNextQ c (rowQ n) (rowZ 0 n) (rowZ 1 n) := by
    intro n
    let sig : ℕ → Sig0 := fun _ => (finZero, finZero, .oneToTwo)
    have hst := ((hsat_all sig).2.2.2.2.2.1 n).1
    rw [shift_valExec] at hst
    unfold fStateTrans at hst
    rw [sat_bigAnd] at hst
    have h1 := hst _ (List.mem_map.mpr ⟨rowQ n, List.mem_range.mpr (hrowQ_lt n), rfl⟩)
    rw [sat_bigAnd] at h1
    have h2 := h1 _ (List.mem_map.mpr ⟨rowZ 0 n, mem_bools _, rfl⟩)
    rw [sat_bigAnd] at h2
    have hinst := h2 _ (List.mem_map.mpr ⟨rowZ 1 n, mem_bools _, rfl⟩)
    have hsh0 : shift (exec f sig) n 0 = exec f sig n := by simp [shift]
    have hsh1 : shift (shift (exec f sig) n) 1 0 = exec f sig (n + 1) := by
      simp [shift, Nat.add_comm]
    have hp1 : pre sig (n + 1) = toSig0 (hAt n 0) := by rw [pre_const_sig0, ← histOf_zero]
    have hp2 : pre sig (n + 2) = toSig0 (hAt (n + 1) 0) := by rw [pre_const_sig0, ← histOf_zero]
    simp only [Formula.Sat, shift_valExec, sat_atomQ1, sat_atomPay1, beq_iff_eq, hsh0, hsh1,
      exec, hp1, hp2] at hinst
    exact hinst ⟨rfl, rfl, rfl⟩
  let sc (r : Fin 2) := simCnt2 c r rowQ rowZ
  have hinv : ∀ (r : Fin 2) n,
      W r n * 3 ^ (sc r n) = 3 ^ (n + 1) ∧ (rowZ r n = true ↔ sc r n = 0) := by
    intro r
    have hz0 : rowZ r 0 = true := by fin_cases r; exact hinit.2.1; exact hinit.2.2
    exact forced_invariant (W r) (rowZ r)
      (fun n => codeMult c r (rowQ n) (rowZ 0 n) (rowZ 1 n)) (sc r)
      rfl ((hzero_guard r 0).mp hz0) (hzero_guard r) (hW_step r) (fun n => by
        dsimp only [sc]
        rw [simCnt2]
        dsimp only [codeMult]
        fin_cases r
        · dsimp only
          by_cases hi : (codeEntry c (rowQ n)).2.1 % 2 = 0
          · by_cases hd : (codeEntry c (rowQ n)).1 = true
            · by_cases hz : rowZ 0 n = true <;> simp [hi, hd, hz]
            · simp [hi, hd]
          · simp [hi]
        · dsimp only
          by_cases hi : (codeEntry c (rowQ n)).2.1 % 2 = 1
          · by_cases hd : (codeEntry c (rowQ n)).1 = true
            · by_cases hz : rowZ 1 n = true <;> simp [hi, hd, hz]
            · simp [hi, hd]
          · simp [hi])
  have hrun_eq : ∀ n, rowQ n = (M.run n).state.val ∧ ∀ r : Fin 2, sc r n = (M.run n).counters r := by
    intro n
    induction n with
    | zero =>
      refine ⟨hinit.1, fun r => ?_⟩
      fin_cases r <;> rfl
    | succ n ih =>
      have hz0_eq : rowZ 0 n = decide ((M.run n).counters 0 = 0) := by
        have h := (hinv 0 n).2; rw [ih.2 0] at h; cases hr : rowZ 0 n <;> simp_all
      have hz1_eq : rowZ 1 n = decide ((M.run n).counters 1 = 0) := by
        have h := (hinv 1 n).2; rw [ih.2 1] at h; cases hr : rowZ 1 n <;> simp_all
      have hsp := cm2_step_props c (M.run n)
      refine ⟨?_, fun r => ?_⟩
      · rw [hQ_step n, ih.1, hz0_eq, hz1_eq]
        exact hsp.1.symm
      · dsimp only [sc] at ih ⊢
        rw [simCnt2, ih.1, ih.2 r, hz0_eq, hz1_eq]
        change _ = ((c.toMachine 2 (by norm_num)).step (M.run n)).counters r
        rcases (hsp.2 r).2.2 with ⟨hm, hc⟩ | ⟨hm, hc⟩ | ⟨hm, _, hc⟩ <;> simp [hm, hc]
  rintro ⟨n, hhalt⟩
  let sig : ℕ → Sig0 := fun _ => (finZero, finZero, .oneToTwo)
  have hnh := (hsat_all sig).2.2.2.2.2.2 n
  rw [shift_valExec, sat_bigAnd] at hnh
  have hmem : (M.run n).state.val ∈ c.2.2.1 := hhalt
  have hnot := hnh _ (List.mem_map.mpr ⟨(M.run n).state.val, hmem, rfl⟩)
  simp only [Formula.Sat, sat_atomQ1] at hnot
  have hsh0 : shift (exec f sig) n 0 = exec f sig n := by simp [shift]
  have hp : pre sig (n + 1) = toSig0 (hAt n 0) := by rw [pre_const_sig0, ← histOf_zero]
  rw [hsh0] at hnot
  simp only [exec, hp] at hnot
  exact hnot (hrun_eq n).1

lemma soundness2 (c : CMCode) (hreal : (red c).Realizable Set.univ) :
    ¬ (c.toMachine 2 (by norm_num)).Halts := by
  obtain ⟨f, hf⟩ := (mk_realizable_iff (outM c.1) (outM c.1) (instFormula c)).mp hreal
  exact soundness2_aux c f hf

end Parametric

theorem section_6_2_gen (pc : PayCode) :
    ∃ red : CMCode → Instance, Computable red ∧
      ∀ c : CMCode, (red c).k1 = 0 ∧ (red c).k2 = 0 ∧ (red c).IsSafety ∧
        ((red c).Realizable Set.univ ↔ ¬ (c.toMachine 2 (by norm_num)).Halts) :=
  ⟨@red pc, @computable_red pc, fun c =>
    ⟨rfl, rfl, @red_isSafety pc c, ⟨@soundness2 pc c, @completeness2 pc c⟩⟩⟩

end DistLTLSynth.Char.Sec62Aux

open DistLTLSynth.Char DistLTLSynth.Char.Sec62Aux in
theorem solution :
    ∃ red : CMCode → Instance, Computable red ∧
      ∀ c : CMCode, (red c).k1 = 0 ∧ (red c).k2 = 0 ∧ (red c).IsSafety ∧
        ((red c).Realizable Set.univ ↔ ¬ (c.toMachine 2 (by norm_num)).Halts) :=
  section_6_2_gen
    { K := 248832
      hK := by norm_num
      equiv := (Equiv.prodCongr ctrFieldEquiv
        ((Equiv.prodCongr ctrFieldEquiv (Equiv.refl (Fin 3))).trans finProdFinEquiv)).trans
        (finProdFinEquiv.trans (finCongr (by norm_num))) }
