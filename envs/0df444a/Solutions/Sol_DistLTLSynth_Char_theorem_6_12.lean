-- Prove2me | solution 1 for DistLTLSynth.Char.theorem_6_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T08:04:10.772778+00:00
-- url     : https://prove2.me/submissions/4935d5f4-8fec-4f6e-a34d-b56b67ca98d8

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_CounterMachine
import Definitions.Def_DistLTLSynth_Char_CounterFormula

namespace DistLTLSynth.Char.Thm612Aux
open DistLTLSynth.Char

/-! ### Part 1: Ternary Counter Arithmetic -/

def wBit (c j : ℕ) : ℕ := (j + 1) / 3 ^ c - j / 3 ^ c

lemma wBit_le_one (c j : ℕ) : wBit c j ≤ 1 := by
  have hd : 0 < 3 ^ c := pow_pos (by decide) c
  have h := Nat.div_le_div_right (show j + 1 ≤ j + 3 ^ c by omega) (c := 3 ^ c)
  rw [Nat.add_div_right _ hd] at h
  unfold wBit
  omega

def wFin (c j : ℕ) : Fin 2 := ⟨wBit c j, by have := wBit_le_one c j; omega⟩

lemma wBit_zero (j : ℕ) : wBit 0 j = 1 := by
  simp [wBit]

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

lemma carryVal_at_zero (c m : ℕ) : carryVal c m 0 = 0 := by
  simp [carryVal]

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

/-! ### Part 2: Finite Prefix Sums -/

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
  | zero =>
    simpa [sumRange] using hbal 0 (by omega)
  | succ k ih =>
    have h1 := ih (fun j hj => hbal j (by omega)) (fun j hj => hlink j (by omega))
    have h2 := hbal (k + 1) (by omega)
    have h3 := hlink k (by omega)
    have hL : sumRange (k + 1 + 1) prom = sumRange (k + 1) prom + prom (k + 1) := rfl
    have hR : sumRange (k + 1 + 1) wt = sumRange (k + 1) wt + wt (k + 1) := rfl
    rw [hL, hR, Nat.mul_add]
    omega

/-! ### Part 3: View Geometry and Reflected Ternary History Indexing -/

def toSig (l : List CommGraph) : List (Signal Unit Unit) :=
  l.map (fun g => ((), (), g))

@[simp] lemma toSig_nil : toSig [] = [] := rfl
@[simp] lemma toSig_append (a b : List CommGraph) : toSig (a ++ b) = toSig a ++ toSig b := by
  simp [toSig]
@[simp] lemma toSig_length (l : List CommGraph) : (toSig l).length = l.length := by
  simp [toSig]

def vdepth : View Unit Unit → ℕ
  | .I1 | .I2 => 0
  | .N1 _ u | .C1 _ u _ _ => vdepth u + 1
  | .N2 _ v | .C2 _ v _ _ => vdepth v + 1

def vcoord : View Unit Unit → ℕ
  | .I1 => 0
  | .I2 => 1
  | .N1 _ u => 3 * vcoord u
  | .N2 _ v => 3 * vcoord v
  | .C1 _ u _ v => vcoord u + 2 * vcoord v
  | .C2 _ v _ u => 2 * vcoord u + vcoord v

lemma views_append_singleton {X1 X2 : Type} (u : List (Signal X1 X2)) (a : Signal X1 X2) :
    views (u ++ [a]) = viewStep (views u) a := by
  simp [views]

lemma views_toSig_snoc (l : List CommGraph) (g : CommGraph) :
    views (toSig (l ++ [g])) = viewStep (views (toSig l)) ((), (), g) := by
  have hs : toSig (l ++ [g]) = toSig l ++ [((), (), g)] := by simp [toSig]
  rw [hs, views_append_singleton]

lemma jIdx_nil : jIdx [] = 0 := rfl

lemma jIdx_append_singleton (h : List CommGraph) (g : CommGraph) :
    jIdx (h ++ [g]) = 3 * jIdx h + if jIdx h % 2 = 0 then delta g else 2 - delta g := by
  unfold jIdx
  rw [List.foldl_append]
  rfl

lemma vdepth_coord_views (h : List CommGraph) :
    vdepth (view1 (toSig h)) = h.length ∧
    vdepth (view2 (toSig h)) = h.length ∧
    (if jIdx h % 2 = 0 then vcoord (view1 (toSig h)) else vcoord (view2 (toSig h))) = jIdx h ∧
    (if jIdx h % 2 = 0 then vcoord (view2 (toSig h)) else vcoord (view1 (toSig h))) = jIdx h + 1 := by
  induction h using List.reverseRecOn with
  | nil => simp [view1, view2, views, vdepth, vcoord, jIdx_nil]
  | append_singleton h g ih =>
    rcases ih with ⟨hd1, hd2, hcL, hcR⟩
    simp only [view1, view2] at hd1 hd2 hcL hcR ⊢
    rw [views_toSig_snoc, jIdx_append_singleton]
    rcases hvs : views (toSig h) with ⟨u, v⟩
    rw [hvs] at hd1 hd2 hcL hcR
    dsimp only at hd1 hd2 hcL hcR
    rcases (show jIdx h % 2 = 0 ∨ jIdx h % 2 = 1 by omega) with hp | hp
    · simp only [hp, ↓reduceIte] at hcL hcR ⊢
      cases g <;> simp [viewStep, vdepth, vcoord, delta, hd1, hd2, hcL, hcR] <;>
        (try split_ifs) <;> omega
    · have hp0 : ¬ (jIdx h % 2 = 0) := by omega
      simp only [hp0, ↓reduceIte] at hcL hcR ⊢
      cases g <;> simp [viewStep, vdepth, vcoord, delta, hd1, hd2, hcL, hcR] <;>
        (try split_ifs) <;> omega

lemma vcoord_mod3_step (uv : View Unit Unit × View Unit Unit) (g : CommGraph) :
    let uv' := viewStep uv ((), (), g)
    (Ctr.mod3 (vcoord uv'.1), Ctr.mod3 (vcoord uv'.2)) =
      Ctr.childPos g (Ctr.mod3 (vcoord uv.1)) (Ctr.mod3 (vcoord uv.2)) := by
  cases g <;>
  · apply Prod.ext <;> apply Fin.ext <;> simp [viewStep, vcoord, Ctr.childPos, Ctr.mod3] <;> omega

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

lemma vcoord_mod3_pre (s : ℕ → Signal Unit Unit) (n : ℕ) :
    (Ctr.mod3 (vcoord (view1 (pre s (n + 1)))), Ctr.mod3 (vcoord (view2 (pre s (n + 1))))) =
      if n = 0 then Ctr.childPos (s 0).2.2 0 1
      else Ctr.childPos (s n).2.2
        (Ctr.mod3 (vcoord (view1 (pre s n)))) (Ctr.mod3 (vcoord (view2 (pre s n)))) := by
  have hpre := pre_snoc s n
  rcases hsn : s n with ⟨⟨⟩, ⟨⟩, g⟩
  cases n with
  | zero =>
    simp only [↓reduceIte]
    have hp1 : pre s 1 = [((), (), g)] := by
      rw [hpre, hsn]
      simp [pre]
    rw [hp1, hsn]
    simpa [view1, view2, views, vcoord, Ctr.mod3] using vcoord_mod3_step (.I1, .I2) g
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    rw [hpre, hsn]
    simp only [view1, view2, views_append_singleton]
    exact vcoord_mod3_step (views (pre s (m + 1))) g

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
    · simp only [hp, decide_true, ↓reduceIte] at hd ⊢
      omega
    · simp only [hp, decide_false, Bool.false_eq_true, ↓reduceIte] at hd ⊢
      omega

lemma histOf_zero (r : ℕ) : histOf r 0 = List.replicate r .oneToTwo := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp [histOf, ih, stepGraph, List.replicate_succ']

lemma three_pow_sub_one_even (r : ℕ) : (3 ^ r - 1) % 2 = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hp : 1 ≤ 3 ^ r := Nat.one_le_pow r 3 (by decide)
    rw [pow_succ]
    omega

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

lemma histOf_shared_view (r : ℕ) :
    ∀ j, j + 1 < 3 ^ r →
      (if j % 2 = 0 then view2 (toSig (histOf r j)) else view1 (toSig (histOf r j))) =
      (if (j + 1) % 2 = 0 then view1 (toSig (histOf r (j + 1))) else view2 (toSig (histOf r (j + 1)))) := by
  induction r with
  | zero =>
    intro j hj
    simp at hj
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
          stepGraph, view2, views_toSig_snoc, viewStep]
      · have hj0 : ¬ (j % 2 = 0) := by omega
        have hj1 : (j + 1) % 2 = 0 := by omega
        have hp' : ¬ ((j / 3) % 2 = 0) := by omega
        simp only [hj0, hj1, ↓reduceIte, histOf, hd, hdiv1, hmod1, hp', decide_false,
          Bool.false_eq_true, stepGraph, view1, views_toSig_snoc, viewStep]
    · have hdiv1 : (j + 1) / 3 = j / 3 := by omega
      have hmod1 : (j + 1) % 3 = 2 := by omega
      rcases (show (j / 3) % 2 = 0 ∨ (j / 3) % 2 = 1 by omega) with hp | hp
      · have hj0 : ¬ (j % 2 = 0) := by omega
        have hj1 : (j + 1) % 2 = 0 := by omega
        simp only [hj0, hj1, ↓reduceIte, histOf, hd, hdiv1, hmod1, hp, decide_true,
          stepGraph, view1, views_toSig_snoc, viewStep]
      · have hj0 : j % 2 = 0 := by omega
        have hj1 : ¬ ((j + 1) % 2 = 0) := by omega
        have hp' : ¬ ((j / 3) % 2 = 0) := by omega
        simp only [hj0, hj1, ↓reduceIte, histOf, hd, hdiv1, hmod1, hp', decide_false,
          Bool.false_eq_true, stepGraph, view2, views_toSig_snoc, viewStep]
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
          decide_false, Bool.false_eq_true, stepGraph, view2, views_toSig_snoc, viewStep]
        exact congrArg (View.N2 ()) hrec
      · have hj0 : ¬ (j % 2 = 0) := by omega
        have hj1 : (j + 1) % 2 = 0 := by omega
        have hp' : ¬ ((j / 3) % 2 = 0) := by omega
        have hp1 : (j / 3 + 1) % 2 = 0 := by omega
        simp only [hp', hp1, ↓reduceIte] at hrec
        simp only [hj0, hj1, ↓reduceIte, histOf, hd, hdiv1, hmod1, hp', hp1, decide_true,
          decide_false, Bool.false_eq_true, stepGraph, view1, views_toSig_snoc, viewStep]
        exact congrArg (View.N1 ()) hrec

def extendSig (h : List CommGraph) : ℕ → Signal Unit Unit :=
  fun n => ((), (), h.getD n .both)

lemma pre_extendSig (h : List CommGraph) (r : ℕ) (hr : r ≤ h.length) :
    pre (extendSig h) r = toSig (h.take r) := by
  apply List.ext_getElem
  · simp [pre, hr]
  · intro i h1 h2
    simp only [pre, List.length_ofFn] at h1
    have hi : i < h.length := by omega
    simp [pre, extendSig, toSig, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

lemma pre_const_sig (g : CommGraph) (r : ℕ) :
    pre (fun _ : ℕ => ((), (), g)) r = toSig (List.replicate r g) := by
  apply List.ext_getElem <;> simp [pre, toSig]

lemma pre_unit_toSig (s : ℕ → Signal Unit Unit) (r : ℕ) :
    pre s r = toSig (pre (graphOf s) r) := by
  apply List.ext_getElem
  · simp [pre, toSig]
  · intro i h1 h2
    simp only [pre, toSig, List.getElem_ofFn, List.getElem_map, graphOf]

/-! ### Part 4: Formula Semantics Helpers -/

lemma sat_tt {X1 X2 Y1 Y2 : Type} (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    (Formula.tt : Formula X1 X2 Y1 Y2).Sat e := by
  simp only [Formula.tt, Formula.Sat]
  exact em _

lemma sat_ff {X1 X2 Y1 Y2 : Type} (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    ¬ (Formula.ff : Formula X1 X2 Y1 Y2).Sat e := by
  simp only [Formula.ff, Formula.Sat]
  exact not_not_intro (sat_tt e)

lemma sat_bigAnd {X1 X2 Y1 Y2 : Type} (l : List (Formula X1 X2 Y1 Y2))
    (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    (Formula.bigAnd l).Sat e ↔ ∀ ψ ∈ l, ψ.Sat e := by
  induction l with
  | nil =>
    simp only [Formula.bigAnd, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
    exact sat_tt e
  | cons a tl ih =>
    simp only [Formula.bigAnd, Formula.Sat, ih, List.mem_cons, forall_eq_or_imp]

lemma sat_bigOr {X1 X2 Y1 Y2 : Type} (l : List (Formula X1 X2 Y1 Y2))
    (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    (Formula.bigOr l).Sat e ↔ ∃ ψ ∈ l, ψ.Sat e := by
  induction l with
  | nil =>
    simp only [Formula.bigOr, List.not_mem_nil, false_and, exists_false, iff_false]
    exact sat_ff e
  | cons a tl ih =>
    simp only [Formula.bigOr, Formula.Sat, ih, List.mem_cons, exists_eq_or_imp]

lemma shift_shift {α : Type} (e : ℕ → α) (a b : ℕ) :
    shift (shift e a) b = shift e (a + b) := by
  funext n; simp only [shift]; congr 1; omega

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
      · exfalso
        apply hneq
        simpa using hstay r0 (by omega)
  · intro h
    by_cases hall : ∀ k, (e k).1.2.2 = g
    · exact Or.inl (fun r => h r (fun k _ => hall k))
    · classical
      push Not at hall
      let r0 := Nat.find hall
      have hr0 : (e r0).1.2.2 ≠ g := Nat.find_spec hall
      refine Or.inr ⟨r0, by simpa using hr0, fun r' hr' => h r' (fun k hk => ?_)⟩
      have hmin := Nat.find_min hall (Nat.lt_of_le_of_lt hk hr')
      push Not at hmin
      exact hmin

lemma sat_atom1 {Q : Type} [Fintype Q] (P : CtrOut Q → Prop)
    (e : ℕ → Signal Unit Unit × (CtrOut Q × CtrOut Q)) :
    (Ctr.atom1 P).Sat e ↔ P (e 0).2.1 := by
  unfold Ctr.atom1
  rw [sat_bigOr]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, heq⟩
    change (e 0).2.1 = y at heq
    rwa [heq]
  · intro hP
    exact ⟨Formula.out1 (e 0).2.1, ⟨(e 0).2.1, hP, rfl⟩, rfl⟩

lemma sat_atom2 {Q : Type} [Fintype Q] (P : CtrOut Q → Prop)
    (e : ℕ → Signal Unit Unit × (CtrOut Q × CtrOut Q)) :
    (Ctr.atom2 P).Sat e ↔ P (e 0).2.2 := by
  unfold Ctr.atom2
  rw [sat_bigOr]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, heq⟩
    change (e 0).2.2 = y at heq
    rwa [heq]
  · intro hP
    exact ⟨Formula.out2 (e 0).2.2, ⟨(e 0).2.2, hP, rfl⟩, rfl⟩

lemma sat_atom12 {Q : Type} [Fintype Q] (R : CtrOut Q → CtrOut Q → Prop)
    (e : ℕ → Signal Unit Unit × (CtrOut Q × CtrOut Q)) :
    (Ctr.atom12 R).Sat e ↔ R (e 0).2.1 (e 0).2.2 := by
  unfold Ctr.atom12
  rw [sat_bigOr]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨⟨y1, y2⟩, hR, rfl⟩, h1, h2⟩
    change (e 0).2.1 = y1 at h1
    change (e 0).2.2 = y2 at h2
    rwa [h1, h2]
  · intro hR
    exact ⟨.and (.out1 (e 0).2.1) (.out2 (e 0).2.2), ⟨((e 0).2.1, (e 0).2.2), hR, rfl⟩, rfl, rfl⟩

lemma mem_graphs (g : CommGraph) : g ∈ Ctr.graphs := by
  cases g <;> simp [Ctr.graphs]

lemma mem_bools (z : Bool) : z ∈ Ctr.bools := by
  cases z <;> simp [Ctr.bools]

lemma mem_states {Q : Type} [Fintype Q] (q : Q) : q ∈ (Ctr.states : List Q) := by
  simp [Ctr.states]

lemma sat_posOrd {Q : Type} [Fintype Q]
    (e : ℕ → Signal Unit Unit × (CtrOut Q × CtrOut Q)) :
    (Ctr.posOrd : CtrFormula Q).Sat e ↔
      ((Ctr.opos (e 0).2.1, Ctr.opos (e 0).2.2) = Ctr.childPos (e 0).1.2.2 0 1 ∧
        ∀ r, (Ctr.opos (e (r + 1)).2.1, Ctr.opos (e (r + 1)).2.2) =
          Ctr.childPos (e (r + 1)).1.2.2 (Ctr.opos (e r).2.1) (Ctr.opos (e r).2.2)) := by
  unfold Ctr.posOrd Ctr.phiPos Ctr.posEq
  constructor
  · rintro ⟨h0, hstep⟩
    rw [sat_bigAnd] at h0
    refine ⟨?_, fun r => ?_⟩
    · have hg := h0 _ (List.mem_map.mpr ⟨(e 0).1.2.2, mem_graphs _, rfl⟩) rfl
      rw [sat_atom12] at hg
      exact Prod.ext hg.1 hg.2
    · have hs := hstep r
      rw [sat_bigAnd] at hs
      let u := Ctr.opos (e r).2.1
      let v := Ctr.opos (e r).2.2
      let g := (e (r + 1)).1.2.2
      have hinst := hs _ (List.mem_flatMap.mpr ⟨u, List.mem_finRange u,
        List.mem_flatMap.mpr ⟨v, List.mem_finRange v,
          List.mem_map.mpr ⟨g, mem_graphs g, rfl⟩⟩⟩)
      simp only [Formula.Sat, sat_atom12, shift_shift] at hinst
      have h1 : (shift e r 0).2.1 = (e r).2.1 := by simp [shift]
      have h2 : (shift e r 0).2.2 = (e r).2.2 := by simp [shift]
      have h3 : shift e (r + 1) 0 = e (r + 1) := by simp [shift]
      rw [h1, h2, h3] at hinst
      have hres := hinst ⟨rfl, rfl⟩ rfl
      exact Prod.ext hres.1 hres.2
  · rintro ⟨h0, hstep⟩
    refine ⟨?_, fun r => ?_⟩
    · rw [sat_bigAnd]
      intro ψ hmem
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hmem
      intro hg
      change (e 0).1.2.2 = g at hg
      rw [sat_atom12, ← hg]
      exact ⟨congrArg Prod.fst h0, congrArg Prod.snd h0⟩
    · rw [sat_bigAnd]
      intro ψ hmem
      obtain ⟨u, _, hmem⟩ := List.mem_flatMap.mp hmem
      obtain ⟨v, _, hmem⟩ := List.mem_flatMap.mp hmem
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hmem
      simp only [Formula.Sat, sat_atom12, shift_shift]
      rintro ⟨hu, hv⟩ hg
      have h1 : (shift e r 0).2.1 = (e r).2.1 := by simp [shift]
      have h2 : (shift e r 0).2.2 = (e r).2.2 := by simp [shift]
      have h3 : shift e (r + 1) 0 = e (r + 1) := by simp [shift]
      rw [h1] at hu
      rw [h2] at hv
      rw [h3] at hg ⊢
      have hs := hstep r
      rw [hu, hv, hg] at hs
      exact ⟨congrArg Prod.fst hs, congrArg Prod.snd hs⟩

lemma posOrd_exec_coords {Q : Type} [Fintype Q]
    (f : Algorithm Unit Unit (CtrOut Q) (CtrOut Q)) (s : ℕ → Signal Unit Unit)
    (hpos : (Ctr.posOrd : CtrFormula Q).Sat (exec f s)) (r : ℕ) :
    (Ctr.opos (exec f s r).2.1, Ctr.opos (exec f s r).2.2) =
      (Ctr.mod3 (vcoord (view1 (pre s (r + 1)))), Ctr.mod3 (vcoord (view2 (pre s (r + 1))))) := by
  obtain ⟨h0, hstep⟩ := (sat_posOrd (exec f s)).mp hpos
  induction r with
  | zero =>
    rw [vcoord_mod3_pre s 0]
    simpa [exec] using h0
  | succ r ih =>
    rw [vcoord_mod3_pre s (r + 1)]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    have ih1 : Ctr.opos (exec f s r).2.1 = Ctr.mod3 (vcoord (view1 (pre s (r + 1)))) :=
      congrArg Prod.fst ih
    have ih2 : Ctr.opos (exec f s r).2.2 = Ctr.mod3 (vcoord (view2 (pre s (r + 1)))) :=
      congrArg Prod.snd ih
    rw [hstep r, ih1, ih2]
    rfl

lemma oneIsLeft_iff_even {Q : Type} [Fintype Q]
    (f : Algorithm Unit Unit (CtrOut Q) (CtrOut Q)) (s : ℕ → Signal Unit Unit)
    (hpos : (Ctr.posOrd : CtrFormula Q).Sat (exec f s)) (r : ℕ) :
    (Ctr.oneIsLeft : CtrFormula Q).Sat (shift (exec f s) r) ↔
      jIdx (pre (graphOf s) (r + 1)) % 2 = 0 := by
  unfold Ctr.oneIsLeft
  rw [sat_atom12]
  have hsh : shift (exec f s) r 0 = exec f s r := by simp [shift]
  rw [hsh]
  have hc := posOrd_exec_coords f s hpos r
  have hpre := pre_unit_toSig s (r + 1)
  rw [hpre] at hc
  have hvc := vdepth_coord_views (pre (graphOf s) (r + 1))
  have h1 := congrArg Prod.fst hc
  have h2 := congrArg Prod.snd hc
  dsimp only at h1 h2
  rw [h1, h2]
  set j := jIdx (pre (graphOf s) (r + 1))
  rcases (show j % 2 = 0 ∨ j % 2 = 1 by omega) with hp | hp
  · simp only [hp, ↓reduceIte] at hvc ⊢
    simp [Ctr.mod3, hvc.2.2.1, hvc.2.2.2]
  · have hp0 : ¬ (j % 2 = 0) := by omega
    simp only [hp0, ↓reduceIte, iff_false] at hvc ⊢
    simp [Ctr.mod3, hvc.2.2.1, hvc.2.2.2]
    omega

/-! ### Part 5: 1-Counter Machine Step Properties -/

lemma cm1_step_props {Q : Type} (M : CounterMachine Q 1) (cfg : Config Q 1) :
    let q := cfg.state
    let c := cfg.counters 0
    let z := decide (c = 0)
    let m := Ctr.mult M q z
    let cfg' := M.step cfg
    cfg'.state = Ctr.nextState M q z ∧
      0 < m ∧ m ≤ 9 ∧
      ((m = 1 ∧ cfg'.counters 0 = c + 1) ∨
        (m = 3 ∧ cfg'.counters 0 = c) ∨
        (m = 9 ∧ 0 < c ∧ cfg'.counters 0 = c - 1)) := by
  dsimp only
  unfold CounterMachine.step Ctr.mult Ctr.nextState
  cases hinstr : M.instr cfg.state with
  | inc i q' =>
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp [Function.update_self]
  | dec i q' q'' =>
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    by_cases hc : cfg.counters 0 = 0
    · simp [hc]
    · have hpos : 0 < cfg.counters 0 := Nat.pos_of_ne_zero hc
      simp [hc, hpos, Function.update_self]

lemma cm1_counter_le_step {Q : Type} (M : CounterMachine Q 1) (n : ℕ) :
    (M.run n).counters 0 ≤ n := by
  induction n with
  | zero => simp [CounterMachine.run]
  | succ n ih =>
    have hs := (cm1_step_props M (M.run n)).2.2.2
    change (M.step (M.run n)).counters 0 ≤ n + 1
    rcases hs with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;> omega

/-! ### Part 6: Completeness (`¬ M.Halts → Realizable`) -/

def nodeOut {Q : Type} (M : CounterMachine Q 1) (t i : ℕ) : CtrOut Q :=
  let cfg := M.run t
  let cfg' := M.run (t + 1)
  let q := cfg.state
  let c := cfg.counters 0
  let c' := cfg'.counters 0
  let z := decide (c = 0)
  let m := Ctr.mult M q z
  have hm := (cm1_step_props M cfg).2
  (q, z, (wFin c i, wFin c' (3 * i), wFin c' (3 * i + 1), wFin c' (3 * i + 2)),
    carryFin c m i hm.1 hm.2.1, Ctr.mod3 i)

def completeAlg {Q : Type} (M : CounterMachine Q 1) :
    Algorithm Unit Unit (CtrOut Q) (CtrOut Q) where
  f1 v := nodeOut M (vdepth v - 1) (vcoord v)
  f2 v := nodeOut M (vdepth v - 1) (vcoord v)

lemma completeness {Q : Type} [Fintype Q] [DecidableEq Q] (M : CounterMachine Q 1)
    (hnh : ¬ M.Halts) : Realizable Set.univ (counterFormula M) := by
  refine ⟨completeAlg M, fun s _ => ?_⟩
  let e := exec (completeAlg M) s
  change (counterFormula M).Sat e
  have hviews : ∀ r,
      (e r).2.1 = nodeOut M r (vcoord (view1 (toSig (pre (graphOf s) (r + 1))))) ∧
      (e r).2.2 = nodeOut M r (vcoord (view2 (toSig (pre (graphOf s) (r + 1))))) := by
    intro r
    have hp := pre_unit_toSig s (r + 1)
    have hvc := vdepth_coord_views (pre (graphOf s) (r + 1))
    have hlen : (pre (graphOf s) (r + 1)).length = r + 1 := by simp [pre]
    dsimp only [e, exec, completeAlg]
    rw [hp, hvc.1, hvc.2.1, hlen, Nat.add_sub_cancel]
    exact ⟨rfl, rfl⟩
  have hpos : (Ctr.posOrd : CtrFormula Q).Sat e := by
    rw [sat_posOrd]
    have hopos : ∀ r, (Ctr.opos (e r).2.1, Ctr.opos (e r).2.2) =
        (Ctr.mod3 (vcoord (view1 (pre s (r + 1)))), Ctr.mod3 (vcoord (view2 (pre s (r + 1))))) := by
      intro r
      rw [(hviews r).1, (hviews r).2, pre_unit_toSig]
      rfl
    refine ⟨?_, fun r => ?_⟩
    · rw [hopos 0, vcoord_mod3_pre s 0]
      rfl
    · rw [hopos (r + 1), vcoord_mod3_pre s (r + 1)]
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      have h1 : Ctr.mod3 (vcoord (view1 (pre s (r + 1)))) = Ctr.opos (e r).2.1 :=
        (congrArg Prod.fst (hopos r)).symm
      have h2 : Ctr.mod3 (vcoord (view2 (pre s (r + 1)))) = Ctr.opos (e r).2.2 :=
        (congrArg Prod.snd (hopos r)).symm
      rw [h1, h2]
      rfl
  have hoil : ∀ r, (Ctr.oneIsLeft : CtrFormula Q).Sat (shift e r) ↔
      jIdx (pre (graphOf s) (r + 1)) % 2 = 0 :=
    oneIsLeft_iff_even (completeAlg M) s hpos
  have hLR1 : ∀ r,
      (if jIdx (pre (graphOf s) (r + 1)) % 2 = 0 then (e r).2.1 else (e r).2.2) =
        nodeOut M r (jIdx (pre (graphOf s) (r + 1))) := by
    intro r
    have hvc := vdepth_coord_views (pre (graphOf s) (r + 1))
    by_cases hp : jIdx (pre (graphOf s) (r + 1)) % 2 = 0
    · simp only [hp, ↓reduceIte] at hvc ⊢
      rw [(hviews r).1, hvc.2.2.1]
    · simp only [hp, ↓reduceIte] at hvc ⊢
      rw [(hviews r).2, hvc.2.2.1]
  have hLR2 : ∀ r,
      (if jIdx (pre (graphOf s) (r + 1)) % 2 = 0 then (e r).2.2 else (e r).2.1) =
        nodeOut M r (jIdx (pre (graphOf s) (r + 1)) + 1) := by
    intro r
    have hvc := vdepth_coord_views (pre (graphOf s) (r + 1))
    by_cases hp : jIdx (pre (graphOf s) (r + 1)) % 2 = 0
    · simp only [hp, ↓reduceIte] at hvc ⊢
      rw [(hviews r).2, hvc.2.2.2]
    · simp only [hp, ↓reduceIte] at hvc ⊢
      rw [(hviews r).1, hvc.2.2.2]
  unfold counterFormula
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- PathAgr
    unfold Ctr.pathAgr
    intro r
    simp only [Formula.Sat, sat_atom12]
    have hsh : shift e r 0 = e r := by simp [shift]
    rw [hsh, (hviews r).1, (hviews r).2]
    exact ⟨rfl, rfl⟩
  · -- LocalSum
    unfold Ctr.localSum Ctr.psi1 Ctr.psi2
    intro r
    rw [sat_bigAnd]
    intro ψ hmem
    obtain ⟨q, _, hmem⟩ := List.mem_flatMap.mp hmem
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hmem
    have hsh : shift e r 0 = e r := by simp [shift]
    have hstep := (cm1_step_props M (M.run r)).2.2.2
    have hcons := fun j => wBit_conservation ((M.run r).counters 0)
      ((M.run (r + 1)).counters 0)
      (Ctr.mult M (M.run r).state (decide ((M.run r).counters 0 = 0))) j hstep
    let j := jIdx (pre (graphOf s) (r + 1))
    have hl1 : (if j % 2 = 0 then (e r).2.1 else (e r).2.2) = nodeOut M r j := hLR1 r
    have hl2 : (if j % 2 = 0 then (e r).2.2 else (e r).2.1) = nodeOut M r (j + 1) := hLR2 r
    refine ⟨?_, ?_⟩
    · intro hl
      have hj : j % 2 = 0 := (hoil r).mp hl
      simp only [Formula.Sat, sat_atom1, sat_atom12, hsh]
      rintro ⟨hq, hz⟩
      have he1 : (e r).2.1 = nodeOut M r j := by simpa [hj] using hl1
      have he2 : (e r).2.2 = nodeOut M r (j + 1) := by simpa [hj] using hl2
      rw [he1] at hq hz ⊢
      rw [he2]
      subst hq hz
      simpa [nodeOut, Ctr.planSum, Ctr.oa, Ctr.ow, Ctr.ocarry, Ctr.oq, Ctr.ozero, wFin, carryFin,
        CounterMachine.run] using hcons j
    · intro hnl
      have hj : ¬ (j % 2 = 0) := fun h => hnl ((hoil r).mpr h)
      simp only [Formula.Sat, sat_atom2, sat_atom12, hsh]
      rintro ⟨hq, hz⟩
      have he2 : (e r).2.2 = nodeOut M r j := by simpa [hj] using hl1
      have he1 : (e r).2.1 = nodeOut M r (j + 1) := by simpa [hj] using hl2
      rw [he2] at hq hz ⊢
      rw [he1]
      subst hq hz
      simpa [nodeOut, Ctr.planSum, Ctr.oa, Ctr.ow, Ctr.ocarry, Ctr.oq, Ctr.ozero, wFin, carryFin,
        CounterMachine.run] using hcons j
  · -- ZeroCheck
    refine ⟨?_, ?_, ?_⟩
    · -- ZeroInd
      unfold Ctr.zeroInd
      intro r
      have hsh : shift e r 0 = e r := by simp [shift]
      let j := jIdx (pre (graphOf s) (r + 1))
      have hl1 : (if j % 2 = 0 then (e r).2.1 else (e r).2.2) = nodeOut M r j := hLR1 r
      by_cases hj : j % 2 = 0
      · refine Or.inl ⟨(hoil r).mpr hj, ?_⟩
        simp only [Formula.Sat, sat_atom1, hsh]
        have he1 : (e r).2.1 = nodeOut M r j := by simpa [hj] using hl1
        rw [he1]
        intro hz
        have hc0 : (M.run r).counters 0 = 0 := of_decide_eq_true hz
        apply Fin.ext
        simp [nodeOut, Ctr.ow, wFin, hc0, wBit_zero]
      · refine Or.inr ⟨fun h => hj ((hoil r).mp h), ?_⟩
        simp only [Formula.Sat, sat_atom2, hsh]
        have he2 : (e r).2.2 = nodeOut M r j := by simpa [hj] using hl1
        rw [he2]
        intro hz
        have hc0 : (M.run r).counters 0 = 0 := of_decide_eq_true hz
        apply Fin.ext
        simp [nodeOut, Ctr.ow, wFin, hc0, wBit_zero]
    · -- LeftMost
      unfold Ctr.leftMost
      rw [sat_weakUntil_not_graph]
      intro r hstay
      have hpre : pre (graphOf s) (r + 1) = histOf (r + 1) 0 := by
        rw [histOf_zero]
        exact pre_eq_replicate (graphOf s) .oneToTwo (r + 1) (fun k hk => hstay k (by omega))
      have hj0 : jIdx (pre (graphOf s) (r + 1)) = 0 := by
        rw [hpre, jIdx_histOf (r + 1) 0 (pow_pos (by decide) _)]
      have he1 : (e r).2.1 = nodeOut M r 0 := by
        have h := hLR1 r
        simpa [hj0] using h
      have hsh : shift e r 0 = e r := by simp [shift]
      simp only [Formula.Sat, sat_atom1, hsh, he1]
      refine ⟨?_, fun hz => ?_⟩
      · apply Fin.ext
        simp [nodeOut, Ctr.ocarry, carryFin, carryVal_at_zero]
      · have hc_ne : (M.run r).counters 0 ≠ 0 := of_decide_eq_false hz
        apply Fin.ext
        simp [nodeOut, Ctr.ow, wFin, wBit_pos_at_zero _ (Nat.pos_of_ne_zero hc_ne)]
    · -- RightMost
      unfold Ctr.rightMost
      rw [sat_weakUntil_not_graph]
      intro r hstay
      have hpre : pre (graphOf s) (r + 1) = histOf (r + 1) (3 ^ (r + 1) - 1) := by
        rw [histOf_last]
        exact pre_eq_replicate (graphOf s) .twoToOne (r + 1) (fun k hk => hstay k (by omega))
      have hp : 1 ≤ 3 ^ (r + 1) := Nat.one_le_pow (r + 1) 3 (by decide)
      have hj : jIdx (pre (graphOf s) (r + 1)) = 3 ^ (r + 1) - 1 := by
        rw [hpre, jIdx_histOf (r + 1) (3 ^ (r + 1) - 1) (by omega)]
      have hev := three_pow_sub_one_even (r + 1)
      have he2 : (e r).2.2 = nodeOut M r (3 ^ (r + 1)) := by
        have h := hLR2 r
        rw [hj] at h
        simpa [hev, Nat.sub_add_cancel hp] using h
      have hsh : shift e r 0 = e r := by simp [shift]
      simp only [sat_atom2, hsh, he2]
      apply Fin.ext
      have hle : (M.run r).counters 0 ≤ r + 1 :=
        (cm1_counter_le_step M r).trans (by omega)
      have hpow : 3 ^ (r + 1) = 3 ^ ((M.run r).counters 0) * 3 ^ (r + 1 - (M.run r).counters 0) := by
        rw [← pow_add, Nat.add_sub_of_le hle]
      simp only [nodeOut, Ctr.ocarry, carryFin, Fin.val_zero]
      rw [hpow]
      exact carryVal_mul_pow _ _ _
  · -- InitCheck
    unfold Ctr.initCheck
    simp only [Formula.Sat, sat_atom1, (hviews 0).1, nodeOut, Ctr.oq, Ctr.ozero, CounterMachine.run,
      decide_true, and_self]
  · -- PropTrans
    unfold Ctr.propTrans
    intro r
    have hsh0 : shift e r 0 = e r := by simp [shift]
    have hsh1 : shift (shift e r) 1 0 = e (r + 1) := by simp [shift, Nat.add_comm]
    refine ⟨?_, ?_⟩
    · -- StateTrans
      unfold Ctr.stateTrans
      rw [sat_bigAnd]
      intro ψ hmem
      obtain ⟨q, _, hmem⟩ := List.mem_flatMap.mp hmem
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hmem
      simp only [Formula.Sat, sat_atom1, hsh0, hsh1, (hviews r).1, (hviews (r + 1)).1]
      rintro ⟨hq, hz⟩
      subst hq hz
      exact (cm1_step_props M (M.run r)).1
    · -- WeightTrans
      unfold Ctr.weightTrans
      rw [sat_bigAnd]
      intro ψ hmem
      obtain ⟨k, _, hmem⟩ := List.mem_flatMap.mp hmem
      obtain ⟨b, _, hmem⟩ := List.mem_flatMap.mp hmem
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hmem
      simp only [Formula.Sat]
      rintro ⟨hg, hdk, hplan⟩
      change (e (1 + r)).1.2.2 = g at hg
      rw [Nat.add_comm 1 r] at hg
      have hgs : graphOf s (r + 1) = g := hg
      have hpre_succ : pre (graphOf s) (r + 2) = pre (graphOf s) (r + 1) ++ [g] := by
        rw [show r + 2 = (r + 1) + 1 from rfl, pre_snoc, hgs]
      let j := jIdx (pre (graphOf s) (r + 1))
      let j' := jIdx (pre (graphOf s) (r + 2))
      have hl1 : (if j % 2 = 0 then (e r).2.1 else (e r).2.2) = nodeOut M r j := hLR1 r
      have hl1' : (if j' % 2 = 0 then (e (r + 1)).2.1 else (e (r + 1)).2.2) =
          nodeOut M (r + 1) j' := hLR1 (r + 1)
      have hk_eq : Ctr.dVal (decide (j % 2 = 0)) g = k.val := by
        unfold Ctr.dK Ctr.dConst at hdk
        rcases hdk with ⟨hl, hc⟩ | ⟨hnl, hc⟩
        · have hj : j % 2 = 0 := (hoil r).mp hl
          simp only [hj, decide_true]
          by_cases hd : Ctr.dVal true g = k.val
          · exact hd
          · simp only [hd, ↓reduceIte] at hc
            exact False.elim (sat_ff _ hc)
        · have hj : ¬ (j % 2 = 0) := fun h => hnl ((hoil r).mpr h)
          simp only [hj, decide_false]
          by_cases hd : Ctr.dVal false g = k.val
          · exact hd
          · simp only [hd, ↓reduceIte] at hc
            exact False.elim (sat_ff _ hc)
      have hj'_eq : j' = 3 * j + k.val := by
        rw [← hk_eq]
        dsimp only [j', j]
        rw [hpre_succ, jIdx_append_singleton]
        by_cases hj : jIdx (pre (graphOf s) (r + 1)) % 2 = 0 <;> simp [Ctr.dVal, hj]
      have hb_eq : Ctr.oa k (nodeOut M r j) = b := by
        unfold Ctr.planL at hplan
        rcases hplan with ⟨hl, ha⟩ | ⟨hnl, ha⟩
        · have hj : j % 2 = 0 := (hoil r).mp hl
          rw [sat_atom1, hsh0] at ha
          have he1 : (e r).2.1 = nodeOut M r j := by simpa [hj] using hl1
          rwa [he1] at ha
        · have hj : ¬ (j % 2 = 0) := fun h => hnl ((hoil r).mpr h)
          rw [sat_atom2, hsh0] at ha
          have he2 : (e r).2.2 = nodeOut M r j := by simpa [hj] using hl1
          rwa [he2] at ha
      have how_eq : Ctr.ow (nodeOut M (r + 1) j') = b := by
        rw [← hb_eq, hj'_eq]
        fin_cases k <;> rfl
      unfold Ctr.planL
      have hsh_next : shift (shift e r) 1 = shift e (r + 1) := by
        rw [shift_shift, Nat.add_comm]
      rw [hsh_next]
      by_cases hj' : j' % 2 = 0
      · refine Or.inl ⟨(hoil (r + 1)).mpr hj', ?_⟩
        rw [sat_atom1]
        have he1' : (shift e (r + 1) 0).2.1 = nodeOut M (r + 1) j' := by
          simp only [shift, zero_add]
          simpa [hj'] using hl1'
        rwa [he1']
      · refine Or.inr ⟨fun h => hj' ((hoil (r + 1)).mp h), ?_⟩
        rw [sat_atom2]
        have he2' : (shift e (r + 1) 0).2.2 = nodeOut M (r + 1) j' := by
          simp only [shift, zero_add]
          simpa [hj'] using hl1'
        rwa [he2']
  · -- NoHalt
    unfold Ctr.noHalt
    intro r
    rw [sat_bigAnd]
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro _ ⟨q, hqF, rfl⟩ hsat
    rw [sat_atom1] at hsat
    have hsh0 : shift e r 0 = e r := by simp [shift]
    rw [hsh0, (hviews r).1] at hsat
    change (M.run r).state = q at hsat
    exact hnh ⟨r, hsat ▸ hqF⟩

/-! ### Part 7: Soundness (`Realizable → ¬ M.Halts`) -/

def simCnt1 {Q : Type} (M : CounterMachine Q 1) (rowQ : ℕ → Q) (rowZ : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      match M.instr (rowQ n) with
      | .inc _ _ => simCnt1 M rowQ rowZ n + 1
      | .dec _ _ _ => if rowZ n then simCnt1 M rowQ rowZ n else simCnt1 M rowQ rowZ n - 1

lemma soundness {Q : Type} [Fintype Q] [DecidableEq Q] (M : CounterMachine Q 1)
    (hreal : Realizable Set.univ (counterFormula M)) : ¬ M.Halts := by
  rcases hreal with ⟨f, hf⟩
  have hsat_all : ∀ s : ℕ → Signal Unit Unit, (counterFormula M).Sat (exec f s) :=
    fun s => hf s (Set.mem_univ _)
  let hAt (n j : ℕ) : List CommGraph := histOf (n + 1) j
  let y1At (n j : ℕ) : CtrOut Q := f.f1 (view1 (toSig (hAt n j)))
  let y2At (n j : ℕ) : CtrOut Q := f.f2 (view2 (toSig (hAt n j)))
  let yL (n j : ℕ) : CtrOut Q := if j % 2 = 0 then y1At n j else y2At n j
  let yR (n j : ℕ) : CtrOut Q := if j % 2 = 0 then y2At n j else y1At n j
  have hlink : ∀ n j, j + 1 < 3 ^ (n + 1) → yR n j = yL n (j + 1) := by
    intro n j hj
    have hsv := histOf_shared_view (n + 1) j hj
    rcases (show j % 2 = 0 ∨ j % 2 = 1 by omega) with hp | hp
    · have hp1 : ¬ ((j + 1) % 2 = 0) := by omega
      simp only [yR, yL, y1At, y2At, hAt, hp, hp1, ↓reduceIte] at hsv ⊢
      exact congrArg f.f2 hsv
    · have hp0 : ¬ (j % 2 = 0) := by omega
      have hp1 : (j + 1) % 2 = 0 := by omega
      simp only [yR, yL, y1At, y2At, hAt, hp0, hp1, ↓reduceIte] at hsv ⊢
      exact congrArg f.f1 hsv
  have hexec_at : ∀ (h : List CommGraph) (n : ℕ), h.length = n + 1 →
      (exec f (extendSig h) n).2 = (f.f1 (view1 (toSig h)), f.f2 (view2 (toSig h))) := by
    intro h n hlen
    have hp := pre_extendSig h (n + 1) (by omega)
    have ht : h.take (n + 1) = h := List.take_of_length_le (by omega)
    rw [ht] at hp
    simp only [exec, hp]
  have hoil_ext : ∀ (s : ℕ → Signal Unit Unit) (n : ℕ),
      (Ctr.oneIsLeft : CtrFormula Q).Sat (shift (exec f s) n) ↔
        jIdx (pre (graphOf s) (n + 1)) % 2 = 0 :=
    fun s n => oneIsLeft_iff_even f s (hsat_all s).1 n
  have hpre_graph_ext : ∀ (h : List CommGraph) (r : ℕ), r ≤ h.length →
      pre (graphOf (extendSig h)) r = h.take r := by
    intro h r hr
    apply List.ext_getElem
    · simp [pre, hr]
    · intro i h1 h2
      simp only [pre, List.length_ofFn] at h1
      have hi : i < h.length := by omega
      simp [pre, graphOf, extendSig, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hpre_hAt : ∀ n j, pre (graphOf (extendSig (hAt n j))) (n + 1) = hAt n j := by
    intro n j
    rw [hpre_graph_ext (hAt n j) (n + 1) (by simp [hAt])]
    simp [hAt]
  let rowQ (n : ℕ) : Q := Ctr.oq (y1At n 0)
  let rowZ (n : ℕ) : Bool := Ctr.ozero (y1At n 0)
  have hpair_agr : ∀ n j, j < 3 ^ (n + 1) →
      Ctr.oq (y1At n j) = Ctr.oq (y2At n j) ∧ Ctr.ozero (y1At n j) = Ctr.ozero (y2At n j) := by
    intro n j _
    let s := extendSig (hAt n j)
    have hpa := (hsat_all s).2.1 n
    simp only [Formula.Sat, sat_atom12] at hpa
    have hsh : shift (exec f s) n 0 = exec f s n := by simp [shift]
    rw [hsh] at hpa
    have hex := hexec_at (hAt n j) n (histOf_length (n + 1) j)
    rwa [show s = extendSig (hAt n j) from rfl, hex] at hpa
  have huniform : ∀ n j, j < 3 ^ (n + 1) →
      Ctr.oq (yL n j) = rowQ n ∧ Ctr.ozero (yL n j) = rowZ n ∧
      Ctr.oq (yR n j) = rowQ n ∧ Ctr.ozero (yR n j) = rowZ n := by
    intro n j hj
    induction j with
    | zero =>
      have hp := hpair_agr n 0 hj
      exact ⟨rfl, rfl, hp.1.symm, hp.2.symm⟩
    | succ j ih =>
      obtain ⟨_, _, hqR, hzR⟩ := ih (by omega)
      have hl := hlink n j hj
      have hp := hpair_agr n (j + 1) hj
      have hqL : Ctr.oq (yL n (j + 1)) = rowQ n := by rw [← hl]; exact hqR
      have hzL : Ctr.ozero (yL n (j + 1)) = rowZ n := by rw [← hl]; exact hzR
      refine ⟨hqL, hzL, ?_, ?_⟩
      · by_cases hev : (j + 1) % 2 = 0 <;> simp only [yL, yR, hev, ↓reduceIte] at hqL ⊢
        · exact hp.1.symm.trans hqL
        · exact hp.1.trans hqL
      · by_cases hev : (j + 1) % 2 = 0 <;> simp only [yL, yR, hev, ↓reduceIte] at hzL ⊢
        · exact hp.2.symm.trans hzL
        · exact hp.2.trans hzL
  have hbal_edge : ∀ n j, j < 3 ^ (n + 1) →
      Ctr.planSum (yL n j) + (Ctr.ocarry (yL n j)).val =
        Ctr.mult M (rowQ n) (rowZ n) * (Ctr.ow (yL n j)).val + (Ctr.ocarry (yR n j)).val := by
    intro n j hj
    let s := extendSig (hAt n j)
    have hls := (hsat_all s).2.2.1 n
    rw [sat_bigAnd] at hls
    have hinst := hls _ (List.mem_flatMap.mpr ⟨rowQ n, mem_states _,
      List.mem_map.mpr ⟨rowZ n, mem_bools _, rfl⟩⟩)
    have hj_eq : jIdx (pre (graphOf s) (n + 1)) = j := by
      change jIdx (pre (graphOf (extendSig (hAt n j))) (n + 1)) = j
      rw [hpre_hAt n j, jIdx_histOf (n + 1) j hj]
    have hoil := hoil_ext s n
    rw [hj_eq] at hoil
    have hsh : shift (exec f s) n 0 = exec f s n := by simp [shift]
    have hex := hexec_at (hAt n j) n (histOf_length (n + 1) j)
    have hex1 : (exec f s n).2.1 = y1At n j := congrArg Prod.fst hex
    have hex2 : (exec f s n).2.2 = y2At n j := congrArg Prod.snd hex
    obtain ⟨hqL, hzL, _, _⟩ := huniform n j hj
    by_cases hev : j % 2 = 0
    · have h1 := hinst.1 (hoil.mpr hev)
      unfold Ctr.psi1 at h1
      simp only [Formula.Sat, sat_atom1, sat_atom12, hsh, hex1, hex2] at h1
      simp only [yL, yR, hev, ↓reduceIte] at hqL hzL ⊢
      exact h1 ⟨hqL, hzL⟩
    · have h2 := hinst.2 (fun h => hev (hoil.mp h))
      unfold Ctr.psi2 at h2
      simp only [Formula.Sat, sat_atom2, sat_atom12, hsh, hex1, hex2] at h2
      simp only [yL, yR, hev, ↓reduceIte] at hqL hzL ⊢
      exact h2 ⟨hqL, hzL⟩
  have hleft_ray : ∀ n, (Ctr.ocarry (yL n 0)).val = 0 ∧
      (rowZ n = false → (Ctr.ow (yL n 0)).val = 0) := by
    intro n
    let s : ℕ → Signal Unit Unit := fun _ => ((), (), .oneToTwo)
    have hlm := (hsat_all s).2.2.2.1.2.1
    unfold Ctr.leftMost at hlm
    rw [sat_weakUntil_not_graph] at hlm
    have hn := hlm n (fun _ _ => rfl)
    have hsh : shift (exec f s) n 0 = exec f s n := by simp [shift]
    have hp : pre s (n + 1) = toSig (hAt n 0) := by
      rw [pre_const_sig, ← histOf_zero]
    simp only [Formula.Sat, sat_atom1, hsh, exec, hp, yL, y1At, Nat.zero_mod, ↓reduceIte,
      rowZ] at hn ⊢
    exact ⟨congrArg Fin.val hn.1, fun hz => congrArg Fin.val (hn.2 hz)⟩
  have hright_ray : ∀ n, (Ctr.ocarry (yR n (3 ^ (n + 1) - 1))).val = 0 := by
    intro n
    let s : ℕ → Signal Unit Unit := fun _ => ((), (), .twoToOne)
    have hrm := (hsat_all s).2.2.2.1.2.2
    unfold Ctr.rightMost at hrm
    rw [sat_weakUntil_not_graph] at hrm
    have hn := hrm n (fun _ _ => rfl)
    have hsh : shift (exec f s) n 0 = exec f s n := by simp [shift]
    have hp : pre s (n + 1) = toSig (hAt n (3 ^ (n + 1) - 1)) := by
      rw [pre_const_sig, ← histOf_last]
    have hev := three_pow_sub_one_even (n + 1)
    simp only [sat_atom2, hsh, exec, hp, yR, y2At, hev, ↓reduceIte] at hn ⊢
    exact congrArg Fin.val hn
  have hchild_wt : ∀ n j (k : Fin 3), j < 3 ^ (n + 1) →
      Ctr.ow (yL (n + 1) (3 * j + k.val)) = Ctr.oa k (yL n j) := by
    intro n j k hj
    let g := stepGraph (decide (j % 2 = 0)) k.val
    have hchild_hist : hAt (n + 1) (3 * j + k.val) = hAt n j ++ [g] := by
      have hk := k.isLt
      have hdiv : (3 * j + k.val) / 3 = j := by omega
      have hmod : (3 * j + k.val) % 3 = k.val := by omega
      simp [hAt, histOf, hdiv, hmod, g]
    let s := extendSig (hAt (n + 1) (3 * j + k.val))
    have hwt := ((hsat_all s).2.2.2.2.2.1 n).2
    unfold Ctr.weightTrans at hwt
    rw [sat_bigAnd] at hwt
    set b := Ctr.oa k (yL n j)
    have hinst := hwt _ (List.mem_flatMap.mpr ⟨k, List.mem_finRange k,
      List.mem_flatMap.mpr ⟨b, List.mem_finRange b,
        List.mem_map.mpr ⟨g, mem_graphs g, rfl⟩⟩⟩)
    have hpre1 : pre (graphOf s) (n + 1) = hAt n j := by
      change pre (graphOf (extendSig (hAt (n + 1) (3 * j + k.val)))) (n + 1) = hAt n j
      have hp := hpre_graph_ext (hAt (n + 1) (3 * j + k.val)) (n + 1) (by simp [hAt])
      rw [hp, hchild_hist, List.take_left' (histOf_length (n + 1) j)]
    have hpre2 : pre (graphOf s) (n + 2) = hAt (n + 1) (3 * j + k.val) :=
      hpre_hAt (n + 1) (3 * j + k.val)
    have hj1 : jIdx (pre (graphOf s) (n + 1)) = j := by
      rw [hpre1, jIdx_histOf (n + 1) j hj]
    have hj2 : jIdx (pre (graphOf s) (n + 2)) = 3 * j + k.val := by
      have hlt2 : 3 * j + k.val < 3 ^ (n + 2) := by
        have hk := k.isLt
        rw [pow_succ]
        omega
      rw [hpre2, jIdx_histOf (n + 2) (3 * j + k.val) hlt2]
    have hg_at : (shift (shift (exec f s) n) 1 0).1.2.2 = g := by
      have hsh : shift (shift (exec f s) n) 1 0 = exec f s (n + 1) := by
        simp [shift, Nat.add_comm]
      rw [hsh]
      simp only [exec, s, extendSig, hchild_hist]
      have hlen : (hAt n j).length = n + 1 := histOf_length (n + 1) j
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp [hlen]
    have hdk_at : (Ctr.dK k g : CtrFormula Q).Sat (shift (exec f s) n) := by
      unfold Ctr.dK Ctr.dConst
      have hd := dVal_stepGraph (decide (j % 2 = 0)) k.val k.isLt
      have hoil1 := hoil_ext s n
      rw [hj1] at hoil1
      by_cases hev : j % 2 = 0
      · simp only [g, hev, decide_true] at hd ⊢
        exact Or.inl ⟨hoil1.mpr hev, by rw [if_pos hd]; exact sat_tt _⟩
      · simp only [g, hev, decide_false] at hd ⊢
        exact Or.inr ⟨fun h => hev (hoil1.mp h), by rw [if_pos hd]; exact sat_tt _⟩
    have hex1 : (exec f s n).2 = (y1At n j, y2At n j) := by
      have hp : pre s (n + 1) = toSig (hAt n j) := by
        rw [pre_unit_toSig, hpre1]
      simp [exec, hp, y1At, y2At]
    have hex2 : (exec f s (n + 1)).2 =
        (y1At (n + 1) (3 * j + k.val), y2At (n + 1) (3 * j + k.val)) := by
      have hp : pre s (n + 2) = toSig (hAt (n + 1) (3 * j + k.val)) := by
        rw [pre_unit_toSig, hpre2]
      simp [exec, hp, y1At, y2At]
    have hplan_at : (Ctr.planL (Ctr.oa k) b : CtrFormula Q).Sat (shift (exec f s) n) := by
      unfold Ctr.planL
      have hoil1 := hoil_ext s n
      rw [hj1] at hoil1
      have hsh0 : shift (exec f s) n 0 = exec f s n := by simp [shift]
      by_cases hev : j % 2 = 0
      · refine Or.inl ⟨hoil1.mpr hev, ?_⟩
        rw [sat_atom1, hsh0, congrArg Prod.fst hex1]
        simp [b, yL, hev]
      · refine Or.inr ⟨fun h => hev (hoil1.mp h), ?_⟩
        rw [sat_atom2, hsh0, congrArg Prod.snd hex1]
        simp [b, yL, hev]
    have hnext := hinst ⟨hg_at, hdk_at, hplan_at⟩
    change (Ctr.planL Ctr.ow b : CtrFormula Q).Sat (shift (shift (exec f s) n) 1) at hnext
    have hsh1 : shift (shift (exec f s) n) 1 = shift (exec f s) (n + 1) := by
      rw [shift_shift, Nat.add_comm]
    rw [hsh1] at hnext
    unfold Ctr.planL at hnext
    have hoil2 := hoil_ext s (n + 1)
    rw [hj2] at hoil2
    have hsh2 : shift (exec f s) (n + 1) 0 = exec f s (n + 1) := by simp [shift]
    rcases hnext with ⟨hl, ha⟩ | ⟨hnl, ha⟩
    · have hev2 : (3 * j + k.val) % 2 = 0 := hoil2.mp hl
      rw [sat_atom1, hsh2, congrArg Prod.fst hex2] at ha
      simpa [yL, hev2] using ha
    · have hev2 : ¬ ((3 * j + k.val) % 2 = 0) := fun h => hnl (hoil2.mpr h)
      rw [sat_atom2, hsh2, congrArg Prod.snd hex2] at ha
      simpa [yL, hev2] using ha
  let W (n : ℕ) : ℕ := sumRange (3 ^ (n + 1)) (fun j => (Ctr.ow (yL n j)).val)
  have hW_step : ∀ n, W (n + 1) = Ctr.mult M (rowQ n) (rowZ n) * W n := by
    intro n
    have hp : 1 ≤ 3 ^ (n + 1) := Nat.one_le_pow (n + 1) 3 (by decide)
    have htel := sumRange_telescope (3 ^ (n + 1) - 1) (Ctr.mult M (rowQ n) (rowZ n))
      (fun j => Ctr.planSum (yL n j)) (fun j => (Ctr.ow (yL n j)).val)
      (fun j => (Ctr.ocarry (yL n j)).val) (fun j => (Ctr.ocarry (yR n j)).val)
      (fun j hj => hbal_edge n j (by omega))
      (fun j hj => congrArg (fun y => (Ctr.ocarry y).val) (hlink n j (by omega)))
    rw [Nat.sub_add_cancel hp, (hleft_ray n).1, hright_ray n, add_zero, add_zero] at htel
    have hsum_child : W (n + 1) = sumRange (3 ^ (n + 1)) (fun j => Ctr.planSum (yL n j)) := by
      dsimp only [W]
      rw [pow_succ', sumRange_mul_three]
      have hcongr : ∀ L, L ≤ 3 ^ (n + 1) →
          sumRange L (fun j => (Ctr.ow (yL (n + 1) (3 * j))).val +
            (Ctr.ow (yL (n + 1) (3 * j + 1))).val + (Ctr.ow (yL (n + 1) (3 * j + 2))).val) =
          sumRange L (fun j => Ctr.planSum (yL n j)) := by
        intro L hL
        induction L with
        | zero => rfl
        | succ L ih =>
          simp only [sumRange, ih (by omega)]
          have h0 := hchild_wt n L 0 (by omega)
          have h1 := hchild_wt n L 1 (by omega)
          have h2 := hchild_wt n L 2 (by omega)
          simp only [Fin.val_zero, add_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
          simp [Ctr.planSum, h0, h1, h2]
      exact hcongr (3 ^ (n + 1)) le_rfl
    rw [hsum_child, htel]
  have hzero_guard : ∀ n, rowZ n = true ↔ W n = 3 ^ (n + 1) := by
    intro n
    constructor
    · intro hz
      have hall : ∀ j < 3 ^ (n + 1), (Ctr.ow (yL n j)).val = 1 := by
        intro j hj
        let s := extendSig (hAt n j)
        have hzi := (hsat_all s).2.2.2.1.1 n
        have hj_eq : jIdx (pre (graphOf s) (n + 1)) = j := by
          change jIdx (pre (graphOf (extendSig (hAt n j))) (n + 1)) = j
          rw [hpre_hAt n j, jIdx_histOf (n + 1) j hj]
        have hoil := hoil_ext s n
        rw [hj_eq] at hoil
        have hsh : shift (exec f s) n 0 = exec f s n := by simp [shift]
        have hex := hexec_at (hAt n j) n (histOf_length (n + 1) j)
        have hex1 : (exec f s n).2.1 = y1At n j := congrArg Prod.fst hex
        have hex2 : (exec f s n).2.2 = y2At n j := congrArg Prod.snd hex
        have hzL : Ctr.ozero (yL n j) = true := (huniform n j hj).2.1.trans hz
        rcases hzi with ⟨hl, h1⟩ | ⟨hnl, h2⟩
        · have hev : j % 2 = 0 := hoil.mp hl
          simp only [Formula.Sat, sat_atom1, hsh, hex1] at h1
          simp only [yL, hev, ↓reduceIte] at hzL ⊢
          exact congrArg Fin.val (h1 hzL)
        · have hev : ¬ (j % 2 = 0) := fun h => hnl (hoil.mpr h)
          simp only [Formula.Sat, sat_atom2, hsh, hex2] at h2
          simp only [yL, hev, ↓reduceIte] at hzL ⊢
          exact congrArg Fin.val (h2 hzL)
      have hcongr : ∀ L, L ≤ 3 ^ (n + 1) →
          sumRange L (fun j => (Ctr.ow (yL n j)).val) = sumRange L (fun _ => 1) := by
        intro L hL
        induction L with
        | zero => rfl
        | succ L ih => simp [sumRange, ih (by omega), hall L (by omega)]
      dsimp only [W]
      rw [hcongr (3 ^ (n + 1)) le_rfl, sumRange_const_one]
    · intro hW
      cases hzn : rowZ n with
      | true => rfl
      | false =>
        have hw0 : (Ctr.ow (yL n 0)).val = 0 := (hleft_ray n).2 hzn
        have hlt := sumRange_lt_of_zero_head (3 ^ (n + 1))
          (fun j => (Ctr.ow (yL n j)).val) (pow_pos (by decide) _) hw0
          (fun j _ => by have := (Ctr.ow (yL n j)).isLt; omega)
        dsimp only [W] at hW
        omega
  have hinit : rowQ 0 = M.init ∧ rowZ 0 = true := by
    let s : ℕ → Signal Unit Unit := fun _ => ((), (), .oneToTwo)
    have hic := (hsat_all s).2.2.2.2.1
    have hp : pre s 1 = toSig (hAt 0 0) := by
      rw [pre_const_sig, ← histOf_zero]
    unfold Ctr.initCheck at hic
    simpa [Formula.Sat, sat_atom1, exec, hp, rowQ, rowZ, y1At] using hic
  have hW0 : W 0 = 3 := (hzero_guard 0).mp hinit.2
  have hQ_step : ∀ n, rowQ (n + 1) = Ctr.nextState M (rowQ n) (rowZ n) := by
    intro n
    let s : ℕ → Signal Unit Unit := fun _ => ((), (), .oneToTwo)
    have hst := ((hsat_all s).2.2.2.2.2.1 n).1
    unfold Ctr.stateTrans at hst
    rw [sat_bigAnd] at hst
    have hinst := hst _ (List.mem_flatMap.mpr ⟨rowQ n, mem_states _,
      List.mem_map.mpr ⟨rowZ n, mem_bools _, rfl⟩⟩)
    have hsh0 : shift (exec f s) n 0 = exec f s n := by simp [shift]
    have hsh1 : shift (shift (exec f s) n) 1 0 = exec f s (n + 1) := by
      simp [shift, Nat.add_comm]
    have hp1 : pre s (n + 1) = toSig (hAt n 0) := by rw [pre_const_sig, ← histOf_zero]
    have hp2 : pre s (n + 2) = toSig (hAt (n + 1) 0) := by rw [pre_const_sig, ← histOf_zero]
    simp only [Formula.Sat, sat_atom1, hsh0, hsh1, exec, hp1, hp2] at hinst
    exact hinst ⟨rfl, rfl⟩
  let sc := simCnt1 M rowQ rowZ
  have hinv := forced_invariant W rowZ (fun n => Ctr.mult M (rowQ n) (rowZ n)) sc
    rfl hW0 hzero_guard hW_step (fun n => by
      dsimp only [sc]
      rw [simCnt1]
      cases hinstr : M.instr (rowQ n) with
      | inc _ _ => simp [Ctr.mult, hinstr]
      | dec _ _ _ =>
        cases rowZ n <;> simp [Ctr.mult, hinstr])
  have hrun_eq : ∀ n, rowQ n = (M.run n).state ∧ sc n = (M.run n).counters 0 := by
    intro n
    induction n with
    | zero => exact ⟨hinit.1, rfl⟩
    | succ n ih =>
      have hzn_eq : rowZ n = decide ((M.run n).counters 0 = 0) := by
        have hziff := (hinv n).2
        rw [ih.2] at hziff
        cases h : rowZ n <;> simp_all
      have hsp := (cm1_step_props M (M.run n)).1
      refine ⟨?_, ?_⟩
      · rw [hQ_step n, ih.1, hzn_eq]
        exact hsp.symm
      · dsimp only [sc] at ih ⊢
        rw [simCnt1, ih.1, ih.2, hzn_eq]
        change _ = (M.step (M.run n)).counters 0
        unfold CounterMachine.step
        cases hinstr : M.instr (M.run n).state with
        | inc i q' =>
          have hi : i = 0 := Subsingleton.elim i 0
          subst hi
          simp [Function.update_self]
        | dec i q' q'' =>
          have hi : i = 0 := Subsingleton.elim i 0
          subst hi
          by_cases hc : (M.run n).counters 0 = 0 <;> simp [hc, Function.update_self]
  rintro ⟨n, hhalt⟩
  let s : ℕ → Signal Unit Unit := fun _ => ((), (), .oneToTwo)
  have hnh_all := (hsat_all s).2.2.2.2.2.2
  unfold Ctr.noHalt at hnh_all
  have hnh := hnh_all n
  rw [sat_bigAnd] at hnh
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hnh
  have hnot := hnh _ ⟨(M.run n).state, hhalt, rfl⟩
  simp only [Formula.Sat, sat_atom1] at hnot
  have hsh0 : shift (exec f s) n 0 = exec f s n := by simp [shift]
  have hp : pre s (n + 1) = toSig (hAt n 0) := by rw [pre_const_sig, ← histOf_zero]
  rw [hsh0] at hnot
  simp only [exec, hp] at hnot
  exact hnot (hrun_eq n).1

end DistLTLSynth.Char.Thm612Aux

open DistLTLSynth.Char DistLTLSynth.Char.Thm612Aux in
theorem solution {Q : Type} [Fintype Q] [DecidableEq Q] (M : CounterMachine Q 1) :
    ¬ M.Halts ↔ Realizable Set.univ (counterFormula M) :=
  ⟨completeness M, soundness M⟩
