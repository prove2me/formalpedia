-- Prove2me | solution 1 for CannonFloydParry.exists_mulEquiv_F_PIPPlusSet_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T20:45:14.394544+00:00
-- url     : https://prove2.me/submissions/f6966b0e-50c2-45bc-98ef-009efd50001c

import Definitions.Def_CannonFloydParry_PIP
import Mathlib
import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Theorems.Thm_CannonFloydParry_exists_isReduced_represents
import Theorems.Thm_CannonFloydParry_exists_mulEquiv_PIPPlusSet_one_PIPPlus01Set

/-!
# Farey and dyadic nodes (for Minkowski's question-mark function)

The dyadic interval `dyadicNode w` reached from `[0,1]` by halving along a path, the Farey
invariants of `fareyNode w`, the increasing integral projective parametrization `phi I` of a
Farey interval, and the covering lemmas.
-/

namespace CannonFloydParry.S7

open FracInterval Set

/-- The dyadic interval reached from `[0,1]` by halving along `w` (`false` = left half,
`true` = right half), read from the root as in `fareyNode`. -/
noncomputable def dyadicNode (w : List Bool) : ℝ × ℝ :=
  w.foldl (fun p b => if b then ((p.1 + p.2) / 2, p.2) else (p.1, (p.1 + p.2) / 2)) (0, 1)

/-- The increasing linear fractional map `[0,1] → [a/b, c/d]`,
`s ↦ (a (1 - s) + c s) / (b (1 - s) + d s)`; in the coordinate `(s, 1)` it is given by the
integer matrix `!![c - a, a; d - b, b]` (determinant `bc - ad`). -/
noncomputable def phi (I : FracInterval) (s : ℝ) : ℝ :=
  ((I.a : ℝ) * (1 - s) + I.c * s) / ((I.b : ℝ) * (1 - s) + I.d * s)

namespace Mink

theorem fareyNode_nil : fareyNode [] = ⟨0, 1, 1, 1⟩ := rfl

theorem fareyNode_append (w : List Bool) (b : Bool) :
    fareyNode (w ++ [b]) = if b then (fareyNode w).rightPart else (fareyNode w).leftPart := by
  simp [fareyNode, List.foldl_append]

theorem fareyNode_append_false (w : List Bool) :
    fareyNode (w ++ [false]) = (fareyNode w).leftPart := by
  simp [fareyNode_append]

theorem fareyNode_append_true (w : List Bool) :
    fareyNode (w ++ [true]) = (fareyNode w).rightPart := by
  simp [fareyNode_append]

theorem dyadicNode_nil : dyadicNode [] = (0, 1) := rfl

theorem dyadicNode_append_false (w : List Bool) :
    dyadicNode (w ++ [false]) =
      ((dyadicNode w).1, ((dyadicNode w).1 + (dyadicNode w).2) / 2) := by
  simp [dyadicNode, List.foldl_append]

theorem dyadicNode_append_true (w : List Bool) :
    dyadicNode (w ++ [true]) =
      (((dyadicNode w).1 + (dyadicNode w).2) / 2, (dyadicNode w).2) := by
  simp [dyadicNode, List.foldl_append]

theorem dyadicNode_width (w : List Bool) :
    (dyadicNode w).2 - (dyadicNode w).1 = (1 / 2 : ℝ) ^ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [dyadicNode_nil]
  | append_singleton w b ih =>
    cases b
    · rw [dyadicNode_append_false]; simp only [List.length_append, List.length_singleton,
        pow_succ]; rw [← ih]; ring
    · rw [dyadicNode_append_true]; simp only [List.length_append, List.length_singleton,
        pow_succ]; rw [← ih]; ring

theorem dyadicNode_bounds (w : List Bool) :
    0 ≤ (dyadicNode w).1 ∧ (dyadicNode w).1 < (dyadicNode w).2 ∧ (dyadicNode w).2 ≤ 1 := by
  induction w using List.reverseRecOn with
  | nil => simp [dyadicNode_nil]
  | append_singleton w b ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    cases b
    · rw [dyadicNode_append_false]; exact ⟨h1, by simp; linarith, by simp; linarith⟩
    · rw [dyadicNode_append_true]; exact ⟨by simp; linarith, by simp; linarith, h3⟩

/-- The dyadic intervals of each depth cover `[0,1]`. -/
theorem dyadic_cover (n : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    ∃ w : List Bool, w.length = n ∧ (dyadicNode w).1 ≤ y ∧ y ≤ (dyadicNode w).2 := by
  induction n with
  | zero => exact ⟨[], rfl, by simpa [dyadicNode_nil] using hy.1, by simpa [dyadicNode_nil]
      using hy.2⟩
  | succ n ih =>
    obtain ⟨w, hw, h1, h2⟩ := ih
    by_cases hm : y ≤ ((dyadicNode w).1 + (dyadicNode w).2) / 2
    · exact ⟨w ++ [false], by simp [hw], by rw [dyadicNode_append_false]; exact h1,
        by rw [dyadicNode_append_false]; exact hm⟩
    · exact ⟨w ++ [true], by simp [hw], by rw [dyadicNode_append_true]; simp only; linarith,
        by rw [dyadicNode_append_true]; exact h2⟩

/-- The Farey invariants of a node of depth `n`. -/
structure Inv (I : FracInterval) (n : ℕ) : Prop where
  hb : 1 ≤ I.b
  hd : 1 ≤ I.d
  hab : I.a ≤ I.b
  hcd : I.c ≤ I.d
  hdet : I.b * I.c = I.a * I.d + 1
  hsum : n + 2 ≤ I.b + I.d

theorem inv_fareyNode (w : List Bool) : Inv (fareyNode w) w.length := by
  induction w using List.reverseRecOn with
  | nil => rw [fareyNode_nil]; exact ⟨le_rfl, le_rfl, by norm_num, le_rfl, rfl, le_rfl⟩
  | append_singleton w b ih =>
    obtain ⟨hb, hd, hab, hcd, hdet, hsum⟩ := ih
    cases b
    · rw [fareyNode_append_false]
      refine ⟨hb, by simp [leftPart]; omega, hab, by simp [leftPart]; omega, ?_,
        by simp [leftPart]; omega⟩
      simp only [leftPart]; rw [Nat.mul_add, hdet, Nat.mul_add]; ring
    · rw [fareyNode_append_true]
      refine ⟨by simp [rightPart]; omega, hd, by simp [rightPart]; omega, hcd, ?_,
        by simp [rightPart]; omega⟩
      simp only [rightPart]; rw [Nat.add_mul, hdet, Nat.add_mul]; ring

theorem isFarey_fareyNode (w : List Bool) : (fareyNode w).IsFarey := by
  obtain ⟨hb, hd, hab, hcd, hdet, -⟩ := inv_fareyNode w
  refine ⟨hb, ?_, hd, hab, hcd, ?_⟩
  · rcases Nat.eq_zero_or_pos (fareyNode w).c with h | h
    · rw [h] at hdet; simp at hdet
    · exact h
  · have : ((fareyNode w).b : ℤ) * (fareyNode w).c = (fareyNode w).a * (fareyNode w).d + 1 := by
      exact_mod_cast hdet
    linarith

section real

variable {I : FracInterval} {n : ℕ}

theorem Inv.hdetR (h : Inv I n) : (I.b : ℝ) * I.c = I.a * I.d + 1 := by
  exact_mod_cast h.hdet

theorem Inv.bpos (h : Inv I n) : (0 : ℝ) < I.b := by
  have := h.hb; exact_mod_cast this

theorem Inv.dpos (h : Inv I n) : (0 : ℝ) < I.d := by
  have := h.hd; exact_mod_cast this

theorem Inv.cdR (h : Inv I n) : (I.c : ℝ) ≤ I.d := by exact_mod_cast h.hcd

theorem Inv.width (h : Inv I n) : I.hi - I.lo = 1 / ((I.b : ℝ) * I.d) := by
  have hb := h.bpos; have hd := h.dpos; have := h.hdetR
  simp only [FracInterval.hi, FracInterval.lo]
  field_simp
  linarith

theorem Inv.width_le (h : Inv I n) : I.hi - I.lo ≤ 1 / ((n : ℝ) + 1) := by
  rw [h.width]
  have hb := h.hb; have hd := h.hd; have hs := h.hsum
  have key : n + 1 ≤ I.b * I.d := by nlinarith
  have key' : (n : ℝ) + 1 ≤ (I.b : ℝ) * I.d := by exact_mod_cast key
  exact one_div_le_one_div_of_le (by positivity) key'

theorem Inv.lo_lt_hi (h : Inv I n) : I.lo < I.hi := by
  have := h.width; have hb := h.bpos; have hd := h.dpos
  have : 0 < 1 / ((I.b : ℝ) * I.d) := by positivity
  linarith

theorem Inv.lo_nonneg (_h : Inv I n) : 0 ≤ I.lo := by
  simp only [FracInterval.lo]; positivity

theorem Inv.hi_le_one (h : Inv I n) : I.hi ≤ 1 := by
  simp only [FracInterval.hi]; rw [div_le_one h.dpos]; exact h.cdR

theorem phi_zero (I : FracInterval) : phi I 0 = I.lo := by
  simp [phi, FracInterval.lo]

theorem phi_one (I : FracInterval) : phi I 1 = I.hi := by
  simp [phi, FracInterval.hi]

theorem phi_root (s : ℝ) : phi (fareyNode []) s = s := by
  simp [phi, fareyNode_nil]

theorem phi_leftPart (h : Inv I n) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    phi I.leftPart s = phi I (s / (1 + s)) := by
  have hb := h.bpos; have hd := h.dpos
  have h1 : (0 : ℝ) < 1 + s := by linarith [hs.1]
  simp only [phi, leftPart]
  push_cast
  have e1 : (I.a : ℝ) * (1 - s / (1 + s)) + I.c * (s / (1 + s)) = (I.a + I.c * s) / (1 + s) := by
    field_simp; ring
  have e2 : (I.b : ℝ) * (1 - s / (1 + s)) + I.d * (s / (1 + s)) = (I.b + I.d * s) / (1 + s) := by
    field_simp; ring
  rw [e1, e2, div_div_div_cancel_right₀ h1.ne']
  congr 1 <;> ring

theorem phi_rightPart (h : Inv I n) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    phi I.rightPart s = phi I (1 / (2 - s)) := by
  have hb := h.bpos; have hd := h.dpos
  have h1 : (0 : ℝ) < 2 - s := by linarith [hs.2]
  simp only [phi, rightPart]
  push_cast
  have e1 : (I.a : ℝ) * (1 - 1 / (2 - s)) + I.c * (1 / (2 - s)) =
      (I.a * (1 - s) + I.c) / (2 - s) := by
    field_simp; ring
  have e2 : (I.b : ℝ) * (1 - 1 / (2 - s)) + I.d * (1 / (2 - s)) =
      (I.b * (1 - s) + I.d) / (2 - s) := by
    field_simp; ring
  rw [e1, e2, div_div_div_cancel_right₀ h1.ne']
  congr 1 <;> ring

end real

/-- The Farey intervals of each depth cover `[0,1]`. -/
theorem farey_cover (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ w : List Bool, w.length = n ∧ (fareyNode w).lo ≤ x ∧ x ≤ (fareyNode w).hi := by
  induction n with
  | zero => exact ⟨[], rfl, by simpa [fareyNode_nil, FracInterval.lo] using hx.1,
      by simpa [fareyNode_nil, FracInterval.hi] using hx.2⟩
  | succ n ih =>
    obtain ⟨w, hw, h1, h2⟩ := ih
    by_cases hm : x ≤ (fareyNode w).leftPart.hi
    · exact ⟨w ++ [false], by simp [hw], by rw [fareyNode_append_false]; exact h1,
        by rw [fareyNode_append_false]; exact hm⟩
    · refine ⟨w ++ [true], by simp [hw], ?_, ?_⟩
      · rw [fareyNode_append_true]
        have : (fareyNode w).rightPart.lo = (fareyNode w).leftPart.hi := rfl
        rw [this]; linarith
      · rw [fareyNode_append_true]; exact h2

end Mink

end CannonFloydParry.S7

/-!
# Minkowski's question-mark function

`mink` is constructed as the pointwise limit of the iterates of the contraction
`T f x = f (x / (1 - x)) / 2` (`x ≤ 1/2`), `1/2 + f (2 - 1/x) / 2` (`x > 1/2`), starting from the
identity.  It satisfies `mink (s / (1 + s)) = mink s / 2` and `mink (1 / (2 - s)) = 1/2 + mink s / 2`
on `[0,1]`, whence the self-similarity on every Farey node, the endpoint values, strict
monotonicity (Farey widths tend to `0`), continuity (monotone with dense range) and surjectivity.
-/

namespace CannonFloydParry.S7

open FracInterval Set Filter Topology

namespace Mink

/-- One step of the defining functional equation. -/
noncomputable def T (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 1 / 2 then f (x / (1 - x)) / 2 else 1 / 2 + f (2 - 1 / x) / 2

/-- The iterates of `T` from the identity. -/
noncomputable def approx : ℕ → ℝ → ℝ
  | 0 => id
  | n + 1 => T (approx n)

/-- Monotone on `[0,1]`, fixing `0` and `1`. -/
def Good (f : ℝ → ℝ) : Prop := MonotoneOn f (Icc 0 1) ∧ f 0 = 0 ∧ f 1 = 1

theorem Good.mem {f : ℝ → ℝ} (hf : Good f) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    f x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hm, h0, h1⟩ := hf
  exact ⟨h0 ▸ hm ⟨le_rfl, zero_le_one⟩ hx hx.1, h1 ▸ hm hx ⟨zero_le_one, le_rfl⟩ hx.2⟩

theorem mapL {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (h : x ≤ 1 / 2) : x / (1 - x) ∈ Icc (0 : ℝ) 1 := by
  have : 0 < 1 - x := by linarith
  refine ⟨div_nonneg hx.1 this.le, ?_⟩
  rw [div_le_one this]; linarith

theorem mapR {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (h : ¬ x ≤ 1 / 2) : 2 - 1 / x ∈ Icc (0 : ℝ) 1 := by
  rw [not_le] at h
  have hx0 : 0 < x := by linarith
  refine ⟨?_, ?_⟩
  · have : 1 / x ≤ 2 := by rw [div_le_iff₀ hx0]; linarith
    linarith
  · have : 1 ≤ 1 / x := by rw [le_div_iff₀ hx0]; linarith [hx.2]
    linarith

theorem Good.T {f : ℝ → ℝ} (hf : Good f) : Good (T f) := by
  obtain ⟨hm, h0, h1⟩ := hf
  have hg : Good f := ⟨hm, h0, h1⟩
  refine ⟨?_, by simp [Mink.T, h0], by norm_num [Mink.T, h1]⟩
  intro x hx y hy hxy
  simp only [Mink.T]
  by_cases h1x : x ≤ 1 / 2
  · by_cases h1y : y ≤ 1 / 2
    · rw [if_pos h1x, if_pos h1y]
      have : x / (1 - x) ≤ y / (1 - y) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
      have := hm (mapL hx h1x) (mapL hy h1y) this; linarith
    · rw [if_pos h1x, if_neg h1y]
      have a := (hg.mem (mapL hx h1x)).2
      have b := (hg.mem (mapR hy h1y)).1
      linarith
  · have h1y : ¬ y ≤ 1 / 2 := fun h => h1x (hxy.trans h)
    rw [if_neg h1x, if_neg h1y]
    have hx0 : 0 < x := by rw [not_le] at h1x; linarith
    have : 1 / y ≤ 1 / x := one_div_le_one_div_of_le hx0 hxy
    have := hm (mapR hx h1x) (mapR hy h1y) (by linarith); linarith

theorem approx_good (n : ℕ) : Good (approx n) := by
  induction n with
  | zero => exact ⟨monotoneOn_id, rfl, rfl⟩
  | succ n ih => exact ih.T

theorem approx_dist (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |approx (n + 1) x - approx n x| ≤ (1 / 2) ^ n := by
  induction n generalizing x with
  | zero =>
    have a := (approx_good 1).mem hx; have b := (approx_good 0).mem hx
    rw [abs_le]; simp only [pow_zero]; constructor <;> linarith [a.1, a.2, b.1, b.2]
  | succ n ih =>
    show |T (approx (n + 1)) x - T (approx n) x| ≤ _
    simp only [Mink.T]
    by_cases h : x ≤ 1 / 2
    · rw [if_pos h, if_pos h]
      have := ih (mapL hx h)
      rw [abs_le] at this ⊢; rw [pow_succ]; constructor <;> linarith [this.1, this.2]
    · rw [if_neg h, if_neg h]
      have := ih (mapR hx h)
      rw [abs_le] at this ⊢; rw [pow_succ]; constructor <;> linarith [this.1, this.2]

theorem approx_cauchy {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : CauchySeq (fun n => approx n x) :=
  cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num) (fun n => by
    rw [Real.dist_eq, abs_sub_comm, one_mul]; exact approx_dist n hx)

end Mink

/-- **Minkowski's question-mark function** on `[0,1]` (its values off `[0,1]` are irrelevant). -/
noncomputable def mink (x : ℝ) : ℝ := limUnder atTop (fun n => Mink.approx n x)

namespace Mink

theorem tendsto_approx {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => approx n x) atTop (𝓝 (mink x)) :=
  (approx_cauchy hx).tendsto_limUnder

theorem mink_T {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : mink x = T mink x := by
  have h1 : Tendsto (fun n => approx (n + 1) x) atTop (𝓝 (mink x)) :=
    (tendsto_approx hx).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => approx (n + 1) x) atTop (𝓝 (T mink x)) := by
    show Tendsto (fun n => T (approx n) x) atTop _
    unfold Mink.T
    by_cases h : x ≤ 1 / 2
    · simp only [if_pos h]
      exact (tendsto_approx (mapL hx h)).div_const 2
    · simp only [if_neg h]
      exact ((tendsto_approx (mapR hx h)).div_const 2).const_add _
  exact tendsto_nhds_unique h1 h2

theorem mink_zero : mink 0 = 0 := by
  have h := tendsto_approx (x := 0) ⟨le_rfl, zero_le_one⟩
  have : (fun n => approx n 0) = fun _ => 0 := funext fun n => (approx_good n).2.1
  rw [this] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem mink_one : mink 1 = 1 := by
  have h := tendsto_approx (x := 1) ⟨zero_le_one, le_rfl⟩
  have : (fun n => approx n 1) = fun _ => 1 := funext fun n => (approx_good n).2.2
  rw [this] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem mink_monotoneOn : MonotoneOn mink (Icc 0 1) := fun _ hx _ hy hxy =>
  le_of_tendsto_of_tendsto' (tendsto_approx hx) (tendsto_approx hy) fun n =>
    (approx_good n).1 hx hy hxy

theorem mink_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : mink x ∈ Icc (0 : ℝ) 1 :=
  Good.mem ⟨mink_monotoneOn, mink_zero, mink_one⟩ hx

theorem memL {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : s / (1 + s) ∈ Icc (0 : ℝ) 1 := by
  have : 0 < 1 + s := by linarith [hs.1]
  exact ⟨div_nonneg hs.1 this.le, by rw [div_le_one this]; linarith [hs.1]⟩

theorem memR {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 1 / (2 - s) ∈ Icc (0 : ℝ) 1 := by
  have : 0 < 2 - s := by linarith [hs.2]
  exact ⟨by positivity, by rw [div_le_one this]; linarith [hs.2]⟩

theorem mink_L {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : mink (s / (1 + s)) = mink s / 2 := by
  have h1 : 0 < 1 + s := by linarith [hs.1]
  have hle : s / (1 + s) ≤ 1 / 2 := by rw [div_le_iff₀ h1]; linarith [hs.2]
  rw [mink_T (memL hs), Mink.T, if_pos hle]
  congr 2
  field_simp
  ring

theorem mink_R {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : mink (1 / (2 - s)) = 1 / 2 + mink s / 2 := by
  have h1 : 0 < 2 - s := by linarith [hs.2]
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · subst h0
    have hh : (1 : ℝ) / (2 - 0) = 1 / 2 := by norm_num
    rw [hh, mink_T ⟨by norm_num, by norm_num⟩, Mink.T, if_pos le_rfl, mink_zero]
    norm_num [mink_one]
  · have hlt : ¬ 1 / (2 - s) ≤ 1 / 2 := by
      rw [not_le, div_lt_div_iff₀ (by norm_num) h1]; linarith
    rw [mink_T (memR hs), Mink.T, if_neg hlt]
    congr 3
    rw [one_div_one_div]; ring

/-- Self-similarity on the Farey node `fareyNode w`. -/
theorem mink_phi (w : List Bool) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    mink (phi (fareyNode w) s) =
      (dyadicNode w).1 + ((dyadicNode w).2 - (dyadicNode w).1) * mink s := by
  induction w using List.reverseRecOn generalizing s with
  | nil => rw [phi_root, dyadicNode_nil]; ring
  | append_singleton w b ih =>
    have hI := inv_fareyNode w
    cases b
    · rw [fareyNode_append_false, phi_leftPart hI hs, ih (memL hs), mink_L hs,
        dyadicNode_append_false]
      ring
    · rw [fareyNode_append_true, phi_rightPart hI hs, ih (memR hs), mink_R hs,
        dyadicNode_append_true]
      ring

theorem mink_lo (w : List Bool) : mink (fareyNode w).lo = (dyadicNode w).1 := by
  rw [← phi_zero, mink_phi w ⟨le_rfl, zero_le_one⟩, mink_zero]; ring

theorem mink_hi (w : List Bool) : mink (fareyNode w).hi = (dyadicNode w).2 := by
  rw [← phi_one, mink_phi w ⟨zero_le_one, le_rfl⟩, mink_one]; ring

theorem mink_strictMonoOn : StrictMonoOn mink (Icc 0 1) := by
  intro x hx y hy hxy
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < (y - x) / 2 by linarith)
  have hm : (x + y) / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
  obtain ⟨w, hw, h1, h2⟩ := farey_cover n hm
  have hI := inv_fareyNode w
  rw [hw] at hI
  have hwid := hI.width_le
  have hlh := hI.lo_lt_hi
  have hlo : x < (fareyNode w).lo := by linarith
  have hhi : (fareyNode w).hi < y := by linarith
  have hlo01 : (fareyNode w).lo ∈ Icc (0 : ℝ) 1 :=
    ⟨hI.lo_nonneg, by linarith [hI.hi_le_one]⟩
  have hhi01 : (fareyNode w).hi ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hI.lo_nonneg], hI.hi_le_one⟩
  have a := mink_monotoneOn hx hlo01 hlo.le
  have b := mink_monotoneOn hhi01 hy hhi.le
  rw [mink_lo] at a; rw [mink_hi] at b
  have := (dyadicNode_bounds w).2.1
  linarith

theorem mink_lt_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : mink t < 1 :=
  mink_one ▸ mink_strictMonoOn ⟨ht0, ht1.le⟩ ⟨zero_le_one, le_rfl⟩ ht1

end Mink

/-- The periodic extension `x ↦ ⌊x⌋ + mink (fract x)`. -/
noncomputable def minkFun (x : ℝ) : ℝ := ⌊x⌋ + mink (Int.fract x)

namespace Mink

theorem minkFun_int_add (k : ℤ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    minkFun (k + t) = k + mink t := by
  have hf : ⌊t⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨ht0, ht1⟩
  have hfr : Int.fract t = t := Int.fract_eq_self.mpr ⟨ht0, ht1⟩
  simp [minkFun, Int.floor_intCast_add, Int.fract_intCast_add, hf, hfr]

theorem minkFun_intCast (k : ℤ) : minkFun k = k := by
  simp [minkFun, mink_zero]

theorem minkFun_eq_mink {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : minkFun x = mink x := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · subst h; simpa [mink_one] using minkFun_intCast 1
  · simpa using minkFun_int_add 0 hx.1 h

theorem minkFun_strictMono : StrictMono minkFun := by
  intro x y hxy
  simp only [minkFun]
  have hx0 := Int.fract_nonneg x; have hx1 := Int.fract_lt_one x
  have hy0 := Int.fract_nonneg y; have hy1 := Int.fract_lt_one y
  have ex := Int.floor_add_fract x; have ey := Int.floor_add_fract y
  rcases (Int.floor_mono hxy.le).lt_or_eq with h | h
  · have h' : ⌊x⌋ + 1 ≤ ⌊y⌋ := Int.add_one_le_of_lt h
    have h'' : (⌊x⌋ : ℝ) + 1 ≤ ⌊y⌋ := by exact_mod_cast h'
    have := mink_lt_one hx0 hx1
    have := (mink_mem ⟨hy0, hy1.le⟩).1
    linarith
  · have hc : (⌊x⌋ : ℝ) = ⌊y⌋ := by rw [h]
    have : Int.fract x < Int.fract y := by linarith
    linarith [mink_strictMonoOn ⟨hx0, hx1.le⟩ ⟨hy0, hy1.le⟩ this]

theorem minkFun_denseRange : DenseRange minkFun := by
  apply dense_of_exists_between
  intro a b hab
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < (b - a) / 2 by linarith)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  obtain ⟨w, hw, h1, h2⟩ := dyadic_cover n (y := Int.fract ((a + b) / 2))
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hwd := dyadicNode_width w
  rw [hw] at hwd
  have hI := inv_fareyNode w
  have ec := Int.floor_add_fract ((a + b) / 2)
  refine ⟨⌊(a + b) / 2⌋ + (dyadicNode w).1, ⟨⌊(a + b) / 2⌋ + (fareyNode w).lo, ?_⟩, ?_, ?_⟩
  · rw [minkFun_int_add _ hI.lo_nonneg (by linarith [hI.lo_lt_hi, hI.hi_le_one]), mink_lo]
  · linarith
  · linarith

theorem minkFun_continuous : Continuous minkFun :=
  minkFun_strictMono.monotone.continuous_of_denseRange minkFun_denseRange

theorem mink_continuousOn : ContinuousOn mink (Icc 0 1) :=
  minkFun_continuous.continuousOn.congr fun _ hx => (minkFun_eq_mink hx).symm

theorem mink_image : mink '' Icc 0 1 = Icc 0 1 := by
  apply subset_antisymm
  · rintro _ ⟨x, hx, rfl⟩; exact mink_mem hx
  · have := intermediate_value_Icc zero_le_one mink_continuousOn
    rwa [mink_zero, mink_one] at this

end Mink

/-- `mink` as a map of `UI`. -/
noncomputable def minkUI (x : UI) : UI := ⟨mink x, Mink.mink_mem x.2⟩

theorem minkUI_strictMono : StrictMono minkUI := fun x y h =>
  Mink.mink_strictMonoOn x.2 y.2 h

theorem minkUI_surjective : Function.Surjective minkUI := by
  intro y
  have : (y : ℝ) ∈ mink '' Icc 0 1 := by rw [Mink.mink_image]; exact y.2
  obtain ⟨x, hx, hxy⟩ := this
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- Minkowski's question-mark function as an order isomorphism of `[0,1]`. -/
noncomputable def minkIso : UI ≃o UI :=
  StrictMono.orderIsoOfSurjective minkUI minkUI_strictMono minkUI_surjective

namespace Mink

/-- The Farey breakpoints of the tree `t` below the node `w` go to the dyadic ones. -/
theorem map_fareyMarksAux (t : TTree) (w : List Bool) :
    (fareyMarksAux t (fareyNode w)).map (fun I => mink I.lo) =
      t.marksAux (dyadicNode w).1 (dyadicNode w).2 := by
  induction t generalizing w with
  | leaf => simp [fareyMarksAux, TTree.marksAux]
  | node l r ihl ihr =>
    simp only [fareyMarksAux, TTree.marksAux, List.map_append, List.map_cons]
    rw [← fareyNode_append_false, ← fareyNode_append_true, ihl, ihr, mink_lo,
      dyadicNode_append_false, dyadicNode_append_true]

theorem map_mink_fareyMarks (t : TTree) : (fareyMarks t).map mink = TTree.marks t := by
  have h := map_fareyMarksAux t []
  rw [dyadicNode_nil] at h
  simp only [fareyMarks, TTree.marks, List.map_cons, List.map_append, List.map_map,
    mink_zero, mink_one]
  rw [← h]
  rfl

end Mink

end CannonFloydParry.S7

/-!
# Farey intervals and integral projective maps of `[0,1]` (CFP §7, pp. 251–253)

Basic facts: the action of `GL(2, ℤ)` on `(t, 1)`, Farey intervals, and the explicit linear
fractional map `mob I J` between two Farey intervals.
-/

namespace CannonFloydParry.S7

open FracInterval

/-! ### `glAct` on `(t, 1)` -/

lemma glAct_t0 (A : GL (Fin 2) ℤ) (t : ℝ) :
    glAct A ![t, 1] 0 = ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) * t +
      ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ) := by
  simp [glAct, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma glAct_t1 (A : GL (Fin 2) ℤ) (t : ℝ) :
    glAct A ![t, 1] 1 = ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * t +
      ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) := by
  simp [glAct, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma det_GL (A : GL (Fin 2) ℤ) :
    (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 ∨
      (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -1 := by
  have h := Matrix.isUnits_det_units A
  rw [Matrix.det_fin_two] at h
  exact Int.isUnit_iff.mp h

lemma glAct_entries (A : GL (Fin 2) ℤ) : ∃ p q r s : ℤ, (p * s - q * r = 1 ∨ p * s - q * r = -1) ∧
    ∀ t : ℝ, glAct A ![t, 1] 0 = (p : ℝ) * t + q ∧ glAct A ![t, 1] 1 = (r : ℝ) * t + s :=
  ⟨_, _, _, _, det_GL A, fun t => ⟨glAct_t0 A t, glAct_t1 A t⟩⟩

/-- The denominator of an integral projective map is positive. -/
lemma denom_pos {A : GL (Fin 2) ℤ} {U : Set ℝ} {f : ℝ → ℝ} (h : IsIntegralProjective01Via A U f)
    {t : ℝ} (ht : t ∈ U) : 0 < glAct A ![t, 1] 1 := by
  obtain ⟨h0, h1, -⟩ := h t ht
  by_contra hle
  have hy : glAct A ![t, 1] 1 = 0 := le_antisymm (not_lt.mp hle) (h0.trans h1)
  have hx : glAct A ![t, 1] 0 = 0 := le_antisymm (hy ▸ h1) h0
  rw [glAct_t0] at hx
  rw [glAct_t1] at hy
  set M := (A : Matrix (Fin 2) (Fin 2) ℤ)
  have hd : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ℝ) = 0 := by
    push_cast
    linear_combination (M 0 0 : ℝ) * hy - (M 1 0 : ℝ) * hx
  rcases det_GL A with h | h <;> rw [h] at hd <;> norm_num at hd

/-! ### Farey intervals -/

section Farey

variable {I : FracInterval}

lemma IsFarey.det (hI : I.IsFarey) : (I.a : ℤ) * I.d - (I.b : ℤ) * I.c = -1 := hI.2.2.2.2.2

lemma IsFarey.detR (hI : I.IsFarey) : (I.a : ℝ) * I.d - (I.b : ℝ) * I.c = -1 := by
  exact_mod_cast (IsFarey.det hI)

lemma IsFarey.b_pos (hI : I.IsFarey) : (0 : ℝ) < I.b := by exact_mod_cast hI.1
lemma IsFarey.d_pos (hI : I.IsFarey) : (0 : ℝ) < I.d := by exact_mod_cast hI.2.2.1
lemma IsFarey.a_le_b (hI : I.IsFarey) : (I.a : ℝ) ≤ I.b := by exact_mod_cast hI.2.2.2.1
lemma IsFarey.c_le_d (hI : I.IsFarey) : (I.c : ℝ) ≤ I.d := by exact_mod_cast hI.2.2.2.2.1

lemma IsFarey.leftPart (hI : I.IsFarey) : I.leftPart.IsFarey := by
  obtain ⟨hb, hc, hd, hab, hcd, hdet⟩ := hI
  refine ⟨hb, by simp [FracInterval.leftPart]; omega, by simp [FracInterval.leftPart]; omega,
    le_refl _ |>.trans hab, by simp [FracInterval.leftPart]; omega, ?_⟩
  simp only [FracInterval.leftPart]
  push_cast
  linear_combination hdet

lemma IsFarey.rightPart (hI : I.IsFarey) : I.rightPart.IsFarey := by
  obtain ⟨hb, hc, hd, hab, hcd, hdet⟩ := hI
  refine ⟨by simp [FracInterval.rightPart]; omega, hc, hd, by simp [FracInterval.rightPart]; omega,
    hcd, ?_⟩
  simp only [FracInterval.rightPart]
  push_cast
  linear_combination hdet

lemma IsFarey.isCoprime_ab (hI : I.IsFarey) : IsCoprime (I.a : ℤ) (I.b : ℤ) :=
  ⟨-(I.d : ℤ), I.c, by linear_combination (-1 : ℤ) * (IsFarey.det hI)⟩

lemma IsFarey.isCoprime_cd (hI : I.IsFarey) : IsCoprime (I.c : ℤ) (I.d : ℤ) :=
  ⟨I.b, -(I.a : ℤ), by linear_combination (-1 : ℤ) * (IsFarey.det hI)⟩

lemma IsFarey.lo_nonneg (hI : I.IsFarey) : 0 ≤ I.lo := by
  unfold FracInterval.lo; positivity

lemma IsFarey.hi_le_one (hI : I.IsFarey) : I.hi ≤ 1 := by
  unfold FracInterval.hi
  rw [div_le_one (IsFarey.d_pos hI)]; exact (IsFarey.c_le_d hI)

lemma IsFarey.lo_lt_hi (hI : I.IsFarey) : I.lo < I.hi := by
  unfold FracInterval.lo FracInterval.hi
  rw [div_lt_div_iff₀ (IsFarey.b_pos hI) (IsFarey.d_pos hI)]
  linarith [(IsFarey.detR hI)]

lemma IsFarey.Icc_subset (hI : I.IsFarey) : Set.Icc I.lo I.hi ⊆ Set.Icc 0 1 :=
  Set.Icc_subset_Icc (IsFarey.lo_nonneg hI) (IsFarey.hi_le_one hI)

end Farey

/-! ### Reduced fractions -/

/-! ### A continuous map with the right bounds maps `[l, h]` onto `[f l, f h]` -/

lemma image_Icc_of_bounds {f : ℝ → ℝ} {l h : ℝ} (hlh : l ≤ h) (hc : ContinuousOn f (Set.Icc l h))
    (hb : ∀ t ∈ Set.Icc l h, f l ≤ f t ∧ f t ≤ f h) : f '' Set.Icc l h = Set.Icc (f l) (f h) := by
  apply le_antisymm
  · rintro _ ⟨t, ht, rfl⟩; exact hb t ht
  · exact intermediate_value_Icc hlh hc

lemma image_Icc_of_bounds' {f : ℝ → ℝ} {l h : ℝ} (hlh : l ≤ h) (hc : ContinuousOn f (Set.Icc l h))
    (hb : ∀ t ∈ Set.Icc l h, f h ≤ f t ∧ f t ≤ f l) : f '' Set.Icc l h = Set.Icc (f h) (f l) := by
  apply le_antisymm
  · rintro _ ⟨t, ht, rfl⟩; exact hb t ht
  · exact intermediate_value_Icc' hlh hc

end CannonFloydParry.S7

/-!
# The linear fractional map between two Farey intervals (CFP §7, p. 252)

`mob I J` is the map `ρ ∘ (M_J M_I⁻¹)` in the coordinate `t`; it is integral projective on
`[I.lo, I.hi]`, maps it onto `[J.lo, J.hi]` endpoint to endpoint, and it is the only integral
projective map on `[I.lo, I.hi]` with those endpoint values.
-/

namespace CannonFloydParry.S7


/-- Numerator of the map `I → J`. -/
noncomputable def mobN (I J : FracInterval) (t : ℝ) : ℝ :=
  ((J.c : ℝ) * I.b - (J.a : ℝ) * I.d) * t + ((J.a : ℝ) * I.c - (J.c : ℝ) * I.a)

/-- Denominator of the map `I → J`. -/
noncomputable def mobD (I J : FracInterval) (t : ℝ) : ℝ :=
  ((J.d : ℝ) * I.b - (J.b : ℝ) * I.d) * t + ((J.b : ℝ) * I.c - (J.d : ℝ) * I.a)

/-- The linear fractional map carrying `[I.lo, I.hi]` onto `[J.lo, J.hi]`. -/
noncomputable def mob (I J : FracInterval) (t : ℝ) : ℝ := mobN I J t / mobD I J t

lemma mobN_eq (I J : FracInterval) (t : ℝ) :
    mobN I J t = ((I.c : ℝ) - I.d * t) * J.a + ((I.b : ℝ) * t - I.a) * J.c := by
  unfold mobN; ring

lemma mobD_eq (I J : FracInterval) (t : ℝ) :
    mobD I J t = ((I.c : ℝ) - I.d * t) * J.b + ((I.b : ℝ) * t - I.a) * J.d := by
  unfold mobD; ring

variable {I J : FracInterval}

lemma alpha_nonneg (hI : I.IsFarey) {t : ℝ} (ht : t ∈ Set.Icc I.lo I.hi) :
    0 ≤ (I.c : ℝ) - I.d * t := by
  have h := ht.2
  unfold FracInterval.hi at h
  rw [le_div_iff₀ (IsFarey.d_pos hI)] at h
  linarith

lemma beta_nonneg (hI : I.IsFarey) {t : ℝ} (ht : t ∈ Set.Icc I.lo I.hi) :
    0 ≤ (I.b : ℝ) * t - I.a := by
  have h := ht.1
  unfold FracInterval.lo at h
  rw [div_le_iff₀ (IsFarey.b_pos hI)] at h
  linarith

lemma alpha_beta (hI : I.IsFarey) (t : ℝ) :
    (I.b : ℝ) * ((I.c : ℝ) - I.d * t) + (I.d : ℝ) * ((I.b : ℝ) * t - I.a) = 1 := by
  linear_combination -(IsFarey.detR hI)

lemma mobD_pos (hI : I.IsFarey) (hJ : J.IsFarey) {t : ℝ} (ht : t ∈ Set.Icc I.lo I.hi) :
    0 < mobD I J t := by
  rw [mobD_eq]
  have hα := alpha_nonneg hI ht
  have hβ := beta_nonneg hI ht
  have hab := alpha_beta hI t
  have hb := IsFarey.b_pos hJ
  have hd := IsFarey.d_pos hJ
  rcases hα.lt_or_eq with hα | hα
  · have := mul_pos hα hb
    nlinarith [mul_nonneg hβ hd.le]
  · rw [← hα] at hab ⊢
    have : 0 < (I.b : ℝ) * t - I.a := by
      by_contra h
      have : (I.b : ℝ) * t - I.a = 0 := le_antisymm (not_lt.mp h) hβ
      rw [this] at hab; simp at hab
    simp only [zero_mul, zero_add]
    exact mul_pos this hd

lemma continuousOn_mob (hI : I.IsFarey) (hJ : J.IsFarey) :
    ContinuousOn (mob I J) (Set.Icc I.lo I.hi) := by
  unfold mob mobN mobD
  exact ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => (mobD_pos hI hJ ht).ne'

/-- The integer matrix of the map. -/
def mobMat (I J : FracInterval) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(J.c : ℤ) * I.b - (J.a : ℤ) * I.d, (J.a : ℤ) * I.c - (J.c : ℤ) * I.a;
     (J.d : ℤ) * I.b - (J.b : ℤ) * I.d, (J.b : ℤ) * I.c - (J.d : ℤ) * I.a]

lemma mobMat_det (hI : I.IsFarey) (hJ : J.IsFarey) : (mobMat I J).det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [mobMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination ((I.a : ℤ) * I.d - (I.b : ℤ) * I.c) * (IsFarey.det hJ) - (IsFarey.det hI)

/-- The matrix as an element of `GL(2, ℤ)`. -/
def glOfDetOne (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M.det = 1) : GL (Fin 2) ℤ :=
  ⟨M, M.adjugate, by rw [Matrix.mul_adjugate, h, one_smul],
    by rw [Matrix.adjugate_mul, h, one_smul]⟩

lemma mob_via (hI : I.IsFarey) (hJ : J.IsFarey) :
    IsIntegralProjective01Via (glOfDetOne (mobMat I J) (mobMat_det hI hJ))
      (Set.Icc I.lo I.hi) (mob I J) := by
  intro t ht
  have e0 : glAct (glOfDetOne (mobMat I J) (mobMat_det hI hJ)) ![t, 1] 0 = mobN I J t := by
    rw [glAct_t0]
    simp [glOfDetOne, mobMat, mobN]
  have e1 : glAct (glOfDetOne (mobMat I J) (mobMat_det hI hJ)) ![t, 1] 1 = mobD I J t := by
    rw [glAct_t1]
    simp [glOfDetOne, mobMat, mobD]
  rw [e0, e1]
  refine ⟨?_, ?_, rfl⟩
  · rw [mobN_eq]
    have := alpha_nonneg hI ht
    have := beta_nonneg hI ht
    positivity
  · rw [mobN_eq, mobD_eq]
    have := mul_nonneg (alpha_nonneg hI ht) (sub_nonneg.mpr (IsFarey.a_le_b hJ))
    have := mul_nonneg (beta_nonneg hI ht) (sub_nonneg.mpr (IsFarey.c_le_d hJ))
    nlinarith

lemma mob_isIP (hI : I.IsFarey) (hJ : J.IsFarey) :
    IsIntegralProjective01 (Set.Icc I.lo I.hi) (mob I J) :=
  ⟨IsFarey.Icc_subset hI, _, mob_via hI hJ⟩

lemma lo_mem (hI : I.IsFarey) : I.lo ∈ Set.Icc I.lo I.hi := ⟨le_rfl, (IsFarey.lo_lt_hi hI).le⟩
lemma hi_mem (hI : I.IsFarey) : I.hi ∈ Set.Icc I.lo I.hi := ⟨(IsFarey.lo_lt_hi hI).le, le_rfl⟩

lemma mob_lo (hI : I.IsFarey) (hJ : J.IsFarey) : mob I J I.lo = J.lo := by
  have hD := mobD_pos hI hJ (lo_mem hI)
  have hb := IsFarey.b_pos hI
  unfold mob FracInterval.lo at *
  rw [div_eq_div_iff hD.ne' (IsFarey.b_pos hJ).ne']
  unfold mobN mobD
  field_simp
  ring

lemma mob_hi (hI : I.IsFarey) (hJ : J.IsFarey) : mob I J I.hi = J.hi := by
  have hD := mobD_pos hI hJ (hi_mem hI)
  have hd := IsFarey.d_pos hI
  unfold mob FracInterval.hi at *
  rw [div_eq_div_iff hD.ne' (IsFarey.d_pos hJ).ne']
  unfold mobN mobD
  field_simp
  ring

lemma mob_bounds (hI : I.IsFarey) (hJ : J.IsFarey) {t : ℝ} (ht : t ∈ Set.Icc I.lo I.hi) :
    J.lo ≤ mob I J t ∧ mob I J t ≤ J.hi := by
  have hD := mobD_pos hI hJ ht
  have hβ := beta_nonneg hI ht
  have hα := alpha_nonneg hI ht
  have hdJ := IsFarey.detR hJ
  unfold mob FracInterval.lo FracInterval.hi
  constructor
  · rw [div_le_div_iff₀ (IsFarey.b_pos hJ) hD, mobN_eq, mobD_eq]
    nlinarith
  · rw [div_le_div_iff₀ hD (IsFarey.d_pos hJ), mobN_eq, mobD_eq]
    nlinarith

lemma mob_image (hI : I.IsFarey) (hJ : J.IsFarey) :
    mob I J '' Set.Icc I.lo I.hi = Set.Icc J.lo J.hi := by
  have h := image_Icc_of_bounds (IsFarey.lo_lt_hi hI).le (continuousOn_mob hI hJ)
    (fun t ht => by rw [mob_lo hI hJ, mob_hi hI hJ]; exact mob_bounds hI hJ ht)
  rwa [mob_lo hI hJ, mob_hi hI hJ] at h

/-! ### Uniqueness -/

lemma prim_mult {x y u v : ℤ} (hc : IsCoprime x y) (hy : 0 < y) (hv : 0 < v)
    (h : x * v = u * y) : ∃ l : ℤ, 0 < l ∧ u = l * x ∧ v = l * y := by
  obtain ⟨k, hk⟩ : y ∣ v := hc.symm.dvd_of_dvd_mul_left ⟨u, by rw [h]; ring⟩
  refine ⟨k, ?_, ?_, by rw [hk]; ring⟩
  · rw [hk] at hv
    exact pos_of_mul_pos_right hv hy.le
  · rw [hk] at h
    have : (u - k * x) * y = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact absurd h' hy.ne'

lemma mob_unique (hI : I.IsFarey) (hJ : J.IsFarey) {g : ℝ → ℝ}
    (hg : IsIntegralProjective01 (Set.Icc I.lo I.hi) g) (hlo : g I.lo = J.lo)
    (hhi : g I.hi = J.hi) : Set.EqOn g (mob I J) (Set.Icc I.lo I.hi) := by
  obtain ⟨-, B, hB⟩ := hg
  obtain ⟨p, q, r, s, hdet, hgl⟩ := glAct_entries B
  have hbI := IsFarey.b_pos hI
  have hdI := IsFarey.d_pos hI
  have hbJ := IsFarey.b_pos hJ
  have hdJ := IsFarey.d_pos hJ
  -- at the left endpoint
  have y0 := denom_pos hB (lo_mem hI)
  have g0 := (hB _ (lo_mem hI)).2.2
  rw [(hgl _).2] at y0
  rw [hlo, (hgl _).1, (hgl _).2] at g0
  have hv0 : (0 : ℝ) < r * I.a + s * I.b := by
    have : (r : ℝ) * I.a + s * I.b = I.b * (r * I.lo + s) := by
      unfold FracInterval.lo; field_simp
    rw [this]; positivity
  have huv0 : (J.a : ℝ) * (r * I.a + s * I.b) = (p * I.a + q * I.b) * J.b := by
    have y0' := y0
    unfold FracInterval.lo at g0 y0'
    rw [div_eq_div_iff hbJ.ne' y0'.ne'] at g0
    field_simp at g0
    linear_combination g0
  -- at the right endpoint
  have y1 := denom_pos hB (hi_mem hI)
  have g1 := (hB _ (hi_mem hI)).2.2
  rw [(hgl _).2] at y1
  rw [hhi, (hgl _).1, (hgl _).2] at g1
  have hv1 : (0 : ℝ) < r * I.c + s * I.d := by
    have : (r : ℝ) * I.c + s * I.d = I.d * (r * I.hi + s) := by
      unfold FracInterval.hi; field_simp
    rw [this]; positivity
  have huv1 : (J.c : ℝ) * (r * I.c + s * I.d) = (p * I.c + q * I.d) * J.d := by
    have y1' := y1
    unfold FracInterval.hi at g1 y1'
    rw [div_eq_div_iff hdJ.ne' y1'.ne'] at g1
    field_simp at g1
    linear_combination g1
  obtain ⟨l, hl, hl1, hl2⟩ := prim_mult (IsFarey.isCoprime_ab hJ) (by exact_mod_cast hJ.1)
    (by exact_mod_cast hv0) (by exact_mod_cast huv0)
  obtain ⟨m, hm, hm1, hm2⟩ := prim_mult (IsFarey.isCoprime_cd hJ) (by exact_mod_cast hJ.2.2.1)
    (by exact_mod_cast hv1) (by exact_mod_cast huv1)
  have hdI' := IsFarey.det hI
  have hdJ' := IsFarey.det hJ
  have hlm : l * m = p * s - q * r := by
    have key : (p * I.a + q * I.b) * (r * I.c + s * I.d) - (p * I.c + q * I.d) * (r * I.a + s * I.b)
        = (p * s - q * r) * ((I.a : ℤ) * I.d - (I.b : ℤ) * I.c) := by ring
    rw [hl1, hl2, hm1, hm2, hdI'] at key
    linear_combination -key + l * m * hdJ'
  have hl1' : l = 1 := by
    rcases hdet with h | h
    · exact Int.eq_one_of_mul_eq_one_right hl.le (hlm.trans h)
    · nlinarith [mul_pos hl hm]
  have hm1' : m = 1 := by
    rw [hl1', one_mul] at hlm
    rcases hdet with h | h
    · exact hlm.trans h
    · nlinarith
  subst hl1' hm1'
  simp only [one_mul] at hl1 hl2 hm1 hm2
  have ep : p = (J.c : ℤ) * I.b - (J.a : ℤ) * I.d := by
    linear_combination (-(I.d : ℤ)) * hl1 + (I.b : ℤ) * hm1 + p * hdI'
  have eq' : q = (J.a : ℤ) * I.c - (J.c : ℤ) * I.a := by
    linear_combination (-(I.a : ℤ)) * hm1 + (I.c : ℤ) * hl1 + q * hdI'
  have er : r = (J.d : ℤ) * I.b - (J.b : ℤ) * I.d := by
    linear_combination (-(I.d : ℤ)) * hl2 + (I.b : ℤ) * hm2 + r * hdI'
  have es : s = (J.b : ℤ) * I.c - (J.d : ℤ) * I.a := by
    linear_combination (-(I.a : ℤ)) * hm2 + (I.c : ℤ) * hl2 + s * hdI'
  intro t ht
  rw [(hB t ht).2.2, (hgl _).1, (hgl _).2, ep, eq', er, es]
  unfold mob mobN mobD
  push_cast
  rfl

end CannonFloydParry.S7

/-!
# Integral subsimplices of `[0,1]` and the maps between them (CFP §7, pp. 251–253)
-/

namespace CannonFloydParry.S7

/-- The root `[0/1, 1/1]` of the Farey tree. -/
def root : FracInterval := ⟨0, 1, 1, 1⟩

lemma root_isFarey : root.IsFarey := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by norm_num [root]⟩

lemma root_Icc : Set.Icc root.lo root.hi = Set.Icc 0 1 := by
  simp [root, FracInterval.lo, FracInterval.hi]

lemma subsimplex_of_farey {K : FracInterval} (hK : K.IsFarey) : IsIntegralSubsimplex01 K.lo K.hi :=
  ⟨mob root K, root_Icc ▸ mob_isIP root_isFarey hK, root_Icc ▸ mob_image root_isFarey hK⟩

/-- Every integral subsimplex of `[0,1]` is a Farey interval. -/
lemma exists_farey_of_subsimplex {p q : ℝ} (h : IsIntegralSubsimplex01 p q) :
    ∃ K : FracInterval, K.IsFarey ∧ K.lo = p ∧ K.hi = q := by
  obtain ⟨f, ⟨-, B, hB⟩, himg⟩ := h
  obtain ⟨P, Q, R, S, hdet, hgl⟩ := glAct_entries B
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have y0 := denom_pos hB h0
  have y1 := denom_pos hB h1
  obtain ⟨x0, xy0, -⟩ := hB 0 h0
  obtain ⟨x1, xy1, -⟩ := hB 1 h1
  rw [(hgl _).2] at y0 y1 xy0 xy1
  rw [(hgl _).1] at x0 x1 xy0 xy1
  simp only [mul_zero, zero_add, mul_one] at y0 y1 xy0 xy1 x0 x1
  have iQ : 0 ≤ Q := by exact_mod_cast x0
  have iS : 0 < S := by exact_mod_cast y0
  have iQS : Q ≤ S := by exact_mod_cast xy0
  have iX : 0 ≤ P + Q := by exact_mod_cast x1
  have iY : 0 < R + S := by exact_mod_cast y1
  have iXY : P + Q ≤ R + S := by exact_mod_cast xy1
  lift Q to ℕ using iQ with a
  lift S to ℕ using iS.le with b
  obtain ⟨c, hc⟩ : ∃ c : ℕ, P + a = c := ⟨(P + a).toNat, (Int.toNat_of_nonneg iX).symm⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, R + b = d := ⟨(R + b).toNat, (Int.toNat_of_nonneg iY.le).symm⟩
  have hP : P = c - a := by omega
  have hR : R = d - b := by omega
  subst hP hR
  have hb : 0 < b := by exact_mod_cast iS
  have hd0 : 0 < d := by omega
  have hab : a ≤ b := by exact_mod_cast iQS
  have hcd : c ≤ d := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  -- the formula for `f`
  have hden : ∀ t ∈ Set.Icc (0 : ℝ) 1, (0 : ℝ) < ((d : ℝ) - b) * t + b := by
    intro t ht
    have := denom_pos hB ht
    rw [(hgl _).2] at this
    push_cast at this
    exact this
  have hf : Set.EqOn f (fun t => (((c : ℝ) - a) * t + a) / (((d : ℝ) - b) * t + b))
      (Set.Icc 0 1) := by
    intro t ht
    rw [(hB t ht).2.2, (hgl _).1, (hgl _).2]
    push_cast
    rfl
  have hcont : ContinuousOn f (Set.Icc 0 1) :=
    ContinuousOn.congr (ContinuousOn.div (by fun_prop) (by fun_prop)
      fun t ht => (hden t ht).ne') hf
  have f0 : f 0 = (a : ℝ) / b := by rw [hf h0]; simp
  have f1 : f 1 = (c : ℝ) / d := by rw [hf h1]; simp
  have hdR' : ((c - a : ℤ) * b - a * (d - b) : ℤ) = (c : ℤ) * b - a * d := by ring
  rcases hdet with hdet | hdet <;> rw [hdR'] at hdet
  · -- orientation preserving: `K = [a/b, c/d]`
    have hK : (⟨a, b, c, d⟩ : FracInterval).IsFarey := by
      refine ⟨hb, ?_, hd0, hab, hcd, by simp only; linarith⟩
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; push_cast at hdet; nlinarith
      · exact h
    have hdetR : (c : ℝ) * b - a * d = 1 := by exact_mod_cast hdet
    have himg' : f '' Set.Icc 0 1 = Set.Icc (f 0) (f 1) := by
      refine image_Icc_of_bounds zero_le_one hcont fun t ht => ?_
      have hD := hden t ht
      rw [f0, f1, hf ht]
      constructor
      · rw [div_le_div_iff₀ hbR hD]; nlinarith [ht.1]
      · rw [div_le_div_iff₀ hD hdR]; nlinarith [ht.2]
    rw [himg', f0, f1] at himg
    have hle : (a : ℝ) / b ≤ c / d := by
      rw [div_le_div_iff₀ hbR hdR]; linarith
    obtain ⟨hp, hq⟩ := (Set.Icc_eq_Icc_iff hle).mp himg
    exact ⟨_, hK, hp, hq⟩
  · -- orientation reversing: `K = [c/d, a/b]`
    have hK : (⟨c, d, a, b⟩ : FracInterval).IsFarey := by
      refine ⟨hd0, ?_, hb, hcd, hab, by simp only; linarith⟩
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h; push_cast at hdet; nlinarith
      · exact h
    have hdetR : (c : ℝ) * b - a * d = -1 := by exact_mod_cast hdet
    have himg' : f '' Set.Icc 0 1 = Set.Icc (f 1) (f 0) := by
      refine image_Icc_of_bounds' zero_le_one hcont fun t ht => ?_
      have hD := hden t ht
      rw [f0, f1, hf ht]
      constructor
      · rw [div_le_div_iff₀ hdR hD]; nlinarith [ht.2]
      · rw [div_le_div_iff₀ hD hbR]; nlinarith [ht.1]
    rw [himg', f0, f1] at himg
    have hle : (c : ℝ) / d ≤ a / b := by
      rw [div_le_div_iff₀ hdR hbR]; linarith
    obtain ⟨hp, hq⟩ := (Set.Icc_eq_Icc_iff hle).mp himg
    exact ⟨_, hK, hp, hq⟩

/-! ### Target: the criterion of p. 251 -/


/-! ### Target: the two parts are integral subsimplices -/


/-! ### Target: the unique integral projective map between two Farey intervals -/


/-! ### Target: restriction and gluing -/


end CannonFloydParry.S7

/-!
# The tree `𝒯′` of integral subsimplices of `[0,1]` (CFP §7, p. 252)
-/

namespace CannonFloydParry.S7

/-- One step down the Farey tree. -/
def fstep (I : FracInterval) (x : Bool) : FracInterval := if x then I.rightPart else I.leftPart

lemma fareyNode_eq (w : List Bool) : fareyNode w = w.foldl fstep root := rfl

lemma fareyNode_nil : fareyNode [] = root := rfl

lemma fareyNode_append (w : List Bool) (x : Bool) :
    fareyNode (w ++ [x]) = fstep (fareyNode w) x := by
  simp [fareyNode_eq, List.foldl_append]

/-- Euclid descent: every Farey interval is a vertex of `𝒯′`. -/
lemma exists_fareyNode_aux (n : ℕ) :
    ∀ K : FracInterval, K.IsFarey → K.b + K.d = n → ∃ w, fareyNode w = K := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rintro ⟨a, b, c, d⟩ ⟨hb, hc, hd, hab, hcd, hdet⟩ hn
  simp only at hb hc hd hab hcd hdet hn
  have hN : a * d + 1 = b * c := by
    have : ((a * d + 1 : ℕ) : ℤ) = ((b * c : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  rcases lt_trichotomy b d with hbd | hbd | hbd
  · -- a left part: parent `[a/b, (c-a)/(d-b)]`
    have hac : a ≤ c := by
      by_contra h
      push Not at h
      nlinarith
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hac
    obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_lt hbd
    have hN' : a * (f + 1) + 1 = b * e := by nlinarith
    have he : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · subst h; simp at hN'
      · exact h
    have hef : e ≤ f + 1 := by
      by_contra h
      push Not at h
      have hb1 : b ≤ 1 := by nlinarith
      have hb1' : b = 1 := by omega
      subst hb1'
      have ha : a ≤ 1 := hab
      interval_cases a <;> omega
    have hlt : b + (f + 1) < n := by omega
    have hZ : (a : ℤ) * (f + 1) + 1 = b * e := by exact_mod_cast hN'
    have hK' : (⟨a, b, e, f + 1⟩ : FracInterval).IsFarey :=
      ⟨hb, he, by simp, hab, hef, by push_cast; linear_combination hZ⟩
    obtain ⟨w, hw⟩ := ih (b + (f + 1)) hlt ⟨a, b, e, f + 1⟩ hK' rfl
    refine ⟨w ++ [false], ?_⟩
    rw [fareyNode_append, hw]
    simp [fstep, FracInterval.leftPart]
    omega
  · -- the root
    subst hbd
    have hca : a < c := by
      by_contra h
      push Not at h
      nlinarith
    have hb1 : b = 1 := by
      have : b * (a + 1) ≤ b * c := Nat.mul_le_mul_left b hca
      nlinarith
    subst hb1
    have hc1 : c = 1 := by omega
    subst hc1
    have ha0 : a = 0 := by omega
    subst ha0
    exact ⟨[], rfl⟩
  · -- a right part: parent `[(a-c)/(b-d), c/d]`
    have hca : c ≤ a := by
      by_contra h
      push Not at h
      nlinarith
    obtain ⟨h', rfl⟩ := Nat.exists_eq_add_of_le hca
    obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_lt hbd
    have hN' : h' * d + 1 = (g + 1) * c := by nlinarith
    have hhg : h' ≤ g + 1 := by
      by_contra h
      push Not at h
      nlinarith
    have hlt : g + 1 + d < n := by omega
    have hZ : (h' : ℤ) * d + 1 = (g + 1) * c := by exact_mod_cast hN'
    have hK' : (⟨h', g + 1, c, d⟩ : FracInterval).IsFarey :=
      ⟨by simp, hc, hd, hhg, hcd, by push_cast; linear_combination hZ⟩
    obtain ⟨w, hw⟩ := ih (g + 1 + d) hlt ⟨h', g + 1, c, d⟩ hK' rfl
    refine ⟨w ++ [true], ?_⟩
    rw [fareyNode_append, hw]
    simp [fstep, FracInterval.rightPart]
    omega

lemma exists_fareyNode {K : FracInterval} (hK : K.IsFarey) : ∃ w, fareyNode w = K :=
  exists_fareyNode_aux _ K hK rfl


end CannonFloydParry.S7

/-!
# Transport through Minkowski's `?`: basic lemmas

List lemmas, the Farey pieces of `fareyMarks`, the conjugation identity
`mink ∘ mob I J = affine ∘ mink` on a Farey node, composition of integral projective maps, and
`IsThompson` from an affine-pieces chain.
-/

namespace CannonFloydParry.S7

open FracInterval Set

/-! ### Lists -/

theorem chain_and {α : Type*} {R S : α → α → Prop} :
    ∀ {l : List α}, l.IsChain R → l.IsChain S → l.IsChain (fun a b => R a b ∧ S a b)
  | [], _, _ => List.IsChain.nil
  | [a], _, _ => List.IsChain.singleton a
  | a :: b :: l, h1, h2 => by
    rw [List.isChain_cons_cons] at h1 h2 ⊢
    exact ⟨⟨h1.1, h2.1⟩, chain_and h1.2 h2.2⟩

theorem chain_cover {R : ℝ → ℝ → Prop} :
    ∀ (l : List ℝ) (a b m : ℝ), (a :: l).IsChain R → (a :: l).getLast? = some b → a < b →
      a ≤ m → m ≤ b → ∃ u v, u ∈ a :: l ∧ v ∈ a :: l ∧ R u v ∧ u ≤ m ∧ m ≤ v
  | [], a, b, m, _, hl, hab, _, _ => by
    simp at hl; subst hl; exact absurd hab (lt_irrefl _)
  | c :: l, a, b, m, hc, hl, hab, ham, hmb => by
    rw [List.isChain_cons_cons] at hc
    by_cases hmc : m ≤ c
    · exact ⟨a, c, by simp, by simp, hc.1, ham, hmc⟩
    · have hl' : (c :: l).getLast? = some b := by
        rw [← hl]; simp [List.getLast?_cons_cons]
      have hcm : c < m := lt_of_not_ge hmc
      obtain ⟨u, v, hu, hv, h⟩ := chain_cover l c b m hc.2 hl' (by linarith) hcm.le hmb
      exact ⟨u, v, List.mem_cons_of_mem _ hu, List.mem_cons_of_mem _ hv, h⟩

theorem chain_join {α : Type*} {R : α → α → Prop} {a b c : α} {xs ys : List α}
    (h1 : (a :: (xs ++ [b])).IsChain R) (h2 : (b :: (ys ++ [c])).IsChain R) :
    (a :: (xs ++ b :: (ys ++ [c]))).IsChain R := by
  have e : a :: (xs ++ b :: (ys ++ [c])) = (a :: (xs ++ [b])) ++ (ys ++ [c]) := by simp
  rw [e, List.isChain_append]
  obtain ⟨y, zs, hy⟩ : ∃ y zs, ys ++ [c] = y :: zs := by
    cases ys with
    | nil => exact ⟨c, [], rfl⟩
    | cons y ys => exact ⟨y, ys ++ [c], rfl⟩
  rw [hy] at h2 ⊢
  rw [List.isChain_cons_cons] at h2
  refine ⟨h1, h2.2, ?_⟩
  intro x hx z hz
  have hx' : x = b := by
    have : (a :: (xs ++ [b])).getLast? = some b := by
      rw [List.getLast?_eq_some_getLast (by simp)]; simp
    rw [this] at hx; exact (Option.mem_some_iff.mp hx).symm
  simp at hz
  subst hx' hz
  exact h2.1

/-! ### Farey pieces -/

/-- `[p, q]` is a node of the Farey tree. -/
def FP (p q : ℝ) : Prop := ∃ w, (fareyNode w).lo = p ∧ (fareyNode w).hi = q

theorem fareyNode_lo_nil : (fareyNode []).lo = 0 := by simp [fareyNode, FracInterval.lo]
theorem fareyNode_hi_nil : (fareyNode []).hi = 1 := by simp [fareyNode, FracInterval.hi]

theorem chain_fareyMarksAux (t : TTree) (w : List Bool) :
    ((fareyNode w).lo :: ((fareyMarksAux t (fareyNode w)).map FracInterval.lo ++
      [(fareyNode w).hi])).IsChain FP := by
  induction t generalizing w with
  | leaf =>
    simp only [fareyMarksAux, List.map_nil, List.nil_append]
    exact List.IsChain.cons_cons ⟨w, rfl, rfl⟩ (List.IsChain.singleton _)
  | node l r ihl ihr =>
    have hl := ihl (w ++ [false])
    have hr := ihr (w ++ [true])
    rw [Mink.fareyNode_append_false] at hl
    rw [Mink.fareyNode_append_true] at hr
    simp only [fareyMarksAux, List.map_append, List.map_cons, List.append_assoc,
      List.cons_append]
    exact chain_join hl hr

theorem fareyMarks_eq (t : TTree) : fareyMarks t = (fareyNode []).lo ::
    ((fareyMarksAux t (fareyNode [])).map FracInterval.lo ++ [(fareyNode []).hi]) := by
  rw [fareyNode_lo_nil, fareyNode_hi_nil]; rfl

theorem chain_fareyMarks (t : TTree) : (fareyMarks t).IsChain FP := by
  rw [fareyMarks_eq]; exact chain_fareyMarksAux t []

theorem mem_fareyMarksAux (t : TTree) (w : List Bool) :
    ∀ K ∈ fareyMarksAux t (fareyNode w), ∃ v, K = fareyNode v := by
  induction t generalizing w with
  | leaf => simp [fareyMarksAux]
  | node l r ihl ihr =>
    intro K hK
    simp only [fareyMarksAux, List.mem_append, List.mem_cons] at hK
    rcases hK with h | h | h
    · rw [← Mink.fareyNode_append_false] at h; exact ihl _ K h
    · exact ⟨w ++ [true], by rw [h, Mink.fareyNode_append_true]⟩
    · rw [← Mink.fareyNode_append_true] at h; exact ihr _ K h

theorem fareyNode_lo_mem (w : List Bool) : (fareyNode w).lo ∈ Icc (0 : ℝ) 1 :=
  ⟨(Mink.inv_fareyNode w).lo_nonneg,
    ((Mink.inv_fareyNode w).lo_lt_hi.trans_le (Mink.inv_fareyNode w).hi_le_one).le⟩

theorem fareyNode_hi_mem (w : List Bool) : (fareyNode w).hi ∈ Icc (0 : ℝ) 1 :=
  ⟨(Mink.inv_fareyNode w).lo_nonneg.trans (Mink.inv_fareyNode w).lo_lt_hi.le,
    (Mink.inv_fareyNode w).hi_le_one⟩

theorem mem_fareyMarks {t : TTree} {x : ℝ} (hx : x ∈ fareyMarks t) : x ∈ Icc (0 : ℝ) 1 := by
  simp only [fareyMarks, List.mem_cons, List.mem_append, List.mem_map] at hx
  rcases hx with h | ⟨K, hK, h⟩ | h
  · subst h; exact ⟨le_rfl, zero_le_one⟩
  · obtain ⟨v, rfl⟩ := mem_fareyMarksAux t [] K hK
    subst h; exact fareyNode_lo_mem v
  · rcases h with h | h
    · subst h; exact ⟨zero_le_one, le_rfl⟩
    · simp at h

theorem fareyNode_Icc_subset (w : List Bool) :
    Icc (fareyNode w).lo (fareyNode w).hi ⊆ Icc 0 1 :=
  Icc_subset_Icc (fareyNode_lo_mem w).1 (fareyNode_hi_mem w).2

/-! ### `mob` and `phi` -/

theorem phi_eq_mob_root (I : FracInterval) (s : ℝ) : phi I s = mob root I s := by
  simp only [phi, mob, mobN, mobD, root]
  push_cast
  congr 1 <;> ring

theorem exists_phi_eq {I : FracInterval} (hI : I.IsFarey) {x : ℝ}
    (hx : x ∈ Icc I.lo I.hi) : ∃ s ∈ Icc (0 : ℝ) 1, phi I s = x := by
  rw [← mob_image root_isFarey hI, root_Icc] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  exact ⟨s, hs, phi_eq_mob_root I s⟩

theorem mob_phi {I J : FracInterval} (hI : I.IsFarey) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    mob I J (phi I s) = phi J s := by
  have hb := IsFarey.b_pos hI
  have hd := IsFarey.d_pos hI
  have hdet := IsFarey.detR hI
  set Q : ℝ := (I.b : ℝ) * (1 - s) + I.d * s with hQdef
  have hQ : 0 < Q := by
    rcases eq_or_lt_of_le hs.2 with h1 | h1
    · rw [hQdef, h1]; simpa using hd
    · have : 0 < 1 - s := by linarith
      nlinarith [hs.1]
  set u := phi I s with hudef
  have hu : u * Q = (I.a : ℝ) * (1 - s) + I.c * s := by
    rw [hudef, phi, ← hQdef, div_mul_cancel₀ _ hQ.ne']
  have e1 : mobN I J u * Q = (J.a : ℝ) * (1 - s) + J.c * s := by
    unfold mobN
    linear_combination ((J.c : ℝ) * I.b - (J.a : ℝ) * I.d) * hu +
      (-((J.a : ℝ) * (1 - s) + J.c * s)) * hdet
  have e2 : mobD I J u * Q = (J.b : ℝ) * (1 - s) + J.d * s := by
    unfold mobD
    linear_combination ((J.d : ℝ) * I.b - (J.b : ℝ) * I.d) * hu +
      (-((J.b : ℝ) * (1 - s) + J.d * s)) * hdet
  rw [mob, ← mul_div_mul_right _ _ hQ.ne', e1, e2, phi]

theorem dyadicNode_width_pos (w : List Bool) : 0 < (dyadicNode w).2 - (dyadicNode w).1 := by
  have := (Mink.dyadicNode_bounds w).2.1; linarith

/-- The conjugation identity on a Farey node. -/
theorem mink_mob (w w' : List Bool) {x : ℝ} (hx : x ∈ Icc (fareyNode w).lo (fareyNode w).hi) :
    mink (mob (fareyNode w) (fareyNode w') x) = (dyadicNode w').1 +
      ((dyadicNode w').2 - (dyadicNode w').1) / ((dyadicNode w).2 - (dyadicNode w).1) *
        (mink x - (dyadicNode w).1) := by
  obtain ⟨s, hs, rfl⟩ := exists_phi_eq (Mink.isFarey_fareyNode w) hx
  rw [mob_phi (Mink.isFarey_fareyNode w) hs, Mink.mink_phi w' hs, Mink.mink_phi w hs]
  have := dyadicNode_width_pos w
  field_simp
  ring

theorem width_ratio (w w' : List Bool) :
    ((dyadicNode w').2 - (dyadicNode w').1) / ((dyadicNode w).2 - (dyadicNode w).1) =
      (2 : ℝ) ^ ((w.length : ℤ) - w'.length) := by
  rw [Mink.dyadicNode_width, Mink.dyadicNode_width, zpow_sub₀ (by norm_num), zpow_natCast,
    zpow_natCast]
  rw [one_div, inv_pow, inv_pow]
  field_simp

/-! ### Composition of integral projective maps -/

theorem glAct_mul_t (A B : GL (Fin 2) ℤ) (t : ℝ) (i : Fin 2) :
    glAct (B * A) ![t, 1] i = glAct B (glAct A ![t, 1]) i := by
  simp only [glAct, Units.val_mul]
  rw [Matrix.mulVec_mulVec]
  congr 2
  ext j k
  simp [Matrix.mul_apply]

theorem glAct_smul_trans (A : GL (Fin 2) ℤ) (c : ℝ) (v : Fin 2 → ℝ) :
    glAct A (c • v) = c • glAct A v := by
  simp only [glAct, Matrix.mulVec_smul]

theorem ip_comp {A B : GL (Fin 2) ℤ} {U V : Set ℝ} {f g : ℝ → ℝ}
    (hg : IsIntegralProjective01Via B V g) (hf : IsIntegralProjective01Via A U f)
    (hmaps : ∀ t ∈ U, f t ∈ V) : IsIntegralProjective01Via (B * A) U (g ∘ f) := by
  intro t ht
  have hy := denom_pos hf ht
  obtain ⟨-, -, hft⟩ := hf t ht
  set y := glAct A ![t, 1] 1
  have hv : glAct A ![t, 1] = y • ![f t, 1] := by
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
      rw [hft]; field_simp
    · simp [y]
  have e : ∀ i, glAct (B * A) ![t, 1] i = y * glAct B ![f t, 1] i := by
    intro i; rw [glAct_mul_t, hv, glAct_smul_trans]; rfl
  obtain ⟨g0, g1, g2⟩ := hg (f t) (hmaps t ht)
  refine ⟨?_, ?_, ?_⟩
  · rw [e]; positivity
  · rw [e, e]; exact mul_le_mul_of_nonneg_left g1 hy.le
  · rw [e, e, Function.comp_apply, g2, mul_div_mul_left _ _ hy.ne']

/-! ### `extend` -/

theorem extend_coe (g : UI ≃o UI) (z : UI) : extend g (z : ℝ) = (g z : ℝ) := by
  rw [extend_apply, extendFun_of_mem g z.2]

theorem extend_mem (g : UI ≃o UI) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    extend g x ∈ Icc (0 : ℝ) 1 := by
  rw [extend_apply, extendFun_of_mem g hx]; exact (g _).2

/-! ### Dyadic numbers -/

theorem isDyadic_add_half {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) :
    IsDyadic ((x + y) / 2) := by
  obtain ⟨m, k, rfl⟩ := hx
  obtain ⟨m', k', rfl⟩ := hy
  refine ⟨m * 2 ^ k' + m' * 2 ^ k, k + k' + 1, ?_⟩
  push_cast
  field_simp
  ring

theorem isDyadic_dyadicNode (w : List Bool) :
    IsDyadic (dyadicNode w).1 ∧ IsDyadic (dyadicNode w).2 := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨⟨0, 0, by simp [Mink.dyadicNode_nil]⟩, ⟨1, 0, by simp [Mink.dyadicNode_nil]⟩⟩
  | append_singleton w b ih =>
    cases b
    · rw [Mink.dyadicNode_append_false]; exact ⟨ih.1, isDyadic_add_half ih.1 ih.2⟩
    · rw [Mink.dyadicNode_append_true]; exact ⟨isDyadic_add_half ih.1 ih.2, ih.2⟩

/-! ### `IsThompson` from a chain of affine pieces -/

/-- An affine piece with power-of-two slope and dyadic ends. -/
def DPiece (G : ℝ → ℝ) (u v : ℝ) : Prop :=
  IsDyadic u ∧ IsDyadic v ∧ ∃ n : ℤ, ∃ c : ℝ, ∀ z ∈ Icc u v, G z = 2 ^ n * z + c

theorem isThompson_of_chain (g : UI ≃o UI) (ys : List ℝ) (h0 : ys.head? = some 0)
    (h1 : ys.getLast? = some 1) (hc : ys.IsChain (DPiece (extend g))) : IsThompson g := by
  classical
  obtain ⟨a, l, rfl⟩ : ∃ a l, ys = a :: l := by
    cases ys with
    | nil => simp at h0
    | cons a l => exact ⟨a, l, rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at h0
  subst h0
  refine ⟨((0 : ℝ) :: l).toFinset.filter IsDyadic, fun b hb => (Finset.mem_filter.mp hb).2, ?_⟩
  intro x y hxy hB
  obtain ⟨u, v, hu, hv, ⟨du, dv, n, c, hpc⟩, hum, hmv⟩ :=
    chain_cover l 0 1 (((x : ℝ) + y) / 2) hc h1 zero_lt_one (by linarith [x.2.1, y.2.1])
      (by linarith [x.2.2, y.2.2])
  have hux : u ≤ x := by
    by_contra hcon
    have : u ∈ Ioo (x : ℝ) y ∩ ↑(((0 : ℝ) :: l).toFinset.filter IsDyadic) :=
      ⟨⟨lt_of_not_ge hcon, by linarith⟩, by simpa [List.mem_toFinset, du] using hu⟩
    rw [hB] at this; exact this
  have hyv : (y : ℝ) ≤ v := by
    by_contra hcon
    have : v ∈ Ioo (x : ℝ) y ∩ ↑(((0 : ℝ) :: l).toFinset.filter IsDyadic) :=
      ⟨⟨by linarith, lt_of_not_ge hcon⟩, by simpa [List.mem_toFinset, dv] using hv⟩
    rw [hB] at this; exact this
  refine ⟨n, c, fun z hz => ?_⟩
  rw [← extend_coe]
  exact hpc z ⟨hux.trans hz.1, hz.2.trans hyv⟩

end CannonFloydParry.S7

namespace CannonFloydParry

end CannonFloydParry

/-!
# Transport of tree diagrams through Minkowski's `?` (CFP p. 253)

`RepresentsPIP d f ↔ Represents d (minkIso * f * minkIso⁻¹)`, the bijection milestone, and
`PIP⁺([0,1])` as the conjugate of `F`.
-/

namespace CannonFloydParry.S7

open Set

/-- Conjugation by Minkowski's `?`. -/
noncomputable def cj : (UI ≃o UI) ≃* (UI ≃o UI) := MulAut.conj minkIso

theorem cj_apply (f : UI ≃o UI) (x : UI) : cj f x = minkIso (f (minkIso.symm x)) := by
  simp only [cj, MulAut.conj_apply]; rfl

theorem minkIso_mk {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    minkIso ⟨x, hx⟩ = ⟨mink x, Mink.mink_mem hx⟩ := Subtype.ext rfl

theorem extend_cj (f : UI ≃o UI) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    extend (cj f) (mink x) = mink (extend f x) := by
  have hm := Mink.mink_mem hx
  rw [extend_apply, extendFun_of_mem _ hm, extend_apply, extendFun_of_mem _ hx, cj_apply,
    ← minkIso_mk hx, OrderIso.symm_apply_apply]
  rfl

theorem mink_injOn : InjOn mink (Icc (0 : ℝ) 1) := Mink.mink_strictMonoOn.injOn

theorem map_mink_inj : ∀ (l₁ l₂ : List ℝ), (∀ x ∈ l₁, x ∈ Icc (0 : ℝ) 1) →
    (∀ x ∈ l₂, x ∈ Icc (0 : ℝ) 1) → l₁.map mink = l₂.map mink → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [mink_injOn (h₁ a (by simp)) (h₂ b (by simp)) h.1,
      map_mink_inj l₁ l₂ (fun x hx => h₁ x (by simp [hx])) (fun x hx => h₂ x (by simp [hx])) h.2]

theorem ip_congr {U : Set ℝ} {f g : ℝ → ℝ} (h : IsIntegralProjective01 U g) (he : EqOn f g U) :
    IsIntegralProjective01 U f := by
  obtain ⟨hU, A, hA⟩ := h
  refine ⟨hU, A, fun t ht => ?_⟩
  rw [he ht]; exact hA t ht

/-- A point of a dyadic node is `mink` of a point of the Farey node. -/
theorem exists_mink_eq (w : List Bool) {z : ℝ}
    (hz : z ∈ Icc (mink (fareyNode w).lo) (mink (fareyNode w).hi)) :
    ∃ x ∈ Icc (fareyNode w).lo (fareyNode w).hi, mink x = z := by
  have hz01 : z ∈ Icc (0 : ℝ) 1 :=
    ⟨(Mink.mink_mem (fareyNode_lo_mem w)).1.trans hz.1,
      hz.2.trans (Mink.mink_mem (fareyNode_hi_mem w)).2⟩
  rw [← Mink.mink_image] at hz01
  obtain ⟨x, hx, rfl⟩ := hz01
  refine ⟨x, ⟨?_, ?_⟩, rfl⟩
  · exact (Mink.mink_strictMonoOn.le_iff_le (fareyNode_lo_mem w) hx).mp hz.1
  · exact (Mink.mink_strictMonoOn.le_iff_le hx (fareyNode_hi_mem w)).mp hz.2

theorem piece_fwd (f : UI ≃o UI) {p q : ℝ} (hip : IsIntegralProjective01 (Icc p q) (extend f))
    (h1 : FP p q) (h2 : FP (extend f p) (extend f q)) :
    DPiece (extend (cj f)) (mink p) (mink q) := by
  obtain ⟨w, rfl, rfl⟩ := h1
  obtain ⟨w', hp', hq'⟩ := h2
  have he := mob_unique (Mink.isFarey_fareyNode w) (Mink.isFarey_fareyNode w') hip hp'.symm
    hq'.symm
  rw [Mink.mink_lo, Mink.mink_hi]
  refine ⟨(isDyadic_dyadicNode w).1, (isDyadic_dyadicNode w).2, (w.length : ℤ) - w'.length,
    (dyadicNode w').1 - 2 ^ ((w.length : ℤ) - w'.length) * (dyadicNode w).1, ?_⟩
  intro z hz
  rw [← Mink.mink_lo, ← Mink.mink_hi] at hz
  obtain ⟨x, hx, rfl⟩ := exists_mink_eq w hz
  rw [extend_cj f (fareyNode_Icc_subset w hx), he hx, mink_mob w w' hx, width_ratio]
  ring

theorem piece_bwd (f : UI ≃o UI) {p q : ℝ} (h1 : FP p q) (h2 : FP (extend f p) (extend f q))
    (ha : ∃ a c : ℝ, ∀ z ∈ Icc (mink p) (mink q), extend (cj f) z = a * z + c) :
    IsIntegralProjective01 (Icc p q) (extend f) := by
  obtain ⟨w, rfl, rfl⟩ := h1
  obtain ⟨w', hp', hq'⟩ := h2
  obtain ⟨a, c, hac⟩ := ha
  set I := fareyNode w
  set J := fareyNode w'
  have hI := Mink.isFarey_fareyNode w
  have hJ := Mink.isFarey_fareyNode w'
  refine ip_congr (mob_isIP hI hJ) (fun x hx => ?_)
  have hx01 := fareyNode_Icc_subset w hx
  apply mink_injOn (extend_mem f hx01) (fareyNode_Icc_subset w' (mob_bounds hI hJ hx))
  have key : ∀ y ∈ Icc I.lo I.hi, mink (extend f y) = a * mink y + c := by
    intro y hy
    rw [← extend_cj f (fareyNode_Icc_subset w hy)]
    exact hac _ ⟨Mink.mink_strictMonoOn.monotoneOn (fareyNode_lo_mem w)
      (fareyNode_Icc_subset w hy) hy.1, Mink.mink_strictMonoOn.monotoneOn
      (fareyNode_Icc_subset w hy) (fareyNode_hi_mem w) hy.2⟩
  have k1 := key _ (lo_mem hI)
  have k2 := key _ (hi_mem hI)
  rw [hp'.symm, hq'.symm] at *
  rw [← hp', Mink.mink_lo, Mink.mink_lo] at k1
  rw [← hq', Mink.mink_hi, Mink.mink_hi] at k2
  rw [key x hx, mink_mob w w' hx]
  have hw := dyadicNode_width_pos w
  have ha' : a = ((dyadicNode w').2 - (dyadicNode w').1) / ((dyadicNode w).2 - (dyadicNode w).1) := by
    field_simp; linarith
  rw [← ha']
  linarith

theorem fareyMarks_head (t : TTree) : (fareyMarks t).head? = some 0 := by simp [fareyMarks]

theorem fareyMarks_getLast (t : TTree) : (fareyMarks t).getLast? = some 1 := by
  simp only [fareyMarks]; rw [← List.cons_append, List.getLast?_append]; simp

theorem map_extend_fareyMarks (f : UI ≃o UI) (t : TTree) :
    (TTree.marks t).map (extend (cj f)) = ((fareyMarks t).map (extend f)).map mink := by
  rw [← Mink.map_mink_fareyMarks, List.map_map, List.map_map]
  apply List.map_congr_left
  intro x hx
  exact extend_cj f (mem_fareyMarks hx)

/-- Backward transport. -/
theorem transport_bwd {d : TreeDiagram} {f : UI ≃o UI}
    (hA : AffineOnPieces (extend (cj f)) (TTree.marks d.dom))
    (hM : (TTree.marks d.dom).map (extend (cj f)) = TTree.marks d.ran) : RepresentsPIP d f := by
  have hmap : (fareyMarks d.dom).map (extend f) = fareyMarks d.ran := by
    rw [map_extend_fareyMarks, ← Mink.map_mink_fareyMarks] at hM
    refine map_mink_inj _ _ ?_ (fun x hx => mem_fareyMarks hx) hM
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact extend_mem f (mem_fareyMarks hy)
  refine ⟨?_, hmap⟩
  have h3 := chain_fareyMarks d.ran
  rw [← hmap, List.isChain_map] at h3
  unfold AffineOnPieces at hA
  rw [← Mink.map_mink_fareyMarks, List.isChain_map] at hA
  exact (chain_and (chain_and (chain_fareyMarks d.dom) h3) hA).imp
    (fun p q hpq => piece_bwd f hpq.1.1 hpq.1.2 hpq.2)

theorem representsPIP_of_represents {d : TreeDiagram} {f : UI ≃o UI}
    (h : Represents d (cj f)) : RepresentsPIP d f :=
  transport_bwd h.2.1 h.2.2

theorem mem_PIPPlus01Set_of_representsPIP {d : TreeDiagram} {f : UI ≃o UI}
    (h : RepresentsPIP d f) : f ∈ PIPPlus01Set := by
  refine ⟨fareyMarks d.dom, ⟨fareyMarks_head _, fareyMarks_getLast _, ?_⟩, h.1⟩
  exact (chain_fareyMarks d.dom).imp (fun p q ⟨w, hp, hq⟩ => by
    rw [← hp, ← hq]; exact subsimplex_of_farey (Mink.isFarey_fareyNode w))

/-- An integral subsimplex is a Farey node. -/
theorem fp_of_subsimplex {p q : ℝ} (h : IsIntegralSubsimplex01 p q) : FP p q := by
  obtain ⟨K, hK, hp, hq⟩ := exists_farey_of_subsimplex h
  obtain ⟨w, rfl⟩ := exists_fareyNode hK
  exact ⟨w, hp, hq⟩

/-- The image of an integral subsimplex under an integral projective order isomorphism. -/
theorem subsimplex_image (f : UI ≃o UI) {p q : ℝ} (h : IsIntegralSubsimplex01 p q)
    (hip : IsIntegralProjective01 (Icc p q) (extend f)) :
    IsIntegralSubsimplex01 (extend f p) (extend f q) := by
  obtain ⟨K, hK, rfl, rfl⟩ := exists_farey_of_subsimplex h
  obtain ⟨-, A, hA⟩ := hip
  have hv := mob_via root_isFarey hK
  rw [root_Icc] at hv
  refine ⟨extend f ∘ mob root K, ⟨subset_rfl, _, ip_comp hA hv ?_⟩, ?_⟩
  · intro t ht
    rw [← root_Icc] at ht
    exact mob_bounds root_isFarey hK ht
  · rw [Set.image_comp, ← root_Icc, mob_image root_isFarey hK, OrderIso.image_Icc]

theorem mem_F_of_mem_PIPPlus01Set {f : UI ≃o UI} (hf : f ∈ PIPPlus01Set) : cj f ∈ F := by
  obtain ⟨xs, ⟨h0, h1, hsub⟩, hip⟩ := hf
  apply mem_F_of_isThompson
  refine isThompson_of_chain _ (xs.map mink) (by rw [List.head?_map, h0]; simp [Mink.mink_zero])
    (by rw [List.getLast?_map, h1]; simp [Mink.mink_one]) ?_
  rw [List.isChain_map]
  exact (chain_and hsub hip).imp (fun p q hpq =>
    piece_fwd f hpq.2 (fp_of_subsimplex hpq.1) (fp_of_subsimplex (subsimplex_image f hpq.1 hpq.2)))

theorem mem_PIPPlus01Set_iff (f : UI ≃o UI) : f ∈ PIPPlus01Set ↔ cj f ∈ F := by
  refine ⟨mem_F_of_mem_PIPPlus01Set, fun h => ?_⟩
  obtain ⟨d, -, hd⟩ := exists_isReduced_represents h
  exact mem_PIPPlus01Set_of_representsPIP (representsPIP_of_represents hd)


/-- `PIP⁺([0,1])` as a subgroup: the conjugate of `F`. -/
noncomputable def PIPPlus01 : Subgroup (UI ≃o UI) := F.map cj.symm.toMonoidHom

theorem coe_PIPPlus01 : (PIPPlus01 : Set (UI ≃o UI)) = PIPPlus01Set := by
  ext f
  simp only [SetLike.mem_coe, PIPPlus01, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  rw [mem_PIPPlus01Set_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩; rwa [MulEquiv.apply_symm_apply]
  · intro h; exact ⟨cj f, h, MulEquiv.symm_apply_apply _ _⟩

/-- `F ≅ PIP⁺([0,1])`, by `g ↦ minkIso⁻¹ g minkIso`. -/
noncomputable def mulEquivF : F ≃* PIPPlus01 :=
  F.equivMapOfInjective cj.symm.toMonoidHom cj.symm.injective

end CannonFloydParry.S7

/-!
# `Δ₁` versus `[0,1]` (CFP p. 251): coordinates, matrices, integral subsimplices
-/

namespace CannonFloydParry.S7

open Set

/-! ### The parametrization `t ↦ (t, 1 - t)` -/

/-- The point `(t, 1 - t)`. -/
def e1 (t : ℝ) : Fin 2 → ℝ := ![t, 1 - t]

@[simp] theorem e1_zero_apply (t : ℝ) : e1 t 0 = t := rfl
@[simp] theorem e1_one_apply (t : ℝ) : e1 t 1 = 1 - t := rfl

/-! ### `Δ₁ ≅ [0,1]` as spaces, and the induced homomorphism -/

/-! ### The change of coordinates `(x₀, x₁) ↦ (x₀, x₀ + x₁)` -/

/-! ### The pointwise dictionary -/

/-! ### Orientation -/

end CannonFloydParry.S7

/-!
# `Δ₁` versus `[0,1]`: integral subsimplices, and the subdivision of `Δ₁` cut out by a
partition of `[0,1]`
-/

namespace CannonFloydParry.S7

open Set

/-! ### Integral subsimplices -/

/-! ### Pieces of a finite set of breakpoints -/

end CannonFloydParry.S7

/-!
# `PIP⁺(Δ₁) ≅ PIP⁺([0,1])` and Theorem 7.2 `F ≅ PIP⁺(Δ₁)`
-/

namespace CannonFloydParry.S7

open Set

/-! ### Lists -/

/-! ### From `PIP⁺([0,1])` to `PIP⁺(Δ₁)` -/

/-! ### From `PIP⁺(Δ₁)` to `PIP⁺([0,1])` -/

/-! ### The targets -/

end CannonFloydParry.S7

open CannonFloydParry in
theorem solution :
    ∃ H : Subgroup (Simplex 1 ≃ₜ Simplex 1),
      (H : Set (Simplex 1 ≃ₜ Simplex 1)) = PIPPlusSet 1 ∧ Nonempty (F ≃* H) := by
  obtain ⟨H, K, hH, hK, φ, -⟩ := exists_mulEquiv_PIPPlusSet_one_PIPPlus01Set
  have hK' : S7.PIPPlus01 = K := SetLike.coe_injective (S7.coe_PIPPlus01.trans hK.symm)
  exact ⟨H, hH, ⟨(S7.mulEquivF.trans (MulEquiv.subgroupCongr hK')).trans φ.symm⟩⟩
