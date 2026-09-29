-- Prove2me | solution 1 for Garrido.isKleinFour_and_levelStabilizer_one_eq_closure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T13:16:24.501115+00:00
-- url     : https://prove2.me/submissions/a7a6a7b3-c6ba-464c-bb03-c22947adc471

import Mathlib
import Definitions.Def_Chou_Classes
import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Growth
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Garrido_Grigorchuk

namespace Garrido.GR.St

open Garrido

local notation "P" => Equiv.Perm (List Bool)
local notation "Γ" => GrigorchukGroup

theorem C1ext {g h : Γ} (H : ∀ w, ((g : BinaryTreeAut) : P) w = ((h : BinaryTreeAut) : P) w) :
    g = h :=
  Subtype.ext (Subtype.ext (Equiv.ext H))

@[simp] theorem C1a_apply (w : List Bool) :
    (((GrigorchukGroup.a : Γ) : BinaryTreeAut) : P) w = grigAFun w := rfl
@[simp] theorem C1b_apply (w : List Bool) :
    (((GrigorchukGroup.b : Γ) : BinaryTreeAut) : P) w = grigBFun w := rfl
@[simp] theorem C1c_apply (w : List Bool) :
    (((GrigorchukGroup.c : Γ) : BinaryTreeAut) : P) w = grigCFun w := rfl
@[simp] theorem C1d_apply (w : List Bool) :
    (((GrigorchukGroup.d : Γ) : BinaryTreeAut) : P) w = grigDFun w := rfl
@[simp] theorem C1mul_apply (g h : Γ) (w : List Bool) :
    (((g * h : Γ) : BinaryTreeAut) : P) w =
      ((g : BinaryTreeAut) : P) (((h : BinaryTreeAut) : P) w) := rfl
@[simp] theorem C1one_apply (w : List Bool) : (((1 : Γ) : BinaryTreeAut) : P) w = w := rfl

theorem C1len (g : Γ) (v : List Bool) : (((g : BinaryTreeAut) : P) v).length = v.length :=
  (g : BinaryTreeAut).2.1 v

theorem C1bcd (w : List Bool) :
    grigBFun (grigCFun w) = grigDFun w ∧ grigCFun (grigBFun w) = grigDFun w ∧
    grigCFun (grigDFun w) = grigBFun w ∧ grigDFun (grigCFun w) = grigBFun w ∧
    grigBFun (grigDFun w) = grigCFun w ∧ grigDFun (grigBFun w) = grigCFun w := by
  induction w with
  | nil => simp [grigBFun, grigCFun, grigDFun]
  | cons x w ih =>
    cases x <;> simp [grigBFun, grigCFun, grigDFun, grigAFun_involutive w, ih]

open GrigorchukGroup in
theorem C1aa : a * a = 1 := C1ext fun w => by simp [grigAFun_involutive w]
open GrigorchukGroup in
theorem C1bb : b * b = 1 := C1ext fun w => by simp [(grigBCD_involutive w).1]
open GrigorchukGroup in
theorem C1cc : c * c = 1 := C1ext fun w => by simp [(grigBCD_involutive w).2.1]
open GrigorchukGroup in
theorem C1dd : d * d = 1 := C1ext fun w => by simp [(grigBCD_involutive w).2.2]
open GrigorchukGroup in
theorem C1bc : b * c = d := C1ext fun w => by simp [(C1bcd w).1]
open GrigorchukGroup in
theorem C1cb : c * b = d := C1ext fun w => by simp [(C1bcd w).2.1]
open GrigorchukGroup in
theorem C1cd : c * d = b := C1ext fun w => by simp [(C1bcd w).2.2.1]
open GrigorchukGroup in
theorem C1dc : d * c = b := C1ext fun w => by simp [(C1bcd w).2.2.2.1]
open GrigorchukGroup in
theorem C1bd : b * d = c := C1ext fun w => by simp [(C1bcd w).2.2.2.2.1]
open GrigorchukGroup in
theorem C1db : d * b = c := C1ext fun w => by simp [(C1bcd w).2.2.2.2.2]
open GrigorchukGroup in
theorem C1ainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right C1aa

/-- Induction over `Γ` along its generators. -/
theorem C1induction {p : Γ → Prop} (one : p 1) (ha : p GrigorchukGroup.a)
    (hb : p GrigorchukGroup.b) (hc : p GrigorchukGroup.c) (hd : p GrigorchukGroup.d)
    (mul : ∀ x y, p x → p y → p (x * y)) (inv : ∀ x, p x → p x⁻¹) (g : Γ) : p g := by
  obtain ⟨g, hg⟩ := g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  | one => exact one
  | mul x y hx hy ihx ihy => exact mul _ _ ihx ihy
  | inv x hx ih => exact inv _ ih

/-! ### Target 1 -/



/-! ### Target 2 -/

theorem C1ne {g h : Γ} (w : List Bool)
    (H : ((g : BinaryTreeAut) : P) w ≠ ((h : BinaryTreeAut) : P) w) : g ≠ h := by
  rintro rfl; exact H rfl

open GrigorchukGroup in
theorem C1closure_bc :
    ((Subgroup.closure {b, c} : Subgroup Γ) : Set Γ) = {1, b, c, d} := by
  apply Set.Subset.antisymm
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => rcases hx with rfl | rfl <;> simp
    | one => simp
    | mul x y _ _ ihx ihy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ihx ihy ⊢
      rcases ihx with rfl | rfl | rfl | rfl <;> rcases ihy with rfl | rfl | rfl | rfl <;>
        simp [C1bb, C1cc, C1dd, C1bc, C1cb, C1cd, C1dc, C1bd, C1db]
    | inv x _ ih =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ih ⊢
      rcases ih with rfl | rfl | rfl | rfl
      · simp
      · rw [inv_eq_of_mul_eq_one_right C1bb]; simp
      · rw [inv_eq_of_mul_eq_one_right C1cc]; simp
      · rw [inv_eq_of_mul_eq_one_right C1dd]; simp
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · rw [← C1bc]
      exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

open GrigorchukGroup in
theorem C1distinct : (1 : Γ) ≠ b ∧ (1 : Γ) ≠ c ∧ (1 : Γ) ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  refine ⟨C1ne [false, false] ?_, C1ne [false, false] ?_, C1ne [true, false, false] ?_,
    C1ne [true, false, false] ?_, C1ne [false, false] ?_, C1ne [false, false] ?_⟩ <;>
    simp [grigAFun, grigBFun, grigCFun, grigDFun]

open GrigorchukGroup in
theorem C1kleinFour : IsKleinFour (Subgroup.closure {b, c} : Subgroup Γ) := by
  have hS := C1closure_bc
  obtain ⟨h1b, h1c, h1d, hbc, hbd, hcd⟩ := C1distinct
  have hbmem : b ∈ (Subgroup.closure {b, c} : Subgroup Γ) := Subgroup.subset_closure (by simp)
  have : Nontrivial (Subgroup.closure {b, c} : Subgroup Γ) :=
    ⟨⟨⟨b, hbmem⟩, 1, fun h => h1b (congrArg Subtype.val h).symm⟩⟩
  refine ⟨?_, ?_⟩
  · rw [← SetLike.coe_sort_coe, hS, Nat.card_coe_set_eq]
    rw [Set.ncard_insert_of_notMem (by simp [h1b, h1c, h1d]),
      Set.ncard_insert_of_notMem (by simp [hbc, hbd]),
      Set.ncard_insert_of_notMem (by simp [hcd]), Set.ncard_singleton]
  · rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    apply orderOf_eq_prime _ hg
    have hmem : (g : Γ) ∈ ({1, b, c, d} : Set Γ) := hS ▸ g.2
    apply Subtype.ext
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    simp only [OneMemClass.coe_one, pow_two]
    rcases hmem with h | h | h | h <;> rw [Subgroup.coe_mul, h]
    · simp
    · exact C1bb
    · exact C1cc
    · exact C1dd

theorem C1mem_st1 {g : Γ} : g ∈ levelStabilizer 1 ↔
    ((g : BinaryTreeAut) : P) [false] = [false] ∧ ((g : BinaryTreeAut) : P) [true] = [true] := by
  constructor
  · intro h; exact ⟨h _ rfl, h _ rfl⟩
  · rintro ⟨h0, h1⟩ v hv
    match v, hv with
    | [false], _ => exact h0
    | [true], _ => exact h1

open GrigorchukGroup in
theorem C1conj (h : Γ) (hh : h ∈ Subgroup.closure {b, c, a⁻¹ * b * a, a⁻¹ * c * a}) :
    a * h * a ∈ Subgroup.closure {b, c, a⁻¹ * b * a, a⁻¹ * c * a} := by
  rw [C1ainv] at hh ⊢
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · have : a * (a * b * a) * a = b := by
        calc a * (a * b * a) * a = (a * a) * b * (a * a) := by group
          _ = b := by simp [C1aa]
      rw [this]; exact Subgroup.subset_closure (by simp)
    · have : a * (a * c * a) * a = c := by
        calc a * (a * c * a) * a = (a * a) * c * (a * a) := by group
          _ = c := by simp [C1aa]
      rw [this]; exact Subgroup.subset_closure (by simp)
  | one => rw [mul_one, C1aa]; exact one_mem _
  | mul x y _ _ ihx ihy =>
    have : a * (x * y) * a = (a * x * a) * (a * y * a) := by
      calc a * (x * y) * a = a * x * (a * a) * y * a := by rw [C1aa]; group
        _ = _ := by group
    rw [this]; exact mul_mem ihx ihy
  | inv x _ ih =>
    have : a * x⁻¹ * a = (a * x * a)⁻¹ := by
      conv_rhs => rw [mul_inv_rev, mul_inv_rev, C1ainv]
      group
    rw [this]; exact inv_mem ih

open GrigorchukGroup in
theorem isKleinFour_and_levelStabilizer_one_eq_closure' :
    ((Subgroup.closure {GrigorchukGroup.b, GrigorchukGroup.c} : Subgroup GrigorchukGroup) :
        Set GrigorchukGroup) = {1, GrigorchukGroup.b, GrigorchukGroup.c, GrigorchukGroup.d} ∧
      IsKleinFour (Subgroup.closure {GrigorchukGroup.b, GrigorchukGroup.c} : Subgroup GrigorchukGroup) ∧
      levelStabilizer 1 = Subgroup.closure {GrigorchukGroup.b, GrigorchukGroup.c,
        GrigorchukGroup.a⁻¹ * GrigorchukGroup.b * GrigorchukGroup.a,
        GrigorchukGroup.a⁻¹ * GrigorchukGroup.c * GrigorchukGroup.a} := by
  refine ⟨C1closure_bc, C1kleinFour, ?_⟩
  set H : Subgroup Γ := Subgroup.closure {b, c, a⁻¹ * b * a, a⁻¹ * c * a} with hH
  have hHst : H ≤ levelStabilizer 1 := by
    rw [hH, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, C1ainv] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> rw [SetLike.mem_coe, C1mem_st1] <;>
      simp [grigAFun, grigBFun, grigCFun, grigDFun]
  have hmemH : ∀ x ∈ ({b, c, a⁻¹ * b * a, a⁻¹ * c * a} : Set Γ), x ∈ H :=
    fun x hx => Subgroup.subset_closure hx
  have hall : ∀ g : Γ, g ∈ H ∨ a * g ∈ H := by
    intro g
    induction g using C1induction with
    | one => exact Or.inl (one_mem _)
    | ha => exact Or.inr (by rw [C1aa]; exact one_mem _)
    | hb => exact Or.inl (hmemH _ (by simp))
    | hc => exact Or.inl (hmemH _ (by simp))
    | hd => exact Or.inl (by rw [← C1bc]; exact mul_mem (hmemH _ (by simp)) (hmemH _ (by simp)))
    | mul x y hx hy =>
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (mul_mem hx hy)
      · right
        have : a * (x * y) = (a * x * a) * (a * y) := by
          calc a * (x * y) = a * x * (a * a) * y := by rw [C1aa]; group
            _ = _ := by group
        rw [this]; exact mul_mem (C1conj x hx) hy
      · right; rw [← mul_assoc]; exact mul_mem hx hy
      · left
        have : x * y = (a * (a * x) * a) * (a * y) := by
          calc x * y = (a * a) * x * (a * a) * y := by rw [C1aa]; group
            _ = _ := by group
        rw [this]; exact mul_mem (C1conj _ hx) hy
    | inv x hx =>
      rcases hx with hx | hx
      · exact Or.inl (inv_mem hx)
      · right
        have : a * x⁻¹ = (a * (a * x) * a)⁻¹ := by
          simp only [mul_inv_rev, C1ainv, mul_assoc, C1aa, mul_one]
        rw [this]; exact inv_mem (C1conj _ hx)
  apply le_antisymm _ hHst
  intro g hg
  rcases hall g with h | h
  · exact h
  · exfalso
    have h1 : a * g ∈ levelStabilizer 1 := hHst h
    have h2 : a ∈ levelStabilizer 1 := by
      have := mul_mem h1 (inv_mem hg)
      rwa [mul_inv_cancel_right] at this
    have := (C1mem_st1.mp h2).1
    simp [grigAFun] at this


/-! ### Target 3 -/



end Garrido.GR.St

namespace Garrido.GR.Sec

open Garrido

local notation "P" => Equiv.Perm (List Bool)


end Garrido.GR.Sec

namespace Garrido.GR.Tor

open Equiv

abbrev P' := Perm (List Bool)

def pairFun (u v : List Bool → List Bool) : List Bool → List Bool
  | [] => []
  | false :: w => false :: u w
  | true :: w => true :: v w

def pr (u v : P') : P' where
  toFun := pairFun u v
  invFun := pairFun ⇑u⁻¹ ⇑v⁻¹
  left_inv w := by rcases w with _ | ⟨_ | _, w⟩ <;> simp [pairFun]
  right_inv w := by rcases w with _ | ⟨_ | _, w⟩ <;> simp [pairFun]

@[simp] lemma pr_nil (u v : P') : pr u v [] = [] := rfl
@[simp] lemma pr_false (u v : P') (w) : pr u v (false :: w) = false :: u w := rfl
@[simp] lemma pr_true (u v : P') (w) : pr u v (true :: w) = true :: v w := rfl

lemma pr_mul (u v u' v' : P') : pr u v * pr u' v' = pr (u * u') (v * v') := by
  ext w; rcases w with _ | ⟨_ | _, w⟩ <;> simp

def σ : P' := ((grigA : BinaryTreeAut) : P')
def eB : P' := ((grigB : BinaryTreeAut) : P')
def eC : P' := ((grigC : BinaryTreeAut) : P')
def eD : P' := ((grigD : BinaryTreeAut) : P')

@[simp] lemma σ_apply (w) : σ w = grigAFun w := rfl
@[simp] lemma eB_apply (w) : eB w = grigBFun w := rfl
@[simp] lemma eC_apply (w) : eC w = grigCFun w := rfl
@[simp] lemma eD_apply (w) : eD w = grigDFun w := rfl

lemma σ_pr (u v : P') : σ * pr u v = pr v u * σ := by
  ext w; rcases w with _ | ⟨_ | _, w⟩ <;> simp [grigAFun]

inductive L | a | b | c | d
  deriving DecidableEq

def ev : L → P'
  | .a => σ
  | .b => eB
  | .c => eC
  | .d => eD

def ew (w : List L) : P' := (w.map ev).prod

@[simp] lemma ew_nil : ew [] = 1 := rfl
@[simp] lemma ew_cons (x : L) (w : List L) : ew (x :: w) = ev x * ew w := by simp [ew]
@[simp] lemma ew_append (u v : List L) : ew (u ++ v) = ew u * ew v := by simp [ew]

lemma ev_sq (x : L) : ev x * ev x = 1 := by
  cases x <;> ext w <;>
    simp [ev, grigAFun_involutive w, (grigBCD_involutive w).1, (grigBCD_involutive w).2.1,
      (grigBCD_involutive w).2.2]

/-! ### The torsion predicate -/


end Garrido.GR.Tor

/-!
# Lemma 4.8 of Garrido's notes: `∑_{v ∈ level 3} l(g|_v) ≤ 3/4 l(g) + 8`

Proof strategy (block decomposition).

* Words in the letters `a, b, c, d` (`Ltr`) evaluate to `Γ` (`ev`).  The level-1 section of the
  element represented by a word is represented by an explicit word (`sec1`), computed letter by
  letter (`b = (a, c)`, `c = (a, d)`, `d = (1, b)`); iterating gives level-3 sections (`sec3`).
* Sections are a cocycle: `sec3 (u ++ u') v = sec3 u (act3 u' v) ++ sec3 u' v`, where
  `act3 u'` is a bijection of the 8 level-3 vertices.  Hence if `u` and `u'` have level-3
  sections of total lengths `≤ K` and `≤ K'`, so has `u ++ u'`, with `K + K'`.
* A shortest word for `g` reduces (free product `ℤ/2 * (ℤ/2)²`) to a normal form
  `[a] x₁ a x₂ a … xₘ a [x]`.  Cut `x₁ a … xₘ a` greedily into blocks `xᵢ a … xⱼ a` with
  `4 F(block) ≤ 3 |block|`, where `F` is the total length of the reduced level-3 sections: a
  finite check (`check_nil_eight`, by `decide`) shows every run of 8 pairs has such a prefix.
  Fewer than 8 pairs left over, and the end letters, cost a bounded amount.

The hypothesis `g ∈ St(3)` is not needed.
-/

namespace Garrido.GR.L48

open Garrido

/-! ### Letters and evaluation -/

inductive Ltr | a | b | c | d
  deriving DecidableEq, Repr

inductive NL | b | c | d
  deriving DecidableEq, Repr

/-- The product of two distinct non-`a` letters. -/
def NL.mul : NL → NL → NL
  | .b, .c => .d
  | .c, .b => .d
  | .b, .d => .c
  | .d, .b => .c
  | .c, .d => .b
  | .d, .c => .b
  | x, _ => x

def ltrAut : Ltr → BinaryTreeAut
  | .a => grigA
  | .b => grigB
  | .c => grigC
  | .d => grigD

theorem ltrAut_mem (x : Ltr) : ltrAut x ∈ GrigorchukGroup := by
  apply Subgroup.subset_closure
  cases x <;> simp [ltrAut]

def ltrG (x : Ltr) : GrigorchukGroup := ⟨ltrAut x, ltrAut_mem x⟩

def ev (u : List Ltr) : GrigorchukGroup := (u.map ltrG).prod

/-! ### Relations -/

/-! ### Sections of words -/

/-! ### Reduction to normal form `[a] x₁ a … xₘ a [x]` -/

structure NF where
  lead : Bool
  xs : List NL
  t : Option NL

/-! ### The finite check -/

/-! ### Bounds on the total length of level-3 sections -/

/-! ### Words and word length in `Γ` -/

/-! ### Lemma 4.8 -/


end Garrido.GR.L48

namespace Garrido.GR.Gro

open Chou

section Ball
variable {G : Type*} [Group G] (S : Set G)

end Ball

section Index
variable {G : Type*} [Group G] (S : Set G) (H : Subgroup G)


end Index

section Grig

section Hyp
variable (h_psi : ∀ n : ℕ,
    (∀ g : GrigorchukGroup, g ∈ levelStabilizer n → ∀ v : Fin n → Bool,
        treeSection (g : BinaryTreeAut) (List.ofFn v) ∈ GrigorchukGroup) ∧
      (∀ g h : GrigorchukGroup, g ∈ levelStabilizer n → h ∈ levelStabilizer n →
        ∀ v : Fin n → Bool, treeSection ((g * h : GrigorchukGroup) : BinaryTreeAut) (List.ofFn v) =
          treeSection (g : BinaryTreeAut) (List.ofFn v) * treeSection (h : BinaryTreeAut) (List.ofFn v)) ∧
      ∀ g h : GrigorchukGroup, g ∈ levelStabilizer n → h ∈ levelStabilizer n →
        (∀ v : Fin n → Bool, treeSection (g : BinaryTreeAut) (List.ofFn v) =
          treeSection (h : BinaryTreeAut) (List.ofFn v)) → g = h)

variable (h48 : ∀ (g : GrigorchukGroup) (hg : g ∈ levelStabilizer 3)
    (h : (Fin 3 → Bool) → GrigorchukGroup)
    (hh : ∀ v, (h v : BinaryTreeAut) = treeSection (g : BinaryTreeAut) (List.ofFn v)),
    (∑ v, (wordLength (h v) : ℝ)) ≤ 3 / 4 * (wordLength g : ℝ) + 8)

variable (h_index : (levelStabilizer 3).index = 2 ^ 7)

end Hyp


end Grig

end Garrido.GR.Gro

namespace Garrido.GR.Final

open Garrido


theorem isKleinFour_and_levelStabilizer_one_eq_closure :
    ((Subgroup.closure {GrigorchukGroup.b, GrigorchukGroup.c} : Subgroup GrigorchukGroup) :
        Set GrigorchukGroup) = {1, GrigorchukGroup.b, GrigorchukGroup.c, GrigorchukGroup.d} ∧
      IsKleinFour (Subgroup.closure {GrigorchukGroup.b, GrigorchukGroup.c} : Subgroup GrigorchukGroup) ∧
      levelStabilizer 1 = Subgroup.closure {GrigorchukGroup.b, GrigorchukGroup.c,
        GrigorchukGroup.a⁻¹ * GrigorchukGroup.b * GrigorchukGroup.a,
        GrigorchukGroup.a⁻¹ * GrigorchukGroup.c * GrigorchukGroup.a} :=
  by first | exact Garrido.GR.St.isKleinFour_and_levelStabilizer_one_eq_closure' | (intros; apply Garrido.GR.St.isKleinFour_and_levelStabilizer_one_eq_closure' <;> assumption)


end Garrido.GR.Final

open Garrido

theorem solution :
    ((Subgroup.closure {GrigorchukGroup.b, GrigorchukGroup.c} : Subgroup GrigorchukGroup) :
        Set GrigorchukGroup) = {1, GrigorchukGroup.b, GrigorchukGroup.c, GrigorchukGroup.d} ∧
      IsKleinFour (Subgroup.closure {GrigorchukGroup.b, GrigorchukGroup.c} : Subgroup GrigorchukGroup) ∧
      levelStabilizer 1 = Subgroup.closure {GrigorchukGroup.b, GrigorchukGroup.c,
        GrigorchukGroup.a⁻¹ * GrigorchukGroup.b * GrigorchukGroup.a,
        GrigorchukGroup.a⁻¹ * GrigorchukGroup.c * GrigorchukGroup.a} :=
  Garrido.GR.Final.isKleinFour_and_levelStabilizer_one_eq_closure
