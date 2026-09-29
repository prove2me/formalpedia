-- Prove2me | solution 1 for Garrido.sum_wordLength_treeSection_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T13:16:24.401028+00:00
-- url     : https://prove2.me/submissions/6f6d229d-5760-4698-afaa-b70e5d5f6b46

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

/-! ### Target 1 -/



/-! ### Target 2 -/



/-! ### Target 3 -/



end Garrido.GR.St

namespace Garrido.GR.Sec

open Garrido

local notation "P" => Equiv.Perm (List Bool)

theorem bta_ext {g h : BinaryTreeAut} (H : ∀ w, (g : P) w = (h : P) w) : g = h :=
  Subtype.ext (Equiv.ext H)

theorem treeSection_apply (g : BinaryTreeAut) (v w : List Bool) :
    ((treeSection g v : BinaryTreeAut) : P) w = ((g : P) (v ++ w)).drop v.length := rfl

theorem treeSection_append (g : BinaryTreeAut) (v v' : List Bool) :
    treeSection g (v ++ v') = treeSection (treeSection g v) v' := by
  apply bta_ext; intro w
  simp [treeSection_apply, List.drop_drop, List.append_assoc]


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

/-- reducible adjacent pair -/
def red (x y : L) : Prop := (x = .a ∧ y = .a) ∨ (x ≠ .a ∧ y ≠ .a)

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

def NL.toL : NL → Ltr
  | .b => .b
  | .c => .c
  | .d => .d

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

def ltrFun : Ltr → List Bool → List Bool
  | .a => grigAFun
  | .b => grigBFun
  | .c => grigCFun
  | .d => grigDFun

theorem ltrAut_apply (x : Ltr) (w : List Bool) :
    ((ltrAut x : BinaryTreeAut) : Equiv.Perm (List Bool)) w = ltrFun x w := by
  cases x <;> rfl

theorem ltrAut_mem (x : Ltr) : ltrAut x ∈ GrigorchukGroup := by
  apply Subgroup.subset_closure
  cases x <;> simp [ltrAut]

def ltrG (x : Ltr) : GrigorchukGroup := ⟨ltrAut x, ltrAut_mem x⟩

def evAut (u : List Ltr) : BinaryTreeAut := (u.map ltrAut).prod

def ev (u : List Ltr) : GrigorchukGroup := (u.map ltrG).prod

theorem coe_ev (u : List Ltr) : (ev u : BinaryTreeAut) = evAut u := by
  induction u with
  | nil => rfl
  | cons x u ih => simp [ev, evAut, ltrG] at ih ⊢; rw [ih]

theorem evAut_cons (x : Ltr) (u : List Ltr) : evAut (x :: u) = ltrAut x * evAut u := by
  simp [evAut]

theorem evAut_append (u u' : List Ltr) : evAut (u ++ u') = evAut u * evAut u' := by
  simp [evAut]

theorem ev_cons (x : Ltr) (u : List Ltr) : ev (x :: u) = ltrG x * ev u := by
  simp [ev]

theorem ev_append (u u' : List Ltr) : ev (u ++ u') = ev u * ev u' := by
  simp [ev]

/-! ### Relations -/

theorem fun_rel (w : List Bool) :
    grigBFun (grigCFun w) = grigDFun w ∧ grigCFun (grigBFun w) = grigDFun w ∧
    grigBFun (grigDFun w) = grigCFun w ∧ grigDFun (grigBFun w) = grigCFun w ∧
    grigCFun (grigDFun w) = grigBFun w ∧ grigDFun (grigCFun w) = grigBFun w := by
  induction w with
  | nil => simp [grigBFun, grigCFun, grigDFun]
  | cons x w ih =>
    cases x <;> simp [grigBFun, grigCFun, grigDFun, grigAFun_involutive w, ih.1, ih.2.1,
      ih.2.2.1, ih.2.2.2.1, ih.2.2.2.2.1, ih.2.2.2.2.2]

theorem ltrFun_invol (x : Ltr) (w : List Bool) : ltrFun x (ltrFun x w) = w := by
  cases x
  · exact grigAFun_involutive w
  · exact (grigBCD_involutive w).1
  · exact (grigBCD_involutive w).2.1
  · exact (grigBCD_involutive w).2.2

theorem ltrAut_mul_self (x : Ltr) : ltrAut x * ltrAut x = 1 := by
  apply Subtype.ext; apply Equiv.ext; intro w
  simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, ltrAut_apply,
    ltrFun_invol, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]

theorem ltrAut_mul_NL (x y : NL) (hxy : x ≠ y) :
    ltrAut x.toL * ltrAut y.toL = ltrAut (x.mul y).toL := by
  apply Subtype.ext; apply Equiv.ext; intro w
  simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, ltrAut_apply]
  have := fun_rel w
  cases x <;> cases y <;> simp_all [NL.toL, NL.mul, ltrFun]

theorem ltrG_mul_self (x : Ltr) : ltrG x * ltrG x = 1 :=
  Subtype.ext (ltrAut_mul_self x)

theorem ltrG_mul_NL (x y : NL) (hxy : x ≠ y) :
    ltrG x.toL * ltrG y.toL = ltrG (x.mul y).toL :=
  Subtype.ext (ltrAut_mul_NL x y hxy)

/-! ### Sections of words -/

/-- Whether letter `x` changes the first letter of a vertex. -/
def flipL : Ltr → Bool → Bool
  | .a, p => !p
  | _, p => p

/-- The level-1 section of a letter at vertex `[p]`, as a word. -/
def secL : Ltr → Bool → List Ltr
  | .a, _ => []
  | .b, false => [.a]
  | .b, true => [.c]
  | .c, false => [.a]
  | .c, true => [.d]
  | .d, false => []
  | .d, true => [.b]

/-- The first letter of the image of vertex `p :: _` under the word `u`. -/
def act1 : List Ltr → Bool → Bool
  | [], p => p
  | x :: u, p => flipL x (act1 u p)

/-- The level-1 section of (the element represented by) `u` at `[p]`, as a word. -/
def sec1 : List Ltr → Bool → List Ltr
  | [], _ => []
  | x :: u, p => secL x (act1 u p) ++ sec1 u p

theorem evAut_apply_cons (x : Ltr) (u : List Ltr) (w : List Bool) :
    ((evAut (x :: u) : BinaryTreeAut) : Equiv.Perm (List Bool)) w =
      ltrFun x (((evAut u : BinaryTreeAut) : Equiv.Perm (List Bool)) w) := by
  rw [evAut_cons]
  simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, ltrAut_apply]

theorem evAut_apply_append (u u' : List Ltr) (w : List Bool) :
    ((evAut (u ++ u') : BinaryTreeAut) : Equiv.Perm (List Bool)) w =
      ((evAut u : BinaryTreeAut) : Equiv.Perm (List Bool))
        (((evAut u' : BinaryTreeAut) : Equiv.Perm (List Bool)) w) := by
  rw [evAut_append]
  simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply]

theorem evAut_nil_apply (w : List Bool) :
    ((evAut [] : BinaryTreeAut) : Equiv.Perm (List Bool)) w = w := rfl

theorem ltrFun_cons (x : Ltr) (p : Bool) (w : List Bool) :
    ltrFun x (p :: w) =
      flipL x p :: ((evAut (secL x p) : BinaryTreeAut) : Equiv.Perm (List Bool)) w := by
  cases x <;> cases p <;>
    simp [ltrFun, flipL, secL, grigAFun, grigBFun, grigCFun, grigDFun, evAut_apply_cons,
      evAut_nil_apply]

theorem evAut_apply_cons_vertex (u : List Ltr) (p : Bool) (w : List Bool) :
    ((evAut u : BinaryTreeAut) : Equiv.Perm (List Bool)) (p :: w) =
      act1 u p :: ((evAut (sec1 u p) : BinaryTreeAut) : Equiv.Perm (List Bool)) w := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    rw [evAut_apply_cons, ih, ltrFun_cons, act1, sec1, evAut_apply_append]

theorem treeSection_append (g : BinaryTreeAut) (v₁ v₂ : List Bool) :
    treeSection g (v₁ ++ v₂) = treeSection (treeSection g v₁) v₂ := by
  apply Subtype.ext; apply Equiv.ext; intro w
  show ((g : Equiv.Perm (List Bool)) ((v₁ ++ v₂) ++ w)).drop (v₁ ++ v₂).length =
    (((g : Equiv.Perm (List Bool)) (v₁ ++ (v₂ ++ w))).drop v₁.length).drop v₂.length
  rw [List.drop_drop, List.append_assoc, List.length_append]

theorem treeSection_evAut_single (u : List Ltr) (p : Bool) :
    treeSection (evAut u) [p] = evAut (sec1 u p) := by
  apply Subtype.ext; apply Equiv.ext; intro w
  show ((evAut u : Equiv.Perm (List Bool)) ([p] ++ w)).drop 1 = _
  rw [List.singleton_append, evAut_apply_cons_vertex]
  rfl

/-- Level-3 vertices. -/
abbrev V3 := Bool × Bool × Bool

def sec3 (u : List Ltr) (v : V3) : List Ltr := sec1 (sec1 (sec1 u v.1) v.2.1) v.2.2

def act3 (u : List Ltr) (v : V3) : V3 :=
  (act1 u v.1, act1 (sec1 u v.1) v.2.1, act1 (sec1 (sec1 u v.1) v.2.1) v.2.2)

theorem treeSection_evAut_three (u : List Ltr) (v : V3) :
    treeSection (evAut u) [v.1, v.2.1, v.2.2] = evAut (sec3 u v) := by
  rw [show [v.1, v.2.1, v.2.2] = [v.1] ++ [v.2.1] ++ [v.2.2] from rfl, treeSection_append,
    treeSection_append, treeSection_evAut_single, treeSection_evAut_single,
    treeSection_evAut_single]
  rfl

theorem act1_append (u u' : List Ltr) (p : Bool) :
    act1 (u ++ u') p = act1 u (act1 u' p) := by
  induction u with
  | nil => rfl
  | cons x u ih => simp [act1, ih]

theorem sec1_append (u u' : List Ltr) (p : Bool) :
    sec1 (u ++ u') p = sec1 u (act1 u' p) ++ sec1 u' p := by
  induction u with
  | nil => rfl
  | cons x u ih => simp [sec1, ih, act1_append]

theorem sec3_append (u u' : List Ltr) (v : V3) :
    sec3 (u ++ u') v = sec3 u (act3 u' v) ++ sec3 u' v := by
  simp [sec3, act3, sec1_append]

theorem act1_injective (u : List Ltr) : Function.Injective (act1 u) := by
  induction u with
  | nil => exact fun _ _ h => h
  | cons x u ih =>
    intro p q h
    apply ih
    cases x <;> simpa [act1, flipL] using h

theorem act3_injective (u : List Ltr) : Function.Injective (act3 u) := by
  rintro ⟨p1, p2, p3⟩ ⟨q1, q2, q3⟩ h
  simp only [act3, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have e1 := act1_injective u h1
  subst e1
  have e2 := act1_injective _ h2
  subst e2
  have e3 := act1_injective _ h3
  subst e3
  rfl

noncomputable def act3Equiv (u : List Ltr) : V3 ≃ V3 :=
  Equiv.ofBijective (act3 u) (Finite.injective_iff_bijective.mp (act3_injective u))

/-! ### Reduction to normal form `[a] x₁ a … xₘ a [x]` -/

structure NF where
  lead : Bool
  xs : List NL
  t : Option NL

/-- `x₁ a x₂ a … xₘ a`. -/
def pw : List NL → List Ltr
  | [] => []
  | x :: xs => x.toL :: .a :: pw xs

def tw : Option NL → List Ltr
  | none => []
  | some y => [y.toL]

def nfw (n : NF) : List Ltr := (if n.lead then [.a] else []) ++ (pw n.xs ++ tw n.t)

def pushN (y : NL) : NF → NF
  | ⟨true, xs, t⟩ => ⟨false, y :: xs, t⟩
  | ⟨false, [], none⟩ => ⟨false, [], some y⟩
  | ⟨false, [], some z⟩ => if y = z then ⟨false, [], none⟩ else ⟨false, [], some (y.mul z)⟩
  | ⟨false, z :: zs, t⟩ => if y = z then ⟨true, zs, t⟩ else ⟨false, (y.mul z) :: zs, t⟩

def push : Ltr → NF → NF
  | .a, ⟨l, xs, t⟩ => ⟨!l, xs, t⟩
  | .b, n => pushN .b n
  | .c, n => pushN .c n
  | .d, n => pushN .d n

def nf : List Ltr → NF
  | [] => ⟨false, [], none⟩
  | x :: u => push x (nf u)

/-- Free-product reduction of a word. -/
def red (u : List Ltr) : List Ltr := nfw (nf u)

theorem pushN_spec (y : NL) (n : NF) :
    ev (nfw (pushN y n)) = ltrG y.toL * ev (nfw n) ∧
      (nfw (pushN y n)).length ≤ (nfw n).length + 1 := by
  obtain ⟨l, xs, t⟩ := n
  cases l
  · cases xs with
    | nil =>
      cases t with
      | none => simp [pushN, nfw, pw, tw, ev]
      | some z =>
        by_cases h : y = z
        · subst h
          simp only [pushN, if_true, nfw, pw, tw]
          refine ⟨?_, by simp⟩
          simp [ev, ltrG_mul_self]
        · simp only [pushN, h, if_false, nfw, pw, tw]
          refine ⟨?_, by simp⟩
          simp [ev, ← ltrG_mul_NL y z h]
    | cons z zs =>
      by_cases h : y = z
      · subst h
        simp only [pushN, if_true, nfw, pw]
        refine ⟨?_, by simp⟩
        simp [ev, ← mul_assoc, ltrG_mul_self]
      · simp only [pushN, h, if_false, nfw, pw]
        refine ⟨?_, by simp⟩
        simp [ev, ← mul_assoc, ← ltrG_mul_NL y z h]
  · simp only [pushN, nfw, pw]
    refine ⟨?_, by simp⟩
    simp [ev]

theorem push_spec (x : Ltr) (n : NF) :
    ev (nfw (push x n)) = ltrG x * ev (nfw n) ∧
      (nfw (push x n)).length ≤ (nfw n).length + 1 := by
  cases x
  · obtain ⟨l, xs, t⟩ := n
    cases l
    · simp [push, nfw, ev]
    · simp only [push, nfw, Bool.not_true, if_true]
      refine ⟨?_, by simp; omega⟩
      simp [ev, ← mul_assoc, ltrG_mul_self]
  · exact pushN_spec .b n
  · exact pushN_spec .c n
  · exact pushN_spec .d n

theorem red_spec (u : List Ltr) : ev (red u) = ev u ∧ (red u).length ≤ u.length := by
  induction u with
  | nil => simp [red, nf, nfw, pw, tw, ev]
  | cons x u ih =>
    obtain ⟨h1, h2⟩ := push_spec x (nf u)
    refine ⟨?_, ?_⟩
    · simp only [red, nf] at ih ⊢
      rw [h1, ih.1, ev_cons]
    · simp only [red, nf] at ih ⊢
      simp only [List.length_cons]
      omega

/-! ### The finite check -/

def verts : List V3 :=
  [(false, false, false), (false, false, true), (false, true, false), (false, true, true),
   (true, false, false), (true, false, true), (true, true, false), (true, true, true)]

/-- Total length of the reduced level-3 sections of `u`. -/
def Fc (u : List Ltr) : ℕ := (verts.map fun v => (red (sec3 u v)).length).sum

theorem Fc_eq (u : List Ltr) : Fc u = ∑ v : V3, (red (sec3 u v)).length := by
  simp only [Fc, verts, Fintype.sum_prod_type, Fintype.sum_bool, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

def good (xs : List NL) : Bool := !xs.isEmpty && decide (4 * Fc (pw xs) ≤ 6 * xs.length)

def check (pre : List NL) : ℕ → Bool
  | 0 => good pre
  | n + 1 => good pre || (check (pre ++ [.b]) n && check (pre ++ [.c]) n && check (pre ++ [.d]) n)

set_option maxRecDepth 100000 in
theorem check_nil_eight : check [] 8 = true := by decide +kernel

/-! ### Bounds on the total length of level-3 sections -/

/-- `Bnd w K`: the level-3 sections of `w` are represented by words of total length `≤ K / 4`. -/
def Bnd (w : List Ltr) (K : ℕ) : Prop :=
  ∃ R : V3 → List Ltr, (∀ v, ev (R v) = ev (sec3 w v)) ∧ 4 * ∑ v, (R v).length ≤ K

theorem bnd_Fc (u : List Ltr) : Bnd u (4 * Fc u) :=
  ⟨fun v => red (sec3 u v), fun v => (red_spec _).1, by rw [Fc_eq]⟩

theorem bnd_mono {u : List Ltr} {K K' : ℕ} (h : Bnd u K) (hK : K ≤ K') : Bnd u K' := by
  obtain ⟨R, h1, h2⟩ := h
  exact ⟨R, h1, h2.trans hK⟩

theorem bnd_append {u u' : List Ltr} {K K' : ℕ} (h : Bnd u K) (h' : Bnd u' K') :
    Bnd (u ++ u') (K + K') := by
  obtain ⟨R, h1, h2⟩ := h
  obtain ⟨R', h1', h2'⟩ := h'
  refine ⟨fun v => R (act3 u' v) ++ R' v, fun v => ?_, ?_⟩
  · rw [ev_append, h1, h1', sec3_append, ev_append]
  · have e : ∑ v, (R (act3 u' v)).length = ∑ v, (R v).length :=
      Equiv.sum_comp (act3Equiv u') (fun v => (R v).length)
    simp only [List.length_append, Finset.sum_add_distrib, e]
    omega

theorem bnd_Fc_le {u : List Ltr} {K : ℕ} (h : 4 * Fc u ≤ K) : Bnd u K :=
  bnd_mono (bnd_Fc u) h

theorem check_spec (n : ℕ) : ∀ pre : List NL, check pre n = true →
    ∀ ys : List NL, n ≤ ys.length → ∃ k ≤ n, good (pre ++ ys.take k) = true := by
  induction n with
  | zero =>
    intro pre h ys _
    exact ⟨0, le_rfl, by simpa [check] using h⟩
  | succ n ih =>
    intro pre h ys hys
    simp only [check, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨⟨hb, hc⟩, hd⟩
    · exact ⟨0, Nat.zero_le _, by simpa using h⟩
    · obtain ⟨y, ys', rfl⟩ : ∃ y ys', ys = y :: ys' := by
        cases ys with
        | nil => simp at hys
        | cons y ys' => exact ⟨y, ys', rfl⟩
      have hys' : n ≤ ys'.length := by simpa using hys
      have key : check (pre ++ [y]) n = true := by cases y <;> assumption
      obtain ⟨k, hk, hg⟩ := ih _ key ys' hys'
      exact ⟨k + 1, by omega, by simpa using hg⟩

theorem good_spec {xs : List NL} (h : good xs = true) :
    xs ≠ [] ∧ 4 * Fc (pw xs) ≤ 6 * xs.length := by
  simp only [good, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    List.isEmpty_eq_false_iff] at h
  exact h

theorem pw_append (xs ys : List NL) : pw (xs ++ ys) = pw xs ++ pw ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pw, ih]

theorem length_pw (xs : List NL) : (pw xs).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pw, ih]; omega

theorem Fc_tw (t : Option NL) : 4 * Fc (tw t) ≤ 8 := by
  rcases t with _ | y
  · decide +kernel
  · cases y <;> decide +kernel

theorem Fc_pw_single (y : NL) : 4 * Fc (pw [y]) ≤ 8 := by
  cases y <;> decide +kernel

theorem bnd_pw_tw (t : Option NL) : ∀ n, ∀ xs : List NL, xs.length = n →
    Bnd (pw xs ++ tw t) (6 * n + 2 * min n 7 + 8) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro xs hxs
    by_cases h8 : 8 ≤ n
    · obtain ⟨k, hk, hg⟩ := check_spec 8 [] check_nil_eight xs (by omega)
      simp only [List.nil_append] at hg
      obtain ⟨hne, hF⟩ := good_spec hg
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · simp at hne
        · exact h
      have hlen : (xs.take k).length = k := by simp; omega
      have hrest := ih (n - k) (by omega) (xs.drop k) (by simp; omega)
      have hsplit : pw xs ++ tw t = pw (xs.take k) ++ (pw (xs.drop k) ++ tw t) := by
        conv_lhs => rw [← List.take_append_drop k xs]
        rw [pw_append, List.append_assoc]
      rw [hsplit]
      refine bnd_mono (bnd_append (bnd_Fc_le (K := 6 * k) (by rw [hlen] at hF; exact hF))
        hrest) ?_
      have : min n 7 = 7 := by omega
      have : min (n - k) 7 ≤ 7 := by omega
      omega
    · cases xs with
      | nil =>
        subst hxs
        exact bnd_mono (bnd_Fc_le (Fc_tw t)) (by simp)
      | cons y ys =>
        simp only [List.length_cons] at hxs
        have hrest := ih ys.length (by omega) ys rfl
        have hsplit : pw (y :: ys) ++ tw t = pw [y] ++ (pw ys ++ tw t) := by
          simp [pw]
        rw [hsplit]
        refine bnd_mono (bnd_append (bnd_Fc_le (Fc_pw_single y)) hrest) ?_
        have : min n 7 = n := by omega
        have : min ys.length 7 = ys.length := by omega
        omega

theorem bnd_nfw (n : NF) : Bnd (nfw n) (3 * (nfw n).length + 22) := by
  have h := bnd_pw_tw n.t n.xs.length n.xs rfl
  have hlead : Bnd (if n.lead then [.a] else []) 0 := by
    split
    · exact bnd_Fc_le (by decide +kernel)
    · exact bnd_Fc_le (by decide +kernel)
  have hlen : 2 * n.xs.length ≤ (nfw n).length := by
    simp [nfw, length_pw]; omega
  refine bnd_mono (bnd_append hlead h) ?_
  have : min n.xs.length 7 ≤ 7 := by omega
  omega

/-! ### Words and word length in `Γ` -/

theorem ltrAut_inv (x : Ltr) : (ltrAut x)⁻¹ = ltrAut x :=
  inv_eq_of_mul_eq_one_right (ltrAut_mul_self x)

theorem ltrG_inv (x : Ltr) : (ltrG x)⁻¹ = ltrG x :=
  inv_eq_of_mul_eq_one_right (ltrG_mul_self x)

theorem evAut_reverse (u : List Ltr) : evAut u.reverse = (evAut u)⁻¹ := by
  induction u with
  | nil => simp [evAut]
  | cons x u ih =>
    rw [List.reverse_cons, evAut_append, ih, evAut_cons x u, mul_inv_rev, ltrAut_inv]
    simp [evAut]

/-- The elements of `BinaryTreeAut` represented by words. -/
def wordSubgroup : Subgroup BinaryTreeAut where
  carrier := {x | ∃ u, evAut u = x}
  mul_mem' := by
    rintro _ _ ⟨u, rfl⟩ ⟨u', rfl⟩
    exact ⟨u ++ u', evAut_append u u'⟩
  one_mem' := ⟨[], rfl⟩
  inv_mem' := by
    rintro _ ⟨u, rfl⟩
    exact ⟨u.reverse, evAut_reverse u⟩

theorem exists_ev_eq (g : GrigorchukGroup) : ∃ u, ev u = g := by
  have hle : GrigorchukGroup ≤ wordSubgroup := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨[.a], by simp [evAut, ltrAut]⟩
    · exact ⟨[.b], by simp [evAut, ltrAut]⟩
    · exact ⟨[.c], by simp [evAut, ltrAut]⟩
    · exact ⟨[.d], by simp [evAut, ltrAut]⟩
  obtain ⟨u, hu⟩ := hle g.2
  exact ⟨u, Subtype.ext (by rw [coe_ev, hu])⟩

theorem ltrG_mem (y : Ltr) : ltrG y ∈ GrigorchukGroup.generators := by
  cases y
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem mem_wordBall_ev (u : List Ltr) :
    ev u ∈ Chou.wordBall GrigorchukGroup.generators u.length :=
  ⟨u.map ltrG, by simp, fun x hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact Or.inl (ltrG_mem y), rfl⟩

theorem wordLength_ev_le (u : List Ltr) : wordLength (ev u) ≤ u.length :=
  Nat.sInf_le (mem_wordBall_ev u)

theorem exists_ltr_of_mem (x : GrigorchukGroup)
    (hx : x ∈ GrigorchukGroup.generators ∨ x⁻¹ ∈ GrigorchukGroup.generators) :
    ∃ y, ltrG y = x := by
  have key : ∀ z ∈ GrigorchukGroup.generators, ∃ y, ltrG y = z := by
    intro z hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨.a, rfl⟩
    · exact ⟨.b, rfl⟩
    · exact ⟨.c, rfl⟩
    · exact ⟨.d, rfl⟩
  rcases hx with hx | hx
  · exact key x hx
  · obtain ⟨y, hy⟩ := key _ hx
    exact ⟨y, by rw [← ltrG_inv, hy, inv_inv]⟩

theorem exists_geodesic (g : GrigorchukGroup) :
    ∃ u : List Ltr, ev u = g ∧ u.length ≤ wordLength g := by
  obtain ⟨u₀, hu₀⟩ := exists_ev_eq g
  have hne : {n | g ∈ Chou.wordBall GrigorchukGroup.generators n}.Nonempty :=
    ⟨u₀.length, hu₀ ▸ mem_wordBall_ev u₀⟩
  obtain ⟨l, hl, hS, hprod⟩ := Nat.sInf_mem hne
  have : ∀ l : List GrigorchukGroup,
      (∀ x ∈ l, x ∈ GrigorchukGroup.generators ∨ x⁻¹ ∈ GrigorchukGroup.generators) →
      ∃ u : List Ltr, u.map ltrG = l := by
    intro l hl
    induction l with
    | nil => exact ⟨[], rfl⟩
    | cons x l ih =>
      obtain ⟨y, hy⟩ := exists_ltr_of_mem x (hl x (by simp))
      obtain ⟨u, hu⟩ := ih (fun z hz => hl z (by simp [hz]))
      exact ⟨y :: u, by simp [hy, hu]⟩
  obtain ⟨u, hu⟩ := this l hS
  refine ⟨u, ?_, ?_⟩
  · rw [ev, hu, hprod]
  · have : u.length = l.length := by rw [← hu, List.length_map]
    rw [this]; exact hl

/-! ### Lemma 4.8 -/

def finEquivV3 : (Fin 3 → Bool) ≃ V3 where
  toFun v := (v 0, v 1, v 2)
  invFun t := ![t.1, t.2.1, t.2.2]
  left_inv v := by funext i; fin_cases i <;> rfl
  right_inv t := rfl

theorem sum_wordLength_treeSection_le' (g : GrigorchukGroup) (hg : g ∈ levelStabilizer 3)
    (h : (Fin 3 → Bool) → GrigorchukGroup)
    (hh : ∀ v, (h v : BinaryTreeAut) = treeSection (g : BinaryTreeAut) (List.ofFn v)) :
    (∑ v, (wordLength (h v) : ℝ)) ≤ 3 / 4 * (wordLength g : ℝ) + 8 := by
  obtain ⟨u, hu, hlen⟩ := exists_geodesic g
  set w := red u with hw
  have hwg : ev w = g := by rw [hw, (red_spec u).1, hu]
  have hwlen : w.length ≤ wordLength g := (red_spec u).2.trans hlen
  obtain ⟨R, hR, hsum⟩ := bnd_nfw (nf u)
  change ∀ v, ev (R v) = ev (sec3 w v) at hR
  change 4 * ∑ v, (R v).length ≤ 3 * w.length + 22 at hsum
  have hhv : ∀ v, h v = ev (R (finEquivV3 v)) := by
    intro v
    apply Subtype.ext
    rw [hh v, hR, coe_ev, ← hwg, coe_ev,
      show List.ofFn v = [(finEquivV3 v).1, (finEquivV3 v).2.1, (finEquivV3 v).2.2] from by
        simp [List.ofFn_succ]; exact ⟨rfl, rfl, rfl⟩,
      treeSection_evAut_three]
  have hle : ∑ v, wordLength (h v) ≤ ∑ v : V3, (R v).length := by
    calc ∑ v, wordLength (h v) ≤ ∑ v, (R (finEquivV3 v)).length := by
          apply Finset.sum_le_sum
          intro v _
          rw [hhv v]
          exact wordLength_ev_le _
      _ = ∑ v : V3, (R v).length := Equiv.sum_comp finEquivV3 (fun v => (R v).length)
  have hle' : 4 * ∑ v, wordLength (h v) ≤ 3 * wordLength g + 32 := by omega
  have hR' : (4 : ℝ) * ∑ v, (wordLength (h v) : ℝ) ≤ 3 * (wordLength g : ℝ) + 32 := by
    exact_mod_cast hle'
  linarith

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

/-- The admissible length profiles. -/
noncomputable def K (m : ℕ) : Finset ((Fin 3 → Bool) → Fin (m + 9)) := by
  classical
  exact Finset.univ.filter (fun κ => (∑ v, ((κ v : ℕ) : ℝ)) ≤ 3 / 4 * (m : ℝ) + 8)

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


theorem sum_wordLength_treeSection_le (g : GrigorchukGroup) (hg : g ∈ levelStabilizer 3)
    (h : (Fin 3 → Bool) → GrigorchukGroup)
    (hh : ∀ v, (h v : BinaryTreeAut) = treeSection (g : BinaryTreeAut) (List.ofFn v)) :
    (∑ v, (wordLength (h v) : ℝ)) ≤ 3 / 4 * (wordLength g : ℝ) + 8 :=
  by first | exact Garrido.GR.L48.sum_wordLength_treeSection_le' | (intros; apply Garrido.GR.L48.sum_wordLength_treeSection_le' <;> assumption)


end Garrido.GR.Final

open Garrido

theorem solution (g : GrigorchukGroup) (hg : g ∈ levelStabilizer 3)
    (h : (Fin 3 → Bool) → GrigorchukGroup)
    (hh : ∀ v, (h v : BinaryTreeAut) = treeSection (g : BinaryTreeAut) (List.ofFn v)) :
    (∑ v, (wordLength (h v) : ℝ)) ≤ 3 / 4 * (wordLength g : ℝ) + 8 :=
  Garrido.GR.Final.sum_wordLength_treeSection_le g hg h hh
