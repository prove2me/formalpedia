-- Prove2me | solution 1 for Garrido.index_levelStabilizer_three
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T13:16:25.338912+00:00
-- url     : https://prove2.me/submissions/3607a84f-aa96-4781-a71a-88ecaca9c110

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



/-! ### Target 3 -/

/-- Level-3 vertices. -/
abbrev T3 := Bool × Bool × Bool
/-- Portraits of depth 3: a flip at the root, at each level-1 vertex, at each level-2 vertex. -/
abbrev Port := Bool × (Bool → Bool) × (Bool → Bool → Bool)

def toW (x : T3) : List Bool := [x.1, x.2.1, x.2.2]
def ofW : List Bool → T3
  | [y1, y2, y3] => (y1, y2, y3)
  | _ => (false, false, false)

theorem ofW_toW (x : T3) : ofW (toW x) = x := rfl
theorem toW_ofW : ∀ l : List Bool, l.length = 3 → toW (ofW l) = l
  | [_, _, _], _ => rfl

/-- The action of `g ∈ Γ` on level 3. -/
def act (g : Γ) (x : T3) : T3 := ofW (((g : BinaryTreeAut) : P) (toW x))

theorem act_mul (g h : Γ) : act (g * h) = act g ∘ act h := by
  funext x
  simp only [act, Function.comp_apply, C1mul_apply]
  rw [toW_ofW _ (by rw [C1len]; rfl)]

theorem act_one : act 1 = id := by funext x; simp [act, ofW_toW]

def port (p : Port) (x : T3) : T3 :=
  (xor x.1 p.1, xor x.2.1 (p.2.1 x.1), xor x.2.2 (p.2.2 x.1 x.2.1))

def pmul (p q : Port) : Port :=
  (xor q.1 p.1, fun x1 => xor (q.2.1 x1) (p.2.1 (xor x1 q.1)),
    fun x1 x2 => xor (q.2.2 x1 x2) (p.2.2 (xor x1 q.1) (xor x2 (q.2.1 x1))))

def pinv (p : Port) : Port :=
  (p.1, fun y1 => p.2.1 (xor y1 p.1),
    fun y1 y2 => p.2.2 (xor y1 p.1) (xor y2 (p.2.1 (xor y1 p.1))))

theorem port_pmul (p q : Port) : port p ∘ port q = port (pmul p q) := by
  funext x; simp [port, pmul]

theorem port_pinv (p : Port) : port p ∘ port (pinv p) = id := by
  funext x; simp [port, pinv]

theorem port_injective : Function.Injective port := by
  rintro ⟨p0, p1, p2⟩ ⟨q0, q1, q2⟩ h
  have h' := fun x => congrFun h x
  simp only [port, Prod.mk.injEq] at h'
  have e0 : p0 = q0 := by simpa using (h' (false, false, false)).1
  have e1 : p1 = q1 := funext fun x => by simpa using (h' (x, false, false)).2.1
  have e2 : p2 = q2 := funext fun x => funext fun y => by simpa using (h' (x, y, false)).2.2
  subst e0 e1 e2; rfl

def pA : Port := (true, fun _ => false, fun _ _ => false)
def pB : Port := (false, fun x => !x, fun x y => x && !y)
def pC : Port := (false, fun x => !x, fun _ _ => false)
def pD : Port := (false, fun _ => false, fun x y => x && !y)

theorem act_a : act GrigorchukGroup.a = port pA := by
  funext x; rcases x with ⟨_ | _, _ | _, _ | _⟩ <;> rfl
theorem act_b : act GrigorchukGroup.b = port pB := by
  funext x; rcases x with ⟨_ | _, _ | _, _ | _⟩ <;> rfl
theorem act_c : act GrigorchukGroup.c = port pC := by
  funext x; rcases x with ⟨_ | _, _ | _, _ | _⟩ <;> rfl
theorem act_d : act GrigorchukGroup.d = port pD := by
  funext x; rcases x with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

theorem range_act_sub (g : Γ) : ∃ p, act g = port p := by
  induction g using C1induction with
  | one => exact ⟨(false, fun _ => false, fun _ _ => false), by
      rw [act_one]; funext x; simp [port]⟩
  | ha => exact ⟨_, act_a⟩
  | hb => exact ⟨_, act_b⟩
  | hc => exact ⟨_, act_c⟩
  | hd => exact ⟨_, act_d⟩
  | mul x y hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨pmul p q, by rw [act_mul, hp, hq, port_pmul]⟩
  | inv x hx =>
    obtain ⟨p, hp⟩ := hx
    refine ⟨pinv p, ?_⟩
    calc act x⁻¹ = act x⁻¹ ∘ (port p ∘ port (pinv p)) := by rw [port_pinv]; rfl
      _ = act (x⁻¹ * x) ∘ port (pinv p) := by rw [act_mul, hp]; rfl
      _ = port (pinv p) := by rw [inv_mul_cancel, act_one]; rfl

/-- The seven single-flip portraits. -/
def bas (i : Fin 7) : Port :=
  (i = 0, fun x => (i = 1 && !x) || (i = 2 && x),
    fun x y => (i = 3 && !x && !y) || (i = 4 && !x && y) || (i = 5 && x && !y) ||
      (i = 6 && x && y))

theorem port_decomp : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    port (b0, fun x => cond x b2 b1, fun x y => cond x (cond y b6 b5) (cond y b4 b3)) =
      (if b0 then port (bas 0) else id) ∘ (if b1 then port (bas 1) else id) ∘
      (if b2 then port (bas 2) else id) ∘ (if b3 then port (bas 3) else id) ∘
      (if b4 then port (bas 4) else id) ∘ (if b5 then port (bas 5) else id) ∘
      (if b6 then port (bas 6) else id) := by
  decide

open GrigorchukGroup in
theorem bas_mem : ∀ i : Fin 7, ∃ g : Γ, act g = port (bas i) := by
  intro i
  fin_cases i
  · exact ⟨a, by rw [act_a]; decide⟩
  · exact ⟨c, by rw [act_c]; decide⟩
  · exact ⟨a * c * a, by rw [act_mul, act_mul, act_a, act_c]; decide⟩
  · exact ⟨a * d * a, by rw [act_mul, act_mul, act_a, act_d]; decide⟩
  · exact ⟨c * (a * d * a) * c, by rw [act_mul, act_mul, act_mul, act_mul, act_a, act_c, act_d]; decide⟩
  · exact ⟨d, by rw [act_d]; decide⟩
  · exact ⟨a * c * a * d * (a * c * a), by
      simp only [act_mul, act_a, act_c, act_d]; decide⟩

theorem act_ite (q : Bool) (h : Γ) : act (if q then h else 1) = if q then act h else id := by
  cases q <;> simp [act_one]

theorem range_act_sup (p : Port) : ∃ g : Γ, act g = port p := by
  obtain ⟨p0, p1, p2⟩ := p
  have e : ((p0, p1, p2) : Port) = (p0, fun x => cond x (p1 true) (p1 false),
      fun x y => cond x (cond y (p2 true true) (p2 true false))
        (cond y (p2 false true) (p2 false false))) := by
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext x; cases x <;> rfl
    · funext x y; cases x <;> cases y <;> rfl
  rw [e, port_decomp]
  choose g hg using bas_mem
  refine ⟨(if p0 then g 0 else 1) * (if p1 false then g 1 else 1) * (if p1 true then g 2 else 1) *
    (if p2 false false then g 3 else 1) * (if p2 false true then g 4 else 1) *
    (if p2 true false then g 5 else 1) * (if p2 true true then g 6 else 1), ?_⟩
  simp only [act_mul, act_ite, hg]
  rfl

/-- The action of `Γ` on level 3, as a homomorphism to permutations. -/
def actHom : Γ →* Equiv.Perm T3 where
  toFun g :=
    { toFun := act g
      invFun := act g⁻¹
      left_inv := fun x => by
        change (act g⁻¹ ∘ act g) x = x
        rw [← act_mul, inv_mul_cancel, act_one]; rfl
      right_inv := fun x => by
        change (act g ∘ act g⁻¹) x = x
        rw [← act_mul, mul_inv_cancel, act_one]; rfl }
  map_one' := Equiv.ext fun x => by
    change act 1 x = x
    rw [act_one]; rfl
  map_mul' g h := Equiv.ext fun x => by
    change act (g * h) x = act g (act h x)
    rw [act_mul]; rfl

theorem ker_actHom : actHom.ker = levelStabilizer 3 := by
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro h v hv
    have hx : act g (ofW v) = ofW v := congrArg (fun σ : Equiv.Perm T3 => σ (ofW v)) h
    rw [← toW_ofW v hv]
    have := congrArg toW hx
    simp only [act] at this
    rwa [toW_ofW _ (by rw [C1len]; rfl)] at this
  · intro h
    apply Equiv.ext; intro x
    change act g x = x
    simp only [act]
    rw [h (toW x) rfl, ofW_toW]

theorem index_levelStabilizer_three' : (levelStabilizer 3).index = 2 ^ 7 := by
  rw [← ker_actHom, Subgroup.index_ker]
  have h1 : Set.range act = Set.range port := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨p, hp⟩ := range_act_sub g
      exact ⟨p, hp.symm⟩
    · rintro ⟨p, rfl⟩
      obtain ⟨g, hg⟩ := range_act_sup p
      exact ⟨g, hg⟩
  have h2 : Set.range act =
      (fun σ : Equiv.Perm T3 => (σ : T3 → T3)) '' (actHom.range : Set (Equiv.Perm T3)) := by
    rw [MonoidHom.coe_range, ← Set.range_comp]; rfl
  calc Nat.card actHom.range
      = Nat.card ((fun σ : Equiv.Perm T3 => (σ : T3 → T3)) ''
          (actHom.range : Set (Equiv.Perm T3))) :=
        (Nat.card_image_of_injective DFunLike.coe_injective _).symm
    _ = Nat.card (Set.range port) := by rw [← h2, h1]
    _ = Nat.card Port := Nat.card_range_of_injective port_injective
    _ = 2 ^ 7 := by simp [Nat.card_eq_fintype_card]


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


theorem index_levelStabilizer_three : (levelStabilizer 3).index = 2 ^ 7 :=
  by first | exact Garrido.GR.St.index_levelStabilizer_three' | (intros; apply Garrido.GR.St.index_levelStabilizer_three' <;> assumption)


end Garrido.GR.Final

open Garrido

theorem solution : (levelStabilizer 3).index = 2 ^ 7 :=
  Garrido.GR.Final.index_levelStabilizer_three
