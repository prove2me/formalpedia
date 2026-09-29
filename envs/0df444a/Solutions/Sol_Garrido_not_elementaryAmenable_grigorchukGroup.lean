-- Prove2me | solution 1 for Garrido.not_elementaryAmenable_grigorchukGroup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T13:16:24.3482+00:00
-- url     : https://prove2.me/submissions/f3023ff0-afa6-442c-9033-2e65c5e6e848

import Theorems.Thm_Garrido_exists_orderOf_eq_two_pow
import Theorems.Thm_Garrido_infinite_and_surjective_treeSection
import Mathlib
import Definitions.Def_Chou_Classes
import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Growth
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Garrido_Grigorchuk
import Theorems.Thm_Chou_isLocallyFinite_of_elementaryAmenable_of_isMulTorsion

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

/-- Proposition 4.7 (p. 14): every element of Γ has order a power of 2. -/
theorem exists_orderOf_eq_two_pow' (g : GrigorchukGroup) : ∃ k : ℕ, orderOf g = 2 ^ k :=
  by
  first
    | exact Garrido.exists_orderOf_eq_two_pow
    | exact Garrido.exists_orderOf_eq_two_pow ..
    | (apply Garrido.exists_orderOf_eq_two_pow <;> first | assumption | infer_instance)
    | simpa using Garrido.exists_orderOf_eq_two_pow


lemma closure_generators : Subgroup.closure GrigorchukGroup.generators = ⊤ := by
  have h : GrigorchukGroup.generators =
      ((↑) : GrigorchukGroup → BinaryTreeAut) ⁻¹' {grigA, grigB, grigC, grigD} := by
    ext x
    simp only [GrigorchukGroup.generators, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_preimage]
    constructor
    · rintro (rfl | rfl | rfl | rfl) <;> simp [GrigorchukGroup.a, GrigorchukGroup.b,
        GrigorchukGroup.c, GrigorchukGroup.d]
    · rintro (h | h | h | h) <;> [left; (right; left); (right; right; left); (right; right; right)]
        <;> exact Subtype.ext h
  rw [h]
  exact Subgroup.closure_closure_coe_preimage

/-- p. 14: "Hence Γ is not in EG". -/
theorem not_elementaryAmenable_grigorchukGroup'
    (h_chou : ∀ {G : Type} [Group G] (hG : Chou.ElementaryAmenable G) (ht : IsMulTorsion G),
      Chou.IsLocallyFinite G)
    (h_inf : Infinite GrigorchukGroup ∧
      ∀ (i : Bool) (x : GrigorchukGroup), ∃ g : GrigorchukGroup, g ∈ levelStabilizer 1 ∧
        treeSection (g : BinaryTreeAut) [i] = x) :
    ¬ Chou.ElementaryAmenable GrigorchukGroup := by
  intro hEA
  have ht : IsMulTorsion GrigorchukGroup := fun g => by
    obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow' g
    exact orderOf_pos_iff.mp (by rw [hk]; positivity)
  have hfin : GrigorchukGroup.generators.Finite := by
    simp [GrigorchukGroup.generators]
  have := h_chou hEA ht _ hfin
  rw [closure_generators] at this
  have : Finite GrigorchukGroup := Finite.of_equiv _ Subgroup.topEquiv.toEquiv
  have := h_inf.1
  exact not_finite GrigorchukGroup

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


theorem closure_generators : Subgroup.closure GrigorchukGroup.generators = ⊤ := by
  have := Subgroup.closure_closure_coe_preimage (k := ({grigA, grigB, grigC, grigD} : Set BinaryTreeAut))
  have e : GrigorchukGroup.generators = ((↑) : GrigorchukGroup → BinaryTreeAut) ⁻¹' {grigA, grigB, grigC, grigD} := by
    ext x
    show x ∈ ({GrigorchukGroup.a, GrigorchukGroup.b, GrigorchukGroup.c, GrigorchukGroup.d} :
      Set GrigorchukGroup) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subtype.ext_iff]
    exact Iff.rfl
  rw [e]; exact this

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


theorem infinite_and_surjective_treeSection :
    Infinite GrigorchukGroup ∧
      ∀ (i : Bool) (x : GrigorchukGroup), ∃ g : GrigorchukGroup, g ∈ levelStabilizer 1 ∧
        treeSection (g : BinaryTreeAut) [i] = x :=
  by
  first
    | exact Garrido.infinite_and_surjective_treeSection
    | exact Garrido.infinite_and_surjective_treeSection ..
    | (apply Garrido.infinite_and_surjective_treeSection <;> first | assumption | infer_instance)
    | simpa using Garrido.infinite_and_surjective_treeSection


theorem exists_orderOf_eq_two_pow (g : GrigorchukGroup) : ∃ k : ℕ, orderOf g = 2 ^ k :=
  by
  try haveI := g; first
    | exact Garrido.exists_orderOf_eq_two_pow g
    | exact Garrido.exists_orderOf_eq_two_pow
    | exact Garrido.exists_orderOf_eq_two_pow ..
    | (apply Garrido.exists_orderOf_eq_two_pow <;> first | assumption | infer_instance)
    | simpa using Garrido.exists_orderOf_eq_two_pow


theorem not_elementaryAmenable_grigorchukGroup : ¬ Chou.ElementaryAmenable GrigorchukGroup :=
  Garrido.GR.Tor.not_elementaryAmenable_grigorchukGroup' (fun hG ht => Chou.isLocallyFinite_of_elementaryAmenable_of_isMulTorsion hG ht) infinite_and_surjective_treeSection


end Garrido.GR.Final

open Garrido

theorem solution : ¬ Chou.ElementaryAmenable GrigorchukGroup :=
  Garrido.GR.Final.not_elementaryAmenable_grigorchukGroup
