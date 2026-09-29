-- Prove2me | solution 1 for Garrido.infinite_and_surjective_treeSection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T13:16:24.410876+00:00
-- url     : https://prove2.me/submissions/bbf06597-433d-4057-a198-4add447942d6

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

theorem len (g : BinaryTreeAut) (v : List Bool) : ((g : P) v).length = v.length := g.2.1 v

theorem treeSection_mul (g h : BinaryTreeAut) (v : List Bool) :
    treeSection (g * h) v = treeSection g ((h : P) v) * treeSection h v := by
  apply bta_ext; intro w
  simp only [treeSection_apply, Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply]
  have e := BinaryTreeAut.append_drop h v w
  rw [len h v]
  conv_lhs => rw [← e]

theorem treeSection_one (v : List Bool) : treeSection 1 v = 1 := by
  apply bta_ext; intro w
  simp [treeSection_apply]

theorem treeSection_inv (g : BinaryTreeAut) (v : List Bool) :
    treeSection g⁻¹ v = (treeSection g (((g⁻¹ : BinaryTreeAut) : P) v))⁻¹ := by
  have h := treeSection_mul g g⁻¹ v
  rw [mul_inv_cancel, treeSection_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem treeSection_append (g : BinaryTreeAut) (v v' : List Bool) :
    treeSection g (v ++ v') = treeSection (treeSection g v) v' := by
  apply bta_ext; intro w
  simp [treeSection_apply, List.drop_drop, List.append_assoc]

theorem grigA_apply (w : List Bool) : (grigA : P) w = grigAFun w := rfl
theorem grigB_apply (w : List Bool) : (grigB : P) w = grigBFun w := rfl
theorem grigC_apply (w : List Bool) : (grigC : P) w = grigCFun w := rfl
theorem grigD_apply (w : List Bool) : (grigD : P) w = grigDFun w := rfl

theorem secA (x : Bool) : treeSection grigA [x] = 1 := by
  apply bta_ext; intro w; simp [treeSection_apply, grigA_apply, grigAFun]

theorem secB0 : treeSection grigB [false] = grigA := by
  apply bta_ext; intro w; simp [treeSection_apply, grigB_apply, grigA_apply, grigBFun]
theorem secB1 : treeSection grigB [true] = grigC := by
  apply bta_ext; intro w; simp [treeSection_apply, grigB_apply, grigC_apply, grigBFun]
theorem secC0 : treeSection grigC [false] = grigA := by
  apply bta_ext; intro w; simp [treeSection_apply, grigC_apply, grigA_apply, grigCFun]
theorem secC1 : treeSection grigC [true] = grigD := by
  apply bta_ext; intro w; simp [treeSection_apply, grigC_apply, grigD_apply, grigCFun]
theorem secD0 : treeSection grigD [false] = 1 := by
  apply bta_ext; intro w; simp [treeSection_apply, grigD_apply, grigDFun]
theorem secD1 : treeSection grigD [true] = grigB := by
  apply bta_ext; intro w; simp [treeSection_apply, grigD_apply, grigB_apply, grigDFun]

theorem gen_mem_A : grigA ∈ GrigorchukGroup := Subgroup.subset_closure (by simp)
theorem gen_mem_B : grigB ∈ GrigorchukGroup := Subgroup.subset_closure (by simp)
theorem gen_mem_C : grigC ∈ GrigorchukGroup := Subgroup.subset_closure (by simp)
theorem gen_mem_D : grigD ∈ GrigorchukGroup := Subgroup.subset_closure (by simp)

/-- Sections of `1, a, b, c, d` stay in `{1, a, b, c, d}`. -/
theorem gen_sections (v : List Bool) : ∀ g : BinaryTreeAut,
    (g = 1 ∨ g = grigA ∨ g = grigB ∨ g = grigC ∨ g = grigD) → treeSection g v ∈ GrigorchukGroup := by
  induction v with
  | nil =>
    intro g hg
    have : treeSection g [] = g := bta_ext (fun w => by simp [treeSection_apply])
    rw [this]
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact gen_mem_A
    · exact gen_mem_B
    · exact gen_mem_C
    · exact gen_mem_D
  | cons x v ih =>
    intro g hg
    rw [show x :: v = [x] ++ v from rfl, treeSection_append]
    apply ih
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> cases x <;>
      simp [treeSection_one, secA, secB0, secB1, secC0, secC1, secD0, secD1]

theorem treeSection_mem {g : BinaryTreeAut} (hg : g ∈ GrigorchukGroup) (v : List Bool) :
    treeSection g v ∈ GrigorchukGroup := by
  induction hg using Subgroup.closure_induction generalizing v with
  | mem g hg =>
    apply gen_sections
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    tauto
  | one => rw [treeSection_one]; exact one_mem _
  | mul g h _ _ ihg ihh =>
    rw [treeSection_mul]; exact mul_mem (ihg _) (ihh _)
  | inv g _ ih =>
    rw [treeSection_inv]; exact inv_mem (ih _)


/-- The subgroup of sections at `[i]` of elements of `St(1)`. -/
def secImage (i : Bool) : Subgroup BinaryTreeAut where
  carrier := {y | ∃ g : GrigorchukGroup, g ∈ levelStabilizer 1 ∧ treeSection (g : BinaryTreeAut) [i] = y}
  mul_mem' := by
    rintro _ _ ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
    refine ⟨g * h, mul_mem hg hh, ?_⟩
    rw [Subgroup.coe_mul, treeSection_mul, hh [i] rfl]
  one_mem' := ⟨1, one_mem _, treeSection_one _⟩
  inv_mem' := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨g⁻¹, inv_mem hg, ?_⟩
    have e : (((g⁻¹ : GrigorchukGroup) : BinaryTreeAut) : P) [i] = [i] := (inv_mem hg) [i] rfl
    rw [Subgroup.coe_inv] at e ⊢
    rw [treeSection_inv, e]

open GrigorchukGroup in
theorem stab1_b : b ∈ levelStabilizer 1 := by
  intro v hv
  match v, hv with
  | [x], _ => cases x <;> rfl
open GrigorchukGroup in
theorem stab1_c : c ∈ levelStabilizer 1 := by
  intro v hv
  match v, hv with
  | [x], _ => cases x <;> rfl
open GrigorchukGroup in
theorem stab1_conj (g : GrigorchukGroup) (hg : g ∈ levelStabilizer 1) :
    a * g * a ∈ levelStabilizer 1 := by
  intro v hv
  match v, hv with
  | [x], _ =>
    change grigAFun (((g : BinaryTreeAut) : P) (grigAFun [x])) = [x]
    simp only [grigAFun]
    rw [hg [!x] rfl]; simp
open GrigorchukGroup in
theorem stab1_d : d ∈ levelStabilizer 1 := by
  intro v hv
  match v, hv with
  | [x], _ => cases x <;> rfl

theorem sec_conj (g : BinaryTreeAut) (x : Bool) :
    treeSection (grigA * g * grigA) [x] = treeSection g [!x] := by
  apply bta_ext; intro w
  simp only [treeSection_apply, Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply,
    grigA_apply]
  have e := BinaryTreeAut.append_drop g [!x] w
  simp only [List.singleton_append, grigAFun] at e ⊢
  rw [← e]
  have hl := len g [!x]
  match h : (g : P) [!x], hl with
  | [y], _ => simp

open GrigorchukGroup in
theorem gens_le (i : Bool) : GrigorchukGroup ≤ secImage i := by
  apply (Subgroup.closure_le _).2
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  have hab := stab1_conj b stab1_b
  have hac := stab1_conj c stab1_c
  have had := stab1_conj d stab1_d
  cases i
  · rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨b, stab1_b, secB0⟩
    · exact ⟨a * d * a, had, by
        simp only [Subgroup.coe_mul]; exact (sec_conj grigD false).trans secD1⟩
    · exact ⟨a * b * a, hab, by
        simp only [Subgroup.coe_mul]; exact (sec_conj grigB false).trans secB1⟩
    · exact ⟨a * c * a, hac, by
        simp only [Subgroup.coe_mul]; exact (sec_conj grigC false).trans secC1⟩
  · rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨a * b * a, hab, by
        simp only [Subgroup.coe_mul]; exact (sec_conj grigB true).trans secB0⟩
    · exact ⟨d, stab1_d, secD1⟩
    · exact ⟨b, stab1_b, secB1⟩
    · exact ⟨c, stab1_c, secC1⟩

theorem infinite_and_surjective_treeSection' :
    Infinite GrigorchukGroup ∧
      ∀ (i : Bool) (x : GrigorchukGroup), ∃ g : GrigorchukGroup, g ∈ levelStabilizer 1 ∧
        treeSection (g : BinaryTreeAut) [i] = x := by
  have surj : ∀ (i : Bool) (x : GrigorchukGroup), ∃ g : GrigorchukGroup, g ∈ levelStabilizer 1 ∧
      treeSection (g : BinaryTreeAut) [i] = x := fun i x => gens_le i x.2
  refine ⟨?_, surj⟩
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  let f : levelStabilizer 1 → GrigorchukGroup :=
    fun g => ⟨treeSection ((g : GrigorchukGroup) : BinaryTreeAut) [false], treeSection_mem g.1.2 _⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, hg, e⟩ := surj false x
    exact ⟨⟨g, hg⟩, Subtype.ext e⟩
  have h1 := Nat.card_le_card_of_surjective f hf
  have hne : levelStabilizer 1 ≠ ⊤ := by
    intro htop
    have : GrigorchukGroup.a ∈ levelStabilizer 1 := htop ▸ Subgroup.mem_top _
    have := this [false] rfl
    exact absurd this (by decide)
  have h2 := Subgroup.card_le_card_group (levelStabilizer 1)
  have h3 : Nat.card (levelStabilizer 1) ≠ Nat.card GrigorchukGroup :=
    fun h => hne (Subgroup.card_eq_iff_eq_top _ |>.1 h)
  omega

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

theorem treeSection_append (g : BinaryTreeAut) (v₁ v₂ : List Bool) :
    treeSection g (v₁ ++ v₂) = treeSection (treeSection g v₁) v₂ := by
  apply Subtype.ext; apply Equiv.ext; intro w
  show ((g : Equiv.Perm (List Bool)) ((v₁ ++ v₂) ++ w)).drop (v₁ ++ v₂).length =
    (((g : Equiv.Perm (List Bool)) (v₁ ++ (v₂ ++ w))).drop v₁.length).drop v₂.length
  rw [List.drop_drop, List.append_assoc, List.length_append]

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


theorem infinite_and_surjective_treeSection :
    Infinite GrigorchukGroup ∧
      ∀ (i : Bool) (x : GrigorchukGroup), ∃ g : GrigorchukGroup, g ∈ levelStabilizer 1 ∧
        treeSection (g : BinaryTreeAut) [i] = x :=
  by first | exact Garrido.GR.Sec.infinite_and_surjective_treeSection' | (intros; apply Garrido.GR.Sec.infinite_and_surjective_treeSection' <;> assumption)


end Garrido.GR.Final

open Garrido

theorem solution :
    Infinite GrigorchukGroup ∧
      ∀ (i : Bool) (x : GrigorchukGroup), ∃ g : GrigorchukGroup, g ∈ levelStabilizer 1 ∧
        treeSection (g : BinaryTreeAut) [i] = x :=
  Garrido.GR.Final.infinite_and_surjective_treeSection
