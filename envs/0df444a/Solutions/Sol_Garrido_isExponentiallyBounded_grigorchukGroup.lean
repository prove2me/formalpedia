-- Prove2me | solution 1 for Garrido.isExponentiallyBounded_grigorchukGroup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T13:16:24.201839+00:00
-- url     : https://prove2.me/submissions/6ea82b55-cb8e-4d24-8c30-34f6ebd1aec4

import Theorems.Thm_Garrido_nat_card_wordBall_le_index_mul
import Theorems.Thm_Garrido_sum_wordLength_treeSection_le
import Theorems.Thm_Garrido_treeSection_mem_and_map_mul_and_injective
import Theorems.Thm_Garrido_index_levelStabilizer_three
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

def tt (w : List L) : ℕ := if L.d ∈ w then 0 else if L.c ∈ w then 1 else 2
def μ (w : List L) : ℕ := 4 * w.length + tt w

/-! ### The torsion predicate -/


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

theorem one_mem_wordBall (k : ℕ) : (1 : G) ∈ wordBall S k :=
  ⟨[], by simp, by simp, by simp⟩

theorem wordBall_mono {k k' : ℕ} (h : k ≤ k') : wordBall S k ⊆ wordBall S k' := by
  rintro g ⟨l, hl, hS, rfl⟩
  exact ⟨l, hl.trans h, hS, rfl⟩

theorem mul_mem_wordBall {x y : G} {a b : ℕ} (hx : x ∈ wordBall S a) (hy : y ∈ wordBall S b) :
    x * y ∈ wordBall S (a + b) := by
  obtain ⟨l, hl, hS, rfl⟩ := hx
  obtain ⟨l', hl', hS', rfl⟩ := hy
  refine ⟨l ++ l', by simp; omega, ?_, by simp⟩
  intro z hz
  rcases List.mem_append.mp hz with h | h
  · exact hS z h
  · exact hS' z h

theorem inv_mem_wordBall {x : G} {a : ℕ} (hx : x ∈ wordBall S a) : x⁻¹ ∈ wordBall S a := by
  obtain ⟨l, hl, hS, rfl⟩ := hx
  refine ⟨(l.map (·⁻¹)).reverse, by simpa using hl, ?_, by simp [List.prod_inv_reverse]⟩
  intro z hz
  simp only [List.mem_reverse, List.mem_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rcases hS w hw with h | h
  · right; simpa using h
  · left; exact h

theorem mem_wordBall_one_of_mem {s : G} (hs : s ∈ S) : s ∈ wordBall S 1 :=
  ⟨[s], by simp, by simp [hs], by simp⟩

/-- `B(k+1) = T₁ · B(k)` where `T₁ = {1} ∪ S ∪ S⁻¹`. -/
theorem mem_wordBall_succ_iff {g : G} {k : ℕ} :
    g ∈ wordBall S (k + 1) ↔ ∃ t : G, (t = 1 ∨ t ∈ S ∨ t⁻¹ ∈ S) ∧ ∃ g' ∈ wordBall S k, g = t * g' := by
  constructor
  · rintro ⟨l, hl, hS, rfl⟩
    cases l with
    | nil => exact ⟨1, Or.inl rfl, 1, one_mem_wordBall S k, by simp⟩
    | cons x l =>
      refine ⟨x, Or.inr (hS x (by simp)), l.prod, ⟨l, by simpa using hl, fun z hz => hS z (by simp [hz]), rfl⟩, by simp⟩
  · rintro ⟨t, ht, g', hg', rfl⟩
    rcases ht with rfl | ht
    · simpa using wordBall_mono S (Nat.le_succ k) hg'
    · have : t ∈ wordBall S 1 := ⟨[t], by simp, by simpa using ht, by simp⟩
      simpa [add_comm] using mul_mem_wordBall S this hg'

theorem wordBall_finite (hS : S.Finite) (k : ℕ) : (wordBall S k).Finite := by
  induction k with
  | zero =>
    apply (Set.finite_singleton (1 : G)).subset
    rintro g ⟨l, hl, -, rfl⟩
    simp at hl; simp [hl]
  | succ k ih =>
    have hT : ({t : G | t = 1 ∨ t ∈ S ∨ t⁻¹ ∈ S}).Finite := by
      have : {t : G | t = 1 ∨ t ∈ S ∨ t⁻¹ ∈ S} = {1} ∪ S ∪ S⁻¹ := by
        ext t; simp [or_assoc]
      rw [this]; exact ((Set.finite_singleton _).union hS).union hS.inv
    apply (hT.image2 (· * ·) ih).subset
    intro g hg
    obtain ⟨t, ht, g', hg', rfl⟩ := (mem_wordBall_succ_iff S).mp hg
    exact ⟨t, ht, g', hg', rfl⟩

theorem exists_mem_wordBall (hgen : Subgroup.closure S = ⊤) (g : G) : ∃ k, g ∈ wordBall S k := by
  have hg : g ∈ Subgroup.closure S := by rw [hgen]; trivial
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact ⟨1, mem_wordBall_one_of_mem S hs⟩
  | one => exact ⟨0, one_mem_wordBall S 0⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, mul_mem_wordBall S ha hb⟩
  | inv x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, inv_mem_wordBall S ha⟩

end Ball

section Index
variable {G : Type*} [Group G] (S : Set G) (H : Subgroup G)

theorem nat_card_wordBall_le_index_mul' {G : Type*} [Group G] (S : Set G) (hS : S.Finite)
    (hgen : Subgroup.closure S = ⊤) (H : Subgroup G) [H.FiniteIndex] (k : ℕ) :
    Nat.card (Chou.wordBall S k) ≤
      H.index * Nat.card ↥(Chou.wordBall S (k + H.index - 1) ∩ (H : Set G)) :=
  by
  try haveI := S; try haveI := hS; try haveI := hgen; try haveI := H; try haveI := k; first
    | exact Garrido.nat_card_wordBall_le_index_mul S hS hgen H k
    | exact Garrido.nat_card_wordBall_le_index_mul
    | exact Garrido.nat_card_wordBall_le_index_mul ..
    | (apply Garrido.nat_card_wordBall_le_index_mul <;> first | assumption | infer_instance)
    | simpa using Garrido.nat_card_wordBall_le_index_mul


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

theorem generators_finite : Set.Finite GrigorchukGroup.generators := by
  unfold GrigorchukGroup.generators
  exact (((Set.finite_singleton _).insert _).insert _).insert _

/-- `γ(k) = |B_S(k)|`. -/
noncomputable def gam (k : ℕ) : ℕ := (wordBall GrigorchukGroup.generators k).ncard

theorem wordLength_le {g : GrigorchukGroup} {m : ℕ} (h : g ∈ wordBall GrigorchukGroup.generators m) :
    wordLength g ≤ m := Nat.sInf_le h

theorem mem_wordBall_wordLength (g : GrigorchukGroup) : g ∈ wordBall GrigorchukGroup.generators (wordLength g) :=
  Nat.sInf_mem (exists_mem_wordBall _ closure_generators g)

open Classical in
/-- The eight sections at level 3, as elements of `Γ` (junk `1` if not in `Γ`). -/
noncomputable def Φ (g : GrigorchukGroup) (v : Fin 3 → Bool) : GrigorchukGroup :=
  if h : treeSection (g : BinaryTreeAut) (List.ofFn v) ∈ GrigorchukGroup then ⟨_, h⟩ else 1

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

include h_psi in
theorem Φ_coe {g : GrigorchukGroup} (hg : g ∈ levelStabilizer 3) (v : Fin 3 → Bool) :
    (Φ g v : BinaryTreeAut) = treeSection (g : BinaryTreeAut) (List.ofFn v) := by
  unfold Φ; rw [dif_pos ((h_psi 3).1 g hg v)]

include h_psi in
theorem Φ_injOn : Set.InjOn Φ (levelStabilizer 3 : Set GrigorchukGroup) := by
  intro g hg h hh e
  apply (h_psi 3).2.2 g h hg hh
  intro v
  rw [← Φ_coe h_psi hg, ← Φ_coe h_psi hh, e]

/-- The admissible length profiles. -/
noncomputable def K (m : ℕ) : Finset ((Fin 3 → Bool) → Fin (m + 9)) := by
  classical
  exact Finset.univ.filter (fun κ => (∑ v, ((κ v : ℕ) : ℝ)) ≤ 3 / 4 * (m : ℝ) + 8)

variable (h48 : ∀ (g : GrigorchukGroup) (hg : g ∈ levelStabilizer 3)
    (h : (Fin 3 → Bool) → GrigorchukGroup)
    (hh : ∀ v, (h v : BinaryTreeAut) = treeSection (g : BinaryTreeAut) (List.ofFn v)),
    (∑ v, (wordLength (h v) : ℝ)) ≤ 3 / 4 * (wordLength g : ℝ) + 8)

include h_psi h48 in
theorem card_St3_le (m : ℕ) :
    (wordBall GrigorchukGroup.generators m ∩ (levelStabilizer 3 : Set GrigorchukGroup)).ncard ≤
      ∑ κ ∈ K m, ∏ v, gam (κ v) := by
  classical
  have hfin := wordBall_finite GrigorchukGroup.generators generators_finite
  let B : ℕ → Finset GrigorchukGroup := fun k => (hfin k).toFinset
  let T := (K m).biUnion (fun κ => Fintype.piFinset (fun v => B (κ v)))
  have hA := (hfin m).inter_of_left (levelStabilizer 3 : Set GrigorchukGroup)
  rw [Set.ncard_eq_toFinset_card _ hA]
  calc hA.toFinset.card ≤ T.card := Finset.card_le_card_of_injOn Φ ?_ ?_
    _ ≤ ∑ κ ∈ K m, (Fintype.piFinset fun v => B (κ v)).card := Finset.card_biUnion_le
    _ = _ := by
      apply Finset.sum_congr rfl; intro κ _
      rw [Fintype.card_piFinset]; apply Finset.prod_congr rfl; intro v _
      simp [B, gam, Set.ncard_eq_toFinset_card _ (hfin _)]
  · intro g hg
    simp only [Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      SetLike.mem_coe] at hg
    obtain ⟨hgm, hg3⟩ := hg
    have hsum := h48 g hg3 (Φ g) (Φ_coe h_psi hg3)
    have hgl : (wordLength g : ℝ) ≤ m := by exact_mod_cast wordLength_le hgm
    have hsum' : (∑ v, (wordLength (Φ g v) : ℝ)) ≤ 3 / 4 * (m : ℝ) + 8 := by linarith
    have hlt : ∀ v, wordLength (Φ g v) < m + 9 := by
      intro v
      have : (wordLength (Φ g v) : ℝ) ≤ ∑ v, (wordLength (Φ g v) : ℝ) :=
        Finset.single_le_sum (f := fun v => (wordLength (Φ g v) : ℝ)) (fun _ _ => by positivity)
          (Finset.mem_univ v)
      have : (wordLength (Φ g v) : ℝ) < m + 9 := by
        have : (0 : ℝ) ≤ m := by positivity
        linarith
      exact_mod_cast this
    simp only [T, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Fintype.coe_piFinset,
      Set.mem_pi, Set.mem_univ, forall_const, exists_prop]
    refine ⟨fun v => ⟨wordLength (Φ g v), hlt v⟩, ?_, fun v => ?_⟩
    · simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hsum'
    · exact (Set.Finite.mem_toFinset _).mpr (mem_wordBall_wordLength _)
  · intro x hx y hy hxy
    simp only [Set.Finite.coe_toFinset] at hx hy
    exact Φ_injOn h_psi hx.2 hy.2 hxy

theorem sum_K_le (m : ℕ) (C μ : ℝ) (hμ : 0 ≤ μ)
    (hC : ∀ j, (gam j : ℝ) ≤ Real.exp (C + μ * j)) :
    (((∑ κ ∈ K m, ∏ v, gam (κ v) : ℕ)) : ℝ) ≤
      ((m : ℝ) + 9) ^ 8 * Real.exp (8 * C + μ * (3 / 4 * m + 8)) := by
  push_cast
  have hcard : ((K m).card : ℝ) ≤ ((m : ℝ) + 9) ^ 8 := by
    have : (K m).card ≤ (m + 9) ^ 8 := by
      calc (K m).card ≤ (Finset.univ : Finset ((Fin 3 → Bool) → Fin (m + 9))).card :=
            Finset.card_le_univ _
        _ = (m + 9) ^ 8 := by simp
    exact_mod_cast this
  calc (∑ κ ∈ K m, ∏ v, (gam (κ v) : ℝ))
      ≤ ∑ κ ∈ K m, Real.exp (8 * C + μ * (3 / 4 * m + 8)) := by
        apply Finset.sum_le_sum
        intro κ hκ
        simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hκ
        calc ∏ v, (gam (κ v) : ℝ) ≤ ∏ v, Real.exp (C + μ * ((κ v : ℕ) : ℝ)) :=
              Finset.prod_le_prod (fun _ _ => by positivity) (fun v _ => hC _)
          _ = Real.exp (∑ v, (C + μ * ((κ v : ℕ) : ℝ))) := (Real.exp_sum _ _).symm
          _ ≤ _ := by
            apply Real.exp_le_exp.mpr
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            simp only [Finset.sum_const, Finset.card_univ]
            have : Fintype.card (Fin 3 → Bool) = 8 := by simp
            rw [this]
            have := mul_le_mul_of_nonneg_left hκ hμ
            simp only [nsmul_eq_mul]
            push_cast
            linarith
    _ = (K m).card * Real.exp (8 * C + μ * (3 / 4 * m + 8)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

variable (h_index : (levelStabilizer 3).index = 2 ^ 7)

include h_psi h48 h_index in
theorem gam_rec (k : ℕ) (C μ : ℝ) (hμ : 0 ≤ μ)
    (hC : ∀ j, (gam j : ℝ) ≤ Real.exp (C + μ * j)) :
    (gam k : ℝ) ≤ 128 * (((k + 127 : ℕ) : ℝ) + 9) ^ 8 *
      Real.exp (8 * C + μ * (3 / 4 * ((k + 127 : ℕ) : ℝ) + 8)) := by
  have : (levelStabilizer 3).FiniteIndex := ⟨by rw [h_index]; norm_num⟩
  have h1 := nat_card_wordBall_le_index_mul' GrigorchukGroup.generators generators_finite closure_generators
    (levelStabilizer 3) k
  rw [h_index, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    show k + 2 ^ 7 - 1 = k + 127 by omega] at h1
  have h2 := card_St3_le h_psi h48 (k + 127)
  have h3 := sum_K_le (k + 127) C μ hμ hC
  have h4 : (gam k : ℝ) ≤ 128 * ((wordBall GrigorchukGroup.generators (k + 127) ∩
      (levelStabilizer 3 : Set GrigorchukGroup)).ncard : ℝ) := by
    exact_mod_cast h1
  have h5 : ((wordBall GrigorchukGroup.generators (k + 127) ∩ (levelStabilizer 3 : Set GrigorchukGroup)).ncard : ℝ) ≤
      (((∑ κ ∈ K (k + 127), ∏ v, gam (κ v) : ℕ)) : ℝ) := by exact_mod_cast h2
  calc (gam k : ℝ) ≤ 128 * _ := h4
    _ ≤ 128 * _ := mul_le_mul_of_nonneg_left (h5.trans h3) (by norm_num)
    _ = _ := by ring

end Hyp

theorem split_wordBall {G : Type*} [Group G] (S : Set G) {g : G} {m n : ℕ}
    (hg : g ∈ wordBall S (m + n)) : ∃ x ∈ wordBall S m, ∃ y ∈ wordBall S n, x * y = g := by
  obtain ⟨l, hl, hS, rfl⟩ := hg
  refine ⟨(l.take m).prod, ⟨l.take m, by simp, fun z hz => hS z (List.mem_of_mem_take hz), rfl⟩,
    (l.drop m).prod, ⟨l.drop m, by simp; omega, fun z hz => hS z (List.mem_of_mem_drop hz), rfl⟩,
    List.prod_take_mul_prod_drop _ _⟩

theorem gam_pos (k : ℕ) : 1 ≤ gam k :=
  (Set.ncard_pos (wordBall_finite _ generators_finite k)).mpr ⟨1, one_mem_wordBall _ k⟩

theorem gam_mono : Monotone gam := fun _ _ h =>
  Set.ncard_le_ncard (wordBall_mono _ h) (wordBall_finite _ generators_finite _)

theorem gam_submul (m n : ℕ) : gam (m + n) ≤ gam m * gam n := by
  have hf := wordBall_finite _ generators_finite
  have : Finite (wordBall GrigorchukGroup.generators m × wordBall GrigorchukGroup.generators n) :=
    @Finite.instProd _ _ (hf m).to_subtype (hf n).to_subtype
  let f : wordBall GrigorchukGroup.generators m × wordBall GrigorchukGroup.generators n →
      wordBall GrigorchukGroup.generators (m + n) :=
    fun p => ⟨p.1 * p.2, mul_mem_wordBall _ p.1.2 p.2.2⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := split_wordBall _ hg
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have := Nat.card_le_card_of_surjective f hsurj
  simpa [Nat.card_prod, Nat.card_coe_set_eq, gam] using this

/-- The analytic part: the recursive inequality forces subexponential growth. -/
theorem growth_of_rec (g : ℕ → ℕ) (hpos : ∀ k, 1 ≤ g k) (hmono : Monotone g)
    (hsub : ∀ m n, g (m + n) ≤ g m * g n)
    (hrec : ∀ C μ : ℝ, 0 ≤ μ → (∀ j, (g j : ℝ) ≤ Real.exp (C + μ * j)) → ∀ k,
      (g k : ℝ) ≤ 128 * (((k + 127 : ℕ) : ℝ) + 9) ^ 8 *
        Real.exp (8 * C + μ * (3 / 4 * ((k + 127 : ℕ) : ℝ) + 8))) :
    ∀ c : ℝ, 1 < c → ∃ N : ℕ, ∀ n ≥ N, (g n : ℝ) ≤ c ^ n := by
  have gpos : ∀ k, (0 : ℝ) < g k := fun k => by have := hpos k; positivity
  set u : ℕ → ℝ := fun n => Real.log (g n) with hu_def
  have hnn : ∀ n, 0 ≤ u n := fun n => Real.log_nonneg (by exact_mod_cast hpos n)
  have hu : Subadditive u := by
    intro m n
    simp only [hu_def]
    rw [← Real.log_mul (gpos m).ne' (gpos n).ne']
    exact Real.log_le_log (gpos _) (by exact_mod_cast hsub m n)
  have hbdd : BddBelow (Set.range fun n => u n / n) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (hnn n) (Nat.cast_nonneg n)⟩
  have ht := hu.tendsto_lim hbdd
  set L := hu.lim with hL
  have hL0 : 0 ≤ L := ge_of_tendsto' ht (fun n => div_nonneg (hnn n) (Nat.cast_nonneg n))
  have hLeq : L = 0 := by
    by_contra hne
    have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hne)
    set μ : ℝ := 9 / 8 * L with hμ
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds (show L < μ by linarith)))
    set C := u N
    have hC0 : 0 ≤ C := hnn N
    have hCu : ∀ j, u j ≤ C + μ * j := by
      intro j
      rcases le_or_gt N j with hj | hj
      · rcases Nat.eq_zero_or_pos j with rfl | hj0
        · obtain rfl : N = 0 := by omega
          simp [C]
        · have h1 := hN j hj
          have hj0' : (0 : ℝ) < j := by exact_mod_cast hj0
          rw [div_lt_iff₀ hj0'] at h1
          linarith
      · have : u j ≤ u N := Real.log_le_log (gpos j) (by exact_mod_cast hmono hj.le)
        have : 0 ≤ μ * j := by positivity
        linarith
    have hC : ∀ j, (g j : ℝ) ≤ Real.exp (C + μ * j) := by
      intro j
      rw [← Real.exp_log (gpos j)]
      exact Real.exp_le_exp.mpr (hCu j)
    have hrec' := hrec C μ (by positivity) hC
    -- logarithmic form
    have hlog : ∀ k : ℕ, u k ≤ Real.log 128 + 8 * Real.log ((k : ℝ) + 136) +
        (8 * C + μ * (3 / 4 * ((k : ℝ) + 127) + 8)) := by
      intro k
      have h := hrec' k
      push_cast at h
      have e : (k : ℝ) + 127 + 9 = k + 136 := by ring
      rw [e] at h
      have hp : (0 : ℝ) < (k : ℝ) + 136 := by positivity
      calc u k ≤ Real.log (128 * ((k : ℝ) + 136) ^ 8 *
            Real.exp (8 * C + μ * (3 / 4 * ((k : ℝ) + 127) + 8))) := Real.log_le_log (gpos k) h
        _ = _ := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
            Real.log_pow, Real.log_exp]
          push_cast; ring
    have hlo := Real.isLittleO_log_id_atTop.bound (show 0 < L / 128 by positivity)
    have htend : Filter.Tendsto (fun k : ℕ => (k : ℝ) + 136) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun k => by linarith) tendsto_natCast_atTop_atTop
    have hev := htend.eventually hlo
    set A : ℝ := Real.log 128 + 136 * L / 16 + 8 * C + μ * (3 / 4 * 127 + 8)
    set R : ℝ := 32 * A / (3 * L)
    obtain ⟨k, hk1, hk2, hk3⟩ := (hev.and ((Filter.eventually_ge_atTop 1).and
      (tendsto_natCast_atTop_atTop.eventually (Filter.eventually_gt_atTop R)))).exists
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk2
    have hLk : L * k ≤ u k := by
      have := hu.lim_le_div hbdd (show k ≠ 0 by omega)
      rwa [le_div_iff₀ hk0] at this
    have hlogk : Real.log ((k : ℝ) + 136) ≤ L / 128 * ((k : ℝ) + 136) := by
      have hp : (0 : ℝ) < (k : ℝ) + 136 := by positivity
      simp only [Real.norm_eq_abs, id] at hk1
      rw [abs_of_pos hp] at hk1
      exact (le_abs_self _).trans hk1
    have hkR : 3 * L * R < 3 * L * k := mul_lt_mul_of_pos_left hk3 (by positivity)
    have hR : 3 * L * R = 32 * A := by
      simp only [R]; field_simp
    have := hlog k
    have hAdef : A = Real.log 128 + 136 * L / 16 + 8 * C + μ * (3 / 4 * 127 + 8) := rfl
    rw [hμ] at this hAdef
    linarith
  intro c hc
  have hlc : 0 < Real.log c := Real.log_pos hc
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (ht.eventually (gt_mem_nhds (show L < Real.log c by linarith)))
  refine ⟨max N 1, fun n hn => ?_⟩
  have h1 := hN n (le_of_max_le_left hn)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [div_lt_iff₀ hn0] at h1
  have hcpos : 0 < c ^ n := by positivity
  rw [← Real.log_le_log_iff (gpos n) hcpos, Real.log_pow]
  simp only [hu_def] at h1
  linarith

theorem isExponentiallyBounded_grigorchukGroup'
    (h_sum : ∀ (g : GrigorchukGroup) (hg : g ∈ levelStabilizer 3)
      (h : (Fin 3 → Bool) → GrigorchukGroup)
      (hh : ∀ v, (h v : BinaryTreeAut) = treeSection (g : BinaryTreeAut) (List.ofFn v)),
      (∑ v, (wordLength (h v) : ℝ)) ≤ 3 / 4 * (wordLength g : ℝ) + 8)
    (h_psi : ∀ n : ℕ,
      (∀ g : GrigorchukGroup, g ∈ levelStabilizer n → ∀ v : Fin n → Bool,
          treeSection (g : BinaryTreeAut) (List.ofFn v) ∈ GrigorchukGroup) ∧
        (∀ g h : GrigorchukGroup, g ∈ levelStabilizer n → h ∈ levelStabilizer n →
          ∀ v : Fin n → Bool, treeSection ((g * h : GrigorchukGroup) : BinaryTreeAut) (List.ofFn v) =
            treeSection (g : BinaryTreeAut) (List.ofFn v) * treeSection (h : BinaryTreeAut) (List.ofFn v)) ∧
        ∀ g h : GrigorchukGroup, g ∈ levelStabilizer n → h ∈ levelStabilizer n →
          (∀ v : Fin n → Bool, treeSection (g : BinaryTreeAut) (List.ofFn v) =
            treeSection (h : BinaryTreeAut) (List.ofFn v)) → g = h)
    (h_index : (levelStabilizer 3).index = 2 ^ 7) :
    Chou.IsExponentiallyBounded GrigorchukGroup := by
  refine ⟨generators_finite.toFinset, by rw [Set.Finite.coe_toFinset]; exact closure_generators,
    fun c hc => ?_⟩
  obtain ⟨N, hN⟩ := growth_of_rec gam gam_pos gam_mono gam_submul
    (fun C μ hμ hC k => gam_rec h_psi h_sum h_index k C μ hμ hC) c hc
  refine ⟨N, fun n hn => ?_⟩
  rw [Set.Finite.coe_toFinset, Nat.card_coe_set_eq]
  exact hN n hn


end Grig

end Garrido.GR.Gro

namespace Garrido.GR.Final

open Garrido


theorem index_levelStabilizer_three : (levelStabilizer 3).index = 2 ^ 7 :=
  by
  first
    | exact Garrido.index_levelStabilizer_three
    | exact Garrido.index_levelStabilizer_three ..
    | (apply Garrido.index_levelStabilizer_three <;> first | assumption | infer_instance)
    | simpa using Garrido.index_levelStabilizer_three


theorem treeSection_mem_and_map_mul_and_injective :
    ((∀ g : levelStabilizer 1,
        (stOnePair g).1 ∈ GrigorchukGroup ∧ (stOnePair g).2 ∈ GrigorchukGroup) ∧
      (∀ g h : levelStabilizer 1, stOnePair (g * h) = stOnePair g * stOnePair h) ∧
      Function.Injective stOnePair) ∧
    ∀ n : ℕ,
      (∀ g : GrigorchukGroup, g ∈ levelStabilizer n → ∀ v : Fin n → Bool,
          treeSection (g : BinaryTreeAut) (List.ofFn v) ∈ GrigorchukGroup) ∧
        (∀ g h : GrigorchukGroup, g ∈ levelStabilizer n → h ∈ levelStabilizer n →
          ∀ v : Fin n → Bool, treeSection ((g * h : GrigorchukGroup) : BinaryTreeAut) (List.ofFn v) =
            treeSection (g : BinaryTreeAut) (List.ofFn v) * treeSection (h : BinaryTreeAut) (List.ofFn v)) ∧
        ∀ g h : GrigorchukGroup, g ∈ levelStabilizer n → h ∈ levelStabilizer n →
          (∀ v : Fin n → Bool, treeSection (g : BinaryTreeAut) (List.ofFn v) =
            treeSection (h : BinaryTreeAut) (List.ofFn v)) → g = h :=
  by
  first
    | exact Garrido.treeSection_mem_and_map_mul_and_injective
    | exact Garrido.treeSection_mem_and_map_mul_and_injective ..
    | (apply Garrido.treeSection_mem_and_map_mul_and_injective <;> first | assumption | infer_instance)
    | simpa using Garrido.treeSection_mem_and_map_mul_and_injective


theorem sum_wordLength_treeSection_le (g : GrigorchukGroup) (hg : g ∈ levelStabilizer 3)
    (h : (Fin 3 → Bool) → GrigorchukGroup)
    (hh : ∀ v, (h v : BinaryTreeAut) = treeSection (g : BinaryTreeAut) (List.ofFn v)) :
    (∑ v, (wordLength (h v) : ℝ)) ≤ 3 / 4 * (wordLength g : ℝ) + 8 :=
  by
  try haveI := g; try haveI := hg; try haveI := h; try haveI := hh; first
    | exact Garrido.sum_wordLength_treeSection_le g hg h hh
    | exact Garrido.sum_wordLength_treeSection_le
    | exact Garrido.sum_wordLength_treeSection_le ..
    | (apply Garrido.sum_wordLength_treeSection_le <;> first | assumption | infer_instance)
    | simpa using Garrido.sum_wordLength_treeSection_le


theorem nat_card_wordBall_le_index_mul {G : Type*} [Group G] (S : Set G) (hS : S.Finite)
    (hgen : Subgroup.closure S = ⊤) (H : Subgroup G) [H.FiniteIndex] (k : ℕ) :
    Nat.card (Chou.wordBall S k) ≤
      H.index * Nat.card ↥(Chou.wordBall S (k + H.index - 1) ∩ (H : Set G)) :=
  by
  try haveI := S; try haveI := hS; try haveI := hgen; try haveI := H; try haveI := k; first
    | exact Garrido.nat_card_wordBall_le_index_mul S hS hgen H k
    | exact Garrido.nat_card_wordBall_le_index_mul
    | exact Garrido.nat_card_wordBall_le_index_mul ..
    | (apply Garrido.nat_card_wordBall_le_index_mul <;> first | assumption | infer_instance)
    | simpa using Garrido.nat_card_wordBall_le_index_mul


theorem isExponentiallyBounded_grigorchukGroup : Chou.IsExponentiallyBounded GrigorchukGroup :=
  Garrido.GR.Gro.isExponentiallyBounded_grigorchukGroup' sum_wordLength_treeSection_le treeSection_mem_and_map_mul_and_injective.2 index_levelStabilizer_three


end Garrido.GR.Final

open Garrido

theorem solution : Chou.IsExponentiallyBounded GrigorchukGroup :=
  Garrido.GR.Final.isExponentiallyBounded_grigorchukGroup
