-- Prove2me | solution 1 for Garrido.nat_card_wordBall_le_index_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T13:16:25.824094+00:00
-- url     : https://prove2.me/submissions/ff7e08a3-cf1d-485f-a35c-f4043eb72a25

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

/-- The cosets reached by words of length `≤ j`. -/
def reach (j : ℕ) : Set (G ⧸ H) := (QuotientGroup.mk : G → G ⧸ H) '' wordBall S j

theorem mem_reach_succ_iff {q : G ⧸ H} {j : ℕ} :
    q ∈ reach S H (j + 1) ↔ ∃ t : G, (t = 1 ∨ t ∈ S ∨ t⁻¹ ∈ S) ∧ ∃ q' ∈ reach S H j, q = t • q' := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨t, ht, g', hg', rfl⟩ := (mem_wordBall_succ_iff S).mp hg
    exact ⟨t, ht, _, ⟨g', hg', rfl⟩, rfl⟩
  · rintro ⟨t, ht, _, ⟨g', hg', rfl⟩, rfl⟩
    exact ⟨t * g', (mem_wordBall_succ_iff S).mpr ⟨t, ht, g', hg', rfl⟩, rfl⟩

theorem reach_stable {j : ℕ} (h : reach S H (j + 1) = reach S H j) (m : ℕ) :
    reach S H (j + m) = reach S H j := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← h]; ext q
    rw [show j + (m + 1) = (j + m) + 1 by omega, mem_reach_succ_iff, mem_reach_succ_iff, ih]

theorem reach_mono {j j' : ℕ} (h : j ≤ j') : reach S H j ⊆ reach S H j' :=
  Set.image_mono (wordBall_mono S h)

theorem reach_univ_or [H.FiniteIndex] (hgen : Subgroup.closure S = ⊤) (j : ℕ) :
    reach S H j = Set.univ ∨ j + 1 ≤ (reach S H j).ncard := by
  induction j with
  | zero =>
    right
    have : reach S H 0 = {((1 : G) : G ⧸ H)} := by
      ext q; constructor
      · rintro ⟨g, ⟨l, hl, -, rfl⟩, rfl⟩
        simp at hl; simp [hl]
      · rintro rfl; exact ⟨1, one_mem_wordBall S 0, rfl⟩
    simp [this]
  | succ j ih =>
    rcases ih with h | h
    · left; exact Set.eq_univ_of_univ_subset (h ▸ reach_mono S H (Nat.le_succ j))
    · by_cases heq : reach S H (j + 1) = reach S H j
      · left
        apply Set.eq_univ_of_forall
        intro q
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        obtain ⟨k, hk⟩ := exists_mem_wordBall S hgen g
        have mem : ((g : G) : G ⧸ H) ∈ reach S H (j + k) := ⟨g, wordBall_mono S (by omega) hk, rfl⟩
        rw [reach_stable S H heq k] at mem
        exact reach_mono S H (Nat.le_succ j) mem
      · right
        have hss : reach S H j ⊂ reach S H (j + 1) :=
          (Set.ssubset_iff_subset_ne).mpr ⟨reach_mono S H (Nat.le_succ j), Ne.symm heq⟩
        have := Set.ncard_lt_ncard hss (Set.toFinite _)
        omega

theorem exists_rep [H.FiniteIndex] (hgen : Subgroup.closure S = ⊤) (q : G ⧸ H) :
    ∃ t ∈ wordBall S (H.index - 1), (t : G ⧸ H) = q := by
  have hn : H.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have huniv : reach S H (H.index - 1) = Set.univ := by
    rcases reach_univ_or S H hgen (H.index - 1) with h | h
    · exact h
    · apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
      rw [Set.ncard_univ, ← Subgroup.index_eq_card]
      omega
  have : q ∈ reach S H (H.index - 1) := by rw [huniv]; trivial
  exact this

theorem nat_card_wordBall_le_index_mul' {G : Type*} [Group G] (S : Set G) (hS : S.Finite)
    (hgen : Subgroup.closure S = ⊤) (H : Subgroup G) [H.FiniteIndex] (k : ℕ) :
    Nat.card (Chou.wordBall S k) ≤
      H.index * Nat.card ↥(Chou.wordBall S (k + H.index - 1) ∩ (H : Set G)) := by
  have hn : H.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  choose rep hrep hrepq using exists_rep S H hgen
  have hfin : Finite ↥(Chou.wordBall S (k + H.index - 1) ∩ (H : Set G)) :=
    ((wordBall_finite S hS _).inter_of_left _).to_subtype
  let f : Chou.wordBall S k → (G ⧸ H) × ↥(Chou.wordBall S (k + H.index - 1) ∩ (H : Set G)) :=
    fun g => ((g : G), ⟨(rep (g : G ⧸ H))⁻¹ * g, by
      refine ⟨?_, ?_⟩
      · have := mul_mem_wordBall S (inv_mem_wordBall S (hrep (g : G ⧸ H))) g.2
        exact wordBall_mono S (by omega) this
      · have := hrepq ((g : G) : G ⧸ H)
        exact QuotientGroup.eq.mp this⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    simp only [f, Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have h3 := congrArg Subtype.val h2
    simp only at h3
    rw [h1] at h3
    exact Subtype.ext (mul_left_cancel h3)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, ← Subgroup.index_eq_card] at this

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


theorem nat_card_wordBall_le_index_mul {G : Type*} [Group G] (S : Set G) (hS : S.Finite)
    (hgen : Subgroup.closure S = ⊤) (H : Subgroup G) [H.FiniteIndex] (k : ℕ) :
    Nat.card (Chou.wordBall S k) ≤
      H.index * Nat.card ↥(Chou.wordBall S (k + H.index - 1) ∩ (H : Set G)) :=
  by first | exact Garrido.GR.Gro.nat_card_wordBall_le_index_mul' | (intros; apply Garrido.GR.Gro.nat_card_wordBall_le_index_mul' <;> assumption)


end Garrido.GR.Final

open Garrido

theorem solution {G : Type*} [Group G] (S : Set G) (hS : S.Finite)
    (hgen : Subgroup.closure S = ⊤) (H : Subgroup G) [H.FiniteIndex] (k : ℕ) :
    Nat.card (Chou.wordBall S k) ≤
      H.index * Nat.card ↥(Chou.wordBall S (k + H.index - 1) ∩ (H : Set G)) :=
  Garrido.GR.Final.nat_card_wordBall_le_index_mul S hS hgen H k
