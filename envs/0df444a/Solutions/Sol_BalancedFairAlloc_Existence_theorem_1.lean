-- Prove2me | solution 1 for BalancedFairAlloc.Existence.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T08:07:16.942388+00:00
-- url     : https://prove2.me/submissions/a933233e-dfd7-44fc-9a54-bdedf52a29e9

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Model

set_option autoImplicit false

namespace BalancedFairAlloc_Theorem1_Proof

open Finset BalancedFairAlloc.Existence Filter Topology
open scoped Classical

/-! ### Part 0: Basic Properties of Allocations, Bundles, `Pbal`, `vmax`, and `fPO` -/

lemma mem_bundle_iff {n m : ℕ} (A : Allocation n m) (i : Fin n) (g : Fin m) :
    g ∈ bundle A i ↔ A g = i := by
  simp [bundle]

lemma disjoint_bundle {n m : ℕ} (A : Allocation n m) {i j : Fin n} (hij : i ≠ j) :
    Disjoint (bundle A i) (bundle A j) := by
  rw [Finset.disjoint_left]
  intro g hgi hgj
  rw [mem_bundle_iff] at hgi hgj
  exact hij (hgi.symm.trans hgj)

lemma sum_bundle_eq_sum_univ {n m : ℕ} {α : Type*} [AddCommMonoid α]
    (A : Allocation n m) (f : Fin m → α) :
    ∑ i : Fin n, ∑ g ∈ bundle A i, f g = ∑ g : Fin m, f g := by
  classical
  have h1 : ∀ i : Fin n, ∑ g ∈ bundle A i, f g = ∑ g : Fin m, if A g = i then f g else 0 := by
    intro i
    simp [bundle, Finset.sum_filter]
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp

lemma sum_card_bundle {n m : ℕ} (A : Allocation n m) :
    ∑ i : Fin n, (bundle A i).card = m := by
  have h := sum_bundle_eq_sum_univ A (fun _ => (1 : ℕ))
  simpa using h

lemma fval_allocMatrix {n m : ℕ} (v : Fin n → Fin m → ℝ) (A : Allocation n m) (i : Fin n) :
    fval v i (allocMatrix A) = bval v i (bundle A i) := by
  simp [fval, allocMatrix, bval, bundle, Finset.sum_filter]

lemma rowSum_allocMatrix {n m : ℕ} (A : Allocation n m) (i : Fin n) :
    ∑ g : Fin m, allocMatrix A i g = ((bundle A i).card : ℝ) := by
  simp [allocMatrix, bundle, Finset.sum_filter]

lemma colSum_allocMatrix {n m : ℕ} (A : Allocation n m) (g : Fin m) :
    ∑ i : Fin n, allocMatrix A i g = 1 := by
  simp [allocMatrix]

lemma allocMatrix_mem_Pbal_iff {n m : ℕ} (A : Allocation n m) :
    allocMatrix A ∈ Pbal n m ↔ IsBalanced A := by
  constructor
  · rintro ⟨_, _, hbal⟩ i
    obtain ⟨hl, hu⟩ := hbal i
    rw [rowSum_allocMatrix] at hl hu
    have hl' : m / n ≤ (bundle A i).card := by exact_mod_cast hl
    have hu' : (bundle A i).card ≤ m / n + 1 := by exact_mod_cast hu
    omega
  · intro hbal
    refine ⟨?_, colSum_allocMatrix A, ?_⟩
    · intro i g
      simp only [allocMatrix]
      split_ifs <;> norm_num
    · intro i
      rw [rowSum_allocMatrix]
      rcases hbal i with h | h <;> rw [h] <;> constructor <;> norm_cast <;> omega

/-- Canonical balanced allocation `g ↦ g mod n`. -/
def canonAlloc (n m : ℕ) (hn : 1 ≤ n) : Allocation n m :=
  fun g => ⟨g.val % n, Nat.mod_lt _ (by omega)⟩

lemma isBalanced_canonAlloc (n m : ℕ) (hn : 1 ≤ n) :
    IsBalanced (canonAlloc n m hn) := by
  intro i
  let k : ℕ := if i.val < m % n then m / n + 1 else m / n
  have hcard : (bundle (canonAlloc n m hn) i).card = k := by
    symm
    rw [← Finset.card_range k]
    refine Finset.card_bij
      (fun t ht => ⟨n * t + i.val, by
        rw [Finset.mem_range] at ht
        have hdm := (Nat.div_add_mod m n).symm
        dsimp [k] at ht
        split_ifs at ht with hi
        · have h1 : n * t ≤ n * (m / n) := Nat.mul_le_mul_left n (by omega)
          omega
        · have h1 : n * (t + 1) ≤ n * (m / n) := Nat.mul_le_mul_left n (by omega)
          have h2 : n * t + n = n * (t + 1) := by ring
          have hi2 : i.val < n := i.isLt
          omega⟩)
      (?_) (?_) (?_)
    · intro t ht
      rw [mem_bundle_iff]
      ext
      dsimp [canonAlloc]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
    · intro t₁ _ t₂ _ heq
      have hval : n * t₁ + i.val = n * t₂ + i.val := congrArg Fin.val heq
      have hmul : n * t₁ = n * t₂ := by omega
      exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
    · intro g hg
      rw [mem_bundle_iff] at hg
      have hmod : g.val % n = i.val := congrArg Fin.val hg
      refine ⟨g.val / n, ?_, ?_⟩
      · rw [Finset.mem_range]
        have hdmg : n * (g.val / n) + i.val = g.val := by
          have := Nat.div_add_mod g.val n
          omega
        have hltm : g.val < n * (m / n) + m % n := by
          have := Nat.div_add_mod m n
          have := g.isLt
          omega
        have hrem_lt : m % n < n := Nat.mod_lt m (by omega)
        dsimp [k]
        split_ifs with hi
        · by_contra hge
          have h1 : n * (m / n + 1) ≤ n * (g.val / n) := Nat.mul_le_mul_left n (by omega)
          have h2 : n * (m / n) + n = n * (m / n + 1) := by ring
          omega
        · by_contra hge
          have h1 : n * (m / n) ≤ n * (g.val / n) := Nat.mul_le_mul_left n (by omega)
          omega
      · ext
        dsimp
        have hdmg := Nat.div_add_mod g.val n
        rw [hmod] at hdmg
        exact hdmg
  rw [hcard]
  dsimp [k]
  split_ifs <;> [exact Or.inr rfl; exact Or.inl rfl]

lemma Pbal_nonempty (n m : ℕ) (hn : 1 ≤ n) : (Pbal n m).Nonempty :=
  ⟨allocMatrix (canonAlloc n m hn),
    (allocMatrix_mem_Pbal_iff _).mpr (isBalanced_canonAlloc n m hn)⟩

lemma entry_le_one_of_mem_Pbal {n m : ℕ} {x : Fin n → Fin m → ℝ} (hx : x ∈ Pbal n m)
    (i : Fin n) (g : Fin m) : x i g ≤ 1 := by
  rcases hx with ⟨hnn, hcol, _⟩
  rw [← hcol g]
  exact Finset.single_le_sum (fun j _ => hnn j g) (Finset.mem_univ i)

lemma isCompact_Pbal (n m : ℕ) : IsCompact (Pbal n m) := by
  let box : Set (Fin n → Fin m → ℝ) :=
    Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1))
  have hbox_compact : IsCompact box :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  have hsub : Pbal n m ⊆ box := by
    intro x hx i _ g _
    exact ⟨hx.1 i g, entry_le_one_of_mem_Pbal hx i g⟩
  have hclosed : IsClosed (Pbal n m) := by
    unfold Pbal
    have hc1 : IsClosed {x : Fin n → Fin m → ℝ | ∀ i g, 0 ≤ x i g} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun g =>
        isClosed_le continuous_const ((continuous_apply g).comp (continuous_apply i))
    have hc2 : IsClosed {x : Fin n → Fin m → ℝ | ∀ g, ∑ i, x i g = 1} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun g =>
        isClosed_eq (continuous_finset_sum _ fun i _ =>
          (continuous_apply g).comp (continuous_apply i)) continuous_const
    have hc3 : IsClosed {x : Fin n → Fin m → ℝ |
        ∀ i, ((m / n : ℕ) : ℝ) ≤ ∑ g, x i g ∧ ∑ g, x i g ≤ ((m / n : ℕ) : ℝ) + 1} := by
      simp only [Set.setOf_forall, Set.setOf_and]
      exact isClosed_iInter fun i => IsClosed.inter
        (isClosed_le continuous_const
          (continuous_finset_sum _ fun g _ => (continuous_apply g).comp (continuous_apply i)))
        (isClosed_le
          (continuous_finset_sum _ fun g _ => (continuous_apply g).comp (continuous_apply i))
          continuous_const)
    exact hc1.inter (hc2.inter hc3)
  exact hbox_compact.of_isClosed_subset hclosed hsub

lemma maximizesWeightedWelfare_imp_isFPOIn {n m : ℕ} (v : Fin n → Fin m → ℝ)
    (α : Fin n → ℝ) (hα : ∀ i, 0 < α i) (P : Set (Fin n → Fin m → ℝ))
    (x : Fin n → Fin m → ℝ) (hmax : MaximizesWeightedWelfare v α P x) :
    IsFPOIn v P x := by
  refine ⟨hmax.1, ?_⟩
  rintro ⟨y, hyP, hle, i₀, hlt⟩
  have hsum_lt : ∑ i, α i * fval v i x < ∑ i, α i * fval v i y := by
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, Finset.mem_univ i₀, ?_⟩
    · exact mul_le_mul_of_nonneg_left (hle i) (le_of_lt (hα i))
    · exact mul_lt_mul_of_pos_left hlt (hα i₀)
  linarith [hmax.2 y hyP]

lemma vmax_nonneg {n m : ℕ} (v : Fin n → Fin m → ℝ) : 0 ≤ vmax v := by
  unfold vmax
  rw [Finset.le_fold_max]
  exact Or.inl le_rfl

lemma abs_val_le_vmax {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n) (g : Fin m) :
    |v i g| ≤ vmax v := by
  unfold vmax
  rw [Finset.le_fold_max]
  exact Or.inr ⟨(i, g), Finset.mem_univ _, le_rfl⟩

lemma M0_pos {n m : ℕ} (v : Fin n → Fin m → ℝ) : 0 < M0 v := by
  have := vmax_nonneg v
  unfold M0
  linarith

/-! ### Pillar 1: Elementary Cycle/Path Rounding for Integrality of `Pbal` -/

section Integrality

def IsFracEntry {n m : ℕ} (x : Fin n → Fin m → ℝ) (i : Fin n) (g : Fin m) : Prop :=
  0 < x i g ∧ x i g < 1

def IsFracRow {n m : ℕ} (x : Fin n → Fin m → ℝ) (i : Fin n) : Prop :=
  ((m / n : ℕ) : ℝ) < ∑ g, x i g ∧ ∑ g, x i g < ((m / n : ℕ) : ℝ) + 1

noncomputable def fracEntrySet {n m : ℕ} (x : Fin n → Fin m → ℝ) : Finset (Fin n × Fin m) :=
  Finset.univ.filter (fun ig => IsFracEntry x ig.1 ig.2)

noncomputable def fracRowSet {n m : ℕ} (x : Fin n → Fin m → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => IsFracRow x i)

@[simp] lemma mem_fracEntrySet {n m : ℕ} {x : Fin n → Fin m → ℝ} {ig : Fin n × Fin m} :
    ig ∈ fracEntrySet x ↔ IsFracEntry x ig.1 ig.2 := by
  simp [fracEntrySet]

@[simp] lemma mem_fracRowSet {n m : ℕ} {x : Fin n → Fin m → ℝ} {i : Fin n} :
    i ∈ fracRowSet x ↔ IsFracRow x i := by
  simp [fracRowSet]

noncomputable def fracPot {n m : ℕ} (x : Fin n → Fin m → ℝ) : ℕ :=
  2 * (fracEntrySet x).card + (fracRowSet x).card

lemma eq_zero_or_one_of_not_isFracEntry {n m : ℕ} {x : Fin n → Fin m → ℝ}
    (hx : x ∈ Pbal n m) {i : Fin n} {g : Fin m} (h : ¬ IsFracEntry x i g) :
    x i g = 0 ∨ x i g = 1 := by
  have h0 : 0 ≤ x i g := hx.1 i g
  have h1 : x i g ≤ 1 := entry_le_one_of_mem_Pbal hx i g
  unfold IsFracEntry at h
  push_neg at h
  rcases lt_or_eq_of_le h0 with hpos | heq0
  · exact Or.inr (le_antisymm h1 (h hpos))
  · exact Or.inl heq0.symm

lemma no_unique_frac_col {n m : ℕ} {x : Fin n → Fin m → ℝ} (hx : x ∈ Pbal n m)
    {i₀ : Fin n} {g : Fin m} (hi₀ : IsFracEntry x i₀ g) :
    ∃ i₁ : Fin n, i₁ ≠ i₀ ∧ IsFracEntry x i₁ g := by
  by_contra hno
  push_neg at hno
  have hcol := hx.2.1 g
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at hcol
  by_cases hex1 : ∃ i₁ ∈ Finset.univ.erase i₀, x i₁ g = 1
  · rcases hex1 with ⟨i₁, hi₁, h1⟩
    have hge : x i₁ g ≤ ∑ i ∈ Finset.univ.erase i₀, x i g :=
      Finset.single_le_sum (fun j _ => hx.1 j g) hi₁
    linarith [hi₀.1]
  · push_neg at hex1
    have hsum0 : ∑ i ∈ Finset.univ.erase i₀, x i g = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
      rcases eq_zero_or_one_of_not_isFracEntry hx (hno i hne) with h0 | h1
      · exact h0
      · exact absurd h1 (hex1 i hi)
    linarith [hi₀.2]

lemma no_unique_frac_int_row {n m : ℕ} {x : Fin n → Fin m → ℝ} (hx : x ∈ Pbal n m)
    {i : Fin n} (hint : ¬ IsFracRow x i) {g₀ : Fin m} (hg₀ : IsFracEntry x i g₀) :
    ∃ g₁ : Fin m, g₁ ≠ g₀ ∧ IsFracEntry x i g₁ := by
  by_contra hno
  push_neg at hno
  obtain ⟨hl, hu⟩ := hx.2.2 i
  have hrow_int : ∃ k : ℕ, ∑ g, x i g = (k : ℝ) := by
    unfold IsFracRow at hint
    push_neg at hint
    rcases lt_or_eq_of_le hl with hgt | heq
    · refine ⟨m / n + 1, ?_⟩
      push_cast
      exact le_antisymm hu (hint hgt)
    · exact ⟨m / n, heq.symm⟩
  rcases hrow_int with ⟨k, hk⟩
  classical
  let S := (Finset.univ.erase g₀).filter (fun g => x i g = 1)
  have hsum_erase : ∑ g ∈ Finset.univ.erase g₀, x i g = (S.card : ℝ) := by
    have hrew : ∀ g ∈ Finset.univ.erase g₀, x i g = if x i g = 1 then (1 : ℝ) else 0 := by
      intro g hg
      have hne : g ≠ g₀ := (Finset.mem_erase.mp hg).1
      rcases eq_zero_or_one_of_not_isFracEntry hx (hno g hne) with h0 | h1
      · simp [h0]
      · simp [h1]
    rw [Finset.sum_congr rfl hrew, Finset.sum_ite]
    simp [S]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ g₀), hsum_erase] at hk
  have hlt1 : (S.card : ℝ) < (k : ℝ) := by linarith [hg₀.1]
  have hlt2 : (k : ℝ) < (S.card : ℝ) + 1 := by linarith [hg₀.2]
  have hn1 : S.card < k := by exact_mod_cast hlt1
  have hn2 : k < S.card + 1 := by exact_mod_cast hlt2
  omega

abbrev BVert (n m : ℕ) := Fin n ⊕ Fin m

def FracAdj {n m : ℕ} (x : Fin n → Fin m → ℝ) : BVert n m → BVert n m → Prop
  | Sum.inl i, Sum.inr g => IsFracEntry x i g
  | Sum.inr g, Sum.inl i => IsFracEntry x i g
  | _, _ => False

lemma fracAdj_symm {n m : ℕ} {x : Fin n → Fin m → ℝ} {u v : BVert n m} :
    FracAdj x u v → FracAdj x v u := by
  cases u <;> cases v <;> simp [FracAdj]

lemma fracAdj_irrefl {n m : ℕ} {x : Fin n → Fin m → ℝ} (u : BVert n m) :
    ¬ FracAdj x u u := by
  cases u <;> simp [FracAdj]

lemma fracAdj_isLeft_iff {n m : ℕ} {x : Fin n → Fin m → ℝ} {u v : BVert n m}
    (h : FracAdj x u v) : u.isLeft ↔ ¬ v.isLeft := by
  cases u <;> cases v <;> simp [FracAdj] at h ⊢

def IsFracWalk {n m L : ℕ} (x : Fin n → Fin m → ℝ) (w : Fin (L + 1) ↪ BVert n m) : Prop :=
  ∀ s : Fin L, FracAdj x (w s.castSucc) (w s.succ)

lemma isFracWalk_rev {n m L : ℕ} {x : Fin n → Fin m → ℝ} {w : Fin (L + 1) ↪ BVert n m}
    (hw : IsFracWalk x w) :
    IsFracWalk x (Fin.revPerm.toEmbedding.trans w) := by
  intro s
  change FracAdj x (w (Fin.rev s.castSucc)) (w (Fin.rev s.succ))
  have h1 : Fin.rev s.castSucc = (Fin.rev s).succ := by
    have := s.isLt
    ext; simp [Fin.rev]; omega
  have h2 : Fin.rev s.succ = (Fin.rev s).castSucc := by
    ext; simp [Fin.rev]
  rw [h1, h2]
  exact fracAdj_symm (hw (Fin.rev s))

lemma walk_isLeft_parity {n m L : ℕ} {x : Fin n → Fin m → ℝ} {w : Fin (L + 1) ↪ BVert n m}
    (hw : IsFracWalk x w) (t : Fin (L + 1)) :
    (w t).isLeft ↔ (Even t.val ↔ (w 0).isLeft) := by
  obtain ⟨tv, htv⟩ := t
  induction tv with
  | zero =>
    have h0 : (⟨0, htv⟩ : Fin (L + 1)) = 0 := by ext; rfl
    rw [h0]
    simp
  | succ k ih =>
    have hs : FracAdj x (w ⟨k, by omega⟩) (w ⟨k + 1, htv⟩) := hw ⟨k, by omega⟩
    have hstep := fracAdj_isLeft_iff hs
    have ihk := ih (by omega)
    have hpar : Even (k + 1) ↔ ¬ Even k := Nat.even_add_one
    tauto

/-- Valid alternating direction for rounding on `Pbal`. -/
structure ValidDir (n m : ℕ) (x : Fin n → Fin m → ℝ) where
  Δ : Fin n → Fin m → ℝ
  S_end : Finset (Fin n)
  exists_nonzero : ∃ i g, Δ i g = 1 ∨ Δ i g = -1
  vals : ∀ i g, Δ i g = -1 ∨ Δ i g = 0 ∨ Δ i g = 1
  supp_frac : ∀ i g, Δ i g ≠ 0 → IsFracEntry x i g
  col_zero : ∀ g, ∑ i, Δ i g = 0
  row_out : ∀ i, i ∉ S_end → ∑ g, Δ i g = 0
  row_in : ∀ i, i ∈ S_end →
    (∑ g, Δ i g = 1 ∨ ∑ g, Δ i g = -1) ∧ IsFracRow x i

lemma validDir_of_even_cycle {n m k : ℕ} (hk : 2 ≤ k) {x : Fin n → Fin m → ℝ}
    (ic : Fin k ↪ Fin n) (gc : Fin k ↪ Fin m)
    (hf1 : ∀ t : Fin k, IsFracEntry x (ic t) (gc t))
    (hf2 : ∀ t : Fin k, IsFracEntry x (ic ⟨(t.val + 1) % k, Nat.mod_lt _ (by omega)⟩) (gc t)) :
    Nonempty (ValidDir n m x) := by
  classical
  let nxt : Equiv.Perm (Fin k) :=
    { toFun := fun t => ⟨(t.val + 1) % k, Nat.mod_lt _ (by omega)⟩
      invFun := fun t => ⟨(t.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
      left_inv := fun t => by
        ext
        show ((t.val + 1) % k + k - 1) % k = t.val
        have ht := t.isLt
        by_cases hlast : t.val + 1 = k
        · rw [hlast, Nat.mod_self, Nat.zero_add]
          have hm : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
          rw [hm]; omega
        · have hm : (t.val + 1) % k = t.val + 1 := Nat.mod_eq_of_lt (by omega)
          rw [hm]
          have : t.val + 1 + k - 1 = t.val + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
      right_inv := fun t => by
        ext
        show ((t.val + k - 1) % k + 1) % k = t.val
        have ht := t.isLt
        by_cases h0 : t.val = 0
        · rw [h0, Nat.zero_add]
          have hm : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
          rw [hm]
          have : k - 1 + 1 = k := by omega
          rw [this, Nat.mod_self]
        · have hlt : t.val + k - 1 = (t.val - 1) + k := by omega
          have hm : (t.val + k - 1) % k = t.val - 1 := by
            rw [hlt, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hm]
          have : t.val - 1 + 1 = t.val := by omega
          rw [this, Nat.mod_eq_of_lt ht] }
  have hnxt_ne : ∀ t : Fin k, nxt t ≠ t := by
    intro t heq
    have hv : (t.val + 1) % k = t.val := congrArg Fin.val heq
    have ht := t.isLt
    by_cases hlast : t.val + 1 = k
    · rw [hlast, Nat.mod_self] at hv; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hv; omega
  let Δ : Fin n → Fin m → ℝ := fun i g =>
    ∑ t : Fin k, ((if ic t = i ∧ gc t = g then (1 : ℝ) else 0) -
      (if ic (nxt t) = i ∧ gc t = g then (1 : ℝ) else 0))
  have hΔ_eval : ∀ i g,
      ((∀ t, gc t ≠ g) → Δ i g = 0) ∧
      (∀ t, gc t = g → Δ i g = (if ic t = i then (1 : ℝ) else 0) -
        (if ic (nxt t) = i then (1 : ℝ) else 0)) := by
    intro i g
    constructor
    · intro hno
      dsimp [Δ]
      refine Finset.sum_eq_zero fun t _ => ?_
      have hne := hno t
      simp [hne]
    · intro t hgt
      dsimp [Δ]
      rw [Finset.sum_eq_single t]
      · simp [hgt]
      · intro s _ hs
        have hgs : gc s ≠ g := fun h => hs (gc.injective (h.trans hgt.symm))
        simp [hgs]
      · intro h; exact absurd (Finset.mem_univ t) h
  refine ⟨{
    Δ := Δ
    S_end := ∅
    exists_nonzero := by
      let t0 : Fin k := ⟨0, by omega⟩
      refine ⟨ic t0, gc t0, Or.inl ?_⟩
      rw [(hΔ_eval (ic t0) (gc t0)).2 t0 rfl]
      have hne : ic (nxt t0) ≠ ic t0 := fun h => hnxt_ne t0 (ic.injective h)
      simp [hne]
    vals := by
      intro i g
      by_cases hex : ∃ t, gc t = g
      · rcases hex with ⟨t, hgt⟩
        rw [(hΔ_eval i g).2 t hgt]
        have hne : ic (nxt t) ≠ ic t := fun h => hnxt_ne t (ic.injective h)
        by_cases h1 : ic t = i
        · subst h1; simp [hne]
        · by_cases h2 : ic (nxt t) = i <;> simp [h1, h2]
      · push_neg at hex
        rw [(hΔ_eval i g).1 hex]
        exact Or.inr (Or.inl rfl)
    supp_frac := by
      intro i g hnz
      by_cases hex : ∃ t, gc t = g
      · rcases hex with ⟨t, hgt⟩
        rw [(hΔ_eval i g).2 t hgt] at hnz
        by_cases h1 : ic t = i
        · subst h1; subst hgt; exact hf1 t
        · by_cases h2 : ic (nxt t) = i
          · subst h2; subst hgt; exact hf2 t
          · simp [h1, h2] at hnz
      · push_neg at hex
        exact absurd ((hΔ_eval i g).1 hex) hnz
    col_zero := by
      intro g
      dsimp [Δ]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [Finset.sum_sub_distrib]
      have s1 : (∑ x : Fin n, if ic t = x ∧ gc t = g then (1 : ℝ) else 0) =
          if gc t = g then 1 else 0 := by
        split_ifs with hg <;> simp [hg]
      have s2 : (∑ x : Fin n, if ic (nxt t) = x ∧ gc t = g then (1 : ℝ) else 0) =
          if gc t = g then 1 else 0 := by
        split_ifs with hg <;> simp [hg]
      rw [s1, s2, sub_self]
    row_out := by
      intro i _
      dsimp [Δ]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_sub_distrib]
      have s1 : ∀ t : Fin k, (∑ g : Fin m, if ic t = i ∧ gc t = g then (1 : ℝ) else 0) =
          if ic t = i then 1 else 0 := by
        intro t; by_cases hi : ic t = i <;> simp [hi]
      have s2 : ∀ t : Fin k, (∑ g : Fin m, if ic (nxt t) = i ∧ gc t = g then (1 : ℝ) else 0) =
          if ic (nxt t) = i then 1 else 0 := by
        intro t; by_cases hi : ic (nxt t) = i <;> simp [hi]
      simp_rw [s1, s2]
      have hperm : (∑ t : Fin k, if ic (nxt t) = i then (1 : ℝ) else 0) =
          ∑ t : Fin k, if ic t = i then (1 : ℝ) else 0 :=
        Equiv.sum_comp nxt (fun t => if ic t = i then (1 : ℝ) else 0)
      linarith
    row_in := by simp
  }⟩

lemma sum_fin_sub_succ {k : ℕ} (f : Fin (k + 1) → ℝ) :
    ∑ t : Fin k, (f t.castSucc - f t.succ) = f 0 - f (Fin.last k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    have ih' := ih (fun s => f s.castSucc)
    simp only [Fin.castSucc_zero, Fin.castSucc_fin_succ] at ih'
    have hlast : (Fin.last k).succ = Fin.last (k + 1) := rfl
    rw [hlast]
    linarith [ih']

lemma validDir_of_frac_path {n m k : ℕ} (hk : 1 ≤ k) {x : Fin n → Fin m → ℝ}
    (ip : Fin (k + 1) ↪ Fin n) (gp : Fin k ↪ Fin m)
    (hf1 : ∀ t : Fin k, IsFracEntry x (ip t.castSucc) (gp t))
    (hf2 : ∀ t : Fin k, IsFracEntry x (ip t.succ) (gp t))
    (hra : IsFracRow x (ip 0)) (hrb : IsFracRow x (ip (Fin.last k))) :
    Nonempty (ValidDir n m x) := by
  classical
  let Δ : Fin n → Fin m → ℝ := fun i g =>
    ∑ t : Fin k, ((if ip t.castSucc = i ∧ gp t = g then (1 : ℝ) else 0) -
      (if ip t.succ = i ∧ gp t = g then (1 : ℝ) else 0))
  have hΔ_eval : ∀ i g,
      ((∀ t, gp t ≠ g) → Δ i g = 0) ∧
      (∀ t, gp t = g → Δ i g = (if ip t.castSucc = i then (1 : ℝ) else 0) -
        (if ip t.succ = i then (1 : ℝ) else 0)) := by
    intro i g
    constructor
    · intro hno
      dsimp [Δ]
      refine Finset.sum_eq_zero fun t _ => ?_
      simp [hno t]
    · intro t hgt
      dsimp [Δ]
      rw [Finset.sum_eq_single t]
      · simp [hgt]
      · intro s _ hs
        have hgs : gp s ≠ g := fun h => hs (gp.injective (h.trans hgt.symm))
        simp [hgs]
      · intro h; exact absurd (Finset.mem_univ t) h
  have hrow_sum : ∀ i : Fin n, ∑ g : Fin m, Δ i g =
      (if ip 0 = i then (1 : ℝ) else 0) - (if ip (Fin.last k) = i then (1 : ℝ) else 0) := by
    intro i
    change (∑ g : Fin m, ∑ t : Fin k,
      ((if ip t.castSucc = i ∧ gp t = g then (1 : ℝ) else 0) -
        (if ip t.succ = i ∧ gp t = g then (1 : ℝ) else 0))) = _
    rw [Finset.sum_comm]
    have hterm : ∀ t : Fin k,
        (∑ g : Fin m, ((if ip t.castSucc = i ∧ gp t = g then (1 : ℝ) else 0) -
          (if ip t.succ = i ∧ gp t = g then (1 : ℝ) else 0))) =
        (if ip t.castSucc = i then (1 : ℝ) else 0) - (if ip t.succ = i then (1 : ℝ) else 0) := by
      intro t
      rw [Finset.sum_sub_distrib]
      have s1 : (∑ g : Fin m, if ip t.castSucc = i ∧ gp t = g then (1 : ℝ) else 0) =
          if ip t.castSucc = i then 1 else 0 := by
        by_cases hi : ip t.castSucc = i <;> simp [hi]
      have s2 : (∑ g : Fin m, if ip t.succ = i ∧ gp t = g then (1 : ℝ) else 0) =
          if ip t.succ = i then 1 else 0 := by
        by_cases hi : ip t.succ = i <;> simp [hi]
      rw [s1, s2]
    simp_rw [hterm]
    exact sum_fin_sub_succ (fun s => if ip s = i then (1 : ℝ) else 0)
  have h0_ne_last : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro heq
    have hv : (0 : ℕ) = k := congrArg Fin.val heq
    omega
  have hip_ne : ip 0 ≠ ip (Fin.last k) := fun h => h0_ne_last (ip.injective h)
  refine ⟨{
    Δ := Δ
    S_end := {ip 0, ip (Fin.last k)}
    exists_nonzero := by
      let t0 : Fin k := ⟨0, by omega⟩
      refine ⟨ip t0.castSucc, gp t0, Or.inl ?_⟩
      rw [(hΔ_eval (ip t0.castSucc) (gp t0)).2 t0 rfl]
      have hne : ip t0.succ ≠ ip t0.castSucc := fun h => by
        have := ip.injective h
        have hv := congrArg Fin.val this
        simp at hv
      simp [hne]
    vals := by
      intro i g
      by_cases hex : ∃ t, gp t = g
      · rcases hex with ⟨t, hgt⟩
        rw [(hΔ_eval i g).2 t hgt]
        have hne : ip t.succ ≠ ip t.castSucc := fun h => by
          have hv := congrArg Fin.val (ip.injective h)
          simp at hv
        by_cases h1 : ip t.castSucc = i
        · subst h1; simp [hne]
        · by_cases h2 : ip t.succ = i <;> simp [h1, h2]
      · push_neg at hex
        rw [(hΔ_eval i g).1 hex]
        exact Or.inr (Or.inl rfl)
    supp_frac := by
      intro i g hnz
      by_cases hex : ∃ t, gp t = g
      · rcases hex with ⟨t, hgt⟩
        rw [(hΔ_eval i g).2 t hgt] at hnz
        by_cases h1 : ip t.castSucc = i
        · subst h1; subst hgt; exact hf1 t
        · by_cases h2 : ip t.succ = i
          · subst h2; subst hgt; exact hf2 t
          · simp [h1, h2] at hnz
      · push_neg at hex
        exact absurd ((hΔ_eval i g).1 hex) hnz
    col_zero := by
      intro g
      dsimp [Δ]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [Finset.sum_sub_distrib]
      have s1 : (∑ x : Fin n, if ip t.castSucc = x ∧ gp t = g then (1 : ℝ) else 0) =
          if gp t = g then 1 else 0 := by
        split_ifs with hg <;> simp [hg]
      have s2 : (∑ x : Fin n, if ip t.succ = x ∧ gp t = g then (1 : ℝ) else 0) =
          if gp t = g then 1 else 0 := by
        split_ifs with hg <;> simp [hg]
      rw [s1, s2, sub_self]
    row_out := by
      intro i hi
      rw [hrow_sum i]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      have h1 : ip 0 ≠ i := Ne.symm hi.1
      have h2 : ip (Fin.last k) ≠ i := Ne.symm hi.2
      simp [h1, h2]
    row_in := by
      intro i hi
      rw [hrow_sum i]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · refine ⟨Or.inl ?_, hra⟩
        simp [hip_ne.symm]
      · refine ⟨Or.inr ?_, hrb⟩
        simp [hip_ne]
  }⟩

lemma cycle_of_head_chord {n m L : ℕ} (hL : 1 ≤ L) {x : Fin n → Fin m → ℝ}
    {w : Fin (L + 1) ↪ BVert n m} (hw : IsFracWalk x w)
    {idx : Fin (L + 1)} (hidx : 2 ≤ idx.val) (hadj : FracAdj x (w idx) (w 0)) :
    Nonempty (ValidDir n m x) := by
  have hidx_lt := idx.isLt
  have hpar := walk_isLeft_parity hw idx
  have hflip := fracAdj_isLeft_iff hadj
  have hnot_even : ¬ Even idx.val := by
    intro hev
    have : (w idx).isLeft ↔ (w 0).isLeft := by tauto
    tauto
  have hodd : Odd idx.val := Nat.not_even_iff_odd.mp hnot_even
  rcases hodd with ⟨k', hk'⟩
  have hk'_ge1 : 1 ≤ k' := by omega
  let k : ℕ := k' + 1
  have hk2 : 2 ≤ k := by omega
  have hidx_eq : idx.val + 1 = 2 * k := by omega
  cases hw0 : w 0 with
  | inl i₀ =>
    have hleft : ∀ t : Fin k, ∃ i : Fin n, w ⟨2 * t.val, by have := t.isLt; omega⟩ = Sum.inl i := by
      intro t
      have ht := t.isLt
      have hp := walk_isLeft_parity hw ⟨2 * t.val, by omega⟩
      rw [hw0] at hp
      have hev_t : Even (2 * t.val) := ⟨t.val, by ring⟩
      rcases hv : w ⟨2 * t.val, by omega⟩ with i | g
      · exact ⟨i, rfl⟩
      · rw [hv] at hp; simp [hev_t] at hp
    have hright : ∀ t : Fin k, ∃ g : Fin m, w ⟨2 * t.val + 1, by have := t.isLt; omega⟩ = Sum.inr g := by
      intro t
      have ht := t.isLt
      have hp := walk_isLeft_parity hw ⟨2 * t.val + 1, by omega⟩
      rw [hw0] at hp
      have hodd_t : ¬ Even (2 * t.val + 1) := by rintro ⟨r, hr⟩; omega
      rcases hv : w ⟨2 * t.val + 1, by omega⟩ with i | g
      · rw [hv] at hp; simp [hodd_t] at hp
      · exact ⟨g, rfl⟩
    choose icf hicf using hleft
    choose gcf hgcf using hright
    let ic : Fin k ↪ Fin n :=
      ⟨icf, fun a b hab => by
        have ha := hicf a; have hb := hicf b
        rw [hab] at ha
        have hv := congrArg Fin.val (w.injective (ha.trans hb.symm))
        ext; dsimp at hv; omega⟩
    let gc : Fin k ↪ Fin m :=
      ⟨gcf, fun a b hab => by
        have ha := hgcf a; have hb := hgcf b
        rw [hab] at ha
        have hv := congrArg Fin.val (w.injective (ha.trans hb.symm))
        ext; dsimp at hv; omega⟩
    refine validDir_of_even_cycle hk2 ic gc ?_ ?_
    · intro t
      have ht := t.isLt
      have hs : FracAdj x (w ⟨2 * t.val, by omega⟩) (w ⟨2 * t.val + 1, by omega⟩) :=
        hw ⟨2 * t.val, by omega⟩
      rw [hicf t, hgcf t] at hs
      exact hs
    · intro t
      have ht := t.isLt
      by_cases hlast : t.val + 1 = k
      · have hmod : (t.val + 1) % k = 0 := by rw [hlast, Nat.mod_self]
        have hic0 : ic ⟨(t.val + 1) % k, Nat.mod_lt _ (by omega)⟩ = ic ⟨0, by omega⟩ := by
          ext; simp [hmod]
        rw [hic0]
        have hidx_fin : (⟨2 * t.val + 1, by omega⟩ : Fin (L + 1)) = idx := by ext; dsimp; omega
        have hadj' := hadj
        rw [← hidx_fin, hgcf t] at hadj'
        have h0_eq : w ⟨2 * (0 : Fin k).val, by omega⟩ = w 0 := by congr 1
        have hic_zero : w 0 = Sum.inl (ic ⟨0, by omega⟩) := by
          rw [← h0_eq]; exact hicf ⟨0, by omega⟩
        rw [hic_zero] at hadj'
        exact hadj'
      · have hlt : t.val + 1 < k := by omega
        have hmod : (t.val + 1) % k = t.val + 1 := Nat.mod_eq_of_lt hlt
        let s_step : Fin L := ⟨2 * t.val + 1, by omega⟩
        have hs : FracAdj x (w s_step.castSucc) (w s_step.succ) := hw s_step
        have hc1 : s_step.castSucc = ⟨2 * t.val + 1, by omega⟩ := rfl
        have hc2 : s_step.succ = ⟨2 * (t.val + 1), by omega⟩ := by ext; simp [s_step]; omega
        rw [hc1, hc2, hgcf t, hicf ⟨t.val + 1, hlt⟩] at hs
        have hic_eq : ic ⟨(t.val + 1) % k, Nat.mod_lt _ (by omega)⟩ = ic ⟨t.val + 1, hlt⟩ := by
          congr 1; ext; exact hmod
        rw [hic_eq]
        exact hs
  | inr g₀ =>
    have hright : ∀ t : Fin k, ∃ g : Fin m, w ⟨2 * t.val, by have := t.isLt; omega⟩ = Sum.inr g := by
      intro t
      have ht := t.isLt
      have hp := walk_isLeft_parity hw ⟨2 * t.val, by omega⟩
      rw [hw0] at hp
      have hev_t : Even (2 * t.val) := ⟨t.val, by ring⟩
      rcases hv : w ⟨2 * t.val, by omega⟩ with i | g
      · rw [hv] at hp; simp [hev_t] at hp
      · exact ⟨g, rfl⟩
    have hleft : ∀ t : Fin k, ∃ i : Fin n, w ⟨2 * t.val + 1, by have := t.isLt; omega⟩ = Sum.inl i := by
      intro t
      have ht := t.isLt
      have hp := walk_isLeft_parity hw ⟨2 * t.val + 1, by omega⟩
      rw [hw0] at hp
      have hodd_t : ¬ Even (2 * t.val + 1) := by rintro ⟨r, hr⟩; omega
      rcases hv : w ⟨2 * t.val + 1, by omega⟩ with i | g
      · exact ⟨i, rfl⟩
      · rw [hv] at hp; simp [hodd_t] at hp
    choose gcf hgcf using hright
    choose icf hicf using hleft
    let ic : Fin k ↪ Fin n :=
      ⟨icf, fun a b hab => by
        have ha := hicf a; have hb := hicf b
        rw [hab] at ha
        have hv := congrArg Fin.val (w.injective (ha.trans hb.symm))
        ext; dsimp at hv; omega⟩
    let gc : Fin k ↪ Fin m :=
      ⟨fun t => gcf ⟨(t.val + 1) % k, Nat.mod_lt _ (by omega)⟩, fun a b hab => by
        dsimp at hab
        have ha := hgcf ⟨(a.val + 1) % k, Nat.mod_lt _ (by omega)⟩
        have hb := hgcf ⟨(b.val + 1) % k, Nat.mod_lt _ (by omega)⟩
        rw [hab] at ha
        have hv := congrArg Fin.val (w.injective (ha.trans hb.symm))
        dsimp at hv
        have hm : (a.val + 1) % k = (b.val + 1) % k := by omega
        have ha_lt := a.isLt; have hb_lt := b.isLt
        ext
        by_cases h1 : a.val + 1 = k <;> by_cases h2 : b.val + 1 = k
        · omega
        · rw [h1, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hm; omega
        · rw [h2, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hm; omega
        · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm; omega⟩
    refine validDir_of_even_cycle hk2 ic gc ?_ ?_
    · intro t
      have ht := t.isLt
      by_cases hlast : t.val + 1 = k
      · have hmod : (t.val + 1) % k = 0 := by rw [hlast, Nat.mod_self]
        have hgc_eq : gc t = gcf ⟨0, by omega⟩ := by
          show gcf ⟨(t.val + 1) % k, _⟩ = gcf ⟨0, _⟩
          congr 1; ext; exact hmod
        rw [hgc_eq]
        have hidx_fin : (⟨2 * t.val + 1, by omega⟩ : Fin (L + 1)) = idx := by ext; dsimp; omega
        have hadj' := hadj
        rw [← hidx_fin, hicf t] at hadj'
        have h0_eq : w ⟨2 * (0 : Fin k).val, by omega⟩ = w 0 := by congr 1
        have hgc_zero : w 0 = Sum.inr (gcf ⟨0, by omega⟩) := by
          rw [← h0_eq]; exact hgcf ⟨0, by omega⟩
        rw [hgc_zero] at hadj'
        exact hadj'
      · have hlt : t.val + 1 < k := by omega
        have hmod : (t.val + 1) % k = t.val + 1 := Nat.mod_eq_of_lt hlt
        let s_step : Fin L := ⟨2 * t.val + 1, by omega⟩
        have hs : FracAdj x (w s_step.castSucc) (w s_step.succ) := hw s_step
        have hc1 : s_step.castSucc = ⟨2 * t.val + 1, by omega⟩ := rfl
        have hc2 : s_step.succ = ⟨2 * (t.val + 1), by omega⟩ := by ext; simp [s_step]; omega
        rw [hc1, hc2, hicf t, hgcf ⟨t.val + 1, hlt⟩] at hs
        have hgc_eq : gc t = gcf ⟨t.val + 1, hlt⟩ := by
          show gcf ⟨(t.val + 1) % k, _⟩ = gcf ⟨t.val + 1, hlt⟩
          congr 1; ext; exact hmod
        rw [hgc_eq]
        exact hs
    · intro t
      let t' : Fin k := ⟨(t.val + 1) % k, Nat.mod_lt _ (by omega)⟩
      have ht' := t'.isLt
      have hs : FracAdj x (w ⟨2 * t'.val, by omega⟩) (w ⟨2 * t'.val + 1, by omega⟩) :=
        hw ⟨2 * t'.val, by omega⟩
      rw [hgcf t', hicf t'] at hs
      exact hs

lemma exists_validDir {n m : ℕ} {x : Fin n → Fin m → ℝ} (hx : x ∈ Pbal n m)
    (hfrac : ∃ i₀ g₀, IsFracEntry x i₀ g₀) :
    Nonempty (ValidDir n m x) := by
  classical
  rcases hfrac with ⟨i₀, g₀, hi₀g₀⟩
  have hcard_vert : Fintype.card (BVert n m) = n + m := by simp [BVert]
  have hex_len : ∀ L : ℕ, (∃ w : Fin (L + 1) ↪ BVert n m, IsFracWalk x w) → L + 1 ≤ n + m := by
    rintro L ⟨w, _⟩
    have := Fintype.card_le_of_injective w w.injective
    simpa [hcard_vert] using this
  let S_len : Finset ℕ := (Finset.range (n + m)).filter
    (fun L => ∃ w : Fin (L + 1) ↪ BVert n m, IsFracWalk x w)
  have h1_mem : 1 ∈ S_len := by
    rw [Finset.mem_filter, Finset.mem_range]
    have hw1 : ∃ w : Fin 2 ↪ BVert n m, IsFracWalk x w := by
      refine ⟨⟨![Sum.inl i₀, Sum.inr g₀], ?_⟩, ?_⟩
      · intro a b hab
        fin_cases a <;> fin_cases b <;> simp at hab ⊢
      · intro s
        fin_cases s
        exact hi₀g₀
    have hle := hex_len 1 hw1
    exact ⟨by omega, hw1⟩
  let L := S_len.max' ⟨1, h1_mem⟩
  have hL_mem : L ∈ S_len := Finset.max'_mem S_len ⟨1, h1_mem⟩
  have hL_ge1 : 1 ≤ L := Finset.le_max' S_len 1 h1_mem
  rw [Finset.mem_filter] at hL_mem
  rcases hL_mem.2 with ⟨w, hw⟩
  have hmax : ∀ L' : ℕ, (∃ w' : Fin (L' + 1) ↪ BVert n m, IsFracWalk x w') → L' ≤ L := by
    intro L' hex'
    have hbnd := hex_len L' hex'
    refine Finset.le_max' S_len L' ?_
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hex'⟩
  have hno_ext : ∀ (w' : Fin (L + 1) ↪ BVert n m), IsFracWalk x w' →
      ∀ v : BVert n m, FracAdj x v (w' 0) → ∃ idx : Fin (L + 1), w' idx = v := by
    intro w' hw' v hv
    by_contra hnot
    push_neg at hnot
    let w_ext : Fin (L + 2) ↪ BVert n m :=
      ⟨Fin.cons v w', by
        intro a b hab
        rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩ <;>
          rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
        · rfl
        · simp only [Fin.cons_zero, Fin.cons_succ] at hab
          exact absurd hab.symm (hnot b')
        · simp only [Fin.cons_succ, Fin.cons_zero] at hab
          exact absurd hab (hnot a')
        · simp only [Fin.cons_succ] at hab
          exact congrArg Fin.succ (w'.injective hab)⟩
    have hw_ext : IsFracWalk x w_ext := by
      intro s
      rcases Fin.eq_zero_or_eq_succ s with rfl | ⟨s', rfl⟩
      · have h1 : w_ext (0 : Fin (L + 1)).castSucc = v := rfl
        have h2 : w_ext (0 : Fin (L + 1)).succ = w' 0 := rfl
        rw [h1, h2]
        exact hv
      · have h1 : w_ext s'.succ.castSucc = w' s'.castSucc := by
          have hcs : s'.succ.castSucc = s'.castSucc.succ := by ext; simp
          rw [hcs]
          rfl
        have h2 : w_ext s'.succ.succ = w' s'.succ := rfl
        rw [h1, h2]
        exact hw' s'
    have := hmax (L + 1) ⟨w_ext, hw_ext⟩
    omega
  by_cases hchord1 : ∃ v : BVert n m, FracAdj x v (w 0) ∧ v ≠ w ⟨1, by omega⟩
  · rcases hchord1 with ⟨v, hv_adj, hv_ne⟩
    rcases hno_ext w hw v hv_adj with ⟨idx, rfl⟩
    have hidx0 : idx ≠ 0 := fun h => by subst h; exact fracAdj_irrefl _ hv_adj
    have hidx1 : idx ≠ ⟨1, by omega⟩ := fun h => hv_ne (congrArg w h)
    have hidx2 : 2 ≤ idx.val := by
      have hv0 : idx.val ≠ 0 := fun h => hidx0 (Fin.ext h)
      have hv1 : idx.val ≠ 1 := fun h => hidx1 (Fin.ext h)
      omega
    exact cycle_of_head_chord hL_ge1 hw hidx2 hv_adj
  · let w_rev := Fin.revPerm.toEmbedding.trans w
    have hw_rev : IsFracWalk x w_rev := isFracWalk_rev hw
    by_cases hchord2 : ∃ v : BVert n m, FracAdj x v (w_rev 0) ∧ v ≠ w_rev ⟨1, by omega⟩
    · rcases hchord2 with ⟨v, hv_adj, hv_ne⟩
      rcases hno_ext w_rev hw_rev v hv_adj with ⟨idx, rfl⟩
      have hidx0 : idx ≠ 0 := fun h => by subst h; exact fracAdj_irrefl _ hv_adj
      have hidx1 : idx ≠ ⟨1, by omega⟩ := fun h => hv_ne (congrArg w_rev h)
      have hidx2 : 2 ≤ idx.val := by
        have hv0 : idx.val ≠ 0 := fun h => hidx0 (Fin.ext h)
        have hv1 : idx.val ≠ 1 := fun h => hidx1 (Fin.ext h)
        omega
      exact cycle_of_head_chord hL_ge1 hw_rev hidx2 hv_adj
    · push_neg at hchord1 hchord2
      have hendpt : ∀ (w' : Fin (L + 1) ↪ BVert n m), IsFracWalk x w' →
          (∀ v, FracAdj x v (w' 0) → v = w' ⟨1, by omega⟩) →
          ∃ i : Fin n, w' 0 = Sum.inl i ∧ IsFracRow x i := by
        intro w' hw' huniq
        have hs0 : FracAdj x (w' 0) (w' ⟨1, by omega⟩) := hw' ⟨0, by omega⟩
        rcases hv0 : w' 0 with i | g
        · rw [hv0] at hs0
          rcases hv1 : w' ⟨1, by omega⟩ with i' | g₀
          · rw [hv1] at hs0; simp [FracAdj] at hs0
          · rw [hv1] at hs0
            refine ⟨i, rfl, ?_⟩
            by_contra hint
            rcases no_unique_frac_int_row hx hint hs0 with ⟨g₁, hg₁_ne, hg₁_frac⟩
            have hadj1 : FracAdj x (Sum.inr g₁) (w' 0) := by rw [hv0]; exact hg₁_frac
            have heq := huniq (Sum.inr g₁) hadj1
            rw [hv1] at heq
            exact hg₁_ne (Sum.inr.inj heq)
        · rw [hv0] at hs0
          rcases hv1 : w' ⟨1, by omega⟩ with i₀' | g'
          · rw [hv1] at hs0
            rcases no_unique_frac_col hx hs0 with ⟨i₁, hi₁_ne, hi₁_frac⟩
            have hadj1 : FracAdj x (Sum.inl i₁) (w' 0) := by rw [hv0]; exact hi₁_frac
            have heq := huniq (Sum.inl i₁) hadj1
            rw [hv1] at heq
            exact absurd (Sum.inl.inj heq) hi₁_ne
          · rw [hv1] at hs0; simp [FracAdj] at hs0
      rcases hendpt w hw hchord1 with ⟨i_a, hw0_eq, hra⟩
      rcases hendpt w_rev hw_rev hchord2 with ⟨i_b, hwlast_eq, hrb⟩
      have hw_last : w (Fin.last L) = Sum.inl i_b := by
        have hrev0 : w_rev 0 = w (Fin.last L) := by
          change w (Fin.rev 0) = w (Fin.last L)
          rw [Fin.rev_zero]
        rwa [hrev0] at hwlast_eq
      have hparL := walk_isLeft_parity hw (Fin.last L)
      rw [hw_last, hw0_eq] at hparL
      have hevenL : Even L := by simpa using hparL
      rcases hevenL with ⟨k, hkL⟩
      have hk_ge1 : 1 ≤ k := by omega
      have hL_eq : L = 2 * k := by omega
      have hleft : ∀ t : Fin (k + 1), ∃ i : Fin n, w ⟨2 * t.val, by have := t.isLt; omega⟩ = Sum.inl i := by
        intro t
        have ht := t.isLt
        have hp := walk_isLeft_parity hw ⟨2 * t.val, by omega⟩
        rw [hw0_eq] at hp
        have hev_t : Even (2 * t.val) := ⟨t.val, by ring⟩
        rcases hv : w ⟨2 * t.val, by omega⟩ with i | g
        · exact ⟨i, rfl⟩
        · rw [hv] at hp; simp [hev_t] at hp
      have hright : ∀ t : Fin k, ∃ g : Fin m, w ⟨2 * t.val + 1, by have := t.isLt; omega⟩ = Sum.inr g := by
        intro t
        have ht := t.isLt
        have hp := walk_isLeft_parity hw ⟨2 * t.val + 1, by omega⟩
        rw [hw0_eq] at hp
        have hodd_t : ¬ Even (2 * t.val + 1) := by rintro ⟨r, hr⟩; omega
        rcases hv : w ⟨2 * t.val + 1, by omega⟩ with i | g
        · rw [hv] at hp; simp [hodd_t] at hp
        · exact ⟨g, rfl⟩
      choose ipf hipf using hleft
      choose gpf hgpf using hright
      let ip : Fin (k + 1) ↪ Fin n :=
        ⟨ipf, fun a b hab => by
          have ha := hipf a; have hb := hipf b
          rw [hab] at ha
          have hv := congrArg Fin.val (w.injective (ha.trans hb.symm))
          ext; dsimp at hv; omega⟩
      let gp : Fin k ↪ Fin m :=
        ⟨gpf, fun a b hab => by
          have ha := hgpf a; have hb := hgpf b
          rw [hab] at ha
          have hv := congrArg Fin.val (w.injective (ha.trans hb.symm))
          ext; dsimp at hv; omega⟩
      have hip0 : ip 0 = i_a := by
        have h0 := hipf 0
        have heq0 : (⟨2 * (0 : Fin (k + 1)).val, by omega⟩ : Fin (L + 1)) = 0 := by ext; rfl
        rw [heq0, hw0_eq] at h0
        exact Sum.inl.inj h0.symm
      have hiplast : ip (Fin.last k) = i_b := by
        have hl := hipf (Fin.last k)
        have heql : (⟨2 * (Fin.last k).val, by simp; omega⟩ : Fin (L + 1)) = Fin.last L := by
          ext; simp [hL_eq]
        rw [heql, hw_last] at hl
        exact Sum.inl.inj hl.symm
      refine validDir_of_frac_path hk_ge1 ip gp ?_ ?_ (hip0 ▸ hra) (hiplast ▸ hrb)
      · intro t
        have ht := t.isLt
        have hs : FracAdj x (w ⟨2 * t.val, by omega⟩) (w ⟨2 * t.val + 1, by omega⟩) :=
          hw ⟨2 * t.val, by omega⟩
        have hc : (⟨2 * t.castSucc.val, by simp; omega⟩ : Fin (L + 1)) = ⟨2 * t.val, by omega⟩ := rfl
        rw [← hc, hipf t.castSucc, hgpf t] at hs
        exact hs
      · intro t
        have ht := t.isLt
        let s_step : Fin L := ⟨2 * t.val + 1, by omega⟩
        have hs : FracAdj x (w s_step.castSucc) (w s_step.succ) := hw s_step
        have hc1 : s_step.castSucc = ⟨2 * t.val + 1, by omega⟩ := rfl
        have hc2 : s_step.succ = ⟨2 * t.succ.val, by simp; omega⟩ := by ext; simp [s_step]; omega
        rw [hc1, hc2, hgpf t, hipf t.succ] at hs
        exact hs

def neg_validDir {n m : ℕ} {x : Fin n → Fin m → ℝ} (d : ValidDir n m x) :
    ValidDir n m x where
  Δ := fun i g => - d.Δ i g
  S_end := d.S_end
  exists_nonzero := by
    rcases d.exists_nonzero with ⟨i, g, h | h⟩
    · exact ⟨i, g, Or.inr (by linarith)⟩
    · exact ⟨i, g, Or.inl (by linarith)⟩
  vals := by
    intro i g
    rcases d.vals i g with h | h | h
    · exact Or.inr (Or.inr (by linarith))
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inl (by linarith)
  supp_frac := by
    intro i g hnz
    exact d.supp_frac i g (by intro h0; apply hnz; linarith)
  col_zero := by intro g; simp [d.col_zero g]
  row_out := by intro i hi; simp [d.row_out i hi]
  row_in := by
    intro i hi
    rcases d.row_in i hi with ⟨h1 | h1, h2⟩
    · exact ⟨Or.inr (by simp [h1]), h2⟩
    · exact ⟨Or.inl (by simp [h1]), h2⟩

lemma round_step_Pbal {n m : ℕ} (c : Fin n → Fin m → ℝ) {x : Fin n → Fin m → ℝ}
    (hx : x ∈ Pbal n m) (hfrac : ∃ i g, IsFracEntry x i g) :
    ∃ x' ∈ Pbal n m,
      (∑ i, ∑ g, c i g * x i g ≤ ∑ i, ∑ g, c i g * x' i g) ∧
      fracPot x' < fracPot x := by
  classical
  rcases exists_validDir hx hfrac with ⟨d₀⟩
  let d : ValidDir n m x :=
    if 0 ≤ ∑ i, ∑ g, c i g * d₀.Δ i g then d₀ else neg_validDir d₀
  have hd_obj : 0 ≤ ∑ i, ∑ g, c i g * d.Δ i g := by
    dsimp [d]
    split_ifs with h
    · exact h
    · change 0 ≤ ∑ i, ∑ g, c i g * (- d₀.Δ i g)
      have : (∑ i, ∑ g, c i g * (- d₀.Δ i g)) = - (∑ i, ∑ g, c i g * d₀.Δ i g) := by
        simp [mul_neg, Finset.sum_neg_distrib]
      linarith
  let E_neg : Finset (Fin n × Fin m) := Finset.univ.filter (fun ig => d.Δ ig.1 ig.2 = -1)
  let E_pos : Finset (Fin n × Fin m) := Finset.univ.filter (fun ig => d.Δ ig.1 ig.2 = 1)
  let R_neg : Finset (Fin n) := d.S_end.filter (fun i => ∑ g, d.Δ i g = -1)
  let R_pos : Finset (Fin n) := d.S_end.filter (fun i => ∑ g, d.Δ i g = 1)
  let cand : Finset ℝ :=
    (E_neg.image (fun ig => x ig.1 ig.2)) ∪
    (E_pos.image (fun ig => 1 - x ig.1 ig.2)) ∪
    (R_neg.image (fun i => (∑ g, x i g) - ((m / n : ℕ) : ℝ))) ∪
    (R_pos.image (fun i => ((m / n : ℕ) : ℝ) + 1 - (∑ g, x i g)))
  have hcand_ne : cand.Nonempty := by
    rcases d.exists_nonzero with ⟨i₀, g₀, h1 | hm1⟩
    · refine ⟨1 - x i₀ g₀, ?_⟩
      simp only [cand, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inr ⟨(i₀, g₀), by simp [E_pos, h1], rfl⟩))
    · refine ⟨x i₀ g₀, ?_⟩
      simp only [cand, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inl ⟨(i₀, g₀), by simp [E_neg, hm1], rfl⟩))
  have hcand_pos : ∀ v ∈ cand, 0 < v := by
    intro v hv
    simp only [cand, Finset.mem_union, Finset.mem_image] at hv
    rcases hv with ((⟨ig, hig, rfl⟩ | ⟨ig, hig, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
    · simp only [E_neg, Finset.mem_filter, Finset.mem_univ, true_and] at hig
      exact (d.supp_frac ig.1 ig.2 (by linarith)).1
    · simp only [E_pos, Finset.mem_filter, Finset.mem_univ, true_and] at hig
      have := (d.supp_frac ig.1 ig.2 (by linarith)).2
      linarith
    · simp only [R_neg, Finset.mem_filter] at hi
      have := (d.row_in i hi.1).2.1
      linarith
    · simp only [R_pos, Finset.mem_filter] at hi
      have := (d.row_in i hi.1).2.2
      linarith
  let δ : ℝ := cand.min' hcand_ne
  have hδ_pos : 0 < δ := hcand_pos δ (Finset.min'_mem cand hcand_ne)
  let x' : Fin n → Fin m → ℝ := fun i g => x i g + δ * d.Δ i g
  have hx'_bounds : ∀ i g, 0 ≤ x' i g ∧ x' i g ≤ 1 := by
    intro i g
    dsimp [x']
    rcases d.vals i g with hm1 | h0 | h1
    · have hle : δ ≤ x i g := by
        refine Finset.min'_le cand (x i g) ?_
        simp only [cand, Finset.mem_union, Finset.mem_image]
        exact Or.inl (Or.inl (Or.inl ⟨(i, g), by simp [E_neg, hm1], rfl⟩))
      have hu := entry_le_one_of_mem_Pbal hx i g
      rw [hm1]; constructor <;> linarith
    · rw [h0, mul_zero, add_zero]
      exact ⟨hx.1 i g, entry_le_one_of_mem_Pbal hx i g⟩
    · have hle : δ ≤ 1 - x i g := by
        refine Finset.min'_le cand (1 - x i g) ?_
        simp only [cand, Finset.mem_union, Finset.mem_image]
        exact Or.inl (Or.inl (Or.inr ⟨(i, g), by simp [E_pos, h1], rfl⟩))
      have hl := hx.1 i g
      rw [h1]; constructor <;> linarith
  have hx'_row : ∀ i, ∑ g, x' i g = (∑ g, x i g) + δ * (∑ g, d.Δ i g) := by
    intro i
    dsimp [x']
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hx'_Pbal : x' ∈ Pbal n m := by
    refine ⟨fun i g => (hx'_bounds i g).1, ?_, ?_⟩
    · intro g
      dsimp [x']
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, d.col_zero g, mul_zero, add_zero]
      exact hx.2.1 g
    · intro i
      rw [hx'_row i]
      by_cases hi : i ∈ d.S_end
      · rcases d.row_in i hi with ⟨h1 | hm1, hfr⟩
        · have hle : δ ≤ ((m / n : ℕ) : ℝ) + 1 - ∑ g, x i g := by
            refine Finset.min'_le cand _ ?_
            simp only [cand, Finset.mem_union, Finset.mem_image]
            exact Or.inr ⟨i, by simp [R_pos, hi, h1], rfl⟩
          rw [h1]; constructor <;> linarith [hfr.1]
        · have hle : δ ≤ (∑ g, x i g) - ((m / n : ℕ) : ℝ) := by
            refine Finset.min'_le cand _ ?_
            simp only [cand, Finset.mem_union, Finset.mem_image]
            exact Or.inl (Or.inr ⟨i, by simp [R_neg, hi, hm1], rfl⟩)
          rw [hm1]; constructor <;> linarith [hfr.2]
      · rw [d.row_out i hi, mul_zero, add_zero]
        exact hx.2.2 i
  have hobj : ∑ i, ∑ g, c i g * x i g ≤ ∑ i, ∑ g, c i g * x' i g := by
    have hexp : (∑ i, ∑ g, c i g * x' i g) =
        (∑ i, ∑ g, c i g * x i g) + δ * (∑ i, ∑ g, c i g * d.Δ i g) := by
      dsimp [x']
      simp_rw [mul_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => by ring
    rw [hexp]
    nlinarith
  have hsub_entry : fracEntrySet x' ⊆ fracEntrySet x := by
    intro ig hig
    simp only [fracEntrySet, Finset.mem_filter, Finset.mem_univ, true_and] at hig ⊢
    by_contra hnot
    have h0 : d.Δ ig.1 ig.2 = 0 := by
      by_contra hnz; exact hnot (d.supp_frac ig.1 ig.2 hnz)
    have heq : x' ig.1 ig.2 = x ig.1 ig.2 := by dsimp [x']; rw [h0]; ring
    unfold IsFracEntry at hig hnot
    rw [heq] at hig
    exact hnot hig
  have hsub_row : fracRowSet x' ⊆ fracRowSet x := by
    intro i hi
    simp only [fracRowSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_contra hnot
    have hnotS : i ∉ d.S_end := fun hs => hnot (d.row_in i hs).2
    have heq : ∑ g, x' i g = ∑ g, x i g := by
      rw [hx'_row i, d.row_out i hnotS, mul_zero, add_zero]
    unfold IsFracRow at hi hnot
    rw [heq] at hi
    exact hnot hi
  have hmin_mem : δ ∈ cand := Finset.min'_mem cand hcand_ne
  simp only [cand, Finset.mem_union, Finset.mem_image] at hmin_mem
  have hpot_lt : fracPot x' < fracPot x := by
    unfold fracPot
    rcases hmin_mem with ((⟨ig, hig, hδ_eq⟩ | ⟨ig, hig, hδ_eq⟩) | ⟨i, hi, hδ_eq⟩) | ⟨i, hi, hδ_eq⟩
    · simp only [E_neg, Finset.mem_filter, Finset.mem_univ, true_and] at hig
      have h_in : ig ∈ fracEntrySet x :=
        mem_fracEntrySet.mpr (d.supp_frac ig.1 ig.2 (by linarith))
      have h_out : ig ∉ fracEntrySet x' := by
        rw [mem_fracEntrySet, IsFracEntry]
        intro h
        have hx'0 : x' ig.1 ig.2 = 0 := by dsimp [x']; rw [hig, ← hδ_eq]; ring
        linarith [h.1]
      have hlt_e : (fracEntrySet x').card < (fracEntrySet x).card :=
        Finset.card_lt_card ⟨hsub_entry, fun h => h_out (h h_in)⟩
      have hle_r : (fracRowSet x').card ≤ (fracRowSet x).card := Finset.card_le_card hsub_row
      omega
    · simp only [E_pos, Finset.mem_filter, Finset.mem_univ, true_and] at hig
      have h_in : ig ∈ fracEntrySet x :=
        mem_fracEntrySet.mpr (d.supp_frac ig.1 ig.2 (by linarith))
      have h_out : ig ∉ fracEntrySet x' := by
        rw [mem_fracEntrySet, IsFracEntry]
        intro h
        have hx'1 : x' ig.1 ig.2 = 1 := by dsimp [x']; rw [hig, ← hδ_eq]; ring
        linarith [h.2]
      have hlt_e : (fracEntrySet x').card < (fracEntrySet x).card :=
        Finset.card_lt_card ⟨hsub_entry, fun h => h_out (h h_in)⟩
      have hle_r : (fracRowSet x').card ≤ (fracRowSet x).card := Finset.card_le_card hsub_row
      omega
    · simp only [R_neg, Finset.mem_filter] at hi
      have h_in : i ∈ fracRowSet x := mem_fracRowSet.mpr (d.row_in i hi.1).2
      have h_out : i ∉ fracRowSet x' := by
        rw [mem_fracRowSet, IsFracRow]
        intro h
        have hr0 : ∑ g, x' i g = ((m / n : ℕ) : ℝ) := by
          rw [hx'_row i, hi.2, ← hδ_eq]; ring
        linarith [h.1]
      have hle_e : (fracEntrySet x').card ≤ (fracEntrySet x).card := Finset.card_le_card hsub_entry
      have hlt_r : (fracRowSet x').card < (fracRowSet x).card :=
        Finset.card_lt_card ⟨hsub_row, fun h => h_out (h h_in)⟩
      omega
    · simp only [R_pos, Finset.mem_filter] at hi
      have h_in : i ∈ fracRowSet x := mem_fracRowSet.mpr (d.row_in i hi.1).2
      have h_out : i ∉ fracRowSet x' := by
        rw [mem_fracRowSet, IsFracRow]
        intro h
        have hr1 : ∑ g, x' i g = ((m / n : ℕ) : ℝ) + 1 := by
          rw [hx'_row i, hi.2, ← hδ_eq]; ring
        linarith [h.2]
      have hle_e : (fracEntrySet x').card ≤ (fracEntrySet x).card := Finset.card_le_card hsub_entry
      have hlt_r : (fracRowSet x').card < (fracRowSet x).card :=
        Finset.card_lt_card ⟨hsub_row, fun h => h_out (h h_in)⟩
      omega
  exact ⟨x', hx'_Pbal, hobj, hpot_lt⟩

lemma exists_allocMatrix_of_no_frac {n m : ℕ} {x : Fin n → Fin m → ℝ}
    (hx : x ∈ Pbal n m) (hno : ¬ ∃ i g, IsFracEntry x i g) :
    ∃ A : Allocation n m, IsBalanced A ∧ x = allocMatrix A := by
  push_neg at hno
  have hex_i : ∀ g : Fin m, ∃ i : Fin n, x i g = 1 := by
    intro g
    by_contra hall0
    push_neg at hall0
    have hsum0 : ∑ i : Fin n, x i g = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases eq_zero_or_one_of_not_isFracEntry hx (hno i g) with h0 | h1
      · exact h0
      · exact absurd h1 (hall0 i)
    linarith [hx.2.1 g]
  choose A hA using hex_i
  have hx_eq : x = allocMatrix A := by
    ext i g
    dsimp [allocMatrix]
    split_ifs with hAg
    · subst hAg; exact hA g
    · by_contra hne0
      rcases eq_zero_or_one_of_not_isFracEntry hx (hno i g) with h0 | h1
      · exact hne0 h0
      · have hsum_ge : x i g + x (A g) g ≤ ∑ j : Fin n, x j g := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          have hmem : A g ∈ Finset.univ.erase i :=
            Finset.mem_erase.mpr ⟨hAg, Finset.mem_univ _⟩
          have hle := Finset.single_le_sum (fun j _ => hx.1 j g) hmem
          linarith
        linarith [h1, hA g, hx.2.1 g]
  refine ⟨A, ?_, hx_eq⟩
  rw [← allocMatrix_mem_Pbal_iff, ← hx_eq]
  exact hx

lemma round_to_integral {n m : ℕ} (c : Fin n → Fin m → ℝ) :
    ∀ (K : ℕ) {x : Fin n → Fin m → ℝ}, x ∈ Pbal n m → fracPot x ≤ K →
      ∃ A : Allocation n m, IsBalanced A ∧
        ∑ i, ∑ g, c i g * x i g ≤ ∑ i, ∑ g, c i g * allocMatrix A i g := by
  intro K
  induction K with
  | zero =>
    intro x hx hpot
    have hno : ¬ ∃ i g, IsFracEntry x i g := by
      rintro ⟨i, g, hig⟩
      have hmem : (i, g) ∈ fracEntrySet x := by simp [fracEntrySet, hig]
      have hpos : 0 < (fracEntrySet x).card := Finset.card_pos.mpr ⟨(i, g), hmem⟩
      unfold fracPot at hpot
      omega
    rcases exists_allocMatrix_of_no_frac hx hno with ⟨A, hbal, rfl⟩
    exact ⟨A, hbal, le_rfl⟩
  | succ K ih =>
    intro x hx hpot
    by_cases hfrac : ∃ i g, IsFracEntry x i g
    · rcases round_step_Pbal c hx hfrac with ⟨x', hx', hobj, hlt⟩
      rcases ih hx' (by omega) with ⟨A, hbal, hobj'⟩
      exact ⟨A, hbal, le_trans hobj hobj'⟩
    · rcases exists_allocMatrix_of_no_frac hx hfrac with ⟨A, hbal, rfl⟩
      exact ⟨A, hbal, le_rfl⟩

/-- Every linear objective `∑ i, ∑ g, c i g * x i g` on `Pbal n m` (`1 ≤ n`) attains its maximum
at `allocMatrix A` for some balanced integral allocation `A`. -/
theorem exists_balanced_maximizer {n m : ℕ} (hn : 1 ≤ n) (c : Fin n → Fin m → ℝ) :
    ∃ A : Allocation n m, IsBalanced A ∧
      ∀ y ∈ Pbal n m, ∑ i, ∑ g, c i g * y i g ≤ ∑ i, ∑ g, c i g * allocMatrix A i g := by
  have hcont : Continuous (fun x : Fin n → Fin m → ℝ => ∑ i, ∑ g, c i g * x i g) :=
    continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun g _ =>
      continuous_const.mul ((continuous_apply g).comp (continuous_apply i))
  obtain ⟨x, hxP, hxMax⟩ :=
    (isCompact_Pbal n m).exists_isMaxOn (Pbal_nonempty n m hn) hcont.continuousOn
  obtain ⟨A, hbal, hle⟩ := round_to_integral c (fracPot x) hxP le_rfl
  refine ⟨A, hbal, fun y hy => ?_⟩
  exact le_trans (hxMax hy) hle

end Integrality

/-! ### Base Cases: `n = 1` and `m / n = 0` -/

lemma theorem_1_one_agent (n m : ℕ) (hn1 : n = 1) (v : Fin n → Fin m → ℝ) :
    ∃ A : Allocation n m,
      IsBalanced A ∧ IsEF11 v A ∧ IsFPOIn v (Pbal n m) (allocMatrix A) ∧
      (n ∣ m → IsSwapEF v A) := by
  have hn : 1 ≤ n := by omega
  obtain ⟨A, hbal, hmax⟩ := exists_balanced_maximizer hn v
  have hsub : Subsingleton (Fin n) := by subst hn1; infer_instance
  refine ⟨A, hbal, ?_, ?_, ?_⟩
  · intro i j
    rw [Subsingleton.elim j i]
    exact ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, by simp, by simp, le_rfl⟩
  · refine maximizesWeightedWelfare_imp_isFPOIn v (fun _ => 1) (fun _ => zero_lt_one)
      (Pbal n m) (allocMatrix A) ⟨(allocMatrix_mem_Pbal_iff A).mpr hbal, ?_⟩
    intro y hy
    simpa [fval, mul_comm] using hmax y hy
  · intro _ i j
    rw [Subsingleton.elim j i]
    exact Or.inl le_rfl

lemma theorem_1_small_items (n m : ℕ) (hn : 1 ≤ n) (hr0 : m / n = 0)
    (v : Fin n → Fin m → ℝ) :
    ∃ A : Allocation n m,
      IsBalanced A ∧ IsEF11 v A ∧ IsFPOIn v (Pbal n m) (allocMatrix A) ∧
      (n ∣ m → IsSwapEF v A) := by
  obtain ⟨A, hbal, hmax⟩ := exists_balanced_maximizer hn v
  have hcard_le1 : ∀ i : Fin n, (bundle A i).card ≤ 1 := by
    intro i
    rcases hbal i with h | h <;> omega
  refine ⟨A, hbal, ?_, ?_, ?_⟩
  · intro i j
    classical
    let C : Finset (Fin m) := if bval v i (bundle A i) < 0 then bundle A i else ∅
    let G : Finset (Fin m) := if 0 < bval v i (bundle A j) then bundle A j else ∅
    refine ⟨C, ?_, G, ?_, ?_, ?_, ?_⟩
    · dsimp [C]; split_ifs <;> [exact Subset.rfl; exact Finset.empty_subset _]
    · dsimp [G]; split_ifs <;> [exact Subset.rfl; exact Finset.empty_subset _]
    · dsimp [C]; split_ifs <;> [exact hcard_le1 i; simp]
    · dsimp [G]; split_ifs <;> [exact hcard_le1 j; simp]
    · have hi_nonneg : 0 ≤ bval v i (bundle A i \ C) := by
        dsimp [C]
        split_ifs with h
        · simp [bval]
        · simp; linarith
      have hj_nonpos : bval v i (bundle A j \ G) ≤ 0 := by
        dsimp [G]
        split_ifs with h
        · simp [bval]
        · simp; linarith
      linarith
  · refine maximizesWeightedWelfare_imp_isFPOIn v (fun _ => 1) (fun _ => zero_lt_one)
      (Pbal n m) (allocMatrix A) ⟨(allocMatrix_mem_Pbal_iff A).mpr hbal, ?_⟩
    intro y hy
    simpa [fval, mul_comm] using hmax y hy
  · intro hdvd i j
    have hlt : m < n := (Nat.div_eq_zero_iff.mp hr0).resolve_left (by omega)
    have hm0 : m = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    subst hm0
    exact Or.inl (by simp [bval, bundle])

/-! ### Pillar 2: Strong LP Duality, Bounded Dual Optima, and Regularized Dual (§3.1–§3.2) -/

section DualityAndRegularization

lemma continuous_sup'_apply {ι X : Type*} [TopologicalSpace X]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → X → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x => s.sup' hs (fun i => f i x)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simpa using hf a (Finset.mem_singleton_self a)
  | cons a t hat hne ih =>
    have hrew : (fun x => (Finset.cons a t hat).sup' (Finset.cons_nonempty hat) (fun i => f i x)) =
        fun x => max (f a x) (t.sup' hne (fun i => f i x)) := by
      ext x
      exact Finset.sup'_cons hne (fun i => f i x)
    rw [hrew]
    exact (hf a (Finset.mem_cons_self a t)).max
      (ih (fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi))))

noncomputable def balAllocFinset (n m : ℕ) : Finset (Allocation n m) :=
  Finset.univ.filter IsBalanced

@[simp] lemma mem_balAllocFinset {n m : ℕ} {A : Allocation n m} :
    A ∈ balAllocFinset n m ↔ IsBalanced A := by
  simp [balAllocFinset]

lemma balAllocFinset_nonempty {n m : ℕ} (hn : 1 ≤ n) :
    (balAllocFinset n m).Nonempty :=
  ⟨canonAlloc n m hn, mem_balAllocFinset.mpr (isBalanced_canonAlloc n m hn)⟩

noncomputable def wstar {n m : ℕ} (hn : 1 ≤ n) (v : Fin n → Fin m → ℝ) (α : Fin n → ℝ) : ℝ :=
  (balAllocFinset n m).sup' (balAllocFinset_nonempty hn)
    (fun A => ∑ i, α i * bval v i (bundle A i))

lemma exists_balAlloc_eq_wstar {n m : ℕ} (hn : 1 ≤ n) (v : Fin n → Fin m → ℝ) (α : Fin n → ℝ) :
    ∃ A : Allocation n m, IsBalanced A ∧ ∑ i, α i * bval v i (bundle A i) = wstar hn v α := by
  obtain ⟨A, hmem, hA⟩ := Finset.exists_mem_eq_sup' (balAllocFinset_nonempty hn)
    (fun A : Allocation n m => ∑ i, α i * bval v i (bundle A i))
  exact ⟨A, mem_balAllocFinset.mp hmem, hA.symm⟩

lemma le_wstar_of_isBalanced {n m : ℕ} (hn : 1 ≤ n) (v : Fin n → Fin m → ℝ) (α : Fin n → ℝ)
    {A : Allocation n m} (hA : IsBalanced A) :
    ∑ i, α i * bval v i (bundle A i) ≤ wstar hn v α :=
  Finset.le_sup' (fun B : Allocation n m => ∑ i, α i * bval v i (bundle B i))
    (mem_balAllocFinset.mpr hA)

lemma le_wstar_of_mem_Pbal {n m : ℕ} (hn : 1 ≤ n) (v : Fin n → Fin m → ℝ) (α : Fin n → ℝ)
    {y : Fin n → Fin m → ℝ} (hy : y ∈ Pbal n m) :
    ∑ i, α i * fval v i y ≤ wstar hn v α := by
  obtain ⟨A, hbal, hmax⟩ := exists_balanced_maximizer hn (fun i g => α i * v i g)
  have h1 : ∑ i, α i * fval v i y = ∑ i, ∑ g, (α i * v i g) * y i g := by
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold fval
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => by ring
  have h2 : ∑ i, ∑ g, (α i * v i g) * allocMatrix A i g = ∑ i, α i * bval v i (bundle A i) := by
    calc ∑ i, ∑ g, (α i * v i g) * allocMatrix A i g
        = ∑ i, α i * fval v i (allocMatrix A) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          unfold fval
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => by ring
      _ = ∑ i, α i * bval v i (bundle A i) := by
          simp_rw [fval_allocMatrix]
  calc ∑ i, α i * fval v i y
      ≤ ∑ i, α i * bval v i (bundle A i) := by rw [h1, ← h2]; exact hmax y hy
    _ ≤ wstar hn v α := le_wstar_of_isBalanced hn v α hbal

lemma continuous_wstar {n m : ℕ} (hn : 1 ≤ n) (v : Fin n → Fin m → ℝ) (ρ : ℝ) :
    Continuous (fun w : Fin n → ℝ => wstar hn v (alphaW ρ w)) := by
  unfold wstar
  refine continuous_sup'_apply _ _ _ fun A _ => ?_
  refine continuous_finset_sum _ fun i _ => ?_
  unfold alphaW
  exact (continuous_const.add (continuous_const.mul (continuous_apply i))).mul continuous_const

/-- Weak LP duality: `∑ i, α i * fval v i x ≤ dualObj n m ξ p` for any `x ∈ Pbal n m`. -/
lemma weak_duality {n m : ℕ} {v : Fin n → Fin m → ℝ} {α ξ : Fin n → ℝ} {p : Fin m → ℝ}
    (hfeas : IsDualFeasible v α ξ p) {x : Fin n → Fin m → ℝ} (hx : x ∈ Pbal n m) :
    ∑ i, α i * fval v i x ≤ dualObj n m ξ p := by
  have hstep1 : ∑ i, α i * fval v i x ≤ ∑ i, ∑ g, (ξ i + p g) * x i g := by
    refine Finset.sum_le_sum fun i _ => ?_
    unfold fval
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun g _ => ?_
    have hnn := hx.1 i g
    have hdf := hfeas i g
    nlinarith
  have hstep2 : (∑ i, ∑ g, (ξ i + p g) * x i g) =
      (∑ g, p g) + ((m / n : ℕ) : ℝ) * (∑ i, ξ i) +
        ∑ i, ξ i * ((∑ g, x i g) - ((m / n : ℕ) : ℝ)) := by
    have ha : (∑ i, ∑ g, (ξ i + p g) * x i g) =
        (∑ i, ξ i * (∑ g, x i g)) + (∑ g, p g * (∑ i, x i g)) := by
      simp_rw [add_mul, Finset.sum_add_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => by rw [Finset.mul_sum]
    have hb : ∑ g, p g * (∑ i, x i g) = ∑ g, p g := by
      refine Finset.sum_congr rfl fun g _ => by rw [hx.2.1 g, mul_one]
    have hc : (∑ i, ξ i * (∑ g, x i g)) =
        ((m / n : ℕ) : ℝ) * (∑ i, ξ i) + ∑ i, ξ i * ((∑ g, x i g) - ((m / n : ℕ) : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [ha, hb, hc]
    ring
  have hstep3 : ∑ i, ξ i * ((∑ g, x i g) - ((m / n : ℕ) : ℝ)) ≤ ∑ i, max (ξ i) 0 := by
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨hl, hu⟩ := hx.2.2 i
    by_cases hxi : 0 ≤ ξ i
    · rw [max_eq_left hxi]; nlinarith
    · rw [max_eq_right (by linarith)]; nlinarith
  unfold dualObj
  linarith

def zA {n m : ℕ} (A : Allocation n m) (i : Fin n) : ℝ :=
  ((bundle A i).card : ℝ) - ((m / n : ℕ) : ℝ)

def edgeSlack {n m : ℕ} (v : Fin n → Fin m → ℝ) (α ξ : Fin n → ℝ) (p : Fin m → ℝ)
    (A : Allocation n m) (i : Fin n) : ℝ :=
  ∑ g ∈ bundle A i, (ξ i + p g - α i * v i g)

def rowSlack {n m : ℕ} (ξ : Fin n → ℝ) (A : Allocation n m) (i : Fin n) : ℝ :=
  max (ξ i) 0 - zA A i * ξ i

lemma edgeSlack_nonneg {n m : ℕ} {v : Fin n → Fin m → ℝ} {α ξ : Fin n → ℝ} {p : Fin m → ℝ}
    (hfeas : IsDualFeasible v α ξ p) (A : Allocation n m) (i : Fin n) :
    0 ≤ edgeSlack v α ξ p A i :=
  Finset.sum_nonneg fun g _ => by linarith [hfeas i g]

lemma zA_eq_zero_or_one {n m : ℕ} {A : Allocation n m} (hbal : IsBalanced A) (i : Fin n) :
    zA A i = 0 ∨ zA A i = 1 := by
  unfold zA
  rcases hbal i with h | h
  · left; rw [h]; ring
  · right; rw [h]; push_cast; ring

lemma rowSlack_nonneg {n m : ℕ} (ξ : Fin n → ℝ) {A : Allocation n m} (hbal : IsBalanced A)
    (i : Fin n) : 0 ≤ rowSlack ξ A i := by
  unfold rowSlack
  rcases zA_eq_zero_or_one hbal i with h0 | h1
  · rw [h0, zero_mul, sub_zero]; exact le_max_right _ _
  · rw [h1, one_mul]; linarith [le_max_left (ξ i) 0]

/-- Equation (7): primal-dual gap decomposes into edge slacks plus row slacks. -/
lemma primal_dual_slack_eq {n m : ℕ} (v : Fin n → Fin m → ℝ) (α ξ : Fin n → ℝ) (p : Fin m → ℝ)
    (A : Allocation n m) :
    ∑ i, (edgeSlack v α ξ p A i + rowSlack ξ A i) =
      dualObj n m ξ p - ∑ i, α i * bval v i (bundle A i) := by
  have he : ∀ i : Fin n, edgeSlack v α ξ p A i =
      ((bundle A i).card : ℝ) * ξ i + (∑ g ∈ bundle A i, p g) - α i * bval v i (bundle A i) := by
    intro i
    unfold edgeSlack bval
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.mul_sum]
  simp_rw [he]
  unfold rowSlack zA dualObj
  have hp_sum : ∑ i : Fin n, ∑ g ∈ bundle A i, p g = ∑ g : Fin m, p g :=
    sum_bundle_eq_sum_univ A p
  have hlin : ∀ i : Fin n,
      (((bundle A i).card : ℝ) * ξ i + (∑ g ∈ bundle A i, p g) - α i * bval v i (bundle A i) +
        (max (ξ i) 0 - (((bundle A i).card : ℝ) - ((m / n : ℕ) : ℝ)) * ξ i)) =
      (∑ g ∈ bundle A i, p g) + ((m / n : ℕ) : ℝ) * ξ i + max (ξ i) 0 -
        α i * bval v i (bundle A i) := by
    intro i; ring
  simp_rw [hlin, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hp_sum, ← Finset.mul_sum]

/-- Existence of `δ`-approximate dual feasible solutions via `geometric_hahn_banach_compact_closed`. -/
lemma exists_approx_dual {n m : ℕ} (hn : 1 ≤ n) (v : Fin n → Fin m → ℝ) (α : Fin n → ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (ξ : Fin n → ℝ) (p : Fin m → ℝ),
      IsDualFeasible v α ξ p ∧ dualObj n m ξ p < wstar hn v α + δ := by
  let B_x : ℝ := (m : ℝ) + 1
  let D := (Fin n → Fin m → ℝ) × (Fin n → ℝ)
  let E := (Fin m → ℝ) × (Fin n → ℝ) × ℝ
  let box : Set D :=
    (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) B_x) ×ˢ
    (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1)
  have hbox_compact : IsCompact box :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).prod
      (isCompact_univ_pi fun _ => isCompact_Icc)
  have hbox_convex : Convex ℝ box :=
    (convex_pi fun _ _ => convex_pi fun _ _ => convex_Icc _ _).prod
      (convex_pi fun _ _ => convex_Icc _ _)
  let ϕ : ((Fin n → Fin m → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ((Fin m → ℝ) × (Fin n → ℝ) × ℝ) :=
    { toFun := fun xs =>
        (fun g => ∑ i, xs.1 i g,
         fun i => (∑ g, xs.1 i g) - xs.2 i,
         ∑ i, ∑ g, α i * v i g * xs.1 i g)
      map_add' := fun a b => by
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · ext g; dsimp; rw [← Finset.sum_add_distrib]
        · ext i; dsimp; rw [Finset.sum_add_distrib]; ring
        · dsimp; simp_rw [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · ext g; dsimp; rw [Finset.mul_sum]
        · ext i; dsimp; rw [← Finset.mul_sum]; ring
        · dsimp
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => by ring }
  have hϕ_cont : Continuous ϕ := by
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
    · exact continuous_pi fun g => continuous_finset_sum _ fun i _ =>
        (continuous_apply g).comp ((continuous_apply i).comp continuous_fst)
    · exact continuous_pi fun i =>
        (continuous_finset_sum _ fun g _ =>
          (continuous_apply g).comp ((continuous_apply i).comp continuous_fst)).sub
        ((continuous_apply i).comp continuous_snd)
    · exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun g _ =>
        continuous_const.mul ((continuous_apply g).comp ((continuous_apply i).comp continuous_fst))
  let K_HB : Set E := ϕ '' box
  have hK_compact : IsCompact K_HB := hbox_compact.image hϕ_cont
  have hK_convex : Convex ℝ K_HB := hbox_convex.linear_image ϕ
  let pt : E := (fun _ => 1, fun _ => ((m / n : ℕ) : ℝ), wstar hn v α + δ)
  have hdisj : Disjoint K_HB {pt} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨⟨x, s⟩, ⟨hx_box, hs_box⟩, heq⟩
    have h1 : ∀ g, ∑ i, x i g = 1 := fun g => congrFun (congrArg Prod.fst heq) g
    have h2 : ∀ i, (∑ g, x i g) - s i = ((m / n : ℕ) : ℝ) :=
      fun i => congrFun (congrArg (Prod.fst ∘ Prod.snd) heq) i
    have h3 : ∑ i, ∑ g, α i * v i g * x i g = wstar hn v α + δ :=
      congrArg (Prod.snd ∘ Prod.snd) heq
    have hx_Pbal : x ∈ Pbal n m := by
      refine ⟨fun i g => (hx_box i trivial g trivial).1, h1, fun i => ?_⟩
      have hs_b := hs_box i trivial
      have h2i := h2 i
      constructor <;> linarith [hs_b.1, hs_b.2]
    have hle := le_wstar_of_mem_Pbal hn v α hx_Pbal
    have hrew : ∑ i, α i * fval v i x = ∑ i, ∑ g, α i * v i g * x i g := by
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold fval; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => by ring
    linarith
  obtain ⟨f, u, v_sep, hfu, huv, hvf⟩ := geometric_hahn_banach_compact_closed
    hK_convex hK_compact (convex_singleton pt) isClosed_singleton hdisj
  have hf_lt : ∀ y ∈ K_HB, f y < f pt := fun y hy =>
    lt_trans (hfu y hy) (lt_trans huv (hvf pt rfl))
  let p_raw : Fin m → ℝ := fun g => - f (Pi.single g 1, 0, 0)
  let ξ_raw : Fin n → ℝ := fun i => - f (0, Pi.single i 1, 0)
  let μ : ℝ := f (0, 0, 1)
  have hf_decomp : ∀ (y₁ : Fin m → ℝ) (y₂ : Fin n → ℝ) (y₃ : ℝ),
      f (y₁, y₂, y₃) = - (∑ g, p_raw g * y₁ g) - (∑ i, ξ_raw i * y₂ i) + μ * y₃ := by
    intro y₁ y₂ y₃
    let e₁ : (Fin m → ℝ) →ₗ[ℝ] E :=
      { toFun := fun y => (y, 0, 0)
        map_add' := fun a b => Prod.ext rfl (Prod.ext (zero_add 0).symm (zero_add 0).symm)
        map_smul' := fun c a => Prod.ext rfl (Prod.ext (smul_zero c).symm (smul_zero c).symm) }
    let e₂ : (Fin n → ℝ) →ₗ[ℝ] E :=
      { toFun := fun y => (0, y, 0)
        map_add' := fun a b => Prod.ext (zero_add 0).symm (Prod.ext rfl (zero_add 0).symm)
        map_smul' := fun c a => Prod.ext (smul_zero c).symm (Prod.ext rfl (smul_zero c).symm) }
    let e₃ : ℝ →ₗ[ℝ] E :=
      { toFun := fun y => (0, 0, y)
        map_add' := fun a b => Prod.ext (zero_add 0).symm (Prod.ext (zero_add 0).symm rfl)
        map_smul' := fun c a => Prod.ext (smul_zero c).symm (Prod.ext (smul_zero c).symm rfl) }
    have hy_split : ((y₁, y₂, y₃) : E) = e₁ y₁ + e₂ y₂ + e₃ (y₃ • (1 : ℝ)) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · ext g; change y₁ g = y₁ g + 0 + 0; ring
      · ext i; change y₂ i = 0 + y₂ i + 0; ring
      · change y₃ = 0 + 0 + y₃ * 1; ring
    have hy₁ : y₁ = ∑ g : Fin m, y₁ g • Pi.single g (1 : ℝ) := by
      ext g; simp [Finset.sum_apply, Pi.single_apply]
    have hy₂ : y₂ = ∑ i : Fin n, y₂ i • Pi.single i (1 : ℝ) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [hy_split, map_add, map_add]
    conv_lhs =>
      rw [hy₁, hy₂, map_sum e₁, map_sum e₂, map_sum f, map_sum f, map_smul e₃, map_smul f]
    simp_rw [map_smul e₁, map_smul e₂, map_smul f, smul_eq_mul]
    dsimp [e₁, e₂, e₃, p_raw, ξ_raw, μ]
    have s1 : (∑ x : Fin m, y₁ x * f (Pi.single x 1, 0, 0)) =
        - ∑ g : Fin m, (- f (Pi.single g 1, 0, 0)) * y₁ g := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun g _ => by ring
    have s2 : (∑ x : Fin n, y₂ x * f (0, Pi.single x 1, 0)) =
        - ∑ i : Fin n, (- f (0, Pi.single i 1, 0)) * y₂ i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [s1, s2]
    ring
  obtain ⟨A₀, hA₀_bal, hA₀_opt⟩ := exists_balAlloc_eq_wstar hn v α
  let x₀ := allocMatrix A₀
  let s₀ : Fin n → ℝ := fun i => zA A₀ i
  have hxs₀_box : (x₀, s₀) ∈ box := by
    refine ⟨fun i _ g _ => ?_, fun i _ => ?_⟩
    · dsimp [x₀, allocMatrix, B_x]
      split_ifs <;> constructor <;> linarith [Nat.cast_nonneg (α := ℝ) m]
    · rcases zA_eq_zero_or_one hA₀_bal i with h0 | h1 <;>
        [exact ⟨by simp [s₀, h0], by simp [s₀, h0]⟩;
         exact ⟨by simp [s₀, h1], by simp [s₀, h1]⟩]
  have hϕ₀ : ϕ (x₀, s₀) = (fun _ => 1, fun _ => ((m / n : ℕ) : ℝ), wstar hn v α) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · ext g; exact colSum_allocMatrix A₀ g
    · ext i
      change (∑ g, allocMatrix A₀ i g) - zA A₀ i = _
      rw [rowSum_allocMatrix]; unfold zA; ring
    · change ∑ i, ∑ g, α i * v i g * allocMatrix A₀ i g = wstar hn v α
      rw [← hA₀_opt]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← fval_allocMatrix]; unfold fval; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => by ring
  have hμ_pos : 0 < μ := by
    have hlt := hf_lt (ϕ (x₀, s₀)) ⟨(x₀, s₀), hxs₀_box, rfl⟩
    rw [hϕ₀, hf_decomp, hf_decomp] at hlt
    have hmul : 0 < μ * δ := by linarith
    nlinarith
  let p₀ : Fin m → ℝ := fun g => p_raw g / μ
  let ξ : Fin n → ℝ := fun i => ξ_raw i / μ
  let s_star : Fin n → ℝ := fun i => if 0 ≤ ξ i then 1 else 0
  let x_star : Fin n → Fin m → ℝ :=
    fun i g => if 0 ≤ α i * v i g - ξ i - p₀ g then B_x else 0
  have hstar_box : (x_star, s_star) ∈ box := by
    refine ⟨fun i _ g _ => ?_, fun i _ => ?_⟩
    · dsimp [x_star, B_x]; split_ifs <;> constructor <;> linarith [Nat.cast_nonneg (α := ℝ) m]
    · dsimp [s_star]; split_ifs <;> norm_num
  have hlt_star := hf_lt (ϕ (x_star, s_star)) ⟨(x_star, s_star), hstar_box, rfl⟩
  rw [hf_decomp, hf_decomp] at hlt_star
  have hdiv : - (∑ g, p₀ g * (∑ i, x_star i g)) - (∑ i, ξ i * ((∑ g, x_star i g) - s_star i)) +
      (∑ i, ∑ g, α i * v i g * x_star i g) <
      - (∑ g, p₀ g * 1) - (∑ i, ξ i * ((m / n : ℕ) : ℝ)) + (wstar hn v α + δ) := by
    have hμ_ne : μ ≠ 0 := ne_of_gt hμ_pos
    have h1 : ∀ y₁ : Fin m → ℝ, ∑ g, p₀ g * y₁ g = (∑ g, p_raw g * y₁ g) / μ := by
      intro y₁; dsimp [p₀]; rw [Finset.sum_div]; refine Finset.sum_congr rfl fun g _ => by ring
    have h2 : ∀ y₂ : Fin n → ℝ, ∑ i, ξ i * y₂ i = (∑ i, ξ_raw i * y₂ i) / μ := by
      intro y₂; dsimp [ξ]; rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [h1, h2, h1, h2]
    have hdiv_lt := div_lt_div_of_pos_right hlt_star hμ_pos
    have hrw1 : ∀ A B C : ℝ, (- A - B + μ * C) / μ = - (A / μ) - (B / μ) + C := by
      intro A B C; field_simp
    rw [hrw1, hrw1] at hdiv_lt
    exact hdiv_lt
  have hrearr : dualObj n m ξ p₀ +
      B_x * (∑ i, ∑ g, max (α i * v i g - ξ i - p₀ g) 0) < wstar hn v α + δ := by
    have hs_max : ∀ i : Fin n, ξ i * s_star i = max (ξ i) 0 := by
      intro i; dsimp [s_star]
      split_ifs with h
      · rw [mul_one, max_eq_left h]
      · rw [mul_zero, max_eq_right (by linarith)]
    have hx_max : ∀ i g, (α i * v i g - ξ i - p₀ g) * x_star i g =
        B_x * max (α i * v i g - ξ i - p₀ g) 0 := by
      intro i g; dsimp [x_star]
      split_ifs with h
      · rw [max_eq_left h]; ring
      · rw [mul_zero, max_eq_right (by linarith), mul_zero]
    have halg : - (∑ g, p₀ g * (∑ i, x_star i g)) -
          (∑ i, ξ i * ((∑ g, x_star i g) - s_star i)) +
          (∑ i, ∑ g, α i * v i g * x_star i g) =
        (∑ i, ∑ g, (α i * v i g - ξ i - p₀ g) * x_star i g) + ∑ i, ξ i * s_star i := by
      have hp : ∑ g, p₀ g * (∑ i, x_star i g) = ∑ i, ∑ g, p₀ g * x_star i g := by
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
      have hξ : ∑ i, ξ i * ((∑ g, x_star i g) - s_star i) =
          (∑ i, ∑ g, ξ i * x_star i g) - ∑ i, ξ i * s_star i := by
        simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [hp, hξ]
      have hcomb : (∑ i, ∑ g, α i * v i g * x_star i g) -
            (∑ i, ∑ g, p₀ g * x_star i g) - (∑ i, ∑ g, ξ i * x_star i g) =
          ∑ i, ∑ g, (α i * v i g - ξ i - p₀ g) * x_star i g := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun g _ => by ring
      linarith
    rw [halg] at hdiv
    simp_rw [hs_max, hx_max, ← Finset.mul_sum] at hdiv
    have hrhs : - (∑ g, p₀ g * 1) - (∑ i, ξ i * ((m / n : ℕ) : ℝ)) =
        - (∑ g, p₀ g) - ((m / n : ℕ) : ℝ) * (∑ i, ξ i) := by
      simp [Finset.mul_sum, mul_comm]
    rw [hrhs] at hdiv
    unfold dualObj
    linarith
  let E_viol : ℝ := ∑ i, ∑ g, max (α i * v i g - ξ i - p₀ g) 0
  have hE_nonneg : 0 ≤ E_viol :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun g _ => le_max_right _ _
  let p : Fin m → ℝ := fun g => p₀ g + E_viol
  refine ⟨ξ, p, ?_, ?_⟩
  · intro i g
    dsimp [p]
    have h1 : α i * v i g - ξ i - p₀ g ≤ max (α i * v i g - ξ i - p₀ g) 0 := le_max_left _ _
    have h2 : max (α i * v i g - ξ i - p₀ g) 0 ≤ ∑ g', max (α i * v i g' - ξ i - p₀ g') 0 :=
      Finset.single_le_sum (f := fun g' => max (α i * v i g' - ξ i - p₀ g') 0)
        (fun g' _ => le_max_right _ _) (Finset.mem_univ g)
    have h3 : (∑ g', max (α i * v i g' - ξ i - p₀ g') 0) ≤ E_viol :=
      Finset.single_le_sum (f := fun i' => ∑ g', max (α i' * v i' g' - ξ i' - p₀ g') 0)
        (fun i' _ => Finset.sum_nonneg fun g' _ => le_max_right _ _) (Finset.mem_univ i)
    linarith
  · have hp_obj : dualObj n m ξ p = dualObj n m ξ p₀ + (m : ℝ) * E_viol := by
      unfold dualObj
      dsimp [p]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
    have hm_le : (m : ℝ) * E_viol ≤ B_x * E_viol := by
      dsimp [B_x]; nlinarith
    linarith

/-- Approximate Lemma 4: clamping/shifting a `δ`-optimal dual (`0 < δ < 1/4`) into `[-M0, M0]`. -/
lemma clamp_approx_dual {n m : ℕ} (hn2 : 2 ≤ n) (hr1 : 1 ≤ m / n)
    (v : Fin n → Fin m → ℝ) (α : Fin n → ℝ) (hα : ∀ i, |α i| ≤ 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4)
    {ξ : Fin n → ℝ} {p : Fin m → ℝ}
    (hfeas : IsDualFeasible v α ξ p)
    (hgap : dualObj n m ξ p < wstar (by omega) v α + δ) :
    ∃ (ξ' : Fin n → ℝ) (p' : Fin m → ℝ),
      IsDualFeasible v α ξ' p' ∧
      dualObj n m ξ' p' < wstar (by omega) v α + δ ∧
      (∀ i, |ξ' i| ≤ M0 v) ∧ (∀ g, |p' g| ≤ M0 v) := by
  have hn : 1 ≤ n := by omega
  obtain ⟨A₀, hA₀_bal, hA₀_opt⟩ := exists_balAlloc_eq_wstar hn v α
  have hslack_sum : ∑ i, (edgeSlack v α ξ p A₀ i + rowSlack ξ A₀ i) < δ := by
    rw [primal_dual_slack_eq, hA₀_opt]; linarith
  have hterm_nn : ∀ i : Fin n, 0 ≤ edgeSlack v α ξ p A₀ i + rowSlack ξ A₀ i :=
    fun i => add_nonneg (edgeSlack_nonneg hfeas A₀ i) (rowSlack_nonneg ξ hA₀_bal i)
  have hedge_lt : ∀ i : Fin n, edgeSlack v α ξ p A₀ i < δ := by
    intro i
    have hle := Finset.single_le_sum (fun j _ => hterm_nn j) (Finset.mem_univ i)
    have hrnn := rowSlack_nonneg ξ hA₀_bal i
    linarith
  have hrow_lt : ∀ i : Fin n, rowSlack ξ A₀ i < δ := by
    intro i
    have hle := Finset.single_le_sum (fun j _ => hterm_nn j) (Finset.mem_univ i)
    have henn := edgeSlack_nonneg hfeas A₀ i
    linarith
  have hαv_le : ∀ i g, |α i * v i g| ≤ vmax v := by
    intro i g
    rw [abs_mul]
    calc |α i| * |v i g| ≤ 1 * vmax v :=
          mul_le_mul (hα i) (abs_val_le_vmax v i g) (abs_nonneg _) zero_le_one
      _ = vmax v := one_mul _
  have hitem_tight : ∀ i : Fin n, ∀ g ∈ bundle A₀ i,
      ξ i + p g - α i * v i g < δ := by
    intro i g hg
    have hle : ξ i + p g - α i * v i g ≤ edgeSlack v α ξ p A₀ i := by
      unfold edgeSlack
      exact Finset.single_le_sum (f := fun g' => ξ i + p g' - α i * v i g')
        (fun g' _ => by linarith [hfeas i g']) hg
    linarith [hedge_lt i]
  have hbundle_ne : ∀ i : Fin n, (bundle A₀ i).Nonempty := by
    intro i
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hc : (bundle A₀ i).card = 0 := by simp [hemp]
    rcases hA₀_bal i with h | h <;> omega
  have hdiff_le : ∀ i j : Fin n, ξ i - ξ j ≤ 2 * vmax v + δ := by
    intro i j
    obtain ⟨g, hg⟩ := hbundle_ne i
    have ht := hitem_tight i g hg
    have hdf := hfeas j g
    have hv1 := (abs_le.mp (hαv_le i g)).2
    have hv2 := (abs_le.mp (hαv_le j g)).1
    linarith
  have hex_short : ∃ i₀ : Fin n, (bundle A₀ i₀).card = m / n := by
    by_contra hall_long
    push_neg at hall_long
    have hall : ∀ i : Fin n, (bundle A₀ i).card = m / n + 1 := by
      intro i
      rcases hA₀_bal i with h | h
      · exact absurd h (hall_long i)
      · exact h
    have hsum := sum_card_bundle A₀
    simp_rw [hall] at hsum
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    have hdm := Nat.div_add_mod m n
    have hmod_lt : m % n < n := Nat.mod_lt m (by omega)
    have : n * (m / n + 1) = n * (m / n) + n := by ring
    omega
  have hV_nn := vmax_nonneg v
  by_cases hex_long : ∃ i₁ : Fin n, (bundle A₀ i₁).card = m / n + 1
  · rcases hex_short with ⟨i₀, hi₀⟩
    rcases hex_long with ⟨i₁, hi₁⟩
    have hξ₀ : ξ i₀ < δ := by
      have hr := hrow_lt i₀
      unfold rowSlack zA at hr
      rw [hi₀] at hr
      linarith [le_max_left (ξ i₀) 0]
    have hξ₁ : - δ < ξ i₁ := by
      have hr := hrow_lt i₁
      unfold rowSlack zA at hr
      rw [hi₁] at hr
      push_cast at hr
      have h0 : 0 ≤ max (ξ i₁) 0 := le_max_right _ _
      linarith
    have hξ_bnd : ∀ i : Fin n, |ξ i| ≤ 2 * vmax v + 2 * δ := by
      intro i
      rw [abs_le]
      exact ⟨by linarith [hdiff_le i₁ i], by linarith [hdiff_le i i₀]⟩
    refine ⟨ξ, p, hfeas, hgap, ?_, ?_⟩
    · intro i; unfold M0; linarith [hξ_bnd i]
    · intro g
      let i := A₀ g
      have hg : g ∈ bundle A₀ i := by simp [bundle, i]
      have ht := hitem_tight i g hg
      have hdf := hfeas i g
      have hv := abs_le.mp (hαv_le i g)
      have hξi := abs_le.mp (hξ_bnd i)
      unfold M0
      rw [abs_le]
      constructor <;> linarith
  · push_neg at hex_long
    have hall_short : ∀ i : Fin n, (bundle A₀ i).card = m / n := by
      intro i
      rcases hA₀_bal i with h | h
      · exact h
      · exact absurd h (hex_long i)
    have hm_eq : m = n * (m / n) := by
      have hsum := sum_card_bundle A₀
      simp_rw [hall_short] at hsum
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
      exact hsum.symm
    have huniv_ne : (Finset.univ : Finset (Fin n)).Nonempty :=
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    let ξ_max : ℝ := Finset.univ.sup' huniv_ne ξ
    obtain ⟨i_max, _, hi_max⟩ := Finset.exists_mem_eq_sup' huniv_ne ξ
    have hξ_max_eq : ξ i_max = ξ_max := hi_max.symm
    let ξ' : Fin n → ℝ := fun i => ξ i - ξ_max
    let p' : Fin m → ℝ := fun g => p g + ξ_max
    have hξ'_bnd : ∀ i : Fin n, |ξ' i| ≤ 2 * vmax v + δ := by
      intro i
      dsimp [ξ']
      have hle0 : ξ i ≤ ξ_max := Finset.le_sup' ξ (Finset.mem_univ i)
      have hge := hdiff_le i_max i
      rw [hξ_max_eq] at hge
      rw [abs_le]
      constructor <;> linarith
    refine ⟨ξ', p', ?_, ?_, ?_, ?_⟩
    · intro i g; dsimp [ξ', p']; linarith [hfeas i g]
    · have hobj_le : dualObj n m ξ' p' ≤ dualObj n m ξ p := by
        unfold dualObj
        dsimp [ξ', p']
        have hmax0 : ∀ i : Fin n, max (ξ i - ξ_max) 0 = 0 := by
          intro i
          exact max_eq_right (by linarith [Finset.le_sup' ξ (Finset.mem_univ i)])
        simp_rw [hmax0, Finset.sum_const_zero, add_zero]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hm_cast : (m : ℝ) = (n : ℝ) * ((m / n : ℕ) : ℝ) := by
          conv_lhs => rw [hm_eq]
          push_cast; ring
        have hmax_nn : 0 ≤ ∑ i : Fin n, max (ξ i) 0 :=
          Finset.sum_nonneg fun i _ => le_max_right _ _
        rw [hm_cast]
        have hcancel : (n : ℝ) * ((m / n : ℕ) : ℝ) * ξ_max +
            ((m / n : ℕ) : ℝ) * (∑ i, ξ i - (n : ℝ) * ξ_max) =
            ((m / n : ℕ) : ℝ) * ∑ i, ξ i := by ring
        linarith
      linarith
    · intro i; unfold M0; linarith [hξ'_bnd i]
    · intro g
      let i := A₀ g
      have hg : g ∈ bundle A₀ i := by simp [bundle, i]
      have ht : ξ' i + p' g - α i * v i g < δ := by
        dsimp [ξ', p']; linarith [hitem_tight i g hg]
      have hdf : α i * v i g ≤ ξ' i + p' g := by
        dsimp [ξ', p']; linarith [hfeas i g]
      have hv := abs_le.mp (hαv_le i g)
      have hξi := abs_le.mp (hξ'_bnd i)
      unfold M0
      rw [abs_le]
      constructor <;> linarith

def BoxDual {n m : ℕ} (v : Fin n → Fin m → ℝ) : Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
  (Set.pi Set.univ fun _ => Set.Icc (- M0 v) (M0 v)) ×ˢ
  (Set.pi Set.univ fun _ => Set.Icc (- M0 v) (M0 v))

lemma mem_BoxDual_iff {n m : ℕ} {v : Fin n → Fin m → ℝ} {zp : (Fin n → ℝ) × (Fin m → ℝ)} :
    zp ∈ BoxDual v ↔ (∀ i, |zp.1 i| ≤ M0 v) ∧ (∀ g, |zp.2 g| ≤ M0 v) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => abs_le.mpr (h1 i trivial), fun g => abs_le.mpr (h2 g trivial)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i _ => abs_le.mp (h1 i), fun g _ => abs_le.mp (h2 g)⟩

lemma isCompact_BoxDual {n m : ℕ} (v : Fin n → Fin m → ℝ) : IsCompact (BoxDual v) :=
  (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)

lemma convex_BoxDual {n m : ℕ} (v : Fin n → Fin m → ℝ) : Convex ℝ (BoxDual v) :=
  (convex_pi fun _ _ => convex_Icc _ _).prod (convex_pi fun _ _ => convex_Icc _ _)

lemma continuous_dualObj (n m : ℕ) :
    Continuous (fun zp : (Fin n → ℝ) × (Fin m → ℝ) => dualObj n m zp.1 zp.2) := by
  unfold dualObj
  refine ((continuous_finset_sum _ fun g _ =>
      (continuous_apply g).comp continuous_snd).add
    (continuous_const.mul (continuous_finset_sum _ fun i _ =>
      (continuous_apply i).comp continuous_fst))).add
    (continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp continuous_fst).max continuous_const)

/-- Strong LP duality + Lemma 4 combined: exact dual optimum inside `BoxDual v`. -/
theorem exists_bounded_dual_optimal {n m : ℕ} (hn2 : 2 ≤ n) (hr1 : 1 ≤ m / n)
    (v : Fin n → Fin m → ℝ) (α : Fin n → ℝ) (hα : ∀ i, |α i| ≤ 1) :
    ∃ zp ∈ BoxDual v, IsDualFeasible v α zp.1 zp.2 ∧
      dualObj n m zp.1 zp.2 = wstar (by omega) v α := by
  have hn : 1 ≤ n := by omega
  have hseq : ∀ k : ℕ, ∃ zp ∈ BoxDual v, IsDualFeasible v α zp.1 zp.2 ∧
      dualObj n m zp.1 zp.2 < wstar hn v α + 1 / ((k : ℝ) + 5) := by
    intro k
    have hδ0 : 0 < 1 / ((k : ℝ) + 5) := by positivity
    have hδ4 : 1 / ((k : ℝ) + 5) < 1 / 4 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith [Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨ξ₀, p₀, hf₀, hg₀⟩ := exists_approx_dual hn v α hδ0
    obtain ⟨ξ', p', hf', hg', hb1, hb2⟩ := clamp_approx_dual hn2 hr1 v α hα hδ0 hδ4 hf₀ hg₀
    exact ⟨(ξ', p'), mem_BoxDual_iff.mpr ⟨hb1, hb2⟩, hf', hg'⟩
  choose zpk hzpk_box hzpk_feas hzpk_gap using hseq
  obtain ⟨zp_lim, hzp_box, φ, hφ_mono, hφ_tend⟩ :=
    (isCompact_BoxDual v).tendsto_subseq hzpk_box
  have hfeas_lim : IsDualFeasible v α zp_lim.1 zp_lim.2 := by
    intro i g
    have h_tend : Tendsto (fun k => (zpk (φ k)).1 i + (zpk (φ k)).2 g)
        atTop (𝓝 (zp_lim.1 i + zp_lim.2 g)) :=
      (((continuous_apply i).comp continuous_fst).continuousAt.tendsto.comp hφ_tend).add
        (((continuous_apply g).comp continuous_snd).continuousAt.tendsto.comp hφ_tend)
    exact ge_of_tendsto h_tend (Eventually.of_forall fun k => hzpk_feas (φ k) i g)
  have hle_wstar : dualObj n m zp_lim.1 zp_lim.2 ≤ wstar hn v α := by
    have h_obj_tend : Tendsto (fun k => dualObj n m (zpk (φ k)).1 (zpk (φ k)).2)
        atTop (𝓝 (dualObj n m zp_lim.1 zp_lim.2)) :=
      (continuous_dualObj n m).continuousAt.tendsto.comp hφ_tend
    have h_rhs_tend : Tendsto (fun k => wstar hn v α + 1 / ((φ k : ℝ) + 5))
        atTop (𝓝 (wstar hn v α + 0)) := by
      refine tendsto_const_nhds.add ?_
      have h1 : Tendsto (fun k : ℕ => ((φ k : ℝ) + 5)) atTop atTop :=
        (tendsto_natCast_atTop_atTop.comp hφ_mono.tendsto_atTop).atTop_add tendsto_const_nhds
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp h1
    rw [add_zero] at h_rhs_tend
    exact le_of_tendsto_of_tendsto h_obj_tend h_rhs_tend
      (Eventually.of_forall fun k => le_of_lt (hzpk_gap (φ k)))
  have hge_wstar : wstar hn v α ≤ dualObj n m zp_lim.1 zp_lim.2 := by
    obtain ⟨A₀, hA₀_bal, hA₀⟩ := exists_balAlloc_eq_wstar hn v α
    rw [← hA₀]
    have hrew : ∑ i, α i * bval v i (bundle A₀ i) = ∑ i, α i * fval v i (allocMatrix A₀) := by
      simp_rw [fval_allocMatrix]
    rw [hrew]
    exact weak_duality hfeas_lim ((allocMatrix_mem_Pbal_iff A₀).mpr hA₀_bal)
  exact ⟨zp_lim, hzp_box, hfeas_lim, le_antisymm hle_wstar hge_wstar⟩

/-! ### §3.2 Regularized Dual Program -/

def K_dual {n m : ℕ} (v : Fin n → Fin m → ℝ) (ρ : ℝ) (w : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
  {zp ∈ BoxDual v | IsDualFeasible v (alphaW ρ w) zp.1 zp.2}

lemma alphaW_bounds {n : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : (n : ℝ) * ρ ≤ 1)
    {w : Fin n → ℝ} (hw : w ∈ stdSimplex ℝ (Fin n)) (i : Fin n) :
    ρ ≤ alphaW ρ w i ∧ alphaW ρ w i ≤ 1 := by
  have hwi0 : 0 ≤ w i := hw.1 i
  have hwi1 : w i ≤ 1 := by
    rw [← hw.2]
    exact Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)
  unfold alphaW
  constructor
  · nlinarith
  · have : ρ + (1 - (n : ℝ) * ρ) * w i ≤ ρ + (1 - (n : ℝ) * ρ) * 1 := by nlinarith
    have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by
      have : 1 ≤ n := by exact Fin.pos i
      exact_mod_cast this
    nlinarith

noncomputable def z_hat {n m : ℕ} (v : Fin n → Fin m → ℝ) : (Fin n → ℝ) × (Fin m → ℝ) :=
  (fun _ => M0 v / 2, fun _ => M0 v / 2)

lemma z_hat_strict_feas {n m : ℕ} (v : Fin n → Fin m → ℝ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : (n : ℝ) * ρ ≤ 1) {w : Fin n → ℝ} (hw : w ∈ stdSimplex ℝ (Fin n)) :
    z_hat v ∈ BoxDual v ∧ ∀ i g, alphaW ρ w i * v i g + 1 ≤ (z_hat v).1 i + (z_hat v).2 g := by
  have hV := vmax_nonneg v
  refine ⟨mem_BoxDual_iff.mpr ⟨fun _ => ?_, fun _ => ?_⟩, fun i g => ?_⟩
  · dsimp [z_hat]; unfold M0; rw [abs_le]; constructor <;> linarith
  · dsimp [z_hat]; unfold M0; rw [abs_le]; constructor <;> linarith
  · dsimp [z_hat]
    have hα := alphaW_bounds hρ0 hρ1 hw i
    have hv := abs_val_le_vmax v i g
    have hprod : alphaW ρ w i * v i g ≤ vmax v := by
      have hle := abs_le.mp hv
      nlinarith
    unfold M0
    linarith

lemma K_dual_nonempty {n m : ℕ} (v : Fin n → Fin m → ℝ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : (n : ℝ) * ρ ≤ 1) {w : Fin n → ℝ} (hw : w ∈ stdSimplex ℝ (Fin n)) :
    (K_dual v ρ w).Nonempty := by
  obtain ⟨hb, hs⟩ := z_hat_strict_feas v hρ0 hρ1 hw
  exact ⟨z_hat v, hb, fun i g => by linarith [hs i g]⟩

lemma isCompact_K_dual {n m : ℕ} (v : Fin n → Fin m → ℝ) (ρ : ℝ) (w : Fin n → ℝ) :
    IsCompact (K_dual v ρ w) := by
  refine (isCompact_BoxDual v).inter_right ?_
  change IsClosed {zp : (Fin n → ℝ) × (Fin m → ℝ) |
    ∀ i g, alphaW ρ w i * v i g ≤ zp.1 i + zp.2 g}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun g =>
    isClosed_le continuous_const
      (((continuous_apply i).comp continuous_fst).add ((continuous_apply g).comp continuous_snd))

lemma convex_K_dual {n m : ℕ} (v : Fin n → Fin m → ℝ) (ρ : ℝ) (w : Fin n → ℝ) :
    Convex ℝ (K_dual v ρ w) := by
  intro a ha b hb u v_c hu hv huv
  refine ⟨convex_BoxDual v ha.1 hb.1 hu hv huv, fun i g => ?_⟩
  have h1 := ha.2 i g
  have h2 := hb.2 i g
  change alphaW ρ w i * v i g ≤ (u * a.1 i + v_c * b.1 i) + (u * a.2 g + v_c * b.2 g)
  calc alphaW ρ w i * v i g
      = u * (alphaW ρ w i * v i g) + v_c * (alphaW ρ w i * v i g) := by
        rw [← add_mul, huv, one_mul]
    _ ≤ u * (a.1 i + a.2 g) + v_c * (b.1 i + b.2 g) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hu) (mul_le_mul_of_nonneg_left h2 hv)
    _ = (u * a.1 i + v_c * b.1 i) + (u * a.2 g + v_c * b.2 g) := by ring

def normSqDual {n m : ℕ} (zp : (Fin n → ℝ) × (Fin m → ℝ)) : ℝ :=
  (∑ i, (zp.1 i) ^ 2) + (∑ g, (zp.2 g) ^ 2)

def regObj (n m : ℕ) (lam : ℝ) (zp : (Fin n → ℝ) × (Fin m → ℝ)) : ℝ :=
  dualObj n m zp.1 zp.2 + lam * normSqDual zp

lemma continuous_regObj (n m : ℕ) (lam : ℝ) : Continuous (regObj n m lam) := by
  unfold regObj normSqDual
  refine (continuous_dualObj n m).add (continuous_const.mul ?_)
  exact (continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp continuous_fst).pow 2).add
    (continuous_finset_sum _ fun g _ =>
      ((continuous_apply g).comp continuous_snd).pow 2)

lemma regObj_midpoint_ineq (n m : ℕ) {lam : ℝ} (hlam : 0 ≤ lam)
    (a b : (Fin n → ℝ) × (Fin m → ℝ)) :
    regObj n m lam ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) ≤
      (regObj n m lam a + regObj n m lam b) / 2 -
        (lam / 4) * normSqDual (a - b) := by
  let mid := (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b
  have hmid1 : ∀ i, mid.1 i = (1 / 2 : ℝ) * a.1 i + (1 / 2 : ℝ) * b.1 i := fun _ => rfl
  have hmid2 : ∀ g, mid.2 g = (1 / 2 : ℝ) * a.2 g + (1 / 2 : ℝ) * b.2 g := fun _ => rfl
  have hdual : dualObj n m mid.1 mid.2 ≤ (dualObj n m a.1 a.2 + dualObj n m b.1 b.2) / 2 := by
    unfold dualObj
    have hp : ∑ g, mid.2 g = (∑ g, a.2 g + ∑ g, b.2 g) / 2 := by
      simp_rw [hmid2]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
    have hξ : ∑ i, mid.1 i = (∑ i, a.1 i + ∑ i, b.1 i) / 2 := by
      simp_rw [hmid1]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
    have hmax : ∑ i, max (mid.1 i) 0 ≤ (∑ i, max (a.1 i) 0 + ∑ i, max (b.1 i) 0) / 2 := by
      rw [← Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hmid1 i]
      have h1 := le_max_left (a.1 i) 0
      have h2 := le_max_left (b.1 i) 0
      have h3 := le_max_right (a.1 i) 0
      have h4 := le_max_right (b.1 i) 0
      exact max_le (by linarith) (by linarith)
    rw [hp, hξ]
    linarith
  have hsq : normSqDual mid = (normSqDual a + normSqDual b) / 2 - normSqDual (a - b) / 4 := by
    unfold normSqDual
    have sq1 : ∑ i, (mid.1 i) ^ 2 =
        (∑ i, (a.1 i) ^ 2 + ∑ i, (b.1 i) ^ 2) / 2 - (∑ i, ((a - b).1 i) ^ 2) / 4 := by
      rw [← Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul,
        div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hsub1 : (a - b).1 i = a.1 i - b.1 i := rfl
      rw [hmid1 i, hsub1]
      ring
    have sq2 : ∑ g, (mid.2 g) ^ 2 =
        (∑ g, (a.2 g) ^ 2 + ∑ g, (b.2 g) ^ 2) / 2 - (∑ g, ((a - b).2 g) ^ 2) / 4 := by
      rw [← Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul,
        div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      have hsub2 : (a - b).2 g = a.2 g - b.2 g := rfl
      rw [hmid2 g, hsub2]
      ring
    rw [sq1, sq2]
    ring
  change dualObj n m mid.1 mid.2 + lam * normSqDual mid ≤ _
  rw [hsq]
  unfold regObj
  nlinarith

lemma eq_of_normSqDual_sub_le_zero {n m : ℕ} {a b : (Fin n → ℝ) × (Fin m → ℝ)}
    (h : normSqDual (a - b) ≤ 0) : a = b := by
  unfold normSqDual at h
  have h1_nn : 0 ≤ ∑ i, ((a - b).1 i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2_nn : 0 ≤ ∑ g, ((a - b).2 g) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1_z : ∑ i, ((a - b).1 i) ^ 2 = 0 := le_antisymm (by linarith) h1_nn
  have h2_z : ∑ g, ((a - b).2 g) ^ 2 = 0 := le_antisymm (by linarith) h2_nn
  have ha1 : ∀ i, ((a - b).1 i) ^ 2 = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h1_z i (Finset.mem_univ i)
  have ha2 : ∀ g, ((a - b).2 g) ^ 2 = 0 := fun g =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h2_z g (Finset.mem_univ g)
  refine Prod.ext (funext fun i => ?_) (funext fun g => ?_)
  · have : a.1 i - b.1 i = 0 := sq_eq_zero_iff.mp (ha1 i)
    linarith
  · have : a.2 g - b.2 g = 0 := sq_eq_zero_iff.mp (ha2 g)
    linarith

lemma exists_unique_regDual {n m : ℕ} (v : Fin n → Fin m → ℝ) {ρ lam : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : (n : ℝ) * ρ ≤ 1) (hlam : 0 < lam)
    {w : Fin n → ℝ} (hw : w ∈ stdSimplex ℝ (Fin n)) :
    ∃! zp : (Fin n → ℝ) × (Fin m → ℝ),
      zp ∈ K_dual v ρ w ∧ ∀ y ∈ K_dual v ρ w, regObj n m lam zp ≤ regObj n m lam y := by
  obtain ⟨zp, hzp_mem, hzp_min⟩ := (isCompact_K_dual v ρ w).exists_isMinOn
    (K_dual_nonempty v hρ0 hρ1 hw) (continuous_regObj n m lam).continuousOn
  refine ⟨zp, ⟨hzp_mem, fun y hy => hzp_min hy⟩, ?_⟩
  rintro zp' ⟨hzp'_mem, hzp'_min⟩
  have heq_val : regObj n m lam zp' = regObj n m lam zp :=
    le_antisymm (hzp'_min zp hzp_mem) (hzp_min hzp'_mem)
  have hmid_mem : (1 / 2 : ℝ) • zp' + (1 / 2 : ℝ) • zp ∈ K_dual v ρ w :=
    convex_K_dual v ρ w hzp'_mem hzp_mem (by norm_num) (by norm_num) (by norm_num)
  have hmid_ge : regObj n m lam zp ≤ regObj n m lam ((1 / 2 : ℝ) • zp' + (1 / 2 : ℝ) • zp) :=
    hzp_min hmid_mem
  have hineq := regObj_midpoint_ineq n m (le_of_lt hlam) zp' zp
  rw [heq_val] at hineq
  have hns_le : normSqDual (zp' - zp) ≤ 0 := by nlinarith
  exact eq_of_normSqDual_sub_le_zero hns_le

/-- The unique regularized dual solution `(ξ^λ(w), p^λ(w))` for `w ∈ stdSimplex ℝ (Fin n)`. -/
noncomputable def regDual {n m : ℕ} (v : Fin n → Fin m → ℝ) (ρ lam : ℝ) (w : Fin n → ℝ) :
    (Fin n → ℝ) × (Fin m → ℝ) :=
  if h : 0 ≤ ρ ∧ (n : ℝ) * ρ ≤ 1 ∧ 0 < lam ∧ w ∈ stdSimplex ℝ (Fin n) then
    Classical.choose (exists_unique_regDual v h.1 h.2.1 h.2.2.1 h.2.2.2)
  else z_hat v

lemma regDual_spec {n m : ℕ} (v : Fin n → Fin m → ℝ) {ρ lam : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : (n : ℝ) * ρ ≤ 1) (hlam : 0 < lam)
    {w : Fin n → ℝ} (hw : w ∈ stdSimplex ℝ (Fin n)) :
    regDual v ρ lam w ∈ K_dual v ρ w ∧
      ∀ y ∈ K_dual v ρ w, regObj n m lam (regDual v ρ lam w) ≤ regObj n m lam y := by
  have hcond : 0 ≤ ρ ∧ (n : ℝ) * ρ ≤ 1 ∧ 0 < lam ∧ w ∈ stdSimplex ℝ (Fin n) :=
    ⟨hρ0, hρ1, hlam, hw⟩
  unfold regDual
  rw [dif_pos hcond]
  exact (Classical.choose_spec (exists_unique_regDual v hρ0 hρ1 hlam hw)).1

/-- Equation (11): `dualObj (regDual) ≤ wstar + λ * (n + m) * M0^2`. -/
lemma regDual_gap {n m : ℕ} (hn2 : 2 ≤ n) (hr1 : 1 ≤ m / n) (v : Fin n → Fin m → ℝ)
    {ρ lam : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : (n : ℝ) * ρ ≤ 1) (hlam : 0 < lam)
    {w : Fin n → ℝ} (hw : w ∈ stdSimplex ℝ (Fin n)) :
    dualObj n m (regDual v ρ lam w).1 (regDual v ρ lam w).2 ≤
      wstar (by omega) v (alphaW ρ w) + lam * (((n : ℝ) + (m : ℝ)) * M0 v ^ 2) := by
  have hα_abs : ∀ i, |alphaW ρ w i| ≤ 1 := by
    intro i
    obtain ⟨hl, hu⟩ := alphaW_bounds hρ0 hρ1 hw i
    rw [abs_le]; constructor <;> linarith
  obtain ⟨zp_opt, hbox, hfeas, hopt⟩ := exists_bounded_dual_optimal hn2 hr1 v (alphaW ρ w) hα_abs
  have hmem_K : zp_opt ∈ K_dual v ρ w := ⟨hbox, hfeas⟩
  have hmin := (regDual_spec v hρ0 hρ1 hlam hw).2 zp_opt hmem_K
  have hns_nn : 0 ≤ normSqDual (regDual v ρ lam w) := by
    unfold normSqDual
    exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hns_ub : normSqDual zp_opt ≤ ((n : ℝ) + (m : ℝ)) * M0 v ^ 2 := by
    obtain ⟨hb1, hb2⟩ := mem_BoxDual_iff.mp hbox
    unfold normSqDual
    have s1 : ∑ i : Fin n, (zp_opt.1 i) ^ 2 ≤ (n : ℝ) * M0 v ^ 2 := by
      calc ∑ i : Fin n, (zp_opt.1 i) ^ 2
          ≤ ∑ _i : Fin n, M0 v ^ 2 := Finset.sum_le_sum fun i _ =>
            sq_le_sq.mpr (by rw [abs_of_pos (M0_pos v)]; exact hb1 i)
        _ = (n : ℝ) * M0 v ^ 2 := by simp [nsmul_eq_mul]
    have s2 : ∑ g : Fin m, (zp_opt.2 g) ^ 2 ≤ (m : ℝ) * M0 v ^ 2 := by
      calc ∑ g : Fin m, (zp_opt.2 g) ^ 2
          ≤ ∑ _g : Fin m, M0 v ^ 2 := Finset.sum_le_sum fun g _ =>
            sq_le_sq.mpr (by rw [abs_of_pos (M0_pos v)]; exact hb2 g)
        _ = (m : ℝ) * M0 v ^ 2 := by simp [nsmul_eq_mul]
    linarith
  unfold regObj at hmin
  rw [hopt] at hmin
  nlinarith

/-- Sequential continuity / closed-graph + lower-hemicontinuity identification of `regDual`
(Appendix C, Lemmas 3 & 23). -/
lemma regDual_eq_of_tendsto {n m : ℕ} (v : Fin n → Fin m → ℝ) {ρ lam : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : (n : ℝ) * ρ ≤ 1) (hlam : 0 < lam)
    {wk : ℕ → Fin n → ℝ} {w : Fin n → ℝ}
    (hwk : ∀ k, wk k ∈ stdSimplex ℝ (Fin n)) (hw : w ∈ stdSimplex ℝ (Fin n))
    (hw_tend : Tendsto wk atTop (𝓝 w))
    {zp_lim : (Fin n → ℝ) × (Fin m → ℝ)}
    (hzp_tend : Tendsto (fun k => regDual v ρ lam (wk k)) atTop (𝓝 zp_lim)) :
    zp_lim = regDual v ρ lam w := by
  have hmem_k : ∀ k, regDual v ρ lam (wk k) ∈ K_dual v ρ (wk k) :=
    fun k => (regDual_spec v hρ0 hρ1 hlam (hwk k)).1
  have hbox_lim : zp_lim ∈ BoxDual v :=
    (isCompact_BoxDual v).isClosed.mem_of_tendsto hzp_tend
      (Eventually.of_forall fun k => (hmem_k k).1)
  have hfeas_lim : IsDualFeasible v (alphaW ρ w) zp_lim.1 zp_lim.2 := by
    intro i g
    have h_lhs : Tendsto (fun k => alphaW ρ (wk k) i * v i g) atTop (𝓝 (alphaW ρ w i * v i g)) := by
      unfold alphaW
      exact ((tendsto_const_nhds.add
        (tendsto_const_nhds.mul ((continuous_apply i).continuousAt.tendsto.comp hw_tend))).mul
        tendsto_const_nhds)
    have h_rhs : Tendsto (fun k => (regDual v ρ lam (wk k)).1 i + (regDual v ρ lam (wk k)).2 g)
        atTop (𝓝 (zp_lim.1 i + zp_lim.2 g)) :=
      (((continuous_apply i).comp continuous_fst).continuousAt.tendsto.comp hzp_tend).add
        (((continuous_apply g).comp continuous_snd).continuousAt.tendsto.comp hzp_tend)
    exact le_of_tendsto_of_tendsto h_lhs h_rhs (Eventually.of_forall fun k => (hmem_k k).2 i g)
  have hmem_lim : zp_lim ∈ K_dual v ρ w := ⟨hbox_lim, hfeas_lim⟩
  have hmin_lim : ∀ y ∈ K_dual v ρ w, regObj n m lam zp_lim ≤ regObj n m lam y := by
    intro y hy
    let err : ℕ → ℝ := fun k => (vmax v) * ∑ i : Fin n, |alphaW ρ (wk k) i - alphaW ρ w i|
    have herr_nn : ∀ k, 0 ≤ err k := fun k =>
      mul_nonneg (vmax_nonneg v) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have herr_tend : Tendsto err atTop (𝓝 0) := by
      dsimp [err]
      rw [show (0 : ℝ) = vmax v * ∑ _i : Fin n, (0 : ℝ) by simp]
      refine tendsto_const_nhds.mul (tendsto_finset_sum _ fun i _ => ?_)
      have hα_tend : Tendsto (fun k => alphaW ρ (wk k) i - alphaW ρ w i) atTop (𝓝 0) := by
        have hcont : Continuous (fun w' : Fin n → ℝ => alphaW ρ w' i - alphaW ρ w i) := by
          unfold alphaW
          exact (continuous_const.add (continuous_const.mul (continuous_apply i))).sub
            continuous_const
        have h0 : alphaW ρ w i - alphaW ρ w i = 0 := sub_self _
        rw [← h0]
        exact (hcont.tendsto w).comp hw_tend
      simpa using hα_tend.abs
    let μk : ℕ → ℝ := fun k => min 1 (err k)
    have hμk_tend : Tendsto μk atTop (𝓝 0) := by
      have hmin0 : min (1 : ℝ) 0 = 0 := min_eq_right zero_le_one
      rw [← hmin0]
      exact (tendsto_const_nhds (x := (1 : ℝ))).min herr_tend
    let yk : ℕ → (Fin n → ℝ) × (Fin m → ℝ) :=
      fun k => (1 - μk k) • y + μk k • z_hat v
    have hyk_tend : Tendsto yk atTop (𝓝 y) := by
      dsimp [yk]
      have h1 : Tendsto (fun k => (1 - μk k) • y) atTop (𝓝 ((1 - (0 : ℝ)) • y)) :=
        (tendsto_const_nhds.sub hμk_tend).smul tendsto_const_nhds
      have h2 : Tendsto (fun k => μk k • z_hat v) atTop (𝓝 ((0 : ℝ) • z_hat v)) :=
        hμk_tend.smul tendsto_const_nhds
      simpa using h1.add h2
    have hyk_mem : ∀ k, yk k ∈ K_dual v ρ (wk k) := by
      intro k
      have hμ0 : 0 ≤ μk k := le_min zero_le_one (herr_nn k)
      have hμ1 : μk k ≤ 1 := min_le_left _ _
      obtain ⟨hzhat_box, hzhat_str⟩ := z_hat_strict_feas v hρ0 hρ1 (hwk k)
      refine ⟨convex_BoxDual v hy.1 hzhat_box (by linarith) hμ0 (by linarith), fun i g => ?_⟩
      by_cases h1 : μk k = 1
      · dsimp [yk]; rw [h1]; simp; linarith [hzhat_str i g]
      · have hμ_eq : μk k = err k :=
          min_eq_right (le_of_not_ge fun hle => h1 (min_eq_left hle))
        have hdiff : alphaW ρ (wk k) i * v i g - alphaW ρ w i * v i g ≤ err k := by
          calc alphaW ρ (wk k) i * v i g - alphaW ρ w i * v i g
              ≤ |(alphaW ρ (wk k) i - alphaW ρ w i) * v i g| := by
                have := le_abs_self ((alphaW ρ (wk k) i - alphaW ρ w i) * v i g)
                linarith
            _ = |alphaW ρ (wk k) i - alphaW ρ w i| * |v i g| := abs_mul _ _
            _ ≤ |alphaW ρ (wk k) i - alphaW ρ w i| * vmax v :=
                mul_le_mul_of_nonneg_left (abs_val_le_vmax v i g) (abs_nonneg _)
            _ ≤ (∑ j : Fin n, |alphaW ρ (wk k) j - alphaW ρ w j|) * vmax v := by
                refine mul_le_mul_of_nonneg_right ?_ (vmax_nonneg v)
                exact Finset.single_le_sum
                  (f := fun j => |alphaW ρ (wk k) j - alphaW ρ w j|)
                  (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
            _ = err k := by dsimp [err]; ring
        have hy_fg := hy.2 i g
        have hz_fg := hzhat_str i g
        change alphaW ρ (wk k) i * v i g ≤
          ((1 - μk k) * y.1 i + μk k * (z_hat v).1 i) +
          ((1 - μk k) * y.2 g + μk k * (z_hat v).2 g)
        rw [hμ_eq] at hμ1 ⊢
        nlinarith
    have hineq_k : ∀ k, regObj n m lam (regDual v ρ lam (wk k)) ≤ regObj n m lam (yk k) :=
      fun k => (regDual_spec v hρ0 hρ1 hlam (hwk k)).2 (yk k) (hyk_mem k)
    exact le_of_tendsto_of_tendsto
      ((continuous_regObj n m lam).continuousAt.tendsto.comp hzp_tend)
      ((continuous_regObj n m lam).continuousAt.tendsto.comp hyk_tend)
      (Eventually.of_forall hineq_k)
  have huniq := (Classical.choose_spec (exists_unique_regDual v hρ0 hρ1 hlam hw)).2
  have heq1 := huniq zp_lim ⟨hmem_lim, hmin_lim⟩
  have hcond : 0 ≤ ρ ∧ (n : ℝ) * ρ ≤ 1 ∧ 0 < lam ∧ w ∈ stdSimplex ℝ (Fin n) :=
    ⟨hρ0, hρ1, hlam, hw⟩
  unfold regDual
  rw [dif_pos hcond]
  exact heq1

end DualityAndRegularization

/-! ### Pillar 3: Self-Contained Kuhn Partial-Sum Proof of KKM (`Lemma 2`) -/

section KuhnKKM

lemma even_card_of_fpf_involution_aux {α : Type*} [DecidableEq α] (f : α → α) :
    ∀ (N : ℕ) (S : Finset α), S.card ≤ N →
      (∀ x ∈ S, f x ∈ S) → (∀ x ∈ S, f (f x) = x) → (∀ x ∈ S, f x ≠ x) →
      Even S.card := by
  intro N
  induction N with
  | zero =>
    intro S hle _ _ _
    have hc : S.card = 0 := by omega
    rw [hc]; exact ⟨0, rfl⟩
  | succ N ih =>
    intro S hle hmem hinv hne
    by_cases hS : S.Nonempty
    · obtain ⟨x, hx⟩ := hS
      let y := f x
      have hy : y ∈ S := hmem x hx
      have hyx : y ≠ x := hne x hx
      have hfy : f y = x := hinv x hx
      let S' : Finset α := (S.erase x).erase y
      have hc1 : (S.erase x).card + 1 = S.card := Finset.card_erase_add_one hx
      have hy_er : y ∈ S.erase x := Finset.mem_erase.mpr ⟨hyx, hy⟩
      have hc2 : S'.card + 1 = (S.erase x).card := Finset.card_erase_add_one hy_er
      have hmem' : ∀ z ∈ S', f z ∈ S' := by
        intro z hz
        obtain ⟨hzy, hzx, hzs⟩ : z ≠ y ∧ z ≠ x ∧ z ∈ S := by
          obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hz
          obtain ⟨h3, h4⟩ := Finset.mem_erase.mp h2
          exact ⟨h1, h3, h4⟩
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hmem z hzs⟩⟩
        · intro hfzy
          apply hzx
          calc z = f (f z) := (hinv z hzs).symm
            _ = f y := by rw [hfzy]
            _ = x := hfy
        · intro hfzx
          apply hzy
          calc z = f (f z) := (hinv z hzs).symm
            _ = f x := by rw [hfzx]
            _ = y := rfl
      have hinv' : ∀ z ∈ S', f (f z) = z := fun z hz =>
        hinv z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz))
      have hne' : ∀ z ∈ S', f z ≠ z := fun z hz =>
        hne z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz))
      obtain ⟨k, hk⟩ := ih S' (by omega) hmem' hinv' hne'
      exact ⟨k + 1, by omega⟩
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      exact ⟨0, rfl⟩

lemma even_card_of_fpf_involution {α : Type*} [DecidableEq α] (S : Finset α) (f : α → α)
    (hmem : ∀ x ∈ S, f x ∈ S) (hinv : ∀ x ∈ S, f (f x) = x) (hne : ∀ x ∈ S, f x ≠ x) :
    Even S.card :=
  even_card_of_fpf_involution_aux f S.card S le_rfl hmem hinv hne

def zExt (d M : ℕ) (z : Fin d → ℕ) (k : ℕ) : ℕ :=
  if k = 0 then M else if h : k - 1 < d then z ⟨k - 1, h⟩ else 0

def kuhnCoords (d M : ℕ) (z : Fin d → ℕ) (i : Fin (d + 1)) : ℕ :=
  zExt d M z i.val - zExt d M z (i.val + 1)

lemma zExt_step_le {d M : ℕ} {z : Fin d → ℕ} (hz_anti : Antitone z)
    (hz_le : ∀ a, z a ≤ M) (k : ℕ) :
    zExt d M z (k + 1) ≤ zExt d M z k := by
  unfold zExt
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    split_ifs with h0
    · exact hz_le ⟨0, h0⟩
    · exact Nat.zero_le M
  · simp only [hk0, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    split_ifs with h1 h2
    · exact hz_anti (show k - 1 ≤ k by omega)
    · omega
    · exact Nat.zero_le _
    · exact le_rfl

lemma sum_range_sub_succ (g : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, (g k - g (k + 1)) = g 0 - g N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

lemma sum_kuhnCoords_real {d M : ℕ} {z : Fin d → ℕ} (hz_anti : Antitone z)
    (hz_le : ∀ a, z a ≤ M) :
    ∑ i : Fin (d + 1), (kuhnCoords d M z i : ℝ) = (M : ℝ) := by
  have hcast : ∀ i : Fin (d + 1),
      (kuhnCoords d M z i : ℝ) = (zExt d M z i.val : ℝ) - (zExt d M z (i.val + 1) : ℝ) := by
    intro i
    unfold kuhnCoords
    exact Nat.cast_sub (zExt_step_le hz_anti hz_le i.val)
  simp_rw [hcast]
  rw [Fin.sum_univ_eq_sum_range (fun k => (zExt d M z k : ℝ) - (zExt d M z (k + 1) : ℝ)) (d + 1),
    sum_range_sub_succ]
  have h0 : zExt d M z 0 = M := by simp [zExt]
  have hd1 : zExt d M z (d + 1) = 0 := by simp [zExt]
  rw [h0, hd1]; simp

abbrev RawSimplex (d M : ℕ) := (Fin d → Fin M) × Equiv.Perm (Fin d)

def IsValidKuhn {d M : ℕ} (s : RawSimplex d M) : Prop :=
  Antitone s.1 ∧ ∀ a b : Fin d, a < b → s.1 a = s.1 b → s.2.symm a < s.2.symm b

noncomputable def kuhnFinset (d M : ℕ) : Finset (RawSimplex d M) :=
  Finset.univ.filter IsValidKuhn

@[simp] lemma mem_kuhnFinset {d M : ℕ} {s : RawSimplex d M} :
    s ∈ kuhnFinset d M ↔ IsValidKuhn s := by
  simp [kuhnFinset]

def kuhnVert {d M : ℕ} (s : RawSimplex d M) (r : Fin (d + 1)) : Fin d → ℕ :=
  fun a => (s.1 a).val + if (s.2.symm a).val < r.val then 1 else 0

lemma kuhnVert_le_M {d M : ℕ} (s : RawSimplex d M) (r : Fin (d + 1)) (a : Fin d) :
    kuhnVert s r a ≤ M := by
  unfold kuhnVert
  have ha := (s.1 a).isLt
  split_ifs <;> omega

lemma kuhnVert_antitone {d M : ℕ} {s : RawSimplex d M} (hs : IsValidKuhn s) (r : Fin (d + 1)) :
    Antitone (kuhnVert s r) := by
  intro a b hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · unfold kuhnVert
    have hle : s.1 b ≤ s.1 a := hs.1 hab
    rcases eq_or_lt_of_le hle with heq | hstrict
    · have htie := hs.2 a b hlt heq.symm
      rw [heq]
      have hval_lt : (s.2.symm a).val < (s.2.symm b).val := htie
      split_ifs with h1 h2 <;> omega
    · have hval_lt : (s.1 b).val < (s.1 a).val := hstrict
      split_ifs <;> omega

/-- Cyclic left shift on `Fin (e + 1)`: `t ↦ (t + 1) mod (e + 1)`. -/
def rotLeftPerm (e : ℕ) : Equiv.Perm (Fin (e + 1)) where
  toFun t := ⟨(t.val + 1) % (e + 1), Nat.mod_lt _ (by omega)⟩
  invFun t := ⟨(t.val + e) % (e + 1), Nat.mod_lt _ (by omega)⟩
  left_inv t := by
    ext
    show ((t.val + 1) % (e + 1) + e) % (e + 1) = t.val
    have ht := t.isLt
    by_cases hlast : t.val + 1 = e + 1
    · rw [hlast, Nat.mod_self, Nat.zero_add]
      have hm : e % (e + 1) = e := Nat.mod_eq_of_lt (by omega)
      rw [hm]; omega
    · have hm : (t.val + 1) % (e + 1) = t.val + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hm]
      have : t.val + 1 + e = t.val + (e + 1) := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
  right_inv t := by
    ext
    show ((t.val + e) % (e + 1) + 1) % (e + 1) = t.val
    have ht := t.isLt
    by_cases h0 : t.val = 0
    · rw [h0, Nat.zero_add]
      have hm : e % (e + 1) = e := Nat.mod_eq_of_lt (by omega)
      rw [hm, Nat.mod_self]
    · have hlt : t.val + e = (t.val - 1) + (e + 1) := by omega
      have hm : (t.val + e) % (e + 1) = t.val - 1 := by
        rw [hlt, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hm]
      have : t.val - 1 + 1 = t.val := by omega
      rw [this, Nat.mod_eq_of_lt ht]

lemma rotLeftPerm_last (e : ℕ) : rotLeftPerm e (Fin.last e) = 0 := by
  ext; simp [rotLeftPerm]

lemma rotLeftPerm_symm_zero (e : ℕ) : (rotLeftPerm e).symm 0 = Fin.last e := by
  ext; simp [rotLeftPerm, Nat.mod_eq_of_lt (Nat.lt_succ_self e)]

lemma rotLeftPerm_symm_val_pos {e : ℕ} {t : Fin (e + 1)} (ht0 : 0 < t.val) :
    ((rotLeftPerm e).symm t).val = t.val - 1 := by
  show (t.val + e) % (e + 1) = t.val - 1
  have ht := t.isLt
  have hlt : t.val + e = (t.val - 1) + (e + 1) := by omega
  rw [hlt, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

lemma rotLeftPerm_val_lt {e : ℕ} {t : Fin (e + 1)} (ht : t.val < e) :
    (rotLeftPerm e t).val = t.val + 1 := by
  show (t.val + 1) % (e + 1) = t.val + 1
  exact Nat.mod_eq_of_lt (by omega)

/-- Boundary facet predicate for `(s, r)` in `RawSimplex (e + 1) M × Fin (e + 2)`. -/
def IsBdryFacet {e M : ℕ} (s : RawSimplex (e + 1) M) (r : Fin (e + 2)) : Prop :=
  if r.val = 0 then ¬ ((s.1 (s.2 0)).val + 1 < M)
  else if h : r.val ≤ e then
    s.2 ⟨r.val - 1, by omega⟩ < s.2 ⟨r.val, by omega⟩ ∧
    s.1 (s.2 ⟨r.val - 1, by omega⟩) = s.1 (s.2 ⟨r.val, by omega⟩)
  else ¬ (0 < (s.1 (s.2 (Fin.last e))).val)

/-- Partner map on `RawSimplex (e + 1) M × Fin (e + 2)` for interior facets. -/
noncomputable def kuhnPartner {e M : ℕ} (sr : RawSimplex (e + 1) M × Fin (e + 2)) :
    RawSimplex (e + 1) M × Fin (e + 2) :=
  let s := sr.1
  let r := sr.2
  if hr0 : r.val = 0 then
    if hlt : (s.1 (s.2 0)).val + 1 < M then
      ((fun a => if a = s.2 0 then ⟨(s.1 (s.2 0)).val + 1, hlt⟩ else s.1 a,
        (rotLeftPerm e).trans s.2),
       Fin.last (e + 1))
    else sr
  else if hre : r.val ≤ e then
    ((s.1, (Equiv.swap (⟨r.val - 1, by omega⟩ : Fin (e + 1)) ⟨r.val, by omega⟩).trans s.2), r)
  else
    if hpos : 0 < (s.1 (s.2 (Fin.last e))).val then
      ((fun a => if a = s.2 (Fin.last e) then
          ⟨(s.1 (s.2 (Fin.last e))).val - 1, by have := (s.1 (s.2 (Fin.last e))).isLt; omega⟩
        else s.1 a,
        (rotLeftPerm e).symm.trans s.2),
       0)
    else sr

lemma kuhnPartner_valid_and_invol {e M : ℕ} {s : RawSimplex (e + 1) M} {r : Fin (e + 2)}
    (hs : IsValidKuhn s) (hnotB : ¬ IsBdryFacet s r) :
    IsValidKuhn (kuhnPartner (s, r)).1 ∧
    ¬ IsBdryFacet (kuhnPartner (s, r)).1 (kuhnPartner (s, r)).2 ∧
    kuhnPartner (kuhnPartner (s, r)) = (s, r) ∧
    kuhnPartner (s, r) ≠ (s, r) := by
  unfold IsBdryFacet at hnotB
  by_cases hr0 : r.val = 0
  · rw [if_pos hr0, not_not] at hnotB
    have hpart : kuhnPartner (s, r) =
        ((fun a => if a = s.2 0 then ⟨(s.1 (s.2 0)).val + 1, hnotB⟩ else s.1 a,
          (rotLeftPerm e).trans s.2),
         Fin.last (e + 1)) := by
      unfold kuhnPartner; simp [hr0, hnotB]
    rw [hpart]
    let a₀ := s.2 0
    have hsymm_a₀ : s.2.symm a₀ = 0 := s.2.symm_apply_apply 0
    have hstrict_before : ∀ c : Fin (e + 1), c < a₀ → (s.1 a₀).val < (s.1 c).val := by
      intro c hc
      have hle : s.1 a₀ ≤ s.1 c := hs.1 (le_of_lt hc)
      rcases eq_or_lt_of_le hle with heq | hlt
      · have htie := hs.2 c a₀ hc heq.symm
        rw [hsymm_a₀] at htie
        exact absurd htie (Fin.not_lt_zero _)
      · exact hlt
    let v' : Fin (e + 1) → Fin M :=
      fun a => if a = a₀ then ⟨(s.1 a₀).val + 1, hnotB⟩ else s.1 a
    let π' : Equiv.Perm (Fin (e + 1)) := (rotLeftPerm e).trans s.2
    have hπ'_last : π' (Fin.last e) = a₀ := by
      change s.2 (rotLeftPerm e (Fin.last e)) = s.2 0
      rw [rotLeftPerm_last]
    have hv'_valid : IsValidKuhn (v', π') := by
      refine ⟨?_, ?_⟩
      · intro a b hab
        rcases eq_or_lt_of_le hab with rfl | hlt
        · exact le_rfl
        · dsimp [v']
          by_cases ha : a = a₀ <;> by_cases hb : b = a₀ <;> simp only [ha, hb, ↓reduceIte]
          · exact absurd (ha.trans hb.symm) (ne_of_lt hlt)
          · have hle : (s.1 b).val ≤ (s.1 a₀).val := by rw [← ha]; exact hs.1 hab
            show (s.1 b).val ≤ (s.1 a₀).val + 1
            omega
          · have hsb := hstrict_before a (hb ▸ hlt)
            show (s.1 a₀).val + 1 ≤ (s.1 a).val
            omega
          · exact hs.1 hab
      · intro a b hlt heq
        dsimp [v'] at heq
        by_cases ha : a = a₀ <;> by_cases hb : b = a₀ <;> simp only [ha, hb, ↓reduceIte] at heq
        · exact absurd (ha.trans hb.symm) (ne_of_lt hlt)
        · have hle : (s.1 b).val ≤ (s.1 a₀).val := by rw [← ha]; exact hs.1 (le_of_lt hlt)
          have hv_eq : (s.1 a₀).val + 1 = (s.1 b).val := congrArg Fin.val heq
          omega
        · have hsymm1 : π'.symm b = Fin.last e := by
            rw [hb]
            change (rotLeftPerm e).symm (s.2.symm a₀) = Fin.last e
            rw [hsymm_a₀, rotLeftPerm_symm_zero]
          have hne_last : π'.symm a ≠ Fin.last e := by
            intro h
            have := π'.symm.injective (h.trans hsymm1.symm)
            exact (ne_of_lt hlt) this
          rw [hsymm1]
          exact lt_of_le_of_ne (Fin.le_last _) hne_last
        · have htie := hs.2 a b hlt heq
          have hsa_pos : 0 < (s.2.symm a).val := by
            by_contra h0
            have hz : s.2.symm a = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
            apply ha
            calc a = s.2 (s.2.symm a) := (s.2.apply_symm_apply a).symm
              _ = a₀ := by rw [hz]
          have hsb_pos : 0 < (s.2.symm b).val := lt_trans hsa_pos htie
          have h1 : (π'.symm a).val = (s.2.symm a).val - 1 :=
            rotLeftPerm_symm_val_pos hsa_pos
          have h2 : (π'.symm b).val = (s.2.symm b).val - 1 :=
            rotLeftPerm_symm_val_pos hsb_pos
          change (π'.symm a).val < (π'.symm b).val
          have : (s.2.symm a).val < (s.2.symm b).val := htie
          omega
    have hnotB' : ¬ IsBdryFacet (v', π') (Fin.last (e + 1)) := by
      unfold IsBdryFacet
      have h1 : ¬ (Fin.last (e + 1)).val = 0 := by simp
      have h2 : ¬ (Fin.last (e + 1)).val ≤ e := by simp
      rw [if_neg h1, dif_neg h2, not_not, hπ'_last]
      dsimp [v']
      simp
    have hinvol : kuhnPartner ((v', π'), Fin.last (e + 1)) = (s, r) := by
      unfold kuhnPartner
      dsimp only
      have h1 : ¬ (Fin.last (e + 1)).val = 0 := by simp
      have h2 : ¬ (Fin.last (e + 1)).val ≤ e := by simp
      have hpos : 0 < (v' (π' (Fin.last e))).val := by
        rw [hπ'_last]; dsimp [v']; simp
      rw [dif_neg h1, dif_neg h2, dif_pos hpos]
      refine Prod.ext (Prod.ext ?_ ?_) ?_
      · funext a
        apply Fin.ext
        rw [apply_ite Fin.val]
        dsimp only
        rw [hπ'_last]
        by_cases ha : a = a₀
        · subst ha; simp [v']
        · simp [v', ha]
      · refine Equiv.ext fun t => ?_
        change s.2 (rotLeftPerm e ((rotLeftPerm e).symm t)) = s.2 t
        simp
      · exact (Fin.ext hr0).symm
    have hne : ((v', π'), Fin.last (e + 1)) ≠ (s, r) := by
      intro heq
      have hr_eq : Fin.last (e + 1) = r := congrArg Prod.snd heq
      have : e + 1 = 0 := by
        have hv := congrArg Fin.val hr_eq
        simpa [hr0] using hv
      omega
    exact ⟨hv'_valid, hnotB', hinvol, hne⟩
  · rw [if_neg hr0] at hnotB
    by_cases hre : r.val ≤ e
    · rw [dif_pos hre] at hnotB
      have hpart : kuhnPartner (s, r) =
          ((s.1, (Equiv.swap (⟨r.val - 1, by omega⟩ : Fin (e + 1)) ⟨r.val, by omega⟩).trans s.2),
           r) := by
        unfold kuhnPartner; simp [hr0, hre]
      rw [hpart]
      let t₁ : Fin (e + 1) := ⟨r.val - 1, by omega⟩
      let t₂ : Fin (e + 1) := ⟨r.val, by omega⟩
      have ht₁_ne_t₂ : t₁ ≠ t₂ := by intro h; have := congrArg Fin.val h; dsimp [t₁, t₂] at this; omega
      let π' := (Equiv.swap t₁ t₂).trans s.2
      have hπ'_symm : ∀ a, π'.symm a = Equiv.swap t₁ t₂ (s.2.symm a) := fun _ => rfl
      have hv'_valid : IsValidKuhn (s.1, π') := by
        refine ⟨hs.1, fun a b hlt heq => ?_⟩
        have htie := hs.2 a b hlt heq
        rw [hπ'_symm, hπ'_symm]
        by_cases ha1 : s.2.symm a = t₁
        · by_cases hb2 : s.2.symm b = t₂
          · exfalso
            apply hnotB
            have ha_eq : a = s.2 t₁ := by rw [← ha1]; simp
            have hb_eq : b = s.2 t₂ := by rw [← hb2]; simp
            rw [← ha_eq, ← hb_eq]
            exact ⟨hlt, heq⟩
          · have hb_ne1 : s.2.symm b ≠ t₁ := by rw [← ha1]; exact s.2.symm.injective.ne (ne_of_gt hlt)
            rw [ha1, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hb_ne1 hb2]
            have hlt_val : t₁.val < (s.2.symm b).val := by rw [← ha1]; exact htie
            have hne_val : (s.2.symm b).val ≠ r.val := fun hv => hb2 (Fin.ext hv)
            change r.val < (s.2.symm b).val
            dsimp [t₁] at hlt_val
            omega
        · by_cases ha2 : s.2.symm a = t₂
          · have hb_ne1 : s.2.symm b ≠ t₁ := by
              intro hb1
              have : t₂ < t₁ := by rw [← ha2, ← hb1]; exact htie
              have hv : r.val < r.val - 1 := this
              omega
            have hb_ne2 : s.2.symm b ≠ t₂ := by rw [← ha2]; exact s.2.symm.injective.ne (ne_of_gt hlt)
            rw [ha2, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hb_ne1 hb_ne2]
            have hlt_val : r.val < (s.2.symm b).val := by rw [ha2] at htie; exact htie
            change r.val - 1 < (s.2.symm b).val
            omega
          · rw [Equiv.swap_apply_of_ne_of_ne ha1 ha2]
            by_cases hb1 : s.2.symm b = t₁
            · rw [hb1, Equiv.swap_apply_left]
              have hlt_val : (s.2.symm a).val < r.val - 1 := by rw [hb1] at htie; exact htie
              change (s.2.symm a).val < r.val
              omega
            · by_cases hb2 : s.2.symm b = t₂
              · rw [hb2, Equiv.swap_apply_right]
                have hlt_val : (s.2.symm a).val < r.val := by rw [hb2] at htie; exact htie
                have hne_val : (s.2.symm a).val ≠ r.val - 1 := fun hv => ha1 (Fin.ext hv)
                change (s.2.symm a).val < r.val - 1
                omega
              · rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2]
                exact htie
      have hnotB' : ¬ IsBdryFacet (s.1, π') r := by
        unfold IsBdryFacet
        rw [if_neg hr0, dif_pos hre]
        rintro ⟨hlt', heq'⟩
        have hp1 : π' t₁ = s.2 t₂ := by change s.2 (Equiv.swap t₁ t₂ t₁) = _; simp
        have hp2 : π' t₂ = s.2 t₁ := by change s.2 (Equiv.swap t₁ t₂ t₂) = _; simp
        rw [hp1, hp2] at hlt' heq'
        have htie := hs.2 (s.2 t₂) (s.2 t₁) hlt' heq'
        simp only [Equiv.symm_apply_apply] at htie
        have hv : r.val < r.val - 1 := htie
        omega
      have hinvol : kuhnPartner ((s.1, π'), r) = (s, r) := by
        unfold kuhnPartner
        dsimp only
        rw [dif_neg hr0, dif_pos hre]
        refine Prod.ext (Prod.ext rfl ?_) rfl
        refine Equiv.ext fun t => ?_
        change s.2 (Equiv.swap t₁ t₂ (Equiv.swap t₁ t₂ t)) = s.2 t
        simp
      have hne : ((s.1, π'), r) ≠ (s, r) := by
        intro heq
        have hp_eq : π' = s.2 := congrArg Prod.snd (congrArg Prod.fst heq)
        have hv : π' t₁ = s.2 t₁ := congrFun (congrArg DFunLike.coe hp_eq) t₁
        have hp1 : π' t₁ = s.2 t₂ := by change s.2 (Equiv.swap t₁ t₂ t₁) = _; simp
        rw [hp1] at hv
        exact ht₁_ne_t₂ (s.2.injective hv).symm
      exact ⟨hv'_valid, hnotB', hinvol, hne⟩
    · rw [dif_neg hre, not_not] at hnotB
      have hr_last : r = Fin.last (e + 1) := by
        have hr_lt := r.isLt
        ext; simp; omega
      have hpart : kuhnPartner (s, r) =
          ((fun a => if a = s.2 (Fin.last e) then
              ⟨(s.1 (s.2 (Fin.last e))).val - 1,
                by have := (s.1 (s.2 (Fin.last e))).isLt; omega⟩
            else s.1 a,
            (rotLeftPerm e).symm.trans s.2),
           0) := by
        unfold kuhnPartner; simp [hr0, hre, hnotB]
      rw [hpart]
      let aL := s.2 (Fin.last e)
      have hsymm_aL : s.2.symm aL = Fin.last e := s.2.symm_apply_apply (Fin.last e)
      have hstrict_after : ∀ c : Fin (e + 1), aL < c → (s.1 c).val < (s.1 aL).val := by
        intro c hc
        have hle : s.1 c ≤ s.1 aL := hs.1 (le_of_lt hc)
        rcases eq_or_lt_of_le hle with heq | hlt
        · have htie := hs.2 aL c hc heq.symm
          rw [hsymm_aL] at htie
          exact absurd htie (not_lt_of_ge (Fin.le_last _))
        · exact hlt
      let v' : Fin (e + 1) → Fin M :=
        fun a => if a = aL then
          ⟨(s.1 aL).val - 1, by have := (s.1 aL).isLt; omega⟩
        else s.1 a
      let π' : Equiv.Perm (Fin (e + 1)) := (rotLeftPerm e).symm.trans s.2
      have hπ'_0 : π' 0 = aL := by
        change s.2 ((rotLeftPerm e).symm 0) = s.2 (Fin.last e)
        rw [rotLeftPerm_symm_zero]
      have hv'_valid : IsValidKuhn (v', π') := by
        refine ⟨?_, ?_⟩
        · intro a b hab
          rcases eq_or_lt_of_le hab with rfl | hlt
          · exact le_rfl
          · dsimp [v']
            by_cases ha : a = aL <;> by_cases hb : b = aL <;> simp only [ha, hb, ↓reduceIte]
            · exact absurd (ha.trans hb.symm) (ne_of_lt hlt)
            · have hsa := hstrict_after b (ha ▸ hlt)
              show (s.1 b).val ≤ (s.1 aL).val - 1
              omega
            · have hle : (s.1 aL).val ≤ (s.1 a).val := by rw [← hb]; exact hs.1 hab
              show (s.1 aL).val - 1 ≤ (s.1 a).val
              omega
            · exact hs.1 hab
        · intro a b hlt heq
          dsimp [v'] at heq
          by_cases ha : a = aL <;> by_cases hb : b = aL <;> simp only [ha, hb, ↓reduceIte] at heq
          · exact absurd (ha.trans hb.symm) (ne_of_lt hlt)
          · have hsymm0 : π'.symm a = 0 := by
              rw [ha]
              change rotLeftPerm e (s.2.symm aL) = 0
              rw [hsymm_aL, rotLeftPerm_last]
            have hne0 : π'.symm b ≠ 0 := by
              intro h
              have := π'.symm.injective (h.trans hsymm0.symm)
              exact (ne_of_gt hlt) this
            rw [hsymm0]
            exact Fin.pos_iff_ne_zero.mpr hne0
          · have hle : (s.1 aL).val ≤ (s.1 a).val := by rw [← hb]; exact hs.1 (le_of_lt hlt)
            have hv_eq : (s.1 a).val = (s.1 aL).val - 1 := congrArg Fin.val heq
            have hpos_aL : 0 < (s.1 aL).val := hnotB
            omega
          · have htie := hs.2 a b hlt heq
            have hsb_lt : (s.2.symm b).val < e := by
              have hlt_e1 := (s.2.symm b).isLt
              have hne_e : s.2.symm b ≠ Fin.last e := by
                intro h
                apply hb
                calc b = s.2 (s.2.symm b) := (s.2.apply_symm_apply b).symm
                  _ = aL := by rw [h]
              have hne_val : (s.2.symm b).val ≠ e := fun hv => hne_e (Fin.ext hv)
              omega
            have hsa_lt : (s.2.symm a).val < e := lt_trans htie hsb_lt
            have h1 : (π'.symm a).val = (s.2.symm a).val + 1 := rotLeftPerm_val_lt hsa_lt
            have h2 : (π'.symm b).val = (s.2.symm b).val + 1 := rotLeftPerm_val_lt hsb_lt
            change (π'.symm a).val < (π'.symm b).val
            have : (s.2.symm a).val < (s.2.symm b).val := htie
            omega
      have hnotB' : ¬ IsBdryFacet (v', π') 0 := by
        unfold IsBdryFacet
        simp only [Fin.val_zero, ↓reduceIte, not_not, hπ'_0]
        dsimp [v']
        simp only [↓reduceIte]
        have := (s.1 aL).isLt
        have hpos_aL : 0 < (s.1 aL).val := hnotB
        omega
      have hinvol : kuhnPartner ((v', π'), 0) = (s, r) := by
        unfold kuhnPartner
        dsimp only
        have hlt_M : (v' (π' 0)).val + 1 < M := by
          rw [hπ'_0]; dsimp [v']; simp; have := (s.1 aL).isLt; have : 0 < (s.1 aL).val := hnotB; omega
        have h0_val : (0 : Fin (e + 2)).val = 0 := rfl
        rw [dif_pos h0_val, dif_pos hlt_M]
        refine Prod.ext (Prod.ext ?_ ?_) hr_last.symm
        · funext a
          apply Fin.ext
          rw [apply_ite Fin.val]
          dsimp only
          rw [hπ'_0]
          have hpos_aL : 0 < (s.1 aL).val := hnotB
          by_cases ha : a = aL
          · subst ha; simp [v']; omega
          · simp [v', ha]
        · refine Equiv.ext fun t => ?_
          change s.2 ((rotLeftPerm e).symm (rotLeftPerm e t)) = s.2 t
          simp
      have hne : ((v', π'), (0 : Fin (e + 2))) ≠ (s, r) := by
        intro heq
        have hr_eq : (0 : Fin (e + 2)) = r := congrArg Prod.snd heq
        exact hr0 (congrArg Fin.val hr_eq).symm
      exact ⟨hv'_valid, hnotB', hinvol, hne⟩

lemma kuhnPartner_same_facet_verts {e M : ℕ} {s : RawSimplex (e + 1) M} {r : Fin (e + 2)}
    (hs : IsValidKuhn s) (hnotB : ¬ IsBdryFacet s r) :
    ∀ q' : Fin (e + 2), q' ≠ (kuhnPartner (s, r)).2 →
      ∃ q : Fin (e + 2), q ≠ r ∧
        kuhnVert (kuhnPartner (s, r)).1 q' = kuhnVert s q := by
  have hzero_case : ∀ (s₀ : RawSimplex (e + 1) M) (r₀ : Fin (e + 2)),
      r₀.val = 0 → ¬ IsBdryFacet s₀ r₀ →
      ∀ q' : Fin (e + 2), q' ≠ (kuhnPartner (s₀, r₀)).2 →
        ∃ q : Fin (e + 2), q ≠ r₀ ∧
          kuhnVert (kuhnPartner (s₀, r₀)).1 q' = kuhnVert s₀ q := by
    intro s₀ r₀ hr₀ hnb₀ q' hq'_ne
    have hltM : (s₀.1 (s₀.2 0)).val + 1 < M := by
      unfold IsBdryFacet at hnb₀; rwa [if_pos hr₀, not_not] at hnb₀
    have hpart : kuhnPartner (s₀, r₀) =
        ((fun a => if a = s₀.2 0 then ⟨(s₀.1 (s₀.2 0)).val + 1, hltM⟩ else s₀.1 a,
          (rotLeftPerm e).trans s₀.2),
         Fin.last (e + 1)) := by
      unfold kuhnPartner; simp [hr₀, hltM]
    rw [hpart] at hq'_ne ⊢
    have hq'_lt : q'.val < e + 1 := by
      have := q'.isLt
      have hne_val : q'.val ≠ e + 1 := fun hv => hq'_ne (Fin.ext hv)
      omega
    let q : Fin (e + 2) := ⟨q'.val + 1, by omega⟩
    refine ⟨q, ?_, ?_⟩
    · intro hqr₀
      have : q'.val + 1 = 0 := (congrArg Fin.val hqr₀).trans hr₀
      omega
    · ext a
      unfold kuhnVert
      dsimp [q]
      by_cases ha : a = s₀.2 0
      · subst ha
        simp only [↓reduceIte]
        change ((s₀.1 (s₀.2 0)).val + 1) +
            (if ((rotLeftPerm e).symm (s₀.2.symm (s₀.2 0))).val < q'.val then 1 else 0) =
          (s₀.1 (s₀.2 0)).val + (if (s₀.2.symm (s₀.2 0)).val < q'.val + 1 then 1 else 0)
        have hs0 : (s₀.2.symm (s₀.2 0)).val = 0 := by rw [s₀.2.symm_apply_apply]; rfl
        have hs_last : ((rotLeftPerm e).symm (s₀.2.symm (s₀.2 0))).val = e := by
          rw [s₀.2.symm_apply_apply, rotLeftPerm_symm_zero]; rfl
        simp only [hs0, hs_last]
        split_ifs with h1 h2 <;> omega
      · simp only [ha, ↓reduceIte]
        change (s₀.1 a).val +
            (if ((rotLeftPerm e).symm (s₀.2.symm a)).val < q'.val then 1 else 0) =
          (s₀.1 a).val + (if (s₀.2.symm a).val < q'.val + 1 then 1 else 0)
        have hs_pos : 0 < (s₀.2.symm a).val := by
          by_contra h0
          have hz : s₀.2.symm a = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
          apply ha
          calc a = s₀.2 (s₀.2.symm a) := (s₀.2.apply_symm_apply a).symm
            _ = s₀.2 0 := by rw [hz]
        have hrot : ((rotLeftPerm e).symm (s₀.2.symm a)).val = (s₀.2.symm a).val - 1 :=
          rotLeftPerm_symm_val_pos hs_pos
        simp only [hrot]
        split_ifs with h1 h2 <;> omega
  by_cases hr0 : r.val = 0
  · exact hzero_case s r hr0 hnotB
  · by_cases hre : r.val ≤ e
    · intro q' hq'_ne
      have hpart : kuhnPartner (s, r) =
          ((s.1, (Equiv.swap (⟨r.val - 1, by omega⟩ : Fin (e + 1)) ⟨r.val, by omega⟩).trans s.2),
           r) := by
        unfold kuhnPartner; simp [hr0, hre]
      rw [hpart] at hq'_ne ⊢
      refine ⟨q', hq'_ne, ?_⟩
      ext a
      unfold kuhnVert
      dsimp
      let t₁ : Fin (e + 1) := ⟨r.val - 1, by omega⟩
      let t₂ : Fin (e + 1) := ⟨r.val, by omega⟩
      change (s.1 a).val + (if (Equiv.swap t₁ t₂ (s.2.symm a)).val < q'.val then 1 else 0) = _
      have hq'_ne_val : q'.val ≠ r.val := fun hv => hq'_ne (Fin.ext hv)
      by_cases ha1 : s.2.symm a = t₁
      · have hsw : (Equiv.swap t₁ t₂ (s.2.symm a)).val = r.val := by
          rw [ha1, Equiv.swap_apply_left]
        have hva : (s.2.symm a).val = r.val - 1 := by rw [ha1]
        simp only [hsw, hva]
        split_ifs with h1 h2 <;> omega
      · by_cases ha2 : s.2.symm a = t₂
        · have hsw : (Equiv.swap t₁ t₂ (s.2.symm a)).val = r.val - 1 := by
            rw [ha2, Equiv.swap_apply_right]
          have hva : (s.2.symm a).val = r.val := by rw [ha2]
          simp only [hsw, hva]
          split_ifs with h1 h2 <;> omega
        · have hsw : Equiv.swap t₁ t₂ (s.2.symm a) = s.2.symm a :=
            Equiv.swap_apply_of_ne_of_ne ha1 ha2
          simp only [hsw]
    · intro q' hq'_ne
      obtain ⟨hs', hnotB', hinvol, _⟩ := kuhnPartner_valid_and_invol hs hnotB
      let s' := (kuhnPartner (s, r)).1
      let r' := (kuhnPartner (s, r)).2
      have hr'0 : r'.val = 0 := by
        have hnb := hnotB
        unfold IsBdryFacet at hnb
        rw [if_neg hr0, dif_neg hre, not_not] at hnb
        dsimp [r']
        unfold kuhnPartner
        simp [hr0, hre, hnb]
      have hinj_vert : ∀ (s_any : RawSimplex (e + 1) M), Function.Injective (kuhnVert s_any) := by
        intro s_any q₁ q₂ hveq
        have hstep : ∀ {u w : Fin (e + 2)}, u < w → kuhnVert s_any u ≠ kuhnVert s_any w := by
          intro u w hlt heq_uw
          have hu_lt : u.val < e + 1 := by have := w.isLt; have : u.val < w.val := hlt; omega
          let a := s_any.2 ⟨u.val, hu_lt⟩
          have hsa : (s_any.2.symm a).val = u.val := by rw [s_any.2.symm_apply_apply]
          have hv_a := congrFun heq_uw a
          unfold kuhnVert at hv_a
          simp only [hsa, lt_self_iff_false, ↓reduceIte] at hv_a
          have hlt_val : u.val < w.val := hlt
          simp only [hlt_val, ↓reduceIte] at hv_a
          omega
        by_contra hne_q
        rcases lt_or_gt_of_ne hne_q with hlt | hgt
        · exact hstep hlt hveq
        · exact hstep hgt hveq.symm
      have hcard_eq : (Finset.univ.erase r').image (kuhnVert s') =
          (Finset.univ.erase r).image (kuhnVert s) := by
        have hsub_rev : (Finset.univ.erase r).image (kuhnVert s) ⊆
            (Finset.univ.erase r').image (kuhnVert s') := by
          intro z hz
          obtain ⟨q, hq_er, rfl⟩ := Finset.mem_image.mp hz
          have hq_ne : q ≠ (kuhnPartner (s', r')).2 := by
            rw [hinvol]; exact (Finset.mem_erase.mp hq_er).1
          obtain ⟨q'', hq''_ne, hvert_eq⟩ := hzero_case s' r' hr'0 hnotB' q hq_ne
          rw [hinvol] at hvert_eq
          exact Finset.mem_image.mpr ⟨q'', Finset.mem_erase.mpr ⟨hq''_ne, Finset.mem_univ _⟩,
            hvert_eq.symm⟩
        have hc1 : ((Finset.univ.erase r).image (kuhnVert s)).card = e + 1 := by
          rw [Finset.card_image_of_injective _ (hinj_vert s),
            Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin]
          omega
        have hc2 : ((Finset.univ.erase r').image (kuhnVert s')).card = e + 1 := by
          rw [Finset.card_image_of_injective _ (hinj_vert s'),
            Finset.card_erase_of_mem (Finset.mem_univ r'), Finset.card_univ, Fintype.card_fin]
          omega
        exact (Finset.eq_of_subset_of_card_le hsub_rev (by omega)).symm
      have hmem : kuhnVert s' q' ∈ (Finset.univ.erase r).image (kuhnVert s) := by
        rw [← hcard_eq]
        exact Finset.mem_image.mpr ⟨q', Finset.mem_erase.mpr ⟨hq'_ne, Finset.mem_univ _⟩, rfl⟩
      obtain ⟨q, hq_er, hveq⟩ := Finset.mem_image.mp hmem
      exact ⟨q, (Finset.mem_erase.mp hq_er).1, hveq.symm⟩

/-- Fiber parity for a single simplex `s`: the number of `r : Fin (e + 2)` whose remaining
`e + 1` vertices hit `Fin.castSucc '' univ` is `1` mod `2` iff `f` is surjective. -/
lemma fiber_goodFacet_card_mod2 {e : ℕ} (f : Fin (e + 2) → Fin (e + 2)) :
    (Finset.univ.filter (fun r : Fin (e + 2) =>
      ∀ j : Fin (e + 1), ∃ q : Fin (e + 2), q ≠ r ∧ f q = j.castSucc)).card % 2 =
    if Function.Surjective f then 1 else 0 := by
  let S_low : Finset (Fin (e + 2)) := Finset.univ.image Fin.castSucc
  have hcard_low : S_low.card = e + 1 := by
    rw [Finset.card_image_of_injective _ (Fin.castSucc_injective (e + 1)),
      Finset.card_univ, Fintype.card_fin]
  let fib := Finset.univ.filter (fun r : Fin (e + 2) =>
    ∀ j : Fin (e + 1), ∃ q : Fin (e + 2), q ≠ r ∧ f q = j.castSucc)
  have hfib_iff : ∀ r : Fin (e + 2), r ∈ fib ↔
      (Finset.univ.erase r).image f = S_low ∧ Set.InjOn f (Finset.univ.erase r) := by
    intro r
    constructor
    · intro hr
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      have hsub : S_low ⊆ (Finset.univ.erase r).image f := by
        intro y hy
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨q, hqr, hfq⟩ := hr j
        exact Finset.mem_image.mpr ⟨q, Finset.mem_erase.mpr ⟨hqr, Finset.mem_univ _⟩, hfq⟩
      have hc_er : (Finset.univ.erase r).card = e + 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin]
        omega
      have hc_le : ((Finset.univ.erase r).image f).card ≤ e + 1 := by
        rw [← hc_er]; exact Finset.card_image_le
      have heq : (Finset.univ.erase r).image f = S_low :=
        (Finset.eq_of_subset_of_card_le hsub (by rw [hcard_low]; exact hc_le)).symm
      have hinj : Set.InjOn f (Finset.univ.erase r) := by
        rw [← Finset.card_image_iff, heq, hcard_low, hc_er]
      exact ⟨heq, hinj⟩
    · rintro ⟨heq, _⟩
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j
      have hj_mem : j.castSucc ∈ (Finset.univ.erase r).image f := by
        rw [heq]; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      obtain ⟨q, hq_er, hfq⟩ := Finset.mem_image.mp hj_mem
      exact ⟨q, (Finset.mem_erase.mp hq_er).1, hfq⟩
  by_cases hsurj : Function.Surjective f
  · rw [if_pos hsurj]
    have hbij : Function.Bijective f := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
    obtain ⟨r₀, hr₀⟩ := hsurj (Fin.last (e + 1))
    have hfib_eq : fib = {r₀} := by
      ext r
      rw [Finset.mem_singleton, hfib_iff]
      constructor
      · rintro ⟨heq, _⟩
        by_contra hne
        have hmem_last : Fin.last (e + 1) ∈ (Finset.univ.erase r).image f :=
          Finset.mem_image.mpr ⟨r₀, Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩, hr₀⟩
        rw [heq] at hmem_last
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem_last
        exact Fin.castSucc_ne_last j hj
      · rintro rfl
        refine ⟨?_, fun a _ b _ hab => hbij.1 hab⟩
        ext y
        simp only [S_low, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
        constructor
        · rintro ⟨q, hqr₀, rfl⟩
          rcases Fin.eq_castSucc_or_eq_last (f q) with ⟨j, hj⟩ | hlast
          · exact ⟨j, hj.symm⟩
          · exact absurd (hbij.1 (hlast.trans hr₀.symm)) hqr₀
        · rintro ⟨j, rfl⟩
          obtain ⟨q, hfq⟩ := hsurj j.castSucc
          refine ⟨q, fun hqr₀ => ?_, hfq⟩
          rw [hqr₀, hr₀] at hfq
          exact Fin.castSucc_ne_last j hfq.symm
    change fib.card % 2 = 1
    rw [hfib_eq, Finset.card_singleton]
  · rw [if_neg hsurj]
    change fib.card % 2 = 0
    by_cases hne_fib : fib.Nonempty
    · obtain ⟨r₁, hr₁⟩ := hne_fib
      obtain ⟨heq₁, hinj₁⟩ := (hfib_iff r₁).mp hr₁
      have hfr₁_low : f r₁ ∈ S_low := by
        rcases Fin.eq_castSucc_or_eq_last (f r₁) with ⟨j, hj⟩ | hlast
        · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj.symm⟩
        · exfalso
          apply hsurj
          intro y
          rcases Fin.eq_castSucc_or_eq_last y with ⟨j, rfl⟩ | rfl
          · have hj_mem : j.castSucc ∈ (Finset.univ.erase r₁).image f := by
              rw [heq₁]; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
            obtain ⟨q, _, hfq⟩ := Finset.mem_image.mp hj_mem
            exact ⟨q, hfq⟩
          · exact ⟨r₁, hlast⟩
      rw [← heq₁] at hfr₁_low
      obtain ⟨r₂, hr₂_er, hfr₂⟩ := Finset.mem_image.mp hfr₁_low
      have hr₂_ne : r₂ ≠ r₁ := (Finset.mem_erase.mp hr₂_er).1
      have hfib_pair : fib = {r₁, r₂} := by
        ext r
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hr
          obtain ⟨_, hinj_r⟩ := (hfib_iff r).mp hr
          by_contra hnot
          push_neg at hnot
          have h1 : (r₁ : Fin (e + 2)) ∈ (Finset.univ.erase r : Set (Fin (e + 2))) :=
            Finset.mem_erase.mpr ⟨Ne.symm hnot.1, Finset.mem_univ _⟩
          have h2 : (r₂ : Fin (e + 2)) ∈ (Finset.univ.erase r : Set (Fin (e + 2))) :=
            Finset.mem_erase.mpr ⟨Ne.symm hnot.2, Finset.mem_univ _⟩
          exact hr₂_ne (hinj_r h2 h1 hfr₂)
        · intro hr_or
          rcases hr_or with hr_eq1 | hr_eq2
          · rw [hr_eq1]; exact hr₁
          · rw [hr_eq2]
            simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and]
            intro j
            have hj_mem : j.castSucc ∈ (Finset.univ.erase r₁).image f := by
              rw [heq₁]; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
            obtain ⟨q, hq_er, hfq⟩ := Finset.mem_image.mp hj_mem
            by_cases hqr₂ : q = r₂
            · exact ⟨r₁, hr₂_ne.symm, by rw [← hfr₂, ← hqr₂, hfq]⟩
            · exact ⟨q, hqr₂, hfq⟩
      rw [hfib_pair, Finset.card_pair hr₂_ne.symm]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne_fib, Finset.card_empty]

/-- Boundary facets `(s, r)` in `goodFacets` must have `r = Fin.last (e + 1)`, `s.2 (Fin.last e) = Fin.last e`,
and `(s.1 (Fin.last e)).val = 0`. -/
lemma bdry_goodFacet_must_be_last {e M : ℕ} {ℓ : (Fin (e + 1) → ℕ) → Fin (e + 2)}
    (hℓ : ∀ z, Antitone z → (∀ a, z a ≤ M) → 0 < kuhnCoords (e + 1) M z (ℓ z))
    {s : RawSimplex (e + 1) M} {r : Fin (e + 2)}
    (hs : IsValidKuhn s) (hB : IsBdryFacet s r)
    (hgood : ∀ j : Fin (e + 1), ∃ q : Fin (e + 2), q ≠ r ∧ ℓ (kuhnVert s q) = j.castSucc) :
    r = Fin.last (e + 1) ∧ s.2 (Fin.last e) = Fin.last e ∧ (s.1 (s.2 (Fin.last e))).val = 0 := by
  unfold IsBdryFacet at hB
  by_cases hr0 : r.val = 0
  · rw [if_pos hr0] at hB
    exfalso
    -- First show `s.2 0 = 0` and `(s.1 0).val = M - 1`
    have ha₀_eq0 : s.2 0 = 0 := by
      by_contra hne0
      have hpos : (0 : Fin (e + 1)) < s.2 0 := Fin.pos_iff_ne_zero.mpr hne0
      have hle : s.1 (s.2 0) ≤ s.1 0 := hs.1 (le_of_lt hpos)
      rcases eq_or_lt_of_le hle with heq | hlt
      · have htie := hs.2 0 (s.2 0) hpos heq.symm
        rw [s.2.symm_apply_apply] at htie
        exact Fin.not_lt_zero _ htie
      · have hv_lt : (s.1 (s.2 0)).val < (s.1 0).val := hlt
        have hv0_lt : (s.1 0).val < M := (s.1 0).isLt
        exact hB (by omega)
    obtain ⟨q, hqr, hℓq⟩ := hgood 0
    have hq_pos : 0 < q.val := by
      have : q.val ≠ 0 := fun hv => hqr (Fin.ext (hv.trans hr0.symm))
      omega
    have hvq0 : kuhnVert s q 0 = M := by
      unfold kuhnVert
      have hs0 : (s.2.symm 0).val = 0 := by
        have : s.2.symm 0 = 0 := by
          calc s.2.symm 0 = s.2.symm (s.2 0) := by rw [ha₀_eq0]
            _ = 0 := s.2.symm_apply_apply 0
        rw [this]; rfl
      simp only [hs0, hq_pos, ↓reduceIte]
      have hM_lt := (s.1 0).isLt
      rw [ha₀_eq0] at hB
      omega
    have hcoord0 : kuhnCoords (e + 1) M (kuhnVert s q) 0 = 0 := by
      unfold kuhnCoords zExt
      simp [hvq0]
    have hpos_coord := hℓ (kuhnVert s q) (kuhnVert_antitone hs q) (kuhnVert_le_M s q)
    have h0_eq : (0 : Fin (e + 1)).castSucc = (0 : Fin (e + 2)) := rfl
    rw [hℓq, h0_eq, hcoord0] at hpos_coord
    omega
  · rw [if_neg hr0] at hB
    by_cases hre : r.val ≤ e
    · rw [dif_pos hre] at hB
      exfalso
      rcases hB with ⟨hlt_a, heq_v⟩
      let a₁ := s.2 ⟨r.val - 1, by omega⟩
      let a₂ := s.2 ⟨r.val, by omega⟩
      have ha₂_succ : a₂.val = a₁.val + 1 := by
        have hlt_val : a₁.val < a₂.val := hlt_a
        by_contra hne_succ
        let c : Fin (e + 1) := ⟨a₁.val + 1, by have := a₂.isLt; omega⟩
        have hc1 : a₁ < c := by show a₁.val < a₁.val + 1; omega
        have hc2 : c < a₂ := by show a₁.val + 1 < a₂.val; omega
        have hv_c1 : s.1 c = s.1 a₁ := le_antisymm (hs.1 (le_of_lt hc1)) (heq_v ▸ hs.1 (le_of_lt hc2))
        have htie1 := hs.2 a₁ c hc1 hv_c1.symm
        have htie2 := hs.2 c a₂ hc2 (hv_c1.trans heq_v)
        have hs1 : s.2.symm a₁ = ⟨r.val - 1, by omega⟩ := s.2.symm_apply_apply _
        have hs2 : s.2.symm a₂ = ⟨r.val, by omega⟩ := s.2.symm_apply_apply _
        rw [hs1] at htie1; rw [hs2] at htie2
        have hv1 : r.val - 1 < (s.2.symm c).val := htie1
        have hv2 : (s.2.symm c).val < r.val := htie2
        omega
      obtain ⟨q, hqr, hℓq⟩ := hgood a₂
      have hqv_ne : q.val ≠ r.val := fun hv => hqr (Fin.ext hv)
      have hv_eq_q : kuhnVert s q a₁ = kuhnVert s q a₂ := by
        unfold kuhnVert
        have hs1 : (s.2.symm a₁).val = r.val - 1 := by rw [s.2.symm_apply_apply]
        have hs2 : (s.2.symm a₂).val = r.val := by rw [s.2.symm_apply_apply]
        have hr_pos : 0 < r.val := Nat.pos_of_ne_zero hr0
        rw [heq_v]
        by_cases hlt_q : q.val < r.val
        · have hc1 : ¬ ((s.2.symm a₁).val < q.val) := by rw [hs1]; omega
          have hc2 : ¬ ((s.2.symm a₂).val < q.val) := by rw [hs2]; omega
          rw [if_neg hc1, if_neg hc2]
        · have hc1 : (s.2.symm a₁).val < q.val := by rw [hs1]; omega
          have hc2 : (s.2.symm a₂).val < q.val := by rw [hs2]; omega
          rw [if_pos hc1, if_pos hc2]
      have hcoord_a₂ : kuhnCoords (e + 1) M (kuhnVert s q) a₂.castSucc = 0 := by
        unfold kuhnCoords zExt
        have ha₂_pos : a₂.val ≠ 0 := by omega
        have ha₂_p1_pos : a₂.val + 1 ≠ 0 := by omega
        have hlt1 : a₂.val - 1 < e + 1 := by have := a₂.isLt; omega
        have hlt2 : a₂.val < e + 1 := a₂.isLt
        change (if a₂.val = 0 then M else if h : a₂.val - 1 < e + 1 then kuhnVert s q ⟨a₂.val - 1, h⟩ else 0) -
          (if a₂.val + 1 = 0 then M else if h : a₂.val < e + 1 then kuhnVert s q ⟨a₂.val, h⟩ else 0) = 0
        rw [if_neg ha₂_pos, dif_pos hlt1, if_neg ha₂_p1_pos, dif_pos hlt2]
        have ha₁_fin : (⟨a₂.val - 1, hlt1⟩ : Fin (e + 1)) = a₁ := by ext; dsimp; omega
        have ha₂_fin : (⟨a₂.val, hlt2⟩ : Fin (e + 1)) = a₂ := by ext; rfl
        rw [ha₁_fin, ha₂_fin, hv_eq_q, Nat.sub_self]
      have hpos_coord := hℓ (kuhnVert s q) (kuhnVert_antitone hs q) (kuhnVert_le_M s q)
      rw [hℓq, hcoord_a₂] at hpos_coord
      omega
    · rw [dif_neg hre] at hB
      have hr_last : r = Fin.last (e + 1) := by
        have := r.isLt; ext; simp; omega
      have hv_zero : (s.1 (s.2 (Fin.last e))).val = 0 := by omega
      have haL_last : s.2 (Fin.last e) = Fin.last e := by
        by_contra hne_last
        have hlt : s.2 (Fin.last e) < Fin.last e := lt_of_le_of_ne (Fin.le_last _) hne_last
        have hle : s.1 (Fin.last e) ≤ s.1 (s.2 (Fin.last e)) := hs.1 (le_of_lt hlt)
        rcases eq_or_lt_of_le hle with heq | hstrict
        · have htie := hs.2 (s.2 (Fin.last e)) (Fin.last e) hlt heq.symm
          rw [s.2.symm_apply_apply] at htie
          exact not_lt_of_ge (Fin.le_last _) htie
        · have : (s.1 (Fin.last e)).val < 0 := by
            have hv : (s.1 (Fin.last e)).val < (s.1 (s.2 (Fin.last e))).val := hstrict
            omega
          omega
      exact ⟨hr_last, haL_last, hv_zero⟩

/-- Extension of `RawSimplex e M` to the `z_last = 0` boundary of `RawSimplex (e + 1) M`. -/
def extRawSimplex {e M : ℕ} (hM : 1 ≤ M) (s' : RawSimplex e M) : RawSimplex (e + 1) M :=
  (fun a => if h : a.val < e then s'.1 ⟨a.val, h⟩ else ⟨0, hM⟩,
   { toFun := fun t => if h : t.val < e then (s'.2 ⟨t.val, h⟩).castSucc else Fin.last e
     invFun := fun t => if h : t.val < e then (s'.2.symm ⟨t.val, h⟩).castSucc else Fin.last e
     left_inv := fun t => by
       by_cases ht : t.val < e
       · simp [ht]
       · have hlast : t = Fin.last e := by have := t.isLt; ext; simp; omega
         subst hlast; simp
     right_inv := fun t => by
       by_cases ht : t.val < e
       · simp [ht]
       · have hlast : t = Fin.last e := by have := t.isLt; ext; simp; omega
         subst hlast; simp })

/-- Discrete Kuhn Lemma: odd number of fully-labeled Kuhn `d`-simplices. -/
lemma discrete_kuhn_odd (d M : ℕ) (hM : 1 ≤ M) :
    ∀ (ℓ : (Fin d → ℕ) → Fin (d + 1)),
      (∀ z : Fin d → ℕ, Antitone z → (∀ a, z a ≤ M) → 0 < kuhnCoords d M z (ℓ z)) →
      Odd ((kuhnFinset d M).filter
        (fun s => Function.Surjective (fun r => ℓ (kuhnVert s r)))).card := by
  induction d with
  | zero =>
    intro ℓ _
    let s₀ : RawSimplex 0 M := (Fin.elim0, Equiv.refl (Fin 0))
    have huniq : (kuhnFinset 0 M).filter
        (fun s => Function.Surjective (fun r => ℓ (kuhnVert s r))) = {s₀} := by
      ext s
      simp only [Finset.mem_filter, mem_kuhnFinset, Finset.mem_singleton]
      constructor
      · intro _
        refine Prod.ext (funext fun a => Fin.elim0 a) (Equiv.ext fun a => Fin.elim0 a)
      · rintro rfl
        refine ⟨⟨fun a => Fin.elim0 a, fun a => Fin.elim0 a⟩, fun y => ?_⟩
        refine ⟨0, Fin.ext ?_⟩
        have hy := y.isLt
        have h0 := (ℓ (kuhnVert s₀ 0)).isLt
        omega
    rw [huniq, Finset.card_singleton]
    exact ⟨0, rfl⟩
  | succ e ih =>
    intro ℓ hℓ
    let fullSet := (kuhnFinset (e + 1) M).filter
      (fun s => Function.Surjective (fun r => ℓ (kuhnVert s r)))
    let goodFacets : Finset (RawSimplex (e + 1) M × Fin (e + 2)) :=
      ((kuhnFinset (e + 1) M) ×ˢ Finset.univ).filter
        (fun sr => ∀ j : Fin (e + 1), ∃ q : Fin (e + 2), q ≠ sr.2 ∧ ℓ (kuhnVert sr.1 q) = j.castSucc)
    -- 1. Relate `goodFacets.card % 2` to `fullSet.card % 2`
    have hmod_eq : goodFacets.card % 2 = fullSet.card % 2 := by
      have hsum_card : goodFacets.card = ∑ s ∈ kuhnFinset (e + 1) M,
          (Finset.univ.filter (fun r : Fin (e + 2) =>
            ∀ j : Fin (e + 1), ∃ q : Fin (e + 2), q ≠ r ∧ ℓ (kuhnVert s q) = j.castSucc)).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.sum_filter, Finset.card_eq_sum_ones]
      have hfull_card : fullSet.card = ∑ s ∈ kuhnFinset (e + 1) M,
          if Function.Surjective (fun r => ℓ (kuhnVert s r)) then 1 else 0 := by
        dsimp [fullSet]
        rw [Finset.card_filter]
      rw [hsum_card, hfull_card, Finset.sum_nat_mod, Finset.sum_nat_mod]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      have hfib := fiber_goodFacet_card_mod2 (fun q => ℓ (kuhnVert s q))
      rw [hfib]
      split_ifs <;> rfl
    -- 2. Split `goodFacets` into boundary and interior
    let goodBdry := goodFacets.filter (fun sr => IsBdryFacet sr.1 sr.2)
    let goodInt := goodFacets.filter (fun sr => ¬ IsBdryFacet sr.1 sr.2)
    have hsplit : goodFacets.card = goodBdry.card + goodInt.card := by
      have hdisj : Disjoint goodBdry goodInt := by
        rw [Finset.disjoint_left]
        intro sr h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hunion : goodBdry ∪ goodInt = goodFacets := by
        ext sr
        simp only [goodBdry, goodInt, Finset.mem_union, Finset.mem_filter]
        by_cases h : IsBdryFacet sr.1 sr.2 <;> simp [h]
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    -- 3. `Even goodInt.card` via `kuhnPartner`
    have heven_int : Even goodInt.card := by
      refine even_card_of_fpf_involution goodInt kuhnPartner ?_ ?_ ?_
      · intro sr hsr
        obtain ⟨hfg, hnotB⟩ := Finset.mem_filter.mp hsr
        obtain ⟨hprod, hgood⟩ := Finset.mem_filter.mp hfg
        have hs : IsValidKuhn sr.1 := mem_kuhnFinset.mp (Finset.mem_product.mp hprod).1
        obtain ⟨hs', hnotB', _, _⟩ := kuhnPartner_valid_and_invol hs hnotB
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, hnotB'⟩
        · exact Finset.mem_product.mpr ⟨mem_kuhnFinset.mpr hs', Finset.mem_univ _⟩
        · intro j
          obtain ⟨q, hqr, hℓq⟩ := hgood j
          -- Use `kuhnPartner_same_facet_verts` applied to `kuhnPartner sr`!
          obtain ⟨_, _, hinvol, _⟩ := kuhnPartner_valid_and_invol hs hnotB
          have hq_ne : q ≠ (kuhnPartner (kuhnPartner sr)).2 := by rw [hinvol]; exact hqr
          obtain ⟨q', hq'_ne, hveq⟩ := kuhnPartner_same_facet_verts hs' hnotB' q hq_ne
          rw [hinvol] at hveq
          exact ⟨q', hq'_ne, by rw [← hveq, hℓq]⟩
      · intro sr hsr
        obtain ⟨hfg, hnotB⟩ := Finset.mem_filter.mp hsr
        have hs : IsValidKuhn sr.1 :=
          mem_kuhnFinset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hfg).1).1
        exact (kuhnPartner_valid_and_invol hs hnotB).2.2.1
      · intro sr hsr
        obtain ⟨hfg, hnotB⟩ := Finset.mem_filter.mp hsr
        have hs : IsValidKuhn sr.1 :=
          mem_kuhnFinset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hfg).1).1
        exact (kuhnPartner_valid_and_invol hs hnotB).2.2.2
    -- 4. Biject `goodBdry` with lower-dimensional fully-labeled simplices
    let z_pad : (Fin e → ℕ) → (Fin (e + 1) → ℕ) :=
      fun z' a => if h : a.val < e then z' ⟨a.val, h⟩ else 0
    let ℓ' : (Fin e → ℕ) → Fin (e + 1) := fun z' =>
      if h : (ℓ (z_pad z')).val < e + 1 then ⟨(ℓ (z_pad z')).val, h⟩ else ⟨0, by omega⟩
    have hz_pad_anti : ∀ {z'}, Antitone z' → Antitone (z_pad z') := by
      intro z' hz' a b hab
      dsimp [z_pad]
      by_cases ha : a.val < e <;> by_cases hb : b.val < e <;> simp only [ha, hb, ↓reduceDIte]
      · exact hz' (show (⟨a.val, ha⟩ : Fin e) ≤ ⟨b.val, hb⟩ from hab)
      · exact Nat.zero_le _
      · have hab_val : a.val ≤ b.val := hab
        omega
      · exact le_rfl
    have hz_pad_le : ∀ {z'}, (∀ a, z' a ≤ M) → ∀ a, z_pad z' a ≤ M := by
      intro z' hle a; dsimp [z_pad]; split_ifs with ha; exact hle ⟨a.val, ha⟩; exact Nat.zero_le M
    have hpad_coords_last : ∀ z', kuhnCoords (e + 1) M (z_pad z') (Fin.last (e + 1)) = 0 := by
      intro z'
      unfold kuhnCoords zExt
      have h1 : e + 1 ≠ 0 := by omega
      have h2 : e < e + 1 := by omega
      have h3 : ¬ (e + 1 < e + 1) := by omega
      simp only [Fin.val_last, h1, ↓reduceIte, Nat.add_sub_cancel, h2, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, h3]
      dsimp [z_pad]
      simp
    have hpad_coords_cast : ∀ z' (j : Fin (e + 1)),
        kuhnCoords (e + 1) M (z_pad z') j.castSucc = kuhnCoords e M z' j := by
      intro z' j
      unfold kuhnCoords zExt
      have hj_lt : j.val < e + 1 := j.isLt
      by_cases hj0 : j.val = 0
      · simp only [Fin.coe_castSucc, hj0, ↓reduceIte, Nat.zero_add, Nat.add_eq_zero_iff,
          one_ne_zero, and_false, Nat.sub_self]
        dsimp [z_pad]
        by_cases he0 : 0 < e <;> simp [he0]
      · have hjm1_e1 : j.val - 1 < e + 1 := by omega
        have hjm1_e : j.val - 1 < e := by omega
        simp only [Fin.coe_castSucc, hj0, ↓reduceIte, hjm1_e1, hjm1_e, hj_lt,
          Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.add_sub_cancel]
        dsimp [z_pad]
        rw [dif_pos hjm1_e]
    have hℓ'_cast : ∀ {z'}, Antitone z' → (∀ a, z' a ≤ M) →
        (ℓ' z').castSucc = ℓ (z_pad z') := by
      intro z' hanti hle
      have hpos := hℓ (z_pad z') (hz_pad_anti hanti) (hz_pad_le hle)
      have hne_last : ℓ (z_pad z') ≠ Fin.last (e + 1) := by
        intro heq
        rw [heq, hpad_coords_last] at hpos
        omega
      have hlt_e1 : (ℓ (z_pad z')).val < e + 1 := by
        have := (ℓ (z_pad z')).isLt
        have : (ℓ (z_pad z')).val ≠ e + 1 := fun hv => hne_last (Fin.ext hv)
        omega
      dsimp [ℓ']
      rw [dif_pos hlt_e1]
      ext; rfl
    have hℓ'_valid : ∀ z' : Fin e → ℕ, Antitone z' → (∀ a, z' a ≤ M) →
        0 < kuhnCoords e M z' (ℓ' z') := by
      intro z' hanti hle
      rw [← hpad_coords_cast, hℓ'_cast hanti hle]
      exact hℓ (z_pad z') (hz_pad_anti hanti) (hz_pad_le hle)
    let fullSub := (kuhnFinset e M).filter
      (fun s' => Function.Surjective (fun q => ℓ' (kuhnVert s' q)))
    have hbij_bdry : goodBdry.card = fullSub.card := by
      symm
      refine Finset.card_bij
        (fun s' _ => (extRawSimplex hM s', Fin.last (e + 1)))
        (?_) (?_) (?_)
      · intro s' hs'
        obtain ⟨hs'_mem, hsurj'⟩ := Finset.mem_filter.mp hs'
        have hs'_val : IsValidKuhn s' := mem_kuhnFinset.mp hs'_mem
        let s := extRawSimplex hM s'
        have hs_val : IsValidKuhn s := by
          refine ⟨?_, ?_⟩
          · intro a b hab
            dsimp [s, extRawSimplex]
            by_cases ha : a.val < e <;> by_cases hb : b.val < e <;>
              simp only [ha, hb, ↓reduceDIte]
            · exact hs'_val.1 (show (⟨a.val, ha⟩ : Fin e) ≤ ⟨b.val, hb⟩ from hab)
            · show 0 ≤ (s'.1 ⟨a.val, ha⟩).val
              exact Nat.zero_le _
            · have hab_val : a.val ≤ b.val := hab
              omega
            · exact le_rfl
          · intro a b hlt heq
            dsimp [s, extRawSimplex] at heq
            by_cases ha : a.val < e <;> by_cases hb : b.val < e <;>
              simp only [ha, hb, ↓reduceDIte] at heq
            · have htie := hs'_val.2 ⟨a.val, ha⟩ ⟨b.val, hb⟩ hlt heq
              change (if h : a.val < e then (s'.2.symm ⟨a.val, h⟩).castSucc else Fin.last e) <
                (if h : b.val < e then (s'.2.symm ⟨b.val, h⟩).castSucc else Fin.last e)
              rw [dif_pos ha, dif_pos hb]
              exact htie
            · change (if h : a.val < e then (s'.2.symm ⟨a.val, h⟩).castSucc else Fin.last e) <
                (if h : b.val < e then (s'.2.symm ⟨b.val, h⟩).castSucc else Fin.last e)
              rw [dif_pos ha, dif_neg hb]
              exact Fin.castSucc_lt_last _
            · have hlt_val : a.val < b.val := hlt
              omega
            · have ha_last : a = Fin.last e := by have := a.isLt; ext; simp; omega
              have hb_last : b = Fin.last e := by have := b.isLt; ext; simp; omega
              rw [ha_last, hb_last] at hlt
              exact absurd hlt (lt_irrefl _)
        have hs_vert : ∀ q : Fin (e + 1), kuhnVert s q.castSucc = z_pad (kuhnVert s' q) := by
          intro q
          ext a
          by_cases ha : a.val < e
          · have h1 : (s.1 a).val = (s'.1 ⟨a.val, ha⟩).val := by dsimp [s, extRawSimplex]; rw [dif_pos ha]
            have h2 : (s.2.symm a).val = (s'.2.symm ⟨a.val, ha⟩).val := by
              change (if h : a.val < e then (s'.2.symm ⟨a.val, h⟩).castSucc else Fin.last e).val = _
              rw [dif_pos ha]; rfl
            have h3 : z_pad (kuhnVert s' q) a = kuhnVert s' q ⟨a.val, ha⟩ := dif_pos ha
            rw [h3]
            unfold kuhnVert
            rw [h1]
            change _ + (if (s.2.symm a).val < q.val then 1 else 0) = _
            split_ifs with c1 c2
            · rfl
            · rw [h2] at c1; omega
            · rw [h2] at c1; omega
            · rfl
          · have h1 : (s.1 a).val = 0 := by dsimp [s, extRawSimplex]; rw [dif_neg ha]
            have h2 : (s.2.symm a).val = e := by
              change (if h : a.val < e then (s'.2.symm ⟨a.val, h⟩).castSucc else Fin.last e).val = e
              rw [dif_neg ha]; rfl
            have h3 : z_pad (kuhnVert s' q) a = 0 := dif_neg ha
            rw [h3]
            unfold kuhnVert
            rw [h1]
            change 0 + (if (s.2.symm a).val < q.val then 1 else 0) = 0
            have hq_lt := q.isLt
            split_ifs with c1
            · rw [h2] at c1; omega
            · rfl
        have hs_bdry : IsBdryFacet s (Fin.last (e + 1)) := by
          unfold IsBdryFacet
          have h1 : ¬ (Fin.last (e + 1)).val = 0 := by simp
          have h2 : ¬ (Fin.last (e + 1)).val ≤ e := by simp
          rw [if_neg h1, dif_neg h2]
          have hπL : s.2 (Fin.last e) = Fin.last e := by dsimp [s, extRawSimplex]; simp
          rw [hπL]
          dsimp [s, extRawSimplex]; simp
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, hs_bdry⟩
        · exact Finset.mem_product.mpr ⟨mem_kuhnFinset.mpr hs_val, Finset.mem_univ _⟩
        · intro j
          obtain ⟨q, hq⟩ := hsurj' j
          dsimp at hq
          refine ⟨q.castSucc, Fin.castSucc_ne_last q, ?_⟩
          rw [hs_vert q, ← hℓ'_cast (kuhnVert_antitone hs'_val q) (kuhnVert_le_M s' q), hq]
      · intro s₁ _ s₂ _ heq
        have hs_eq : extRawSimplex hM s₁ = extRawSimplex hM s₂ := congrArg Prod.fst heq
        refine Prod.ext (funext fun a => ?_) (Equiv.ext fun t => ?_)
        · have hv := congrFun (congrArg Prod.fst hs_eq) a.castSucc
          dsimp [extRawSimplex] at hv
          simpa [a.isLt] using hv
        · have hp := congrFun (congrArg DFunLike.coe (congrArg Prod.snd hs_eq)) t.castSucc
          dsimp [extRawSimplex] at hp
          simp only [t.isLt, ↓reduceDIte] at hp
          exact Fin.castSucc_injective e hp
      · intro sr hsr
        obtain ⟨hfg, hB⟩ := Finset.mem_filter.mp hsr
        obtain ⟨hprod, hgood⟩ := Finset.mem_filter.mp hfg
        have hs : IsValidKuhn sr.1 := mem_kuhnFinset.mp (Finset.mem_product.mp hprod).1
        obtain ⟨hr_last, hπL, hv0⟩ := bdry_goodFacet_must_be_last hℓ hs hB hgood
        rw [hπL] at hv0
        have hπ_lt : ∀ t : Fin e, (sr.1.2 t.castSucc).val < e := by
          intro t
          have hne : sr.1.2 t.castSucc ≠ Fin.last e := fun h =>
            Fin.castSucc_ne_last t (sr.1.2.injective (h.trans hπL.symm))
          have := (sr.1.2 t.castSucc).isLt
          have : (sr.1.2 t.castSucc).val ≠ e := fun hv => hne (Fin.ext hv)
          omega
        have hπsymm_lt : ∀ t : Fin e, (sr.1.2.symm t.castSucc).val < e := by
          intro t
          have hsymmL : sr.1.2.symm (Fin.last e) = Fin.last e := by
            calc sr.1.2.symm (Fin.last e) = sr.1.2.symm (sr.1.2 (Fin.last e)) := by rw [hπL]
              _ = Fin.last e := sr.1.2.symm_apply_apply _
          have hne : sr.1.2.symm t.castSucc ≠ Fin.last e := fun h =>
            Fin.castSucc_ne_last t (sr.1.2.symm.injective (h.trans hsymmL.symm))
          have := (sr.1.2.symm t.castSucc).isLt
          have : (sr.1.2.symm t.castSucc).val ≠ e := fun hv => hne (Fin.ext hv)
          omega
        let s' : RawSimplex e M :=
          (fun a => sr.1.1 a.castSucc,
           { toFun := fun t => ⟨(sr.1.2 t.castSucc).val, hπ_lt t⟩
             invFun := fun t => ⟨(sr.1.2.symm t.castSucc).val, hπsymm_lt t⟩
             left_inv := fun t => by
               ext; dsimp
               have hc : (⟨(sr.1.2 t.castSucc).val, hπ_lt t⟩ : Fin e).castSucc = sr.1.2 t.castSucc := by
                 ext; rfl
               have h1 := congrArg (fun x => (sr.1.2.symm x).val) hc
               dsimp at h1
               rw [h1, sr.1.2.symm_apply_apply]; rfl
             right_inv := fun t => by
               ext; dsimp
               have hc : (⟨(sr.1.2.symm t.castSucc).val, hπsymm_lt t⟩ : Fin e).castSucc =
                   sr.1.2.symm t.castSucc := by ext; rfl
               have h1 := congrArg (fun x => (sr.1.2 x).val) hc
               dsimp at h1
               rw [h1, sr.1.2.apply_symm_apply]; rfl })
        have hext_eq : extRawSimplex hM s' = sr.1 := by
          refine Prod.ext (funext fun a => ?_) (Equiv.ext fun t => ?_)
          · dsimp [extRawSimplex, s']
            split_ifs with ha
            · rfl
            · have haL : a = Fin.last e := by have := a.isLt; ext; simp; omega
              subst haL; ext; exact hv0.symm
          · dsimp [extRawSimplex, s']
            split_ifs with ht
            · ext; rfl
            · have htL : t = Fin.last e := by have := t.isLt; ext; simp; omega
              subst htL; exact hπL.symm
        have hs'_val : IsValidKuhn s' := by
          refine ⟨fun a b hab => hs.1 (Fin.castSucc_le_castSucc_iff.mpr hab), fun a b hlt heq => ?_⟩
          have htie := hs.2 a.castSucc b.castSucc hlt heq
          exact htie
        have hs_vert : ∀ q : Fin (e + 1), kuhnVert sr.1 q.castSucc = z_pad (kuhnVert s' q) := by
          intro q
          rw [← hext_eq]
          ext a
          by_cases ha : a.val < e
          · have h1 : ((extRawSimplex hM s').1 a).val = (s'.1 ⟨a.val, ha⟩).val := by
              dsimp [extRawSimplex]; rw [dif_pos ha]
            have h2 : ((extRawSimplex hM s').2.symm a).val = (s'.2.symm ⟨a.val, ha⟩).val := by
              change (if h : a.val < e then (s'.2.symm ⟨a.val, h⟩).castSucc else Fin.last e).val = _
              rw [dif_pos ha]; rfl
            have h3 : z_pad (kuhnVert s' q) a = kuhnVert s' q ⟨a.val, ha⟩ := dif_pos ha
            rw [h3]
            unfold kuhnVert
            rw [h1]
            change _ + (if ((extRawSimplex hM s').2.symm a).val < q.val then 1 else 0) = _
            split_ifs with c1 c2
            · rfl
            · rw [h2] at c1; omega
            · rw [h2] at c1; omega
            · rfl
          · have h1 : ((extRawSimplex hM s').1 a).val = 0 := by
              dsimp [extRawSimplex]; rw [dif_neg ha]
            have h2 : ((extRawSimplex hM s').2.symm a).val = e := by
              change (if h : a.val < e then (s'.2.symm ⟨a.val, h⟩).castSucc else Fin.last e).val = e
              rw [dif_neg ha]; rfl
            have h3 : z_pad (kuhnVert s' q) a = 0 := dif_neg ha
            rw [h3]
            unfold kuhnVert
            rw [h1]
            change 0 + (if ((extRawSimplex hM s').2.symm a).val < q.val then 1 else 0) = 0
            have hq_lt := q.isLt
            split_ifs with c1
            · rw [h2] at c1; omega
            · rfl
        refine ⟨s', Finset.mem_filter.mpr ⟨mem_kuhnFinset.mpr hs'_val, ?_⟩,
          Prod.ext hext_eq hr_last.symm⟩
        intro j
        obtain ⟨q, hqr, hℓq⟩ := hgood j
        rw [hr_last] at hqr
        rcases Fin.eq_castSucc_or_eq_last q with ⟨q₀, rfl⟩ | rfl
        · refine ⟨q₀, ?_⟩
          have hc := hℓ'_cast (kuhnVert_antitone hs'_val q₀) (kuhnVert_le_M s' q₀)
          rw [← hs_vert q₀, hℓq] at hc
          exact Fin.castSucc_injective (e + 1) hc
        · exact absurd rfl hqr
    have hodd_sub : Odd fullSub.card := ih ℓ' hℓ'_valid
    rw [← hbij_bdry] at hodd_sub
    rcases hodd_sub with ⟨k₁, hk₁⟩
    rcases heven_int with ⟨k₂, hk₂⟩
    have hgf_mod1 : goodFacets.card % 2 = 1 := by omega
    rw [hmod_eq] at hgf_mod1
    exact Nat.odd_iff.mpr hgf_mod1

/-- Lemma 2 (KKM Lemma on `stdSimplex ℝ (Fin n)`). -/
theorem kkm_stdSimplex (n : ℕ) (hn : 1 ≤ n) (F : Fin n → Set (Fin n → ℝ))
    (hClosed : ∀ i, IsClosed (F i))
    (hFace : ∀ T : Finset (Fin n), T.Nonempty → simplexFace T ⊆ ⋃ i ∈ T, F i) :
    (⋂ i : Fin n, F i).Nonempty := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = d + 1 := ⟨n - 1, by omega⟩
  -- For each `t : ℕ`, apply `discrete_kuhn_odd` at grid resolution `M = t + 1`
  have hex_seq : ∀ t : ℕ, ∃ w₀ ∈ stdSimplex ℝ (Fin (d + 1)),
      ∀ i : Fin (d + 1), ∃ w_i ∈ F i, ∀ j : Fin (d + 1), |w_i j - w₀ j| ≤ 1 / ((t : ℝ) + 1) := by
    intro t
    let M : ℕ := t + 1
    have hM : 1 ≤ M := by omega
    have hM_pos : (0 : ℝ) < (M : ℝ) := by positivity
    let pt : (Fin d → ℕ) → (Fin (d + 1) → ℝ) :=
      fun z i => (kuhnCoords d M z i : ℝ) / (M : ℝ)
    have hpt_simplex : ∀ {z : Fin d → ℕ}, Antitone z → (∀ a, z a ≤ M) →
        pt z ∈ stdSimplex ℝ (Fin (d + 1)) := by
      intro z hanti hle
      refine ⟨fun i => by positivity, ?_⟩
      dsimp [pt]
      rw [← Finset.sum_div, sum_kuhnCoords_real hanti hle, div_self (ne_of_gt hM_pos)]
    have hex_label : ∀ z : Fin d → ℕ, ∃ idx : Fin (d + 1),
        Antitone z → (∀ a, z a ≤ M) → 0 < kuhnCoords d M z idx ∧ pt z ∈ F idx := by
      intro z
      by_cases hz : Antitone z ∧ ∀ a, z a ≤ M
      · let T : Finset (Fin (d + 1)) := Finset.univ.filter (fun i => 0 < kuhnCoords d M z i)
        have hT_ne : T.Nonempty := by
          by_contra hemp
          rw [Finset.not_nonempty_iff_eq_empty] at hemp
          have hall0 : ∀ i : Fin (d + 1), kuhnCoords d M z i = 0 := by
            intro i
            by_contra hpos
            have : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hpos⟩
            rw [hemp] at this; exact Finset.notMem_empty i this
          have hsum := sum_kuhnCoords_real hz.1 hz.2
          simp_rw [hall0] at hsum
          simp at hsum
          linarith
        have hmem_face : pt z ∈ simplexFace T := by
          refine ⟨hpt_simplex hz.1 hz.2, fun i hi => ?_⟩
          have hc0 : kuhnCoords d M z i = 0 := by
            by_contra hnz
            exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hnz⟩)
          simp [pt, hc0]
        have hmem_union := hFace T hT_ne hmem_face
        simp only [Set.mem_iUnion, exists_prop] at hmem_union
        obtain ⟨idx, hidx_T, hidx_F⟩ := hmem_union
        exact ⟨idx, fun _ _ => ⟨(Finset.mem_filter.mp hidx_T).2, hidx_F⟩⟩
      · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hz⟩
    choose ℓ hℓ using hex_label
    have hodd := discrete_kuhn_odd d M hM ℓ (fun z h1 h2 => (hℓ z h1 h2).1)
    have hne_full : ((kuhnFinset d M).filter
        (fun s => Function.Surjective (fun r => ℓ (kuhnVert s r)))).Nonempty := by
      rw [← Finset.card_pos]
      rcases hodd with ⟨k, hk⟩; omega
    obtain ⟨s, hs_mem⟩ := hne_full
    obtain ⟨hs_kuhn, hsurj⟩ := Finset.mem_filter.mp hs_mem
    have hs_val : IsValidKuhn s := mem_kuhnFinset.mp hs_kuhn
    let w₀ := pt (kuhnVert s 0)
    refine ⟨w₀, hpt_simplex (kuhnVert_antitone hs_val 0) (kuhnVert_le_M s 0), fun i => ?_⟩
    obtain ⟨r, hr⟩ := hsurj i
    refine ⟨pt (kuhnVert s r), ?_, fun j => ?_⟩
    · rw [← hr]
      exact (hℓ (kuhnVert s r) (kuhnVert_antitone hs_val r) (kuhnVert_le_M s r)).2
    · dsimp [pt, w₀]
      rw [← sub_div, abs_div, abs_of_pos hM_pos]
      have hcast_M : (M : ℝ) = (t : ℝ) + 1 := by dsimp [M]; push_cast; ring
      rw [hcast_M]
      refine div_le_div_of_nonneg_right ?_ (le_of_lt (hcast_M ▸ hM_pos))
      have hc_r : (kuhnCoords d M (kuhnVert s r) j : ℝ) =
          (zExt d M (kuhnVert s r) j.val : ℝ) - (zExt d M (kuhnVert s r) (j.val + 1) : ℝ) :=
        Nat.cast_sub (zExt_step_le (kuhnVert_antitone hs_val r) (kuhnVert_le_M s r) j.val)
      have hc_0 : (kuhnCoords d M (kuhnVert s 0) j : ℝ) =
          (zExt d M (kuhnVert s 0) j.val : ℝ) - (zExt d M (kuhnVert s 0) (j.val + 1) : ℝ) :=
        Nat.cast_sub (zExt_step_le (kuhnVert_antitone hs_val 0) (kuhnVert_le_M s 0) j.val)
      have hz_diff : ∀ k : ℕ, (zExt d M (kuhnVert s 0) k : ℝ) ≤ (zExt d M (kuhnVert s r) k : ℝ) ∧
          (zExt d M (kuhnVert s r) k : ℝ) ≤ (zExt d M (kuhnVert s 0) k : ℝ) + 1 := by
        intro k
        unfold zExt
        split_ifs with hk0 hkd
        · constructor <;> linarith
        · unfold kuhnVert
          simp only [Fin.val_zero, not_lt_zero', ↓reduceIte, add_zero]
          split_ifs <;> constructor <;> norm_cast <;> omega
        · constructor <;> norm_num
      obtain ⟨hl1, hu1⟩ := hz_diff j.val
      obtain ⟨hl2, hu2⟩ := hz_diff (j.val + 1)
      rw [hc_r, hc_0, abs_le]
      constructor <;> linarith
  choose wt hwt_simp hwt_close using hex_seq
  obtain ⟨w_star, hw_star_simp, φ, hφ_mono, hφ_tend⟩ :=
    (isCompact_stdSimplex ℝ (Fin (d + 1))).tendsto_subseq hwt_simp
  refine ⟨w_star, Set.mem_iInter.mpr fun i => ?_⟩
  choose wit hwit_F hwit_dist using fun k => hwt_close (φ k) i
  have hwit_tend : Tendsto wit atTop (𝓝 w_star) := by
    rw [tendsto_pi_nhds]
    intro j
    have hdiff_tend : Tendsto (fun k => wit k j - wt (φ k) j) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun k => 1 / ((φ k : ℝ) + 1)) (fun k => ?_) ?_
      · rw [Real.norm_eq_abs]
        exact hwit_dist k j
      · have h1 : Tendsto (fun k : ℕ => ((φ k : ℝ) + 1)) atTop atTop :=
          (tendsto_natCast_atTop_atTop.comp hφ_mono.tendsto_atTop).atTop_add tendsto_const_nhds
        simp only [one_div]
        exact tendsto_inv_atTop_zero.comp h1
    have hwt_j : Tendsto (fun k => wt (φ k) j) atTop (𝓝 (w_star j)) :=
      (continuous_apply j).continuousAt.tendsto.comp hφ_tend
    have hsum := hdiff_tend.add hwt_j
    simpa using hsum
  exact (hClosed i).mem_of_tendsto hwit_tend (Eventually.of_forall hwit_F)

end KuhnKKM

/-! ### §3.3 & §3.4: Prefix Perturbation and Price Interlacing (`Lemma 5`) -/

section PrefixAndInterlacing

def validSubs {α : Type*} [DecidableEq α] (S : Finset α) (c : ℕ) : Finset (Finset α) :=
  S.powerset.filter (fun T => T.card ≤ c)

lemma empty_mem_validSubs {α : Type*} [DecidableEq α] (S : Finset α) (c : ℕ) :
    ∅ ∈ validSubs S c := by
  simp [validSubs]

noncomputable def maxSubSum {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ) (c : ℕ) : ℝ :=
  (validSubs S c).sup' ⟨∅, empty_mem_validSubs S c⟩ (fun T => ∑ x ∈ T, f x)

lemma le_maxSubSum {α : Type*} [DecidableEq α] {S T : Finset α} {c : ℕ} (hTS : T ⊆ S)
    (hc : T.card ≤ c) (f : α → ℝ) :
    ∑ x ∈ T, f x ≤ maxSubSum S f c := by
  unfold maxSubSum
  refine Finset.le_sup' (fun U : Finset α => ∑ x ∈ U, f x) ?_
  simp [validSubs, hTS, hc]

lemma maxSubSum_nonneg {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ) (c : ℕ) :
    0 ≤ maxSubSum S f c := by
  simpa using le_maxSubSum (Finset.empty_subset S) (Nat.zero_le c) f

lemma maxSubSum_le_of_bound {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ) (c : ℕ)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x ∈ S, f x ≤ B) :
    maxSubSum S f c ≤ (c : ℝ) * B := by
  unfold maxSubSum
  refine Finset.sup'_le _ _ fun T hT => ?_
  simp only [validSubs, Finset.mem_filter, Finset.mem_powerset] at hT
  calc ∑ x ∈ T, f x
      ≤ ∑ _x ∈ T, B := Finset.sum_le_sum fun x hx => hB x (hT.1 hx)
    _ = (T.card : ℝ) * B := by simp [nsmul_eq_mul]
    _ ≤ (c : ℝ) * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hT.2) hB0

lemma continuous_maxSubSum {m : ℕ} (S : Finset (Fin m)) (c : ℕ)
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    Continuous (fun p : Fin m → ℝ => maxSubSum S (fun g => φ (p g)) c) := by
  unfold maxSubSum
  refine continuous_sup'_apply _ _ _ fun T _ => ?_
  exact continuous_finsetSum _ fun g _ => hφ.comp (continuous_apply g)

lemma maxSubSum_filter_pos {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x) (c : ℕ) :
    maxSubSum S f c = maxSubSum (S.filter (fun x => 0 < f x)) f c := by
  refine le_antisymm ?_ ?_
  · unfold maxSubSum
    refine Finset.sup'_le _ _ fun T hT => ?_
    simp only [validSubs, Finset.mem_filter, Finset.mem_powerset] at hT
    let T' := T.filter (fun x => 0 < f x)
    have hT'_sub : T' ⊆ S.filter (fun x => 0 < f x) :=
      Finset.filter_subset_filter _ hT.1
    have hT'_card : T'.card ≤ c := le_trans (Finset.card_filter_le _ _) hT.2
    have hsum_eq : ∑ x ∈ T, f x = ∑ x ∈ T', f x := by
      rw [← Finset.sum_filter_add_sum_filter_not T (fun x => 0 < f x)]
      have hz : ∑ x ∈ T.filter (fun x => ¬ 0 < f x), f x = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        obtain ⟨hxT, hnot⟩ := Finset.mem_filter.mp hx
        exact le_antisymm (le_of_not_gt hnot) (hf x (hT.1 hxT))
      rw [hz, add_zero]
    rw [hsum_eq]
    exact le_maxSubSum hT'_sub hT'_card f
  · unfold maxSubSum
    refine Finset.sup'_le _ _ fun T hT => ?_
    simp only [validSubs, Finset.mem_filter, Finset.mem_powerset] at hT
    exact le_maxSubSum (Subset.trans hT.1 (Finset.filter_subset _ S)) hT.2 f

lemma maxSubSum_fin_equiv {α : Type*} [DecidableEq α] {k : ℕ}
    (W : Finset α) (e : Fin k ≃ W) (f : α → ℝ) (c : ℕ) :
    maxSubSum W f c = maxSubSum (Finset.univ : Finset (Fin k)) (fun t => f (e t).1) c := by
  refine le_antisymm ?_ ?_
  · unfold maxSubSum
    refine Finset.sup'_le _ _ fun T hT => ?_
    simp only [validSubs, Finset.mem_filter, Finset.mem_powerset] at hT
    let T' : Finset (Fin k) := Finset.univ.filter (fun t => (e t).1 ∈ T)
    have hbij : ∀ (t : Fin k), t ∈ T' → (e t).1 ∈ T := fun _ ht => (Finset.mem_filter.mp ht).2
    have hinj : ∀ t₁ ∈ T', ∀ t₂ ∈ T', (e t₁).1 = (e t₂).1 → t₁ = t₂ :=
      fun _ _ _ _ heq => e.injective (Subtype.ext heq)
    have hsurj : ∀ w ∈ T, ∃ t, ∃ (_ : t ∈ T'), (e t).1 = w := by
      intro w hw
      let t := e.symm ⟨w, hT.1 hw⟩
      have het : e t = ⟨w, hT.1 hw⟩ := e.apply_symm_apply _
      have ht_mem : t ∈ T' := Finset.mem_filter.mpr ⟨Finset.mem_univ t, by rw [het]; exact hw⟩
      exact ⟨t, ht_mem, congrArg Subtype.val het⟩
    have hcard_eq : T'.card = T.card := Finset.card_bij (fun t _ => (e t).1) hbij hinj hsurj
    have hsum_eq : (∑ t ∈ T', f (e t).1) = ∑ w ∈ T, f w :=
      Finset.sum_bij (fun t _ => (e t).1) hbij hinj hsurj (fun _ _ => rfl)
    rw [← hsum_eq]
    exact le_maxSubSum (Finset.subset_univ T') (hcard_eq.trans_le hT.2) (fun t => f (e t).1)
  · unfold maxSubSum
    refine Finset.sup'_le _ _ fun T' hT' => ?_
    simp only [validSubs, Finset.mem_filter, Finset.mem_powerset] at hT'
    let T : Finset α := T'.image (fun t => (e t).1)
    have hT_sub : T ⊆ W := by
      intro w hw
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hw
      exact (e t).2
    have hinj : Set.InjOn (fun t : Fin k => (e t).1) T' :=
      fun _ _ _ _ heq => e.injective (Subtype.ext heq)
    have hcard_T : T.card ≤ c := by
      dsimp [T]
      rw [Finset.card_image_of_injOn hinj]
      exact hT'.2
    have hsum_T : (∑ w ∈ T, f w) = ∑ t ∈ T', f (e t).1 := Finset.sum_image hinj
    rw [← hsum_T]
    exact le_maxSubSum hT_sub hcard_T f

lemma maxSubSum_antitone_fin {k : ℕ} {g : Fin k → ℝ} (hanti : Antitone g)
    (hnn : ∀ t, 0 ≤ g t) (c : ℕ) :
    maxSubSum (Finset.univ : Finset (Fin k)) g c =
      ∑ t ∈ Finset.univ.filter (fun t : Fin k => t.val < c), g t := by
  let L := Finset.univ.filter (fun t : Fin k => t.val < c)
  have hL_card : L.card ≤ c := by
    by_cases hck : c ≤ k
    · have hcard : L.card = c := by
        symm
        rw [← Finset.card_range c]
        refine Finset.card_bij (fun t ht => (⟨t, by rw [Finset.mem_range] at ht; omega⟩ : Fin k))
          (fun t ht => by simp [L, Finset.mem_range.mp ht])
          (fun t₁ _ t₂ _ heq => congrArg Fin.val heq)
          (fun t ht => ⟨t.val, Finset.mem_range.mpr (Finset.mem_filter.mp ht).2, by ext; rfl⟩)
      omega
    · calc L.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
        _ = k := by simp
        _ ≤ c := by omega
  refine le_antisymm ?_ (le_maxSubSum (Finset.subset_univ L) hL_card g)
  unfold maxSubSum
  refine Finset.sup'_le _ _ fun T hT => ?_
  simp only [validSubs, Finset.mem_filter, Finset.mem_powerset] at hT
  by_cases hc0 : c = 0
  · have hT0 : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hc0; rw [hT0]; simp [L]
  · by_cases hck : k ≤ c
    · have hL_univ : L = Finset.univ := by
        ext t; simp [L]; have := t.isLt; omega
      change ∑ x ∈ T, g x ≤ ∑ t ∈ L, g t
      rw [hL_univ]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun t _ _ => hnn t)
    · have hc_pos : 1 ≤ c := by omega
      have hck_lt : c < k := by omega
      let T_in := T.filter (fun t => t.val < c)
      let T_out := T.filter (fun t => ¬ (t.val < c))
      let L_miss := L \ T_in
      have hT_split : ∑ t ∈ T, g t = ∑ t ∈ T_in, g t + ∑ t ∈ T_out, g t :=
        (Finset.sum_filter_add_sum_filter_not T (fun t => t.val < c) g).symm
      have hT_card_split : T_in.card + T_out.card = T.card :=
        Finset.card_filter_add_card_filter_not (s := T) (fun t : Fin k => t.val < c)
      have hTin_sub_L : T_in ⊆ L := by
        intro t ht
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ t, (Finset.mem_filter.mp ht).2⟩
      have hL_card_eq : L.card = c := by
        symm
        rw [← Finset.card_range c]
        refine Finset.card_bij (fun t ht => (⟨t, by rw [Finset.mem_range] at ht; omega⟩ : Fin k))
          (fun t ht => by simp [L, Finset.mem_range.mp ht])
          (fun t₁ _ t₂ _ heq => congrArg Fin.val heq)
          (fun t ht => ⟨t.val, Finset.mem_range.mpr (Finset.mem_filter.mp ht).2, by ext; rfl⟩)
      have hL_split : ∑ t ∈ L, g t = ∑ t ∈ T_in, g t + ∑ t ∈ L_miss, g t := by
        have hdisj : Disjoint T_in L_miss := disjoint_sdiff_self_right
        have hun : T_in ∪ L_miss = L := Finset.union_sdiff_of_subset hTin_sub_L
        rw [← hun, Finset.sum_union hdisj]
      have hL_card_split : T_in.card + L_miss.card = c := by
        have hdisj : Disjoint T_in L_miss := disjoint_sdiff_self_right
        have hun : T_in ∪ L_miss = L := Finset.union_sdiff_of_subset hTin_sub_L
        rw [← hL_card_eq, ← hun, Finset.card_union_of_disjoint hdisj]
      have hout_le_miss : T_out.card ≤ L_miss.card := by omega
      let idx_piv : Fin k := ⟨c - 1, by omega⟩
      have hpiv_nn : 0 ≤ g idx_piv := hnn idx_piv
      have hout_ub : ∑ t ∈ T_out, g t ≤ (T_out.card : ℝ) * g idx_piv := by
        calc ∑ t ∈ T_out, g t
            ≤ ∑ _t ∈ T_out, g idx_piv := Finset.sum_le_sum fun t ht => by
              have hge : ¬ (t.val < c) := (Finset.mem_filter.mp ht).2
              exact hanti (show idx_piv.val ≤ t.val by dsimp [idx_piv]; omega)
          _ = (T_out.card : ℝ) * g idx_piv := by simp [nsmul_eq_mul]
      have hmiss_lb : (L_miss.card : ℝ) * g idx_piv ≤ ∑ t ∈ L_miss, g t := by
        calc (L_miss.card : ℝ) * g idx_piv
            = ∑ _t ∈ L_miss, g idx_piv := by simp [nsmul_eq_mul]
          _ ≤ ∑ t ∈ L_miss, g t := Finset.sum_le_sum fun t ht => by
              have hlt : t.val < c := (Finset.mem_filter.mp (Finset.sdiff_subset ht)).2
              exact hanti (show t.val ≤ idx_piv.val by dsimp [idx_piv]; omega)
      have hmid : (T_out.card : ℝ) * g idx_piv ≤ (L_miss.card : ℝ) * g idx_piv :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hout_le_miss) hpiv_nn
      rw [hT_split, hL_split]
      linarith

def posPrice {m : ℕ} (p : Fin m → ℝ) (g : Fin m) : ℝ := max (p g) 0
def negPrice {m : ℕ} (p : Fin m → ℝ) (g : Fin m) : ℝ := max (- p g) 0

noncomputable def phiPot (n m : ℕ) (p : Fin m → ℝ) (A : Allocation n m) : ℝ :=
  ∑ i : Fin n, ∑ l ∈ Finset.Icc 1 (m / n + 1),
    (maxSubSum (bundle A i) (posPrice p) l + maxSubSum (bundle A i) (negPrice p) l)

noncomputable def C_Phi (n m : ℕ) (v : Fin n → Fin m → ℝ) : ℝ :=
  2 * (n : ℝ) * (((m / n : ℕ) : ℝ) + 1) ^ 2 * M0 v

lemma phiPot_bounds {n m : ℕ} {v : Fin n → Fin m → ℝ} {p : Fin m → ℝ}
    (hp : ∀ g, |p g| ≤ M0 v) (A : Allocation n m) :
    0 ≤ phiPot n m p A ∧ phiPot n m p A ≤ C_Phi n m v := by
  have hM0_nn : 0 ≤ M0 v := le_of_lt (M0_pos v)
  constructor
  · unfold phiPot
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l _ =>
      add_nonneg (maxSubSum_nonneg _ _ _) (maxSubSum_nonneg _ _ _)
  · unfold phiPot C_Phi
    have hpos_le : ∀ g, posPrice p g ≤ M0 v := fun g =>
      max_le (le_trans (le_abs_self _) (hp g)) hM0_nn
    have hneg_le : ∀ g, negPrice p g ≤ M0 v := fun g =>
      max_le (le_trans (neg_le_abs _) (hp g)) hM0_nn
    let B_inner : ℝ := 2 * (((m / n : ℕ) : ℝ) + 1) * M0 v
    have hinner : ∀ i : Fin n,
        (∑ l ∈ Finset.Icc 1 (m / n + 1),
          (maxSubSum (bundle A i) (posPrice p) l + maxSubSum (bundle A i) (negPrice p) l)) ≤
        (((m / n : ℕ) : ℝ) + 1) * B_inner := by
      intro i
      calc ∑ l ∈ Finset.Icc 1 (m / n + 1),
            (maxSubSum (bundle A i) (posPrice p) l + maxSubSum (bundle A i) (negPrice p) l)
          ≤ ∑ _l ∈ Finset.Icc 1 (m / n + 1), B_inner := by
            refine Finset.sum_le_sum fun l hl => ?_
            have hl_ub : (l : ℝ) ≤ ((m / n : ℕ) : ℝ) + 1 := by
              have hle : l ≤ m / n + 1 := (Finset.mem_Icc.mp hl).2
              exact_mod_cast hle
            have h1 := maxSubSum_le_of_bound (bundle A i) (posPrice p) l hM0_nn
              (fun g _ => hpos_le g)
            have h2 := maxSubSum_le_of_bound (bundle A i) (negPrice p) l hM0_nn
              (fun g _ => hneg_le g)
            dsimp [B_inner]
            nlinarith
        _ = ((Finset.Icc 1 (m / n + 1)).card : ℝ) * B_inner := by simp [nsmul_eq_mul]
        _ = (((m / n : ℕ) : ℝ) + 1) * B_inner := by
            have hcard : (Finset.Icc 1 (m / n + 1)).card = m / n + 1 := by simp
            rw [hcard]; push_cast; ring
    calc ∑ i : Fin n, ∑ l ∈ Finset.Icc 1 (m / n + 1),
          (maxSubSum (bundle A i) (posPrice p) l + maxSubSum (bundle A i) (negPrice p) l)
        ≤ ∑ _i : Fin n, (((m / n : ℕ) : ℝ) + 1) * B_inner :=
          Finset.sum_le_sum fun i _ => hinner i
      _ = (n : ℝ) * ((((m / n : ℕ) : ℝ) + 1) * B_inner) := by simp [nsmul_eq_mul]
      _ = 2 * (n : ℝ) * (((m / n : ℕ) : ℝ) + 1) ^ 2 * M0 v := by dsimp [B_inner]; ring

lemma continuous_phiPot (n m : ℕ) (A : Allocation n m) :
    Continuous (fun p : Fin m → ℝ => phiPot n m p A) := by
  unfold phiPot
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun l _ => ?_
  exact (continuous_maxSubSum (bundle A i) l (fun t => max t 0)
      (continuous_id.max continuous_const)).add
    (continuous_maxSubSum (bundle A i) l (fun t => max (- t) 0)
      (continuous_neg.max continuous_const))

noncomputable def scorePert {n m : ℕ} (v : Fin n → Fin m → ℝ) (ρ lam eps : ℝ)
    (w : Fin n → ℝ) (A : Allocation n m) : ℝ :=
  (∑ i, alphaW ρ w i * bval v i (bundle A i)) + eps * phiPot n m (regDual v ρ lam w).2 A

def IsScoreMax {n m : ℕ} (v : Fin n → Fin m → ℝ) (ρ lam eps : ℝ)
    (w : Fin n → ℝ) (A : Allocation n m) : Prop :=
  IsBalanced A ∧ ∀ B : Allocation n m, IsBalanced B →
    scorePert v ρ lam eps w B ≤ scorePert v ρ lam eps w A

lemma exists_isScoreMax {n m : ℕ} (hn : 1 ≤ n) (v : Fin n → Fin m → ℝ)
    (ρ lam eps : ℝ) (w : Fin n → ℝ) :
    ∃ A : Allocation n m, IsScoreMax v ρ lam eps w A := by
  obtain ⟨A, hmem, hmax⟩ := Finset.exists_mem_eq_sup' (balAllocFinset_nonempty hn)
    (fun B => scorePert v ρ lam eps w B)
  refine ⟨A, mem_balAllocFinset.mp hmem, fun B hB => ?_⟩
  rw [← hmax]
  exact Finset.le_sup' (fun X => scorePert v ρ lam eps w X) (mem_balAllocFinset.mpr hB)

/-- Equation (14): welfare gap of any `A ∈ R_{λ, ε}(w)` is at most `ε * C_Phi`. -/
lemma scoreMax_welfare_gap {n m : ℕ} (hn : 1 ≤ n) (v : Fin n → Fin m → ℝ)
    {ρ lam eps : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : (n : ℝ) * ρ ≤ 1) (hlam : 0 < lam) (heps : 0 ≤ eps)
    {w : Fin n → ℝ} (hw : w ∈ stdSimplex ℝ (Fin n))
    {A : Allocation n m} (hA : IsScoreMax v ρ lam eps w A) :
    wstar hn v (alphaW ρ w) - eps * C_Phi n m v ≤
      ∑ i, alphaW ρ w i * bval v i (bundle A i) := by
  obtain ⟨A_star, hA_star_bal, hA_star_opt⟩ := exists_balAlloc_eq_wstar hn v (alphaW ρ w)
  have hscore_le := hA.2 A_star hA_star_bal
  unfold scorePert at hscore_le
  rw [hA_star_opt] at hscore_le
  have hbox := (regDual_spec v hρ0 hρ1 hlam hw).1.1
  have hp_bnd := (mem_BoxDual_iff.mp hbox).2
  have hphi_A := phiPot_bounds hp_bnd A
  have hphi_star := phiPot_bounds hp_bnd A_star
  nlinarith

/-! #### Two-Coloring of Two Involutions on a Finite Set -/

lemma two_color_involutions_aux {V : Type*} [DecidableEq V] :
    ∀ (N : ℕ) (S : Finset V) (α β : V → V),
      S.card ≤ N →
      (∀ x ∈ S, α x ∈ S) → (∀ x ∈ S, α (α x) = x) → (∀ x ∈ S, α x ≠ x) →
      (∀ x ∈ S, β x ∈ S) → (∀ x ∈ S, β (β x) = x) →
      ∃ c : V → Bool,
        (∀ x ∈ S, c (α x) = ! c x) ∧ (∀ x ∈ S, β x ≠ x → c (β x) = ! c x) := by
  intro N
  induction N with
  | zero =>
    intro S _ _ hle _ _ _ _ _
    have hemp : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hemp
    exact ⟨fun _ => false, by simp, by simp⟩
  | succ N ih =>
    intro S α β hle hα_mem hα_inv hα_fpf hβ_mem hβ_inv
    by_cases hex_mov : ∃ u ∈ S, β u ≠ u
    · obtain ⟨u, huS, hβu_ne⟩ := hex_mov
      by_cases hαβ : α u = β u
      · -- 2-cycle `{u, α u}` closed under both `α` and `β`
        let v := α u
        have hvS : v ∈ S := hα_mem u huS
        have hvu : v ≠ u := hα_fpf u huS
        let S' := (S.erase u).erase v
        have hc1 : (S.erase u).card + 1 = S.card := Finset.card_erase_add_one huS
        have hc2 : S'.card + 1 = (S.erase u).card :=
          Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hvu, hvS⟩)
        have hα_S' : ∀ x ∈ S', α x ∈ S' := by
          intro x hx
          obtain ⟨hxv, hxu, hxS⟩ : x ≠ v ∧ x ≠ u ∧ x ∈ S := by
            obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hx
            obtain ⟨h3, h4⟩ := Finset.mem_erase.mp h2
            exact ⟨h1, h3, h4⟩
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hα_mem x hxS⟩⟩
          · intro h; apply hxu; rw [← hα_inv x hxS, h, hα_inv u huS]
          · intro h; apply hxv; rw [← hα_inv x hxS, h]
        have hβ_S' : ∀ x ∈ S', β x ∈ S' := by
          intro x hx
          obtain ⟨hxv, hxu, hxS⟩ : x ≠ v ∧ x ≠ u ∧ x ∈ S := by
            obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hx
            obtain ⟨h3, h4⟩ := Finset.mem_erase.mp h2
            exact ⟨h1, h3, h4⟩
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hβ_mem x hxS⟩⟩
          · intro h; apply hxu; rw [← hβ_inv x hxS, h, show v = β u from hαβ, hβ_inv u huS]
          · intro h; apply hxv; rw [← hβ_inv x hxS, h]; exact hαβ.symm
        obtain ⟨c', hc'α, hc'β⟩ := ih S' α β (by omega) hα_S'
          (fun x hx => hα_inv x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
          (fun x hx => hα_fpf x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
          hβ_S'
          (fun x hx => hβ_inv x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
        let c : V → Bool := fun x => if x = u then true else if x = v then false else c' x
        refine ⟨c, ?_, ?_⟩
        · intro x hxS
          by_cases hxu : x = u
          · rw [hxu]
            have hcu : c u = true := if_pos rfl
            have hcv : c (α u) = false := by dsimp [c]; rw [if_neg hvu, if_pos rfl]
            rw [hcu, hcv]; rfl
          · by_cases hxv : x = v
            · rw [hxv]
              have hcv : c v = false := by dsimp [c]; rw [if_neg hvu, if_pos rfl]
              have hcu : c (α v) = true := by dsimp [c]; rw [hα_inv u huS, if_pos rfl]
              rw [hcv, hcu]; rfl
            · have hxS' : x ∈ S' := Finset.mem_erase.mpr ⟨hxv, Finset.mem_erase.mpr ⟨hxu, hxS⟩⟩
              have hαxS' : α x ∈ S' := hα_S' x hxS'
              obtain ⟨hαxv, hαxu, _⟩ : α x ≠ v ∧ α x ≠ u ∧ α x ∈ S := by
                obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hαxS'
                obtain ⟨h3, h4⟩ := Finset.mem_erase.mp h2
                exact ⟨h1, h3, h4⟩
              have hcx : c x = c' x := by dsimp [c]; rw [if_neg hxu, if_neg hxv]
              have hcαx : c (α x) = c' (α x) := by dsimp [c]; rw [if_neg hαxu, if_neg hαxv]
              rw [hcx, hcαx]; exact hc'α x hxS'
        · intro x hxS hβx
          by_cases hxu : x = u
          · rw [hxu]
            have hcu : c u = true := if_pos rfl
            have hcv : c (β u) = false := by rw [← hαβ]; dsimp [c]; rw [if_neg hvu, if_pos rfl]
            rw [hcu, hcv]; rfl
          · by_cases hxv : x = v
            · rw [hxv]
              have hcv : c v = false := by dsimp [c]; rw [if_neg hvu, if_pos rfl]
              have hβv : β v = u := by dsimp [v]; rw [hαβ, hβ_inv u huS]
              have hcu : c (β v) = true := by rw [hβv]; exact if_pos rfl
              rw [hcv, hcu]; rfl
            · have hxS' : x ∈ S' := Finset.mem_erase.mpr ⟨hxv, Finset.mem_erase.mpr ⟨hxu, hxS⟩⟩
              have hβxS' : β x ∈ S' := hβ_S' x hxS'
              obtain ⟨hβxv, hβxu, _⟩ : β x ≠ v ∧ β x ≠ u ∧ β x ∈ S := by
                obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hβxS'
                obtain ⟨h3, h4⟩ := Finset.mem_erase.mp h2
                exact ⟨h1, h3, h4⟩
              have hcx : c x = c' x := by dsimp [c]; rw [if_neg hxu, if_neg hxv]
              have hcβx : c (β x) = c' (β x) := by dsimp [c]; rw [if_neg hβxu, if_neg hβxv]
              rw [hcx, hcβx]; exact hc'β x hxS' hβx
      · -- Splice out `{u, β u}` and join `α u ↔ α (β u)`
        let w := β u
        let a₁ := α u
        let a₂ := α w
        have hwS : w ∈ S := hβ_mem u huS
        have ha₁S : a₁ ∈ S := hα_mem u huS
        have ha₂S : a₂ ∈ S := hα_mem w hwS
        have hwu : w ≠ u := hβu_ne
        have ha₁_ne_u : a₁ ≠ u := hα_fpf u huS
        have ha₁_ne_w : a₁ ≠ w := hαβ
        have ha₂_ne_w : a₂ ≠ w := hα_fpf w hwS
        have ha₂_ne_u : a₂ ≠ u := by
          intro h; apply hαβ; calc α u = α (α w) := by rw [← h]
            _ = w := hα_inv w hwS
        have ha₁_ne_a₂ : a₁ ≠ a₂ := by
          intro h; apply hwu.symm; calc u = α a₁ := (hα_inv u huS).symm
            _ = α a₂ := by rw [h]
            _ = w := hα_inv w hwS
        let S' := (S.erase u).erase w
        have hc1 : (S.erase u).card + 1 = S.card := Finset.card_erase_add_one huS
        have hc2 : S'.card + 1 = (S.erase u).card :=
          Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hwu, hwS⟩)
        have ha₁_S' : a₁ ∈ S' :=
          Finset.mem_erase.mpr ⟨ha₁_ne_w, Finset.mem_erase.mpr ⟨ha₁_ne_u, ha₁S⟩⟩
        have ha₂_S' : a₂ ∈ S' :=
          Finset.mem_erase.mpr ⟨ha₂_ne_w, Finset.mem_erase.mpr ⟨ha₂_ne_u, ha₂S⟩⟩
        let α' : V → V := fun x => if x = a₁ then a₂ else if x = a₂ then a₁ else α x
        have hα'_S' : ∀ x ∈ S', α' x ∈ S' := by
          intro x hx
          dsimp [α']
          by_cases hx1 : x = a₁
          · rw [if_pos hx1]; exact ha₂_S'
          · rw [if_neg hx1]
            by_cases hx2 : x = a₂
            · rw [if_pos hx2]; exact ha₁_S'
            · rw [if_neg hx2]
              obtain ⟨hxw, hxu, hxS⟩ : x ≠ w ∧ x ≠ u ∧ x ∈ S := by
                obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hx
                obtain ⟨h3, h4⟩ := Finset.mem_erase.mp h2
                exact ⟨h1, h3, h4⟩
              refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hα_mem x hxS⟩⟩
              · intro h; apply hx2; calc x = α (α x) := (hα_inv x hxS).symm
                  _ = α w := by rw [h]
              · intro h; apply hx1; calc x = α (α x) := (hα_inv x hxS).symm
                  _ = α u := by rw [h]
        have hα'_inv : ∀ x ∈ S', α' (α' x) = x := by
          intro x hx
          have hxS : x ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
          by_cases hx1 : x = a₁
          · subst hx1
            have h1 : α' a₁ = a₂ := if_pos rfl
            have h2 : α' a₂ = a₁ := by dsimp [α']; rw [if_neg ha₁_ne_a₂.symm, if_pos rfl]
            rw [h1, h2]
          · by_cases hx2 : x = a₂
            · subst hx2
              have h1 : α' a₂ = a₁ := by dsimp [α']; rw [if_neg ha₁_ne_a₂.symm, if_pos rfl]
              have h2 : α' a₁ = a₂ := if_pos rfl
              rw [h1, h2]
            · have h1 : α' x = α x := by dsimp [α']; rw [if_neg hx1, if_neg hx2]
              obtain ⟨hxw, hxu, _⟩ : x ≠ w ∧ x ≠ u ∧ x ∈ S := by
                obtain ⟨c_1, c_2⟩ := Finset.mem_erase.mp hx
                obtain ⟨c_3, c_4⟩ := Finset.mem_erase.mp c_2
                exact ⟨c_1, c_3, c_4⟩
              have hαx_ne1 : α x ≠ a₁ := fun h => hxu (by rw [← hα_inv x hxS, h, hα_inv u huS])
              have hαx_ne2 : α x ≠ a₂ := fun h => hxw (by rw [← hα_inv x hxS, h, hα_inv w hwS])
              rw [h1]
              dsimp [α']
              rw [if_neg hαx_ne1, if_neg hαx_ne2, hα_inv x hxS]
        have hα'_fpf : ∀ x ∈ S', α' x ≠ x := by
          intro x hx
          have hxS : x ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
          dsimp [α']
          by_cases hx1 : x = a₁
          · subst hx1; rw [if_pos rfl]; exact ha₁_ne_a₂.symm
          · rw [if_neg hx1]
            by_cases hx2 : x = a₂
            · subst hx2; rw [if_pos rfl]; exact ha₁_ne_a₂
            · rw [if_neg hx2]; exact hα_fpf x hxS
        have hβ_S' : ∀ x ∈ S', β x ∈ S' := by
          intro x hx
          obtain ⟨hxw, hxu, hxS⟩ : x ≠ w ∧ x ≠ u ∧ x ∈ S := by
            obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hx
            obtain ⟨h3, h4⟩ := Finset.mem_erase.mp h2
            exact ⟨h1, h3, h4⟩
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hβ_mem x hxS⟩⟩
          · intro h; apply hxu; rw [← hβ_inv x hxS, h, hβ_inv u huS]
          · intro h; apply hxw; rw [← hβ_inv x hxS, h]
        obtain ⟨c', hc'α, hc'β⟩ := ih S' α' β (by omega) hα'_S' hα'_inv hα'_fpf hβ_S'
          (fun x hx => hβ_inv x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
        have hc'_a₁a₂ : c' a₂ = ! c' a₁ := by
          have := hc'α a₁ ha₁_S'
          have h1 : α' a₁ = a₂ := if_pos rfl
          rwa [h1] at this
        let c : V → Bool := fun x => if x = u then ! c' a₁ else if x = w then ! c' a₂ else c' x
        refine ⟨c, ?_, ?_⟩
        · intro x hxS
          by_cases hxu : x = u
          · rw [hxu]
            have hcu : c u = ! c' a₁ := if_pos rfl
            have hca₁ : c a₁ = c' a₁ := by dsimp [c]; rw [if_neg ha₁_ne_u, if_neg ha₁_ne_w]
            change c a₁ = ! c u
            rw [hca₁, hcu, Bool.not_not]
          · by_cases hxw : x = w
            · rw [hxw]
              have hcw : c w = ! c' a₂ := by dsimp [c]; rw [if_neg hwu, if_pos rfl]
              have hca₂ : c a₂ = c' a₂ := by dsimp [c]; rw [if_neg ha₂_ne_u, if_neg ha₂_ne_w]
              change c a₂ = ! c w
              rw [hca₂, hcw, Bool.not_not]
            · by_cases hx1 : x = a₁
              · rw [hx1]
                have hca₁ : c a₁ = c' a₁ := by dsimp [c]; rw [if_neg ha₁_ne_u, if_neg ha₁_ne_w]
                have hαa₁ : α a₁ = u := hα_inv u huS
                have hcu : c u = ! c' a₁ := if_pos rfl
                rw [hαa₁, hcu, hca₁]
              · by_cases hx2 : x = a₂
                · rw [hx2]
                  have hca₂ : c a₂ = c' a₂ := by dsimp [c]; rw [if_neg ha₂_ne_u, if_neg ha₂_ne_w]
                  have hαa₂ : α a₂ = w := hα_inv w hwS
                  have hcw : c w = ! c' a₂ := by dsimp [c]; rw [if_neg hwu, if_pos rfl]
                  rw [hαa₂, hcw, hca₂]
                · have hxS' : x ∈ S' := Finset.mem_erase.mpr ⟨hxw, Finset.mem_erase.mpr ⟨hxu, hxS⟩⟩
                  have hα'x : α' x = α x := by dsimp [α']; rw [if_neg hx1, if_neg hx2]
                  have hαxS' : α x ∈ S' := hα'x ▸ hα'_S' x hxS'
                  obtain ⟨hαxw, hαxu, _⟩ : α x ≠ w ∧ α x ≠ u ∧ α x ∈ S := by
                    obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hαxS'
                    obtain ⟨h3, h4⟩ := Finset.mem_erase.mp h2
                    exact ⟨h1, h3, h4⟩
                  have hcx : c x = c' x := by dsimp [c]; rw [if_neg hxu, if_neg hxw]
                  have hcαx : c (α x) = c' (α x) := by dsimp [c]; rw [if_neg hαxu, if_neg hαxw]
                  rw [hcx, hcαx, ← hα'x]
                  exact hc'α x hxS'
        · intro x hxS hβx
          by_cases hxu : x = u
          · rw [hxu]
            have hcu : c u = ! c' a₁ := if_pos rfl
            have hcw : c w = ! c' a₂ := by dsimp [c]; rw [if_neg hwu, if_pos rfl]
            change c w = ! c u
            rw [hcw, hcu, hc'_a₁a₂]
          · by_cases hxw : x = w
            · rw [hxw]
              have hcu : c u = ! c' a₁ := if_pos rfl
              have hcw : c w = ! c' a₂ := by dsimp [c]; rw [if_neg hwu, if_pos rfl]
              have hβw : β w = u := hβ_inv u huS
              rw [hβw, hcu, hcw, hc'_a₁a₂, Bool.not_not]
            · have hxS' : x ∈ S' := Finset.mem_erase.mpr ⟨hxw, Finset.mem_erase.mpr ⟨hxu, hxS⟩⟩
              have hβxS' : β x ∈ S' := hβ_S' x hxS'
              obtain ⟨hβxw, hβxu, _⟩ : β x ≠ w ∧ β x ≠ u ∧ β x ∈ S := by
                obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hβxS'
                obtain ⟨h3, h4⟩ := Finset.mem_erase.mp h2
                exact ⟨h1, h3, h4⟩
              have hcx : c x = c' x := by dsimp [c]; rw [if_neg hxu, if_neg hxw]
              have hcβx : c (β x) = c' (β x) := by dsimp [c]; rw [if_neg hβxu, if_neg hβxw]
              rw [hcx, hcβx]
              exact hc'β x hxS' hβx
    · push_neg at hex_mov
      by_cases hS_ne : S.Nonempty
      · obtain ⟨u, huS⟩ := hS_ne
        let v := α u
        have hvS : v ∈ S := hα_mem u huS
        have hvu : v ≠ u := hα_fpf u huS
        let S' := (S.erase u).erase v
        have hc1 : (S.erase u).card + 1 = S.card := Finset.card_erase_add_one huS
        have hc2 : S'.card + 1 = (S.erase u).card :=
          Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hvu, hvS⟩)
        have hα_S' : ∀ x ∈ S', α x ∈ S' := by
          intro x hx
          obtain ⟨hxv, hxu, hxS⟩ : x ≠ v ∧ x ≠ u ∧ x ∈ S := by
            obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hx
            obtain ⟨h3, h4⟩ := Finset.mem_erase.mp h2
            exact ⟨h1, h3, h4⟩
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hα_mem x hxS⟩⟩
          · intro h; apply hxu; rw [← hα_inv x hxS, h, hα_inv u huS]
          · intro h; apply hxv; rw [← hα_inv x hxS, h]
        have hβ_S' : ∀ x ∈ S', β x ∈ S' := fun x hx => by
          rw [hex_mov x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))]; exact hx
        obtain ⟨c', hc'α, _⟩ := ih S' α β (by omega) hα_S'
          (fun x hx => hα_inv x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
          (fun x hx => hα_fpf x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
          hβ_S'
          (fun x hx => hβ_inv x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
        let c : V → Bool := fun x => if x = u then true else if x = v then false else c' x
        refine ⟨c, ?_, fun x hxS hne => absurd (hex_mov x hxS) hne⟩
        intro x hxS
        by_cases hxu : x = u
        · rw [hxu]
          have hcu : c u = true := if_pos rfl
          have hcv : c (α u) = false := by dsimp [c]; rw [if_neg hvu, if_pos rfl]
          rw [hcu, hcv]; rfl
        · by_cases hxv : x = v
          · rw [hxv]
            have hcv : c v = false := by dsimp [c]; rw [if_neg hvu, if_pos rfl]
            have hcu : c (α v) = true := by dsimp [c]; rw [hα_inv u huS, if_pos rfl]
            rw [hcv, hcu]; rfl
          · have hxS' : x ∈ S' := Finset.mem_erase.mpr ⟨hxv, Finset.mem_erase.mpr ⟨hxu, hxS⟩⟩
            have hαxS' : α x ∈ S' := hα_S' x hxS'
            obtain ⟨hαxv, hαxu, _⟩ : α x ≠ v ∧ α x ≠ u ∧ α x ∈ S := by
              obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hαxS'
              obtain ⟨h3, h4⟩ := Finset.mem_erase.mp h2
              exact ⟨h1, h3, h4⟩
            have hcx : c x = c' x := by dsimp [c]; rw [if_neg hxu, if_neg hxv]
            have hcαx : c (α x) = c' (α x) := by dsimp [c]; rw [if_neg hαxu, if_neg hαxv]
            rw [hcx, hcαx]; exact hc'α x hxS'
      · rw [Finset.not_nonempty_iff_eq_empty.mp hS_ne]
        exact ⟨fun _ => false, by simp, by simp⟩

lemma two_color_involutions {V : Type*} [Fintype V] [DecidableEq V] (α β : V → V)
    (hα_inv : ∀ x, α (α x) = x) (hα_fpf : ∀ x, α x ≠ x) (hβ_inv : ∀ x, β (β x) = x) :
    ∃ c : V → Bool, (∀ x, c (α x) = ! c x) ∧ (∀ x, β x ≠ x → c (β x) = ! c x) := by
  obtain ⟨c, h1, h2⟩ := two_color_involutions_aux (Finset.univ : Finset V).card Finset.univ α β
    le_rfl (fun _ _ => Finset.mem_univ _) (fun x _ => hα_inv x) (fun x _ => hα_fpf x)
    (fun _ _ => Finset.mem_univ _) (fun x _ => hβ_inv x)
  exact ⟨c, fun x => h1 x (Finset.mem_univ x), fun x => h2 x (Finset.mem_univ x)⟩

/-! #### Sorted Pairing on `Fin k` and Agent-Matching for Lemma 5 -/

def pairFin (k : ℕ) (t : Fin k) : Fin k :=
  if t.val % 2 = 0 then
    if h : t.val + 1 < k then ⟨t.val + 1, h⟩ else t
  else
    ⟨t.val - 1, by have := t.isLt; omega⟩

lemma pairFin_invol (k : ℕ) (t : Fin k) : pairFin k (pairFin k t) = t := by
  have ht := t.isLt
  unfold pairFin
  by_cases hev : t.val % 2 = 0
  · rw [if_pos hev]
    by_cases hlt : t.val + 1 < k
    · rw [dif_pos hlt]
      have hodd : ¬ ((t.val + 1) % 2 = 0) := by omega
      dsimp
      rw [if_neg hodd]
    · rw [dif_neg hlt, if_pos hev, dif_neg hlt]
  · rw [if_neg hev]
    have hev' : (t.val - 1) % 2 = 0 := by omega
    have hlt' : (t.val - 1) + 1 < k := by omega
    dsimp
    rw [if_pos hev', dif_pos hlt']
    ext; dsimp; omega

lemma pairFin_fixed_card_le_one (k : ℕ) :
    (Finset.univ.filter (fun t : Fin k => pairFin k t = t)).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  have ha_eq := (Finset.mem_filter.mp ha).2
  have hb_eq := (Finset.mem_filter.mp hb).2
  have ha_lt := a.isLt
  have hb_lt := b.isLt
  have ha_last : a.val = k - 1 := by
    unfold pairFin at ha_eq
    by_cases hev : a.val % 2 = 0
    · rw [if_pos hev] at ha_eq
      by_cases hlt : a.val + 1 < k
      · rw [dif_pos hlt] at ha_eq
        have hv := congrArg Fin.val ha_eq; dsimp at hv; omega
      · omega
    · rw [if_neg hev] at ha_eq
      have hv := congrArg Fin.val ha_eq; dsimp at hv; omega
  have hb_last : b.val = k - 1 := by
    unfold pairFin at hb_eq
    by_cases hev : b.val % 2 = 0
    · rw [if_pos hev] at hb_eq
      by_cases hlt : b.val + 1 < k
      · rw [dif_pos hlt] at hb_eq
        have hv := congrArg Fin.val hb_eq; dsimp at hv; omega
      · omega
    · rw [if_neg hev] at hb_eq
      have hv := congrArg Fin.val hb_eq; dsimp at hv; omega
  exact Fin.ext (ha_last.trans hb_last.symm)

lemma pairFin_lt_two_mul {k l : ℕ} (h2l : 2 * l ≤ k) {t : Fin k} (ht : t.val < 2 * l) :
    (pairFin k t).val < 2 * l ∧ pairFin k t ≠ t := by
  unfold pairFin
  by_cases hev : t.val % 2 = 0
  · rw [if_pos hev]
    have hlt1 : t.val + 1 < 2 * l := by omega
    have hlt_k : t.val + 1 < k := by omega
    rw [dif_pos hlt_k]
    refine ⟨hlt1, fun heq => ?_⟩
    have hv := congrArg Fin.val heq; dsimp at hv; omega
  · rw [if_neg hev]
    refine ⟨by dsimp; omega, fun heq => ?_⟩
    have hv := congrArg Fin.val heq; dsimp at hv; omega

/-- General parity-splitting bound for a set `P` stabilized by an involution `f` with `≤ 1` fixed point:
if `c` flips along non-fixed edges of `f`, then `# {x ∈ P | c x = b}` has `2 * count - P.card ∈ {-1, 0, 1}`. -/
lemma involution_color_split {V : Type*} [DecidableEq V] (P : Finset V) (f : V → V) (c : V → Bool)
    (hmem : ∀ x ∈ P, f x ∈ P) (hinv : ∀ x ∈ P, f (f x) = x)
    (hfix_le1 : (P.filter (fun x => f x = x)).card ≤ 1)
    (hflip : ∀ x ∈ P, f x ≠ x → c (f x) = ! c x) (b : Bool) :
    2 * (P.filter (fun x => c x = b)).card ≤ P.card + 1 ∧
      P.card ≤ 2 * (P.filter (fun x => c x = b)).card + 1 := by
  let P_b := P.filter (fun x => c x = b)
  let P_mov := P.filter (fun x => f x ≠ x)
  let P_fix := P.filter (fun x => f x = x)
  have hP_card : P_mov.card + P_fix.card = P.card := by
    have hrew : P_fix = P.filter (fun x => ¬ (f x ≠ x)) := by
      ext x; simp [P_fix]
    rw [hrew]
    exact Finset.card_filter_add_card_filter_not (s := P) (fun x => f x ≠ x)
  let M_b := P_mov.filter (fun x => c x = b)
  let M_nb := P_mov.filter (fun x => c x = ! b)
  have hM_sum : M_b.card + M_nb.card = P_mov.card := by
    have hrew : M_nb = P_mov.filter (fun x => ¬ (c x = b)) := by
      ext x; simp only [M_nb, Finset.mem_filter]; cases c x <;> cases b <;> simp
    rw [hrew]
    exact Finset.card_filter_add_card_filter_not (s := P_mov) (fun x => c x = b)
  have hM_eq : M_b.card = M_nb.card := by
    refine Finset.card_bij (fun x _ => f x) ?_ ?_ ?_
    · intro x hx
      obtain ⟨hx_mov, hcx⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxP, hfx_ne⟩ := Finset.mem_filter.mp hx_mov
      have hfxP : f x ∈ P := hmem x hxP
      have hffx : f (f x) ≠ f x := fun h => hfx_ne (h.symm.trans (hinv x hxP))
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hfxP, hffx⟩,
        by rw [hflip x hxP hfx_ne, hcx]⟩
    · intro x₁ hx₁ x₂ hx₂ heq
      have hx₁P := (Finset.mem_filter.mp (Finset.mem_filter.mp hx₁).1).1
      have hx₂P := (Finset.mem_filter.mp (Finset.mem_filter.mp hx₂).1).1
      calc x₁ = f (f x₁) := (hinv x₁ hx₁P).symm
        _ = f (f x₂) := by rw [heq]
        _ = x₂ := hinv x₂ hx₂P
    · intro y hy
      obtain ⟨hy_mov, hcy⟩ := Finset.mem_filter.mp hy
      obtain ⟨hyP, hfy_ne⟩ := Finset.mem_filter.mp hy_mov
      have hfyP : f y ∈ P := hmem y hyP
      have hffy : f (f y) ≠ f y := fun h => hfy_ne (h.symm.trans (hinv y hyP))
      refine ⟨f y, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hfyP, hffy⟩, ?_⟩, hinv y hyP⟩
      rw [hflip y hyP hfy_ne, hcy, Bool.not_not]
  let F_b := P_fix.filter (fun x => c x = b)
  have hPb_eq : P_b.card = M_b.card + F_b.card := by
    have hdisj : Disjoint M_b F_b := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx1).1).2
        (Finset.mem_filter.mp (Finset.mem_filter.mp hx2).1).2
    have hun : M_b ∪ F_b = P_b := by
      ext x
      simp only [M_b, F_b, P_b, P_mov, P_fix, Finset.mem_union, Finset.mem_filter]
      by_cases hfx : f x = x <;> simp [hfx]
    rw [← hun, Finset.card_union_of_disjoint hdisj]
  have hFb_le : F_b.card ≤ P_fix.card := Finset.card_filter_le _ _
  have hPfix_le1 : P_fix.card ≤ 1 := hfix_le1
  change 2 * P_b.card ≤ P.card + 1 ∧ P.card ≤ 2 * P_b.card + 1
  omega

def revPermFin (k : ℕ) : Equiv.Perm (Fin k) where
  toFun t := ⟨k - 1 - t.val, by have := t.isLt; omega⟩
  invFun t := ⟨k - 1 - t.val, by have := t.isLt; omega⟩
  left_inv t := by ext; dsimp; have := t.isLt; omega
  right_inv t := by ext; dsimp; have := t.isLt; omega

lemma revPermFin_antitone (k : ℕ) : Antitone (revPermFin k) :=
  fun a b (hab : a.val ≤ b.val) => show k - 1 - b.val ≤ k - 1 - a.val by omega

/-- Sorted equivalence `Fin W.card ≃ W` ordering `wt` in non-increasing (`Antitone`) order. -/
noncomputable def sortedEquiv {α : Type*} [DecidableEq α] (W : Finset α) (wt : α → ℝ) :
    Fin W.card ≃ W :=
  let e₀ : Fin W.card ≃ W := W.equivFin.symm
  let σ : Equiv.Perm (Fin W.card) := (revPermFin W.card).trans (Tuple.sort (fun t => wt (e₀ t).1))
  σ.trans e₀

lemma sortedEquiv_antitone {α : Type*} [DecidableEq α] (W : Finset α) (wt : α → ℝ) :
    Antitone (fun t : Fin W.card => wt (sortedEquiv W wt t).1) := by
  let e₀ : Fin W.card ≃ W := W.equivFin.symm
  have hmono : Monotone ((fun t : Fin W.card => wt (e₀ t).1) ∘
      Tuple.sort (fun t : Fin W.card => wt (e₀ t).1)) :=
    Tuple.monotone_sort _
  exact hmono.comp_antitone (revPermFin_antitone W.card)

/-- Combined vertices owned by agent `i` across two allocations `A` and `B`. -/
def ownedVerts {n m : ℕ} (A B : Allocation n m) (i : Fin n) : Finset (Fin m × Bool) :=
  Finset.univ.filter (fun v => (if v.2 then B v.1 else A v.1) = i)

lemma card_ownedVerts {n m : ℕ} (A B : Allocation n m) (i : Fin n) :
    (ownedVerts A B i).card = (bundle A i).card + (bundle B i).card := by
  let VA := (bundle A i).image (fun g => (g, false))
  let VB := (bundle B i).image (fun g => (g, true))
  have hdisj : Disjoint VA VB := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    obtain ⟨g₁, _, rfl⟩ := Finset.mem_image.mp hv1
    obtain ⟨g₂, _, heq⟩ := Finset.mem_image.mp hv2
    exact Bool.false_ne_true (congrArg Prod.snd heq).symm
  have hun : VA ∪ VB = ownedVerts A B i := by
    ext ⟨g, b⟩
    simp only [VA, VB, ownedVerts, bundle, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    cases b <;> simp
  have hcA : VA.card = (bundle A i).card :=
    Finset.card_image_of_injective _ (fun g₁ g₂ h => congrArg Prod.fst h)
  have hcB : VB.card = (bundle B i).card :=
    Finset.card_image_of_injective _ (fun g₁ g₂ h => congrArg Prod.fst h)
  rw [← hun, Finset.card_union_of_disjoint hdisj, hcA, hcB]

lemma sum_ownedVerts {n m : ℕ} (A B : Allocation n m) (i : Fin n) (f : Fin m → ℝ) :
    ∑ v ∈ ownedVerts A B i, f v.1 = (∑ g ∈ bundle A i, f g) + (∑ g ∈ bundle B i, f g) := by
  let VA := (bundle A i).image (fun g => (g, false))
  let VB := (bundle B i).image (fun g => (g, true))
  have hdisj : Disjoint VA VB := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    obtain ⟨g₁, _, rfl⟩ := Finset.mem_image.mp hv1
    obtain ⟨g₂, _, heq⟩ := Finset.mem_image.mp hv2
    exact Bool.false_ne_true (congrArg Prod.snd heq).symm
  have hun : VA ∪ VB = ownedVerts A B i := by
    ext ⟨g, b⟩
    simp only [VA, VB, ownedVerts, bundle, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    cases b <;> simp
  rw [← hun, Finset.sum_union hdisj,
    Finset.sum_image (fun g₁ _ g₂ _ h => congrArg Prod.fst h),
    Finset.sum_image (fun g₁ _ g₂ _ h => congrArg Prod.fst h)]

lemma maxSubSum_ownedVerts_ge {n m : ℕ} (A B : Allocation n m) (i : Fin n)
    (f : Fin m → ℝ) (l : ℕ) :
    maxSubSum (bundle A i) f l + maxSubSum (bundle B i) f l ≤
      maxSubSum (ownedVerts A B i) (fun v => f v.1) (2 * l) := by
  obtain ⟨SA, hSA_mem, hSA_eq⟩ := Finset.exists_mem_eq_sup'
    ⟨∅, empty_mem_validSubs (bundle A i) l⟩ (fun T => ∑ g ∈ T, f g)
  obtain ⟨SB, hSB_mem, hSB_eq⟩ := Finset.exists_mem_eq_sup'
    ⟨∅, empty_mem_validSubs (bundle B i) l⟩ (fun T => ∑ g ∈ T, f g)
  have hSA : SA ⊆ bundle A i ∧ SA.card ≤ l := by
    simpa [validSubs] using hSA_mem
  have hSB : SB ⊆ bundle B i ∧ SB.card ≤ l := by
    simpa [validSubs] using hSB_mem
  let UA := SA.image (fun g => (g, false))
  let UB := SB.image (fun g => (g, true))
  have hdisj : Disjoint UA UB := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    obtain ⟨g₁, _, rfl⟩ := Finset.mem_image.mp hv1
    obtain ⟨g₂, _, heq⟩ := Finset.mem_image.mp hv2
    exact Bool.false_ne_true (congrArg Prod.snd heq).symm
  have hsub : UA ∪ UB ⊆ ownedVerts A B i := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv1 | hv2
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hv1
      have hgA := mem_bundle_iff A i g |>.mp (hSA.1 hg)
      simp [ownedVerts, hgA]
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hv2
      have hgB := mem_bundle_iff B i g |>.mp (hSB.1 hg)
      simp [ownedVerts, hgB]
  have hcard : (UA ∪ UB).card ≤ 2 * l := by
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun g₁ g₂ h => congrArg Prod.fst h),
      Finset.card_image_of_injective _ (fun g₁ g₂ h => congrArg Prod.fst h)]
    have := hSA.2; have := hSB.2; omega
  have hsum : ∑ v ∈ UA ∪ UB, f v.1 = (∑ g ∈ SA, f g) + (∑ g ∈ SB, f g) := by
    rw [Finset.sum_union hdisj,
      Finset.sum_image (fun g₁ _ g₂ _ h => congrArg Prod.fst h),
      Finset.sum_image (fun g₁ _ g₂ _ h => congrArg Prod.fst h)]
  change (validSubs (bundle A i) l).sup' _ _ + (validSubs (bundle B i) l).sup' _ _ ≤ _
  rw [hSA_eq, hSB_eq, ← hsum]
  exact le_maxSubSum hsub hcard (fun v => f v.1)

/-- Helper transferring an even-paired sorted class `W_cls ⊆ V_i` under a coloring `c` into
a subset sum of `bundle C i` and `bundle D i` achieving `maxSubSum V_i wt (2 * l)`. -/
lemma class_prefix_recomb_ge {m : ℕ} (V_i : Finset (Fin m × Bool))
    (wt : Fin m → ℝ) (hwt_nn : ∀ g, 0 ≤ wt g)
    (W_cls : Finset (Fin m × Bool))
    (hW_eq : W_cls = V_i.filter (fun v => 0 < wt v.1))
    (β : Fin m × Bool → Fin m × Bool)
    (hβ_cls : ∀ t : Fin W_cls.card, pairFin W_cls.card t ≠ t →
      β (sortedEquiv W_cls (fun v => wt v.1) t).1 =
        (sortedEquiv W_cls (fun v => wt v.1) (pairFin W_cls.card t)).1)
    (c : Fin m × Bool → Bool)
    (hc_flip : ∀ v ∈ V_i, β v ≠ v → c (β v) = ! c v)
    (S_C S_D : Finset (Fin m))
    (hC_bij : ∀ v ∈ V_i, c v = true → v.1 ∈ S_C)
    (hC_inj : Set.InjOn Prod.fst (V_i.filter (fun v => c v = true) : Set (Fin m × Bool)))
    (hD_bij : ∀ v ∈ V_i, c v = false → v.1 ∈ S_D)
    (hD_inj : Set.InjOn Prod.fst (V_i.filter (fun v => c v = false) : Set (Fin m × Bool)))
    (l : ℕ) :
    maxSubSum V_i (fun v => wt v.1) (2 * l) ≤
      maxSubSum S_C wt l + maxSubSum S_D wt l := by
  let k := W_cls.card
  let e := sortedEquiv W_cls (fun v => wt v.1)
  have hanti : Antitone (fun t : Fin k => wt (e t).1.1) :=
    sortedEquiv_antitone W_cls (fun v => wt v.1)
  have hmax_eq : maxSubSum V_i (fun v => wt v.1) (2 * l) =
      ∑ t ∈ Finset.univ.filter (fun t : Fin k => t.val < 2 * l), wt (e t).1.1 := by
    rw [maxSubSum_filter_pos V_i (fun v => wt v.1) (fun v _ => hwt_nn v.1) (2 * l),
      ← hW_eq, maxSubSum_fin_equiv W_cls e (fun v => wt v.1) (2 * l)]
    exact maxSubSum_antitone_fin hanti (fun t => hwt_nn _) (2 * l)
  -- Take `P_idx := Finset.univ.filter (fun t : Fin k => t.val < 2 * l)` (`⊆ Fin k`)
  let P_idx : Finset (Fin k) := Finset.univ.filter (fun t : Fin k => t.val < 2 * l)
  have hP_stab : ∀ t ∈ P_idx, pairFin k t ∈ P_idx := by
    intro t ht
    have ht_lt : t.val < 2 * l := (Finset.mem_filter.mp ht).2
    by_cases h2l : 2 * l ≤ k
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (pairFin_lt_two_mul h2l ht_lt).1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (pairFin k t).isLt (by omega)⟩
  have hP_fix_le1 : (P_idx.filter (fun t => pairFin k t = t)).card ≤ 1 := by
    refine le_trans (Finset.card_le_card ?_) (pairFin_fixed_card_le_one k)
    exact Finset.filter_subset_filter _ (Finset.subset_univ P_idx)
  have hP_flip : ∀ t ∈ P_idx, pairFin k t ≠ t → c (e (pairFin k t)).1 = ! c (e t).1 := by
    intro t _ hne
    have hv_mem : (e t).1 ∈ V_i := by
      have hw : (e t).1 ∈ V_i.filter (fun v => 0 < wt v.1) := hW_eq ▸ (e t).2
      exact (Finset.mem_filter.mp hw).1
    have hβ_eq := hβ_cls t hne
    have hβ_ne : β (e t).1 ≠ (e t).1 := by
      rw [hβ_eq]; intro heq
      exact hne (e.injective (Subtype.ext heq))
    rw [← hβ_eq]
    exact hc_flip (e t).1 hv_mem hβ_ne
  have hP_card_le : P_idx.card ≤ 2 * l := by
    by_cases h2l : 2 * l ≤ k
    · have hcard : P_idx.card = 2 * l := by
        symm; rw [← Finset.card_range (2 * l)]
        refine Finset.card_bij (fun s hs => (⟨s, by rw [Finset.mem_range] at hs; omega⟩ : Fin k))
          (fun s hs => by simp [P_idx, Finset.mem_range.mp hs])
          (fun s₁ _ s₂ _ h => congrArg Fin.val h)
          (fun t ht => ⟨t.val, Finset.mem_range.mpr (Finset.mem_filter.mp ht).2, by ext; rfl⟩)
      omega
    · calc P_idx.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
        _ = k := by simp
        _ ≤ 2 * l := by omega
  let col : Fin k → Bool := fun t => c (e t).1
  have hP_sub_card_le : ∀ b : Bool, (P_idx.filter (fun t => c (e t).1 = b)).card ≤ l := by
    intro b
    have hsp := involution_color_split P_idx (pairFin k) col
      hP_stab (fun t _ => pairFin_invol k t) hP_fix_le1 hP_flip b
    have heq_flt : P_idx.filter (fun t => c (e t).1 = b) = P_idx.filter (fun t => col t = b) := by
      ext t; simp [col]
    rw [heq_flt]
    omega
  let P_true := P_idx.filter (fun t => c (e t).1 = true)
  let P_false := P_idx.filter (fun t => c (e t).1 = false)
  have hsum_split : ∑ t ∈ P_idx, wt (e t).1.1 =
      (∑ t ∈ P_true, wt (e t).1.1) + (∑ t ∈ P_false, wt (e t).1.1) := by
    have hrew : P_false = P_idx.filter (fun t => ¬ (c (e t).1 = true)) := by
      ext t; simp only [P_false, Finset.mem_filter]; cases c (e t).1 <;> simp
    rw [hrew]
    exact (Finset.sum_filter_add_sum_filter_not P_idx (fun t => c (e t).1 = true) _).symm
  let T_C : Finset (Fin m) := P_true.image (fun t => (e t).1.1)
  let T_D : Finset (Fin m) := P_false.image (fun t => (e t).1.1)
  have hTC_sub : T_C ⊆ S_C := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hg
    have hw : (e t).1 ∈ V_i.filter (fun v => 0 < wt v.1) := hW_eq ▸ (e t).2
    exact hC_bij (e t).1 (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp ht).2
  have hTD_sub : T_D ⊆ S_D := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hg
    have hw : (e t).1 ∈ V_i.filter (fun v => 0 < wt v.1) := hW_eq ▸ (e t).2
    exact hD_bij (e t).1 (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp ht).2
  have hinj_true : Set.InjOn (fun t : Fin k => (e t).1.1) P_true := by
    intro t₁ ht₁ t₂ ht₂ heq
    have hw₁ : (e t₁).1 ∈ V_i.filter (fun v => 0 < wt v.1) := hW_eq ▸ (e t₁).2
    have hw₂ : (e t₂).1 ∈ V_i.filter (fun v => 0 < wt v.1) := hW_eq ▸ (e t₂).2
    have hm₁ : (e t₁).1 ∈ V_i.filter (fun v => c v = true) :=
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw₁).1, (Finset.mem_filter.mp ht₁).2⟩
    have hm₂ : (e t₂).1 ∈ V_i.filter (fun v => c v = true) :=
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw₂).1, (Finset.mem_filter.mp ht₂).2⟩
    exact e.injective (Subtype.ext (hC_inj hm₁ hm₂ heq))
  have hinj_false : Set.InjOn (fun t : Fin k => (e t).1.1) P_false := by
    intro t₁ ht₁ t₂ ht₂ heq
    have hw₁ : (e t₁).1 ∈ V_i.filter (fun v => 0 < wt v.1) := hW_eq ▸ (e t₁).2
    have hw₂ : (e t₂).1 ∈ V_i.filter (fun v => 0 < wt v.1) := hW_eq ▸ (e t₂).2
    have hm₁ : (e t₁).1 ∈ V_i.filter (fun v => c v = false) :=
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw₁).1, (Finset.mem_filter.mp ht₁).2⟩
    have hm₂ : (e t₂).1 ∈ V_i.filter (fun v => c v = false) :=
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw₂).1, (Finset.mem_filter.mp ht₂).2⟩
    exact e.injective (Subtype.ext (hD_inj hm₁ hm₂ heq))
  have hTC_card : T_C.card ≤ l := by
    dsimp [T_C]; rw [Finset.card_image_of_injOn hinj_true]; exact hP_sub_card_le true
  have hTD_card : T_D.card ≤ l := by
    dsimp [T_D]; rw [Finset.card_image_of_injOn hinj_false]; exact hP_sub_card_le false
  have hTC_sum : ∑ g ∈ T_C, wt g = ∑ t ∈ P_true, wt (e t).1.1 :=
    Finset.sum_image hinj_true
  have hTD_sum : ∑ g ∈ T_D, wt g = ∑ t ∈ P_false, wt (e t).1.1 :=
    Finset.sum_image hinj_false
  rw [hmax_eq, hsum_split, ← hTC_sum, ← hTD_sum]
  exact add_le_add (le_maxSubSum hTC_sub hTC_card wt) (le_maxSubSum hTD_sub hTD_card wt)

/-- Lemma 5 (Price Interlacing in variational prefix-sum form): for any `A, B ∈ R_{λ, ε}(w)`
(`ε > 0`), every agent `i` and prefix length `1 ≤ l ≤ m / n + 1` achieves the maximum combined
`2l`-subset sum for both positive prices and negative price magnitudes. -/
theorem price_interlacing_prefix_eq {n m : ℕ} (v : Fin n → Fin m → ℝ)
    {ρ lam eps : ℝ} (heps : 0 < eps) (w : Fin n → ℝ)
    {A B : Allocation n m}
    (hA : IsScoreMax v ρ lam eps w A) (hB : IsScoreMax v ρ lam eps w B) :
    let p := (regDual v ρ lam w).2
    ∀ (i : Fin n), ∀ l ∈ Finset.Icc 1 (m / n + 1),
      maxSubSum (bundle A i) (posPrice p) l + maxSubSum (bundle B i) (posPrice p) l =
        maxSubSum (ownedVerts A B i) (fun v => posPrice p v.1) (2 * l) ∧
      maxSubSum (bundle A i) (negPrice p) l + maxSubSum (bundle B i) (negPrice p) l =
        maxSubSum (ownedVerts A B i) (fun v => negPrice p v.1) (2 * l) := by
  intro p
  let owner : Fin m × Bool → Fin n := fun v_x => if v_x.2 then B v_x.1 else A v_x.1
  let V_pos : Fin n → Finset (Fin m × Bool) :=
    fun i => (ownedVerts A B i).filter (fun v_x => 0 < posPrice p v_x.1)
  let V_neg : Fin n → Finset (Fin m × Bool) :=
    fun i => (ownedVerts A B i).filter (fun v_x => 0 < negPrice p v_x.1)
  have hdisj_pn : ∀ i, Disjoint (V_pos i) (V_neg i) := by
    intro i
    rw [Finset.disjoint_left]
    intro v_x h1 h2
    have hp1 : 0 < max (p v_x.1) 0 := (Finset.mem_filter.mp h1).2
    have hp2 : 0 < max (- p v_x.1) 0 := (Finset.mem_filter.mp h2).2
    have : 0 < p v_x.1 := by by_contra h; rw [max_eq_right (le_of_not_gt h)] at hp1; linarith
    have : p v_x.1 < 0 := by by_contra h; rw [max_eq_right (by linarith)] at hp2; linarith
    linarith
  -- Paired subsets inside `V_pos i` and `V_neg i`
  let e_pos (i : Fin n) := sortedEquiv (V_pos i) (fun v_x => posPrice p v_x.1)
  let e_neg (i : Fin n) := sortedEquiv (V_neg i) (fun v_x => negPrice p v_x.1)
  let P_pos (i : Fin n) : Finset (Fin m × Bool) :=
    (Finset.univ.filter (fun t : Fin (V_pos i).card => pairFin (V_pos i).card t ≠ t)).image
      (fun t => (e_pos i t).1)
  let P_neg (i : Fin n) : Finset (Fin m × Bool) :=
    (Finset.univ.filter (fun t : Fin (V_neg i).card => pairFin (V_neg i).card t ≠ t)).image
      (fun t => (e_neg i t).1)
  have hPpos_sub : ∀ i, P_pos i ⊆ V_pos i := by
    intro i x hx; obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx; exact (e_pos i t).2
  have hPneg_sub : ∀ i, P_neg i ⊆ V_neg i := by
    intro i x hx; obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx; exact (e_neg i t).2
  have hdisj_Ppn : ∀ i, Disjoint (P_pos i) (P_neg i) :=
    fun i => Disjoint.mono (hPpos_sub i) (hPneg_sub i) (hdisj_pn i)
  let V_rem (i : Fin n) : Finset (Fin m × Bool) :=
    ownedVerts A B i \ (P_pos i ∪ P_neg i)
  let e_rem (i : Fin n) : Fin (V_rem i).card ≃ V_rem i := (V_rem i).equivFin.symm
  -- Define agent involution `β` on `Fin m × Bool`
  have hmem_Vrem : ∀ x : Fin m × Bool,
      x ∉ P_pos (owner x) → x ∉ P_neg (owner x) → x ∈ V_rem (owner x) := fun x hnp hnn =>
    Finset.mem_sdiff.mpr ⟨by simp [ownedVerts, owner], by simp [Finset.mem_union, hnp, hnn]⟩
  let β : Fin m × Bool → Fin m × Bool := fun x =>
    if hx_pos : x ∈ P_pos (owner x) then
      (e_pos (owner x) (pairFin (V_pos (owner x)).card
        ((e_pos (owner x)).symm ⟨x, hPpos_sub (owner x) hx_pos⟩))).1
    else if hx_neg : x ∈ P_neg (owner x) then
      (e_neg (owner x) (pairFin (V_neg (owner x)).card
        ((e_neg (owner x)).symm ⟨x, hPneg_sub (owner x) hx_neg⟩))).1
    else
      (e_rem (owner x) (pairFin (V_rem (owner x)).card
        ((e_rem (owner x)).symm ⟨x, hmem_Vrem x hx_pos hx_neg⟩))).1
  have hβ_owner : ∀ x, owner (β x) = owner x := by
    intro x
    dsimp [β]
    split_ifs with hx_pos hx_neg
    · have hm := (e_pos (owner x) (pairFin (V_pos (owner x)).card
        ((e_pos (owner x)).symm ⟨x, hPpos_sub (owner x) hx_pos⟩))).2
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
    · have hm := (e_neg (owner x) (pairFin (V_neg (owner x)).card
        ((e_neg (owner x)).symm ⟨x, hPneg_sub (owner x) hx_neg⟩))).2
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
    · have hm := (e_rem (owner x) (pairFin (V_rem (owner x)).card
        ((e_rem (owner x)).symm ⟨x, hmem_Vrem x hx_pos hx_neg⟩))).2
      exact (Finset.mem_filter.mp (Finset.sdiff_subset hm)).2
  have hPpos_iff : ∀ (i : Fin n) (t : Fin (V_pos i).card),
      (e_pos i t).1 ∈ P_pos i ↔ pairFin (V_pos i).card t ≠ t := by
    intro i t
    constructor
    · intro hm
      obtain ⟨t', ht', heq⟩ := Finset.mem_image.mp hm
      have htt' : t' = t := (e_pos i).injective (Subtype.ext heq)
      subst htt'
      exact (Finset.mem_filter.mp ht').2
    · intro hne
      exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, hne⟩, rfl⟩
  have hPneg_iff : ∀ (i : Fin n) (t : Fin (V_neg i).card),
      (e_neg i t).1 ∈ P_neg i ↔ pairFin (V_neg i).card t ≠ t := by
    intro i t
    constructor
    · intro hm
      obtain ⟨t', ht', heq⟩ := Finset.mem_image.mp hm
      have htt' : t' = t := (e_neg i).injective (Subtype.ext heq)
      subst htt'
      exact (Finset.mem_filter.mp ht').2
    · intro hne
      exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, hne⟩, rfl⟩
  have hβ_eval_pos : ∀ (i : Fin n) (y : Fin m × Bool) (hy_own : owner y = i)
      (hy_pos : y ∈ P_pos i),
      β y = (e_pos i (pairFin (V_pos i).card ((e_pos i).symm ⟨y, hPpos_sub i hy_pos⟩))).1 := by
    intro i y hy_own hy_pos
    dsimp [β]
    subst hy_own
    rw [dif_pos hy_pos]
  have hβ_eval_neg : ∀ (i : Fin n) (y : Fin m × Bool) (hy_own : owner y = i)
      (hy_np : y ∉ P_pos i) (hy_neg : y ∈ P_neg i),
      β y = (e_neg i (pairFin (V_neg i).card ((e_neg i).symm ⟨y, hPneg_sub i hy_neg⟩))).1 := by
    intro i y hy_own hy_np hy_neg
    dsimp [β]
    subst hy_own
    rw [dif_neg hy_np, dif_pos hy_neg]
  have hβ_eval_rem : ∀ (i : Fin n) (y : Fin m × Bool) (hy_own : owner y = i)
      (hy_rem : y ∈ V_rem i),
      β y = (e_rem i (pairFin (V_rem i).card ((e_rem i).symm ⟨y, hy_rem⟩))).1 := by
    intro i y hy_own hy_rem
    obtain ⟨_, hy_not_P⟩ := Finset.mem_sdiff.mp hy_rem
    have hy_np : y ∉ P_pos i := fun h => hy_not_P (Finset.mem_union_left _ h)
    have hy_nn : y ∉ P_neg i := fun h => hy_not_P (Finset.mem_union_right _ h)
    dsimp [β]
    subst hy_own
    rw [dif_neg hy_np, dif_neg hy_nn]
  have hβ_Ppos : ∀ (i : Fin n) {x : Fin m × Bool} (hx : x ∈ P_pos i),
      β x ∈ P_pos i ∧ β x ≠ x ∧ β (β x) = x := by
    intro i x hx
    have hx_own : owner x = i :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp (hPpos_sub i hx)).1).2
    let t := (e_pos i).symm ⟨x, hPpos_sub i hx⟩
    have het : (e_pos i t).1 = x := congrArg Subtype.val ((e_pos i).apply_symm_apply _)
    have ht_ne : pairFin (V_pos i).card t ≠ t := (hPpos_iff i t).mp (het.symm ▸ hx)
    have hβx_eq : β x = (e_pos i (pairFin (V_pos i).card t)).1 := hβ_eval_pos i x hx_own hx
    let t' := pairFin (V_pos i).card t
    have ht'_ne : pairFin (V_pos i).card t' ≠ t' := by
      rw [pairFin_invol]; exact ht_ne.symm
    have hβx_mem : β x ∈ P_pos i := by
      rw [hβx_eq]; exact (hPpos_iff i t').mpr ht'_ne
    have hβx_ne : β x ≠ x := by
      rw [hβx_eq, ← het]
      intro h; exact ht_ne ((e_pos i).injective (Subtype.ext h))
    have hββx : β (β x) = x := by
      have hown' : owner (β x) = i := (hβ_owner x).trans hx_own
      rw [hβ_eval_pos i (β x) hown' hβx_mem]
      have hsymm_y : (e_pos i).symm ⟨β x, hPpos_sub i hβx_mem⟩ = t' := by
        apply (e_pos i).injective
        rw [(e_pos i).apply_symm_apply]
        exact Subtype.ext hβx_eq
      rw [hsymm_y, pairFin_invol, het]
    exact ⟨hβx_mem, hβx_ne, hββx⟩
  have hβ_Pneg : ∀ (i : Fin n) {x : Fin m × Bool} (hx : x ∈ P_neg i),
      β x ∈ P_neg i ∧ β x ≠ x ∧ β (β x) = x := by
    intro i x hx
    have hx_own : owner x = i :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp (hPneg_sub i hx)).1).2
    have hx_not_pos : x ∉ P_pos i := Finset.disjoint_right.mp (hdisj_Ppn i) hx
    let t := (e_neg i).symm ⟨x, hPneg_sub i hx⟩
    have het : (e_neg i t).1 = x := congrArg Subtype.val ((e_neg i).apply_symm_apply _)
    have ht_ne : pairFin (V_neg i).card t ≠ t := (hPneg_iff i t).mp (het.symm ▸ hx)
    have hβx_eq : β x = (e_neg i (pairFin (V_neg i).card t)).1 :=
      hβ_eval_neg i x hx_own hx_not_pos hx
    let t' := pairFin (V_neg i).card t
    have ht'_ne : pairFin (V_neg i).card t' ≠ t' := by
      rw [pairFin_invol]; exact ht_ne.symm
    have hβx_mem : β x ∈ P_neg i := by
      rw [hβx_eq]; exact (hPneg_iff i t').mpr ht'_ne
    have hβx_not_pos : β x ∉ P_pos i := Finset.disjoint_right.mp (hdisj_Ppn i) hβx_mem
    have hβx_ne : β x ≠ x := by
      rw [hβx_eq, ← het]
      intro h; exact ht_ne ((e_neg i).injective (Subtype.ext h))
    have hββx : β (β x) = x := by
      have hown' : owner (β x) = i := (hβ_owner x).trans hx_own
      rw [hβ_eval_neg i (β x) hown' hβx_not_pos hβx_mem]
      have hsymm_y : (e_neg i).symm ⟨β x, hPneg_sub i hβx_mem⟩ = t' := by
        apply (e_neg i).injective
        rw [(e_neg i).apply_symm_apply]
        exact Subtype.ext hβx_eq
      rw [hsymm_y, pairFin_invol, het]
    exact ⟨hβx_mem, hβx_ne, hββx⟩
  have hβ_Vrem : ∀ (i : Fin n) {x : Fin m × Bool} (hx : x ∈ V_rem i),
      β x = (e_rem i (pairFin (V_rem i).card ((e_rem i).symm ⟨x, hx⟩))).1 ∧
      β x ∈ V_rem i ∧ β (β x) = x := by
    intro i x hx
    obtain ⟨hx_Vi, _⟩ := Finset.mem_sdiff.mp hx
    have hx_own : owner x = i := (Finset.mem_filter.mp hx_Vi).2
    let t := (e_rem i).symm ⟨x, hx⟩
    have het : (e_rem i t).1 = x := congrArg Subtype.val ((e_rem i).apply_symm_apply _)
    have hβx_eq : β x = (e_rem i (pairFin (V_rem i).card t)).1 := hβ_eval_rem i x hx_own hx
    let t' := pairFin (V_rem i).card t
    have hβx_mem : β x ∈ V_rem i := by rw [hβx_eq]; exact (e_rem i t').2
    have hββx : β (β x) = x := by
      have hown' : owner (β x) = i := (hβ_owner x).trans hx_own
      rw [hβ_eval_rem i (β x) hown' hβx_mem]
      have hsymm_y : (e_rem i).symm ⟨β x, hβx_mem⟩ = t' := by
        apply (e_rem i).injective
        rw [(e_rem i).apply_symm_apply]
        exact Subtype.ext hβx_eq
      rw [hsymm_y, pairFin_invol, het]
    exact ⟨hβx_eq, hβx_mem, hββx⟩
  have hβ_invol : ∀ x, β (β x) = x := by
    intro x
    let i := owner x
    by_cases hx_pos : x ∈ P_pos i
    · exact (hβ_Ppos i hx_pos).2.2
    · by_cases hx_neg : x ∈ P_neg i
      · exact (hβ_Pneg i hx_neg).2.2
      · have hx_rem : x ∈ V_rem i := Finset.mem_sdiff.mpr
          ⟨by simp [ownedVerts, i, owner], by simp [Finset.mem_union, hx_pos, hx_neg]⟩
        exact (hβ_Vrem i hx_rem).2.2
  -- Item involution `α_item (g, b) = (g, ! b)`
  let α_item : Fin m × Bool → Fin m × Bool := fun x => (x.1, ! x.2)
  obtain ⟨c, hc_item, hc_agent⟩ := two_color_involutions α_item β
    (fun ⟨g, b⟩ => by simp [α_item])
    (fun ⟨g, b⟩ => by intro h; have := congrArg Prod.snd h; cases b <;> simp [α_item] at this)
    hβ_invol
  -- Define the recolored allocations `C` and `D`
  let C : Allocation n m := fun g => if c (g, false) then A g else B g
  let D : Allocation n m := fun g => if c (g, false) then B g else A g
  -- Bijection between `V_i.filter (c = true)` and `bundle C i` (and `c = false` with `bundle D i`)
  have hC_iff : ∀ (i : Fin n) (g : Fin m),
      g ∈ bundle C i ↔ ∃ b : Bool, (g, b) ∈ ownedVerts A B i ∧ c (g, b) = true := by
    intro i g
    rw [mem_bundle_iff]
    have hct := hc_item (g, false)
    simp only [α_item, Bool.not_false] at hct
    constructor
    · intro hCg
      dsimp [C] at hCg
      by_cases hcf : c (g, false) = true
      · rw [if_pos hcf] at hCg
        exact ⟨false, by simp [ownedVerts, hCg], hcf⟩
      · have hcf_f : c (g, false) = false := Bool.eq_false_iff.mpr hcf
        rw [hcf_f] at hCg hct; simp at hCg hct
        exact ⟨true, by simp [ownedVerts, hCg], hct⟩
    · rintro ⟨b, hown, hcb⟩
      have hown' : (if b then B g else A g) = i := (Finset.mem_filter.mp hown).2
      dsimp [C]
      cases b
      · simp at hown'
        rw [if_pos hcb]; exact hown'
      · simp at hown'
        rw [hct] at hcb
        have hcf_f : c (g, false) = false := by
          by_cases h0 : c (g, false) = false
          · exact h0
          · have h1 : c (g, false) = true := Bool.eq_true_of_not_eq_false h0
            rw [h1] at hcb; simp at hcb
        rw [hcf_f]; simp; exact hown'
  have hD_iff : ∀ (i : Fin n) (g : Fin m),
      g ∈ bundle D i ↔ ∃ b : Bool, (g, b) ∈ ownedVerts A B i ∧ c (g, b) = false := by
    intro i g
    rw [mem_bundle_iff]
    have hct := hc_item (g, false)
    simp only [α_item, Bool.not_false] at hct
    constructor
    · intro hDg
      dsimp [D] at hDg
      by_cases hcf : c (g, false) = true
      · rw [if_pos hcf] at hDg
        rw [hcf] at hct; simp at hct
        exact ⟨true, by simp [ownedVerts, hDg], hct⟩
      · have hcf_f : c (g, false) = false := Bool.eq_false_iff.mpr hcf
        rw [hcf_f] at hDg; simp at hDg
        exact ⟨false, by simp [ownedVerts, hDg], hcf_f⟩
    · rintro ⟨b, hown, hcb⟩
      have hown' : (if b then B g else A g) = i := (Finset.mem_filter.mp hown).2
      dsimp [D]
      cases b
      · simp at hown'
        rw [hcb]; simp; exact hown'
      · simp at hown'
        rw [hct] at hcb
        have hcf_t : c (g, false) = true := by
          by_cases h0 : c (g, false) = true
          · exact h0
          · have h1 : c (g, false) = false := Bool.eq_false_iff.mpr h0
            rw [h1] at hcb; simp at hcb
        rw [if_pos hcf_t]; exact hown'
  have hinj_color : ∀ (i : Fin n) (b_col : Bool),
      Set.InjOn Prod.fst ((ownedVerts A B i).filter (fun v_x => c v_x = b_col) :
        Set (Fin m × Bool)) := by
    intro i b_col ⟨g₁, b₁⟩ h₁ ⟨g₂, b₂⟩ h₂ hg_eq
    dsimp at hg_eq
    subst hg_eq
    have hc1 : c (g₁, b₁) = b_col := (Finset.mem_filter.mp h₁).2
    have hc2 : c (g₁, b₂) = b_col := (Finset.mem_filter.mp h₂).2
    have hct := hc_item (g₁, false)
    simp only [α_item, Bool.not_false] at hct
    cases b₁ <;> cases b₂
    · rfl
    · rw [hct] at hc2; rw [hc1] at hc2; cases b_col <;> simp at hc2
    · rw [hct] at hc1; rw [hc2] at hc1; cases b_col <;> simp at hc1
    · rfl
  have hbundleC_image : ∀ i : Fin n,
      bundle C i = ((ownedVerts A B i).filter (fun v_x => c v_x = true)).image Prod.fst := by
    intro i; ext g
    rw [hC_iff i g, Finset.mem_image]
    constructor
    · rintro ⟨b, h1, h2⟩; exact ⟨(g, b), Finset.mem_filter.mpr ⟨h1, h2⟩, rfl⟩
    · rintro ⟨⟨g', b⟩, hm, rfl⟩
      exact ⟨b, (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2⟩
  have hbundleD_image : ∀ i : Fin n,
      bundle D i = ((ownedVerts A B i).filter (fun v_x => c v_x = false)).image Prod.fst := by
    intro i; ext g
    rw [hD_iff i g, Finset.mem_image]
    constructor
    · rintro ⟨b, h1, h2⟩; exact ⟨(g, b), Finset.mem_filter.mpr ⟨h1, h2⟩, rfl⟩
    · rintro ⟨⟨g', b⟩, hm, rfl⟩
      exact ⟨b, (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2⟩
  -- At most 1 fixed point of `β` on `ownedVerts A B i`
  have hfix_Vi_le1 : ∀ i : Fin n, ((ownedVerts A B i).filter (fun x => β x = x)).card ≤ 1 := by
    intro i
    have hsub_rem : (ownedVerts A B i).filter (fun x => β x = x) ⊆
        (Finset.univ.filter (fun t : Fin (V_rem i).card => pairFin (V_rem i).card t = t)).image
          (fun t => (e_rem i t).1) := by
      intro x hx
      obtain ⟨hx_Vi, hβx⟩ := Finset.mem_filter.mp hx
      have hx_np : x ∉ P_pos i := fun hp => (hβ_Ppos i hp).2.1 hβx
      have hx_nn : x ∉ P_neg i := fun hn => (hβ_Pneg i hn).2.1 hβx
      have hx_rem : x ∈ V_rem i := Finset.mem_sdiff.mpr
        ⟨hx_Vi, by simp [Finset.mem_union, hx_np, hx_nn]⟩
      let t := (e_rem i).symm ⟨x, hx_rem⟩
      have hβ_eq := (hβ_Vrem i hx_rem).1
      have ht_fix : pairFin (V_rem i).card t = t := by
        apply (e_rem i).injective
        apply Subtype.ext
        rw [← hβ_eq, hβx, ((e_rem i).apply_symm_apply _)]
      exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht_fix⟩,
        congrArg Subtype.val ((e_rem i).apply_symm_apply _)⟩
    calc ((ownedVerts A B i).filter (fun x => β x = x)).card
        ≤ ((Finset.univ.filter (fun t : Fin (V_rem i).card =>
            pairFin (V_rem i).card t = t)).image (fun t => (e_rem i t).1)).card :=
          Finset.card_le_card hsub_rem
      _ ≤ (Finset.univ.filter (fun t : Fin (V_rem i).card =>
            pairFin (V_rem i).card t = t)).card := Finset.card_image_le
      _ ≤ 1 := pairFin_fixed_card_le_one _
  have hβ_stab_Vi : ∀ i : Fin n, ∀ x ∈ ownedVerts A B i, β x ∈ ownedVerts A B i := by
    intro i x hx
    have hown := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hβ_owner x).trans hown⟩
  -- Check `IsBalanced C` and `IsBalanced D`
  have hbalC : IsBalanced C := by
    intro i
    have hcard_eq : (bundle C i).card =
        ((ownedVerts A B i).filter (fun v_x => c v_x = true)).card := by
      rw [hbundleC_image i, Finset.card_image_of_injOn (hinj_color i true)]
    have hsp := involution_color_split (ownedVerts A B i) β c (hβ_stab_Vi i)
      (fun x _ => hβ_invol x) (hfix_Vi_le1 i) (fun x _ hne => hc_agent x hne) true
    have hVi_card := card_ownedVerts A B i
    rcases hA.1 i with ha | ha <;> rcases hB.1 i with hb | hb <;> omega
  have hbalD : IsBalanced D := by
    intro i
    have hcard_eq : (bundle D i).card =
        ((ownedVerts A B i).filter (fun v_x => c v_x = false)).card := by
      rw [hbundleD_image i, Finset.card_image_of_injOn (hinj_color i false)]
    have hsp := involution_color_split (ownedVerts A B i) β c (hβ_stab_Vi i)
      (fun x _ => hβ_invol x) (hfix_Vi_le1 i) (fun x _ hne => hc_agent x hne) false
    have hVi_card := card_ownedVerts A B i
    rcases hA.1 i with ha | ha <;> rcases hB.1 i with hb | hb <;> omega
  -- Equation (16): welfare conservation per agent `i`
  have hwelfare_eq : ∀ i : Fin n,
      bval v i (bundle C i) + bval v i (bundle D i) =
        bval v i (bundle A i) + bval v i (bundle B i) := by
    intro i
    unfold bval
    rw [hbundleC_image i, hbundleD_image i,
      Finset.sum_image (hinj_color i true), Finset.sum_image (hinj_color i false)]
    have hrew : (ownedVerts A B i).filter (fun v_x => c v_x = false) =
        (ownedVerts A B i).filter (fun v_x => ¬ (c v_x = true)) := by
      ext v_x; simp only [Finset.mem_filter]; cases c v_x <;> simp
    rw [hrew, Finset.sum_filter_add_sum_filter_not, sum_ownedVerts]
  -- Equations (17) & (18): prefix inequalities for all `i` and `l`
  have hpos_ge : ∀ (i : Fin n) (l : ℕ),
      maxSubSum (ownedVerts A B i) (fun v_x => posPrice p v_x.1) (2 * l) ≤
        maxSubSum (bundle C i) (posPrice p) l + maxSubSum (bundle D i) (posPrice p) l := by
    intro i l
    have hβ_cls_pos : ∀ t : Fin (V_pos i).card, pairFin (V_pos i).card t ≠ t →
        β (sortedEquiv (V_pos i) (fun v_x => posPrice p v_x.1) t).1 =
          (sortedEquiv (V_pos i) (fun v_x => posPrice p v_x.1) (pairFin (V_pos i).card t)).1 := by
      intro t hne
      change β (e_pos i t).1 = (e_pos i (pairFin (V_pos i).card t)).1
      have hx_pos : (e_pos i t).1 ∈ P_pos i := (hPpos_iff i t).mpr hne
      have hx_own : owner (e_pos i t).1 = i :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp (e_pos i t).2).1).2
      rw [hβ_eval_pos i (e_pos i t).1 hx_own hx_pos]
      have hsymm : (e_pos i).symm ⟨(e_pos i t).1, hPpos_sub i hx_pos⟩ = t := by
        apply (e_pos i).injective
        rw [(e_pos i).apply_symm_apply]
      rw [hsymm]
    have hC_mem : ∀ x ∈ ownedVerts A B i, c x = true → x.1 ∈ bundle C i := by
      intro x hx hcx
      rw [hbundleC_image i]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hcx⟩, rfl⟩
    have hD_mem : ∀ x ∈ ownedVerts A B i, c x = false → x.1 ∈ bundle D i := by
      intro x hx hcx
      rw [hbundleD_image i]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hcx⟩, rfl⟩
    exact class_prefix_recomb_ge (ownedVerts A B i) (posPrice p)
      (fun _ => le_max_right _ _) (V_pos i) rfl β hβ_cls_pos c (fun x _ hne => hc_agent x hne)
      (bundle C i) (bundle D i) hC_mem (hinj_color i true) hD_mem (hinj_color i false) l
  have hneg_ge : ∀ (i : Fin n) (l : ℕ),
      maxSubSum (ownedVerts A B i) (fun v_x => negPrice p v_x.1) (2 * l) ≤
        maxSubSum (bundle C i) (negPrice p) l + maxSubSum (bundle D i) (negPrice p) l := by
    intro i l
    have hβ_cls_neg : ∀ t : Fin (V_neg i).card, pairFin (V_neg i).card t ≠ t →
        β (sortedEquiv (V_neg i) (fun v_x => negPrice p v_x.1) t).1 =
          (sortedEquiv (V_neg i) (fun v_x => negPrice p v_x.1) (pairFin (V_neg i).card t)).1 := by
      intro t hne
      change β (e_neg i t).1 = (e_neg i (pairFin (V_neg i).card t)).1
      have hx_neg : (e_neg i t).1 ∈ P_neg i := (hPneg_iff i t).mpr hne
      have hx_not_pos : (e_neg i t).1 ∉ P_pos i := Finset.disjoint_right.mp (hdisj_Ppn i) hx_neg
      have hx_own : owner (e_neg i t).1 = i :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp (e_neg i t).2).1).2
      rw [hβ_eval_neg i (e_neg i t).1 hx_own hx_not_pos hx_neg]
      have hsymm : (e_neg i).symm ⟨(e_neg i t).1, hPneg_sub i hx_neg⟩ = t := by
        apply (e_neg i).injective
        rw [(e_neg i).apply_symm_apply]
      rw [hsymm]
    have hC_mem : ∀ x ∈ ownedVerts A B i, c x = true → x.1 ∈ bundle C i := by
      intro x hx hcx
      rw [hbundleC_image i]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hcx⟩, rfl⟩
    have hD_mem : ∀ x ∈ ownedVerts A B i, c x = false → x.1 ∈ bundle D i := by
      intro x hx hcx
      rw [hbundleD_image i]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hcx⟩, rfl⟩
    exact class_prefix_recomb_ge (ownedVerts A B i) (negPrice p)
      (fun _ => le_max_right _ _) (V_neg i) rfl β hβ_cls_neg c (fun x _ hne => hc_agent x hne)
      (bundle C i) (bundle D i) hC_mem (hinj_color i true) hD_mem (hinj_color i false) l
  -- Score comparison forces every nonnegative gap to vanish!
  let gapPos (i : Fin n) (l : ℕ) : ℝ :=
    (maxSubSum (bundle C i) (posPrice p) l + maxSubSum (bundle D i) (posPrice p) l) -
    (maxSubSum (bundle A i) (posPrice p) l + maxSubSum (bundle B i) (posPrice p) l)
  let gapNeg (i : Fin n) (l : ℕ) : ℝ :=
    (maxSubSum (bundle C i) (negPrice p) l + maxSubSum (bundle D i) (negPrice p) l) -
    (maxSubSum (bundle A i) (negPrice p) l + maxSubSum (bundle B i) (negPrice p) l)
  have hgapPos_nn : ∀ i l, 0 ≤ gapPos i l := fun i l => by
    dsimp [gapPos]
    linarith [maxSubSum_ownedVerts_ge A B i (posPrice p) l, hpos_ge i l]
  have hgapNeg_nn : ∀ i l, 0 ≤ gapNeg i l := fun i l => by
    dsimp [gapNeg]
    linarith [maxSubSum_ownedVerts_ge A B i (negPrice p) l, hneg_ge i l]
  have hscore_sum_le : scorePert v ρ lam eps w C + scorePert v ρ lam eps w D ≤
      scorePert v ρ lam eps w A + scorePert v ρ lam eps w B :=
    add_le_add (hA.2 C hbalC) (hB.2 D hbalD)
  have hscore_diff : (scorePert v ρ lam eps w C + scorePert v ρ lam eps w D) -
      (scorePert v ρ lam eps w A + scorePert v ρ lam eps w B) =
      eps * ∑ i : Fin n, ∑ l ∈ Finset.Icc 1 (m / n + 1), (gapPos i l + gapNeg i l) := by
    unfold scorePert phiPot
    have hw_sum : (∑ i, alphaW ρ w i * bval v i (bundle C i)) +
          (∑ i, alphaW ρ w i * bval v i (bundle D i)) =
        (∑ i, alphaW ρ w i * bval v i (bundle A i)) +
          (∑ i, alphaW ρ w i * bval v i (bundle B i)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_add, ← mul_add, hwelfare_eq i]
    have hphi_diff : (phiPot n m p C + phiPot n m p D) - (phiPot n m p A + phiPot n m p B) =
        ∑ i : Fin n, ∑ l ∈ Finset.Icc 1 (m / n + 1), (gapPos i l + gapNeg i l) := by
      unfold phiPot
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => by dsimp [gapPos, gapNeg]; ring
    unfold phiPot at hphi_diff
    change ((∑ i, alphaW ρ w i * bval v i (bundle C i)) + eps * phiPot n m p C +
        ((∑ i, alphaW ρ w i * bval v i (bundle D i)) + eps * phiPot n m p D)) -
      ((∑ i, alphaW ρ w i * bval v i (bundle A i)) + eps * phiPot n m p A +
        ((∑ i, alphaW ρ w i * bval v i (bundle B i)) + eps * phiPot n m p B)) = _
    have hphi_diff' : (phiPot n m p C + phiPot n m p D) - (phiPot n m p A + phiPot n m p B) =
        ∑ i : Fin n, ∑ l ∈ Finset.Icc 1 (m / n + 1), (gapPos i l + gapNeg i l) := by
      unfold phiPot
      exact hphi_diff
    linarith [show eps * (phiPot n m p C + phiPot n m p D - (phiPot n m p A + phiPot n m p B)) =
      eps * phiPot n m p C + eps * phiPot n m p D - (eps * phiPot n m p A + eps * phiPot n m p B) by ring,
      congrArg (eps * ·) hphi_diff']
  have hsum_zero : ∑ i : Fin n, ∑ l ∈ Finset.Icc 1 (m / n + 1), (gapPos i l + gapNeg i l) = 0 := by
    have hle0 : ∑ i : Fin n, ∑ l ∈ Finset.Icc 1 (m / n + 1), (gapPos i l + gapNeg i l) ≤ 0 := by
      nlinarith
    have hge0 : 0 ≤ ∑ i : Fin n, ∑ l ∈ Finset.Icc 1 (m / n + 1), (gapPos i l + gapNeg i l) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l _ =>
        add_nonneg (hgapPos_nn i l) (hgapNeg_nn i l)
    exact le_antisymm hle0 hge0
  intro i l hl
  have hi_zero : ∑ l' ∈ Finset.Icc 1 (m / n + 1), (gapPos i l' + gapNeg i l') = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i' _ => Finset.sum_nonneg fun l' _ =>
      add_nonneg (hgapPos_nn i' l') (hgapNeg_nn i' l'))).mp hsum_zero i (Finset.mem_univ i)
  have hl_zero : gapPos i l + gapNeg i l = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun l' _ =>
      add_nonneg (hgapPos_nn i l') (hgapNeg_nn i l'))).mp hi_zero l hl
  have hgp0 : gapPos i l = 0 := by linarith [hgapPos_nn i l, hgapNeg_nn i l]
  have hgn0 : gapNeg i l = 0 := by linarith [hgapPos_nn i l, hgapNeg_nn i l]
  dsimp [gapPos] at hgp0
  dsimp [gapNeg] at hgn0
  exact ⟨le_antisymm (maxSubSum_ownedVerts_ge A B i (posPrice p) l) (by linarith [hpos_ge i l]),
         le_antisymm (maxSubSum_ownedVerts_ge A B i (negPrice p) l) (by linarith [hneg_ge i l])⟩

end PrefixAndInterlacing

/-! ### §3.5: KKM Selection (`Lemmas 6, 7, 8`) -/

section KKMSelection

noncomputable def subseqOfUnbounded (S : Set ℕ) (hunb : ∀ M : ℕ, ∃ k ∈ S, M < k) : ℕ → ℕ
  | 0 => Classical.choose (hunb 0)
  | t + 1 => Classical.choose (hunb (subseqOfUnbounded S hunb t))

lemma exists_strictMono_of_infinite {S : Set ℕ} (hS : S.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ t, φ t ∈ S := by
  have hunb : ∀ M : ℕ, ∃ k ∈ S, M < k := by
    intro M
    by_contra hnot
    push_neg at hnot
    have hsub : S ⊆ ((Finset.Iic M : Finset ℕ) : Set ℕ) := by
      intro k hk
      exact Finset.mem_coe.mpr (Finset.mem_Iic.mpr (hnot k hk))
    exact hS ((Finset.finite_toSet (Finset.Iic M)).subset hsub)
  refine ⟨subseqOfUnbounded S hunb, strictMono_nat_of_lt_succ fun t => ?_, fun t => ?_⟩
  · exact (Classical.choose_spec (hunb (subseqOfUnbounded S hunb t))).2
  · cases t with
    | zero => exact (Classical.choose_spec (hunb 0)).1
    | succ t => exact (Classical.choose_spec (hunb (subseqOfUnbounded S hunb t))).1

lemma exists_const_subseq_of_finite {α : Type*} [Finite α] (f : ℕ → α) :
    ∃ (y : α) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ t, f (φ t) = y := by
  obtain ⟨y, hinf⟩ := Finite.exists_infinite_fiber f
  obtain ⟨φ, hmono, hmem⟩ := exists_strictMono_of_infinite (Set.infinite_coe_iff.mp hinf)
  exact ⟨y, φ, hmono, fun t => Set.mem_singleton_iff.mp (hmem t)⟩

lemma tendsto_inv_nat_succ_comp {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Tendsto (fun k : ℕ => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => ((φ k : ℝ) + 1)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop).atTop_add tendsto_const_nhds
  simp only [one_div]
  exact tendsto_inv_atTop_zero.comp h1

def qSize (n m : ℕ) : ℕ := if n ∣ m then m / n else m / n + 1

lemma bundle_nonempty_of_isBalanced {n m : ℕ} (hr1 : 1 ≤ m / n)
    {A : Allocation n m} (hbal : IsBalanced A) (i : Fin n) :
    (bundle A i).Nonempty :=
  Finset.card_pos.mp (by rcases hbal i with h | h <;> omega)

lemma card_bundle_eq_div_of_dvd {n m : ℕ} {A : Allocation n m}
    (hbal : IsBalanced A) (hdvd : n ∣ m) (i : Fin n) :
    (bundle A i).card = m / n := by
  by_contra hne
  have hi_eq : (bundle A i).card = m / n + 1 := (hbal i).resolve_left hne
  have hle : ∀ k ∈ (Finset.univ : Finset (Fin n)), m / n ≤ (bundle A k).card := by
    intro k _
    rcases hbal k with h | h <;> omega
  have hlt : ∑ _k : Fin n, (m / n) < ∑ k : Fin n, (bundle A k).card :=
    Finset.sum_lt_sum hle ⟨i, Finset.mem_univ i, by omega⟩
  have hlhs : (∑ _k : Fin n, (m / n)) = m := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact Nat.mul_div_cancel' hdvd
  have hrhs := sum_card_bundle A
  omega

lemma card_bundle_le_qSize {n m : ℕ} {A : Allocation n m}
    (hbal : IsBalanced A) (i : Fin n) :
    (bundle A i).card ≤ qSize n m := by
  unfold qSize
  split_ifs with hdvd
  · rw [card_bundle_eq_div_of_dvd hbal hdvd i]
  · rcases hbal i with h | h <;> omega

lemma qSize_bounds {n m : ℕ} (hr1 : 1 ≤ m / n) :
    1 ≤ qSize n m ∧ m / n ≤ qSize n m ∧ qSize n m ≤ m / n + 1 := by
  unfold qSize
  split_ifs <;> refine ⟨by omega, by omega, by omega⟩

noncomputable def minBundleVal {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n)
    (S : Finset (Fin m)) : ℝ :=
  if h : S.Nonempty then S.inf' h (fun g => v i g) else 0

noncomputable def maxBundleVal {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n)
    (S : Finset (Fin m)) : ℝ :=
  if h : S.Nonempty then S.sup' h (fun g => v i g) else 0

noncomputable def hatMin {n m : ℕ} (v : Fin n → Fin m → ℝ) (A : Allocation n m)
    (i k : Fin n) : ℝ :=
  if (bundle A k).card = qSize n m then minBundleVal v i (bundle A k)
  else min 0 (minBundleVal v i (bundle A k))

noncomputable def hatMax {n m : ℕ} (v : Fin n → Fin m → ℝ) (A : Allocation n m)
    (i k : Fin n) : ℝ :=
  if (bundle A k).card = qSize n m then maxBundleVal v i (bundle A k)
  else max 0 (maxBundleVal v i (bundle A k))

def envy {n m : ℕ} (v : Fin n → Fin m → ℝ) (A : Allocation n m) (i j : Fin n) : ℝ :=
  bval v i (bundle A j) - bval v i (bundle A i)

noncomputable def resEnvy {n m : ℕ} (v : Fin n → Fin m → ℝ) (A : Allocation n m)
    (i j : Fin n) : ℝ :=
  min (envy v A i j) (envy v A i j + hatMin v A i i - hatMax v A i j)

lemma abs_minMaxBundleVal_le_vmax {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n)
    (S : Finset (Fin m)) :
    |minBundleVal v i S| ≤ vmax v ∧ |maxBundleVal v i S| ≤ vmax v := by
  have hV := vmax_nonneg v
  unfold minBundleVal maxBundleVal
  split_ifs with hne
  · obtain ⟨g₁, hg₁, heq₁⟩ := Finset.exists_mem_eq_inf' hne (fun g => v i g)
    obtain ⟨g₂, hg₂, heq₂⟩ := Finset.exists_mem_eq_sup' hne (fun g => v i g)
    rw [heq₁, heq₂]
    exact ⟨abs_val_le_vmax v i g₁, abs_val_le_vmax v i g₂⟩
  · simp [hV]

lemma abs_hatMinMax_le_vmax {n m : ℕ} (v : Fin n → Fin m → ℝ) (A : Allocation n m)
    (i k : Fin n) :
    |hatMin v A i k| ≤ vmax v ∧ |hatMax v A i k| ≤ vmax v := by
  have hV := vmax_nonneg v
  obtain ⟨hm, hM⟩ := abs_minMaxBundleVal_le_vmax v i (bundle A k)
  obtain ⟨hm1, hm2⟩ := abs_le.mp hm
  obtain ⟨hM1, hM2⟩ := abs_le.mp hM
  constructor
  · unfold hatMin
    split_ifs
    · exact hm
    · rw [abs_le]; exact ⟨le_min (by linarith) hm1, le_trans (min_le_left _ _) hV⟩
  · unfold hatMax
    split_ifs
    · exact hM
    · rw [abs_le]; exact ⟨le_trans (by linarith) (le_max_left _ _), max_le hV hM2⟩

lemma envy_and_resEnvy_bounds {n m : ℕ} (v : Fin n → Fin m → ℝ)
    {A : Allocation n m} (hbal : IsBalanced A) (i j : Fin n) :
    let K := 2 * (((m / n : ℕ) : ℝ) + 1) * vmax v
    let H := 2 * (((m / n : ℕ) : ℝ) + 2) * vmax v
    |envy v A i j| ≤ K ∧ resEnvy v A i j ≤ envy v A i j ∧ - H ≤ resEnvy v A i j := by
  intro K H
  have hV := vmax_nonneg v
  have hbval_le : ∀ k : Fin n, |bval v i (bundle A k)| ≤ (((m / n : ℕ) : ℝ) + 1) * vmax v := by
    intro k
    unfold bval
    have hcard_le : ((bundle A k).card : ℝ) ≤ ((m / n : ℕ) : ℝ) + 1 := by
      rcases hbal k with h | h <;> rw [h] <;> push_cast <;> linarith
    calc |∑ g ∈ bundle A k, v i g|
        ≤ ∑ g ∈ bundle A k, |v i g| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _g ∈ bundle A k, vmax v := Finset.sum_le_sum fun g _ => abs_val_le_vmax v i g
      _ = ((bundle A k).card : ℝ) * vmax v := by simp [nsmul_eq_mul]
      _ ≤ (((m / n : ℕ) : ℝ) + 1) * vmax v := mul_le_mul_of_nonneg_right hcard_le hV
  have henvy_abs : |envy v A i j| ≤ K := by
    unfold envy
    have hj := abs_le.mp (hbval_le j)
    have hi := abs_le.mp (hbval_le i)
    rw [abs_le]
    dsimp [K]
    constructor <;> linarith
  obtain ⟨hmin_abs, _⟩ := abs_hatMinMax_le_vmax v A i i
  obtain ⟨_, hmax_abs⟩ := abs_hatMinMax_le_vmax v A i j
  have he := abs_le.mp henvy_abs
  have hm := abs_le.mp hmin_abs
  have hM := abs_le.mp hmax_abs
  refine ⟨henvy_abs, min_le_left _ _, le_min ?_ ?_⟩
  · dsimp [H, K] at he ⊢; linarith
  · dsimp [H, K] at he ⊢; linarith

noncomputable def flowF {n m : ℕ} (v : Fin n → Fin m → ℝ) (ρ γ : ℝ)
    (A : Allocation n m) (w : Fin n → ℝ) (i j : Fin n) : ℝ :=
  max (alphaW ρ w i * resEnvy v A i j + γ * (alphaW ρ w j - alphaW ρ w i)) 0

noncomputable def divD {n m : ℕ} (v : Fin n → Fin m → ℝ) (ρ γ : ℝ)
    (A : Allocation n m) (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, flowF v ρ γ A w i j) -
  (∑ j ∈ Finset.univ.erase i, flowF v ρ γ A w j i)

lemma flowF_nonneg {n m : ℕ} (v : Fin n → Fin m → ℝ) (ρ γ : ℝ)
    (A : Allocation n m) (w : Fin n → ℝ) (i j : Fin n) :
    0 ≤ flowF v ρ γ A w i j := le_max_right _ _

lemma continuous_flowF {n m : ℕ} (v : Fin n → Fin m → ℝ) (ρ γ : ℝ)
    (A : Allocation n m) (i j : Fin n) :
    Continuous (fun w : Fin n → ℝ => flowF v ρ γ A w i j) := by
  unfold flowF alphaW
  have hc_i : Continuous (fun w : Fin n → ℝ => ρ + (1 - (n : ℝ) * ρ) * w i) :=
    continuous_const.add (continuous_const.mul (continuous_apply i))
  have hc_j : Continuous (fun w : Fin n → ℝ => ρ + (1 - (n : ℝ) * ρ) * w j) :=
    continuous_const.add (continuous_const.mul (continuous_apply j))
  exact ((hc_i.mul continuous_const).add (continuous_const.mul (hc_j.sub hc_i))).max continuous_const

lemma continuous_divD {n m : ℕ} (v : Fin n → Fin m → ℝ) (ρ γ : ℝ)
    (A : Allocation n m) (i : Fin n) :
    Continuous (fun w : Fin n → ℝ => divD v ρ γ A w i) := by
  unfold divD
  exact (continuous_finsetSum _ fun j _ => continuous_flowF v ρ γ A i j).sub
    (continuous_finsetSum _ fun j _ => continuous_flowF v ρ γ A j i)

lemma sum_divD_eq_zero {n m : ℕ} (v : Fin n → Fin m → ℝ) (ρ γ : ℝ)
    (A : Allocation n m) (w : Fin n → ℝ) :
    ∑ i : Fin n, divD v ρ γ A w i = 0 := by
  unfold divD
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  have her : ∀ i : Fin n, Finset.univ.erase i = Finset.univ.filter (fun j : Fin n => j ≠ i) := by
    intro i; ext j; simp
  have h1 : (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, flowF v ρ γ A w i j) =
      ∑ i : Fin n, ∑ j : Fin n, if j ≠ i then flowF v ρ γ A w i j else 0 := by
    refine Finset.sum_congr rfl fun i _ => by rw [her i, Finset.sum_filter]
  have h2 : (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, flowF v ρ γ A w j i) =
      ∑ i : Fin n, ∑ j : Fin n, if j ≠ i then flowF v ρ γ A w j i else 0 := by
    refine Finset.sum_congr rfl fun i _ => by rw [her i, Finset.sum_filter]
  rw [h1, h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  by_cases hij : i = j
  · subst hij; simp
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji]

/-- KKM label set `F_i^{λ, ε}` (Equation (23)). -/
def kkmSet {n m : ℕ} (v : Fin n → Fin m → ℝ) (ρ γ lam eps : ℝ) (i : Fin n) :
    Set (Fin n → ℝ) :=
  {w | w ∈ stdSimplex ℝ (Fin n) ∧
    ∃ A : Allocation n m, IsScoreMax v ρ lam eps w A ∧
      ∀ k : Fin n, divD v ρ γ A w i ≤ divD v ρ γ A w k}

/-- Lemma 6 (Closed cover): `kkmSet` is closed for every agent `i`. -/
lemma isClosed_kkmSet {n m : ℕ} (v : Fin n → Fin m → ℝ)
    {ρ γ lam eps : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : (n : ℝ) * ρ ≤ 1) (hlam : 0 < lam)
    (i : Fin n) :
    IsClosed (kkmSet v ρ γ lam eps i) := by
  refine IsSeqClosed.isClosed fun wt w hwt_mem hwt_tend => ?_
  have hwt_simp : ∀ t, wt t ∈ stdSimplex ℝ (Fin n) := fun t => (hwt_mem t).1
  have hw_simp : w ∈ stdSimplex ℝ (Fin n) :=
    (isCompact_stdSimplex ℝ (Fin n)).isClosed.mem_of_tendsto hwt_tend
      (Eventually.of_forall hwt_simp)
  choose At hAt_score hAt_div using fun t => (hwt_mem t).2
  obtain ⟨A, φ₁, hφ₁_mono, hA_const⟩ := exists_const_subseq_of_finite At
  have hzp_box : ∀ k, regDual v ρ lam (wt (φ₁ k)) ∈ BoxDual v :=
    fun k => (regDual_spec v hρ0 hρ1 hlam (hwt_simp (φ₁ k))).1.1
  obtain ⟨zp_lim, _, φ₂, hφ₂_mono, hzp_tend⟩ :=
    (isCompact_BoxDual v).tendsto_subseq hzp_box
  let ψ : ℕ → ℕ := fun k => φ₁ (φ₂ k)
  have hwt_ψ_tend : Tendsto (fun k => wt (ψ k)) atTop (𝓝 w) :=
    hwt_tend.comp (hφ₁_mono.comp hφ₂_mono).tendsto_atTop
  have hzp_eq : zp_lim = regDual v ρ lam w :=
    regDual_eq_of_tendsto v hρ0 hρ1 hlam (fun k => hwt_simp (ψ k)) hw_simp hwt_ψ_tend hzp_tend
  have hp_tend : Tendsto (fun k => (regDual v ρ lam (wt (ψ k))).2) atTop
      (𝓝 (regDual v ρ lam w).2) := by
    rw [← hzp_eq]
    exact continuous_snd.continuousAt.tendsto.comp hzp_tend
  have hscore_tend : ∀ X : Allocation n m,
      Tendsto (fun k => scorePert v ρ lam eps (wt (ψ k)) X) atTop
        (𝓝 (scorePert v ρ lam eps w X)) := by
    intro X
    unfold scorePert
    refine (tendsto_finsetSum _ fun l _ => ?_).add
      (tendsto_const_nhds.mul (((continuous_phiPot n m X).tendsto _).comp hp_tend))
    unfold alphaW
    exact (tendsto_const_nhds.add (tendsto_const_nhds.mul
      ((continuous_apply l).continuousAt.tendsto.comp hwt_ψ_tend))).mul tendsto_const_nhds
  have hA_bal : IsBalanced A := by
    rw [← hA_const 0]; exact (hAt_score (φ₁ 0)).1
  have hA_max : IsScoreMax v ρ lam eps w A := by
    refine ⟨hA_bal, fun B hB => ?_⟩
    have hineq : ∀ k, scorePert v ρ lam eps (wt (ψ k)) B ≤
        scorePert v ρ lam eps (wt (ψ k)) A := by
      intro k
      have hAk : At (ψ k) = A := hA_const (φ₂ k)
      rw [← hAk]
      exact (hAt_score (ψ k)).2 B hB
    exact le_of_tendsto_of_tendsto (hscore_tend B) (hscore_tend A)
      (Eventually.of_forall hineq)
  have hA_div_lim : ∀ k' : Fin n, divD v ρ γ A w i ≤ divD v ρ γ A w k' := by
    intro k'
    have hineq : ∀ k, divD v ρ γ A (wt (ψ k)) i ≤ divD v ρ γ A (wt (ψ k)) k' := by
      intro k
      have hAk : At (ψ k) = A := hA_const (φ₂ k)
      rw [← hAk]
      exact hAt_div (ψ k) k'
    exact le_of_tendsto_of_tendsto
      (((continuous_divD v ρ γ A i).tendsto w).comp hwt_ψ_tend)
      (((continuous_divD v ρ γ A k').tendsto w).comp hwt_ψ_tend)
      (Eventually.of_forall hineq)
  exact ⟨hw_simp, A, hA_max, hA_div_lim⟩

def swapAlloc {n m : ℕ} (i k : Fin n) (A : Allocation n m) : Allocation n m :=
  fun g => Equiv.swap i k (A g)

lemma bundle_swapAlloc {n m : ℕ} (i k : Fin n) (A : Allocation n m) (l : Fin n) :
    bundle (swapAlloc i k A) l = bundle A (Equiv.swap i k l) := by
  ext g
  simp only [mem_bundle_iff, swapAlloc]
  constructor <;> intro h
  · rw [← h, Equiv.swap_apply_self]
  · rw [h, Equiv.swap_apply_self]

lemma isBalanced_swapAlloc {n m : ℕ} (i k : Fin n) {A : Allocation n m} (hbal : IsBalanced A) :
    IsBalanced (swapAlloc i k A) := by
  intro l
  rw [bundle_swapAlloc]
  exact hbal (Equiv.swap i k l)

lemma phiPot_swapAlloc {n m : ℕ} (p : Fin m → ℝ) (i k : Fin n) (A : Allocation n m) :
    phiPot n m p (swapAlloc i k A) = phiPot n m p A := by
  unfold phiPot
  simp_rw [bundle_swapAlloc]
  exact Equiv.sum_comp (Equiv.swap i k) (fun l => ∑ c ∈ Finset.Icc 1 (m / n + 1),
    (maxSubSum (bundle A l) (posPrice p) c + maxSubSum (bundle A l) (negPrice p) c))

/-- Lemma 7 (Boundary / KKM face condition): holds for all `lam > 0` and all `eps`! -/
lemma face_kkmSet {n m : ℕ} (hn2 : 2 ≤ n) (v : Fin n → Fin m → ℝ)
    {γ ρ lam eps : ℝ} (hγ : 0 < γ) (hρ_pos : 0 < ρ)
    (hρ_ub : ρ ≤ γ / (4 * (n : ℝ) * (γ + 2 * (((m / n : ℕ) : ℝ) + 2) * vmax v +
      ((n : ℝ) - 1) * (2 * (((m / n : ℕ) : ℝ) + 1) * vmax v))))
    (T : Finset (Fin n)) (hT : T.Nonempty) :
    simplexFace T ⊆ ⋃ i ∈ T, kkmSet v ρ γ lam eps i := by
  intro w hw_face
  obtain ⟨hw_simp, hw_zero⟩ := hw_face
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  let K : ℝ := 2 * (((m / n : ℕ) : ℝ) + 1) * vmax v
  let H : ℝ := 2 * (((m / n : ℕ) : ℝ) + 2) * vmax v
  have hV : 0 ≤ vmax v := vmax_nonneg v
  have hK_nn : 0 ≤ K := by dsimp [K]; positivity
  have hH_nn : 0 ≤ H := by dsimp [H]; positivity
  have hn_sub_nn : 0 ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hdenom_pos : 0 < γ + H + ((n : ℝ) - 1) * K := by positivity
  have hρ1 : (n : ℝ) * ρ ≤ 1 := by
    have hmul : 4 * (n : ℝ) * (γ + H + ((n : ℝ) - 1) * K) * ρ ≤ γ := by
      have hd_pos : 0 < 4 * (n : ℝ) * (γ + H + ((n : ℝ) - 1) * K) := by positivity
      exact (le_div_iff₀' hd_pos).mp hρ_ub
    have hγ_le : γ ≤ γ + H + ((n : ℝ) - 1) * K := by nlinarith
    nlinarith
  -- Pick any score maximizer `A` at `w`, and an agent `i_min` minimizing `divD ... A w`
  obtain ⟨A, hA_score⟩ := exists_isScoreMax hn1 v ρ lam eps w
  have huniv_ne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn1⟩, Finset.mem_univ _⟩
  obtain ⟨i_min, _, hi_min_eq⟩ := Finset.exists_mem_eq_inf' huniv_ne
    (fun k => divD v ρ γ A w k)
  have hi_min_le : ∀ k : Fin n, divD v ρ γ A w i_min ≤ divD v ρ γ A w k := by
    intro k
    rw [← hi_min_eq]
    exact Finset.inf'_le _ (Finset.mem_univ k)
  have hi_min_nonpos : divD v ρ γ A w i_min ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    have hsum_pos : 0 < ∑ k : Fin n, divD v ρ γ A w k := by
      calc (0 : ℝ) < (n : ℝ) * divD v ρ γ A w i_min := mul_pos hn_pos hpos
        _ = ∑ _k : Fin n, divD v ρ γ A w i_min := by simp [nsmul_eq_mul]
        _ ≤ ∑ k : Fin n, divD v ρ γ A w k := Finset.sum_le_sum fun k _ => hi_min_le k
    linarith [sum_divD_eq_zero v ρ γ A w]
  -- Show `i_min ∈ T` by proving `i ∉ T → 0 < divD v ρ γ A w i`
  have hi_in_T : i_min ∈ T := by
    by_contra hi_not_T
    have hwi : w i_min = 0 := hw_zero i_min hi_not_T
    have hα_i : alphaW ρ w i_min = ρ := by unfold alphaW; rw [hwi]; ring
    -- Find `a ∈ T` with `1 / n ≤ w a`
    have hex_a : ∃ a ∈ T, 1 / (n : ℝ) ≤ w a := by
      by_contra hlt_all
      push_neg at hlt_all
      have hsum_T : ∑ l ∈ T, w l = 1 := by
        rw [← hw_simp.2]
        symm
        rw [← Finset.sum_subset (Finset.subset_univ T)]
        intro l _ hl_not_T
        exact hw_zero l hl_not_T
      have hcard_T : (T.card : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Finset.card_le_univ T).trans_eq (Fintype.card_fin n)
      have hsum_lt : ∑ l ∈ T, w l < ∑ _l ∈ T, (1 / (n : ℝ)) :=
        Finset.sum_lt_sum (fun l hl => le_of_lt (hlt_all l hl))
          (let ⟨a₀, ha₀⟩ := hT; ⟨a₀, ha₀, hlt_all a₀ ha₀⟩)
      have hrhs_le : (∑ _l ∈ T, (1 / (n : ℝ))) ≤ 1 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        calc (T.card : ℝ) * (1 / (n : ℝ))
            ≤ (n : ℝ) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_right hcard_T (by positivity)
          _ = 1 := mul_one_div_cancel (ne_of_gt hn_pos)
      linarith
    obtain ⟨a, haT, hwa⟩ := hex_a
    have ha_ne_i : a ≠ i_min := fun heq => hi_not_T (heq ▸ haT)
    have hα_a : 1 / (n : ℝ) ≤ alphaW ρ w a := by
      unfold alphaW
      have h1 : (1 - (n : ℝ) * ρ) * (1 / (n : ℝ)) ≤ (1 - (n : ℝ) * ρ) * w a :=
        mul_le_mul_of_nonneg_left hwa (by linarith)
      have h2 : ρ + (1 - (n : ℝ) * ρ) * (1 / (n : ℝ)) = 1 / (n : ℝ) := by
        field_simp [ne_of_gt hn_pos]; ring
      linarith
    -- Lower bound outgoing flow `flowF ... i_min a`
    have hout_ia : γ * (1 / (n : ℝ) - ρ) - ρ * H ≤ flowF v ρ γ A w i_min a := by
      unfold flowF
      refine le_trans ?_ (le_max_left _ _)
      rw [hα_i]
      have hres_lb := (envy_and_resEnvy_bounds v hA_score.1 i_min a).2.2
      have hmul1 : - (ρ * H) ≤ ρ * resEnvy v A i_min a := by
        have := mul_le_mul_of_nonneg_left hres_lb (le_of_lt hρ_pos)
        linarith
      have hmul2 : γ * (1 / (n : ℝ) - ρ) ≤ γ * (alphaW ρ w a - ρ) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hγ)
      linarith
    have hout_sum : γ * (1 / (n : ℝ) - ρ) - ρ * H ≤
        ∑ j ∈ Finset.univ.erase i_min, flowF v ρ γ A w i_min j := by
      refine le_trans hout_ia ?_
      exact Finset.single_le_sum (fun j _ => flowF_nonneg v ρ γ A w i_min j)
        (Finset.mem_erase.mpr ⟨ha_ne_i, Finset.mem_univ a⟩)
    -- Upper bound incoming flow `flowF ... k i_min ≤ ρ * K` for every `k ≠ i_min` via bundle swap!
    have hin_ub : ∀ k ∈ Finset.univ.erase i_min, flowF v ρ γ A w k i_min ≤ ρ * K := by
      intro k hk_er
      have hki : k ≠ i_min := (Finset.mem_erase.mp hk_er).1
      let A_sw := swapAlloc i_min k A
      have hsw_bal : IsBalanced A_sw := isBalanced_swapAlloc i_min k hA_score.1
      have hsw_le := hA_score.2 A_sw hsw_bal
      unfold scorePert at hsw_le
      rw [phiPot_swapAlloc _ i_min k A] at hsw_le
      have hwelf_le : ∑ l : Fin n, alphaW ρ w l * bval v l (bundle A_sw l) ≤
          ∑ l : Fin n, alphaW ρ w l * bval v l (bundle A l) := by linarith
      -- Cancel all agents `l ∉ {i_min, k}`
      let R : Finset (Fin n) := (Finset.univ.erase i_min).erase k
      have hsplit : ∀ f : Fin n → ℝ,
          ∑ l : Fin n, f l = f i_min + (f k + ∑ l ∈ R, f l) := by
        intro f
        rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ i_min),
          ← Finset.add_sum_erase (Finset.univ.erase i_min) f hk_er]
      rw [hsplit (fun l => alphaW ρ w l * bval v l (bundle A_sw l)),
          hsplit (fun l => alphaW ρ w l * bval v l (bundle A l))] at hwelf_le
      have hR_eq : ∑ l ∈ R, alphaW ρ w l * bval v l (bundle A_sw l) =
          ∑ l ∈ R, alphaW ρ w l * bval v l (bundle A l) := by
        refine Finset.sum_congr rfl fun l hl => ?_
        obtain ⟨hlk, hl_er⟩ := Finset.mem_erase.mp hl
        have hli : l ≠ i_min := (Finset.mem_erase.mp hl_er).1
        dsimp [A_sw]
        rw [bundle_swapAlloc, Equiv.swap_apply_of_ne_of_ne hli hlk]
      have hbi : bundle A_sw i_min = bundle A k := by
        dsimp [A_sw]; rw [bundle_swapAlloc, Equiv.swap_apply_left]
      have hbk : bundle A_sw k = bundle A i_min := by
        dsimp [A_sw]; rw [bundle_swapAlloc, Equiv.swap_apply_right]
      rw [hR_eq, hbi, hbk, hα_i] at hwelf_le
      have henvy_k : alphaW ρ w k * envy v A k i_min ≤ ρ * (- envy v A i_min k) := by
        unfold envy; linarith
      have henvy_ik_abs := (envy_and_resEnvy_bounds v hA_score.1 i_min k).1
      have hneg_le_K : - envy v A i_min k ≤ K := by linarith [(abs_le.mp henvy_ik_abs).1]
      have hαk_nn : 0 ≤ alphaW ρ w k := by
        have := (alphaW_bounds (le_of_lt hρ_pos) hρ1 hw_simp k).1; linarith
      have hαi_le_αk : alphaW ρ w i_min ≤ alphaW ρ w k := by
        rw [hα_i]; unfold alphaW
        have hwk_nn : 0 ≤ w k := hw_simp.1 k
        have : 0 ≤ (1 - (n : ℝ) * ρ) * w k := mul_nonneg (by linarith) hwk_nn
        linarith
      have hres_le_envy := (envy_and_resEnvy_bounds v hA_score.1 k i_min).2.1
      unfold flowF
      refine max_le ?_ (mul_nonneg (le_of_lt hρ_pos) hK_nn)
      have h1 : alphaW ρ w k * resEnvy v A k i_min ≤ alphaW ρ w k * envy v A k i_min :=
        mul_le_mul_of_nonneg_left hres_le_envy hαk_nn
      have h2 : γ * (alphaW ρ w i_min - alphaW ρ w k) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hγ) (by linarith)
      have h3 : ρ * (- envy v A i_min k) ≤ ρ * K :=
        mul_le_mul_of_nonneg_left hneg_le_K (le_of_lt hρ_pos)
      linarith
    have hin_sum : ∑ k ∈ Finset.univ.erase i_min, flowF v ρ γ A w k i_min ≤
        ((n : ℝ) - 1) * (ρ * K) := by
      calc ∑ k ∈ Finset.univ.erase i_min, flowF v ρ γ A w k i_min
          ≤ ∑ _k ∈ Finset.univ.erase i_min, (ρ * K) := Finset.sum_le_sum hin_ub
        _ = ((Finset.univ.erase i_min).card : ℝ) * (ρ * K) := by simp [nsmul_eq_mul]
        _ = ((n : ℝ) - 1) * (ρ * K) := by
            have hc : (Finset.univ.erase i_min).card + 1 = n := by
              simpa using Finset.card_erase_add_one (Finset.mem_univ i_min)
            have hc_r : ((Finset.univ.erase i_min).card : ℝ) = (n : ℝ) - 1 := by
              have : ((Finset.univ.erase i_min).card : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hc
              linarith
            rw [hc_r]
    -- Combine outgoing lower bound and incoming upper bound
    have hdiv_lb : γ / (n : ℝ) - ρ * (γ + H + ((n : ℝ) - 1) * K) ≤ divD v ρ γ A w i_min := by
      have hrew : γ * (1 / (n : ℝ) - ρ) - ρ * H - ((n : ℝ) - 1) * (ρ * K) =
          γ / (n : ℝ) - ρ * (γ + H + ((n : ℝ) - 1) * K) := by ring
      unfold divD
      linarith
    have hρ_prod_le : ρ * (γ + H + ((n : ℝ) - 1) * K) ≤ γ / (4 * (n : ℝ)) := by
      have hd_pos : 0 < 4 * (n : ℝ) * (γ + H + ((n : ℝ) - 1) * K) := by positivity
      have hmul : ρ * (4 * (n : ℝ) * (γ + H + ((n : ℝ) - 1) * K)) ≤ γ :=
        (le_div_iff₀ hd_pos).mp hρ_ub
      have h4n_pos : 0 < 4 * (n : ℝ) := by positivity
      rw [le_div_iff₀ h4n_pos]
      linarith
    have hγ_pos_div : 0 < γ / (n : ℝ) - γ / (4 * (n : ℝ)) := by
      have : γ / (n : ℝ) - γ / (4 * (n : ℝ)) = 3 * γ / (4 * (n : ℝ)) := by
        field_simp [ne_of_gt hn_pos]; ring
      rw [this]; positivity
    linarith
  exact Set.mem_iUnion₂.mpr ⟨i_min, hi_in_T, hw_simp, A, hA_score, hi_min_le⟩

/-- Lemma 8 (Applying KKM): yields a common weight `w*` and agent witness family `B`. -/
lemma exists_kkm_witnesses {n m : ℕ} (hn2 : 2 ≤ n) (v : Fin n → Fin m → ℝ)
    {γ ρ lam eps : ℝ} (hγ : 0 < γ) (hρ_pos : 0 < ρ)
    (hρ_ub : ρ ≤ γ / (4 * (n : ℝ) * (γ + 2 * (((m / n : ℕ) : ℝ) + 2) * vmax v +
      ((n : ℝ) - 1) * (2 * (((m / n : ℕ) : ℝ) + 1) * vmax v))))
    (hlam : 0 < lam) :
    ∃ (w_star : Fin n → ℝ) (B : Fin n → Allocation n m),
      w_star ∈ stdSimplex ℝ (Fin n) ∧
      ∀ idx : Fin n, IsScoreMax v ρ lam eps w_star (B idx) ∧
        ∀ k : Fin n, divD v ρ γ (B idx) w_star idx ≤ divD v ρ γ (B idx) w_star k := by
  have hn1 : 1 ≤ n := by omega
  have hρ1 : (n : ℝ) * ρ ≤ 1 := by
    let K : ℝ := 2 * (((m / n : ℕ) : ℝ) + 1) * vmax v
    let H : ℝ := 2 * (((m / n : ℕ) : ℝ) + 2) * vmax v
    have hV : 0 ≤ vmax v := vmax_nonneg v
    have hK_nn : 0 ≤ K := by dsimp [K]; positivity
    have hH_nn : 0 ≤ H := by dsimp [H]; positivity
    have hn_sub_nn : 0 ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith
    have hd_pos : 0 < 4 * (n : ℝ) * (γ + H + ((n : ℝ) - 1) * K) := by positivity
    have hγ_le : γ ≤ γ + H + ((n : ℝ) - 1) * K := by nlinarith
    have hmul : 4 * (n : ℝ) * (γ + H + ((n : ℝ) - 1) * K) * ρ ≤ γ :=
      (le_div_iff₀' hd_pos).mp hρ_ub
    nlinarith
  obtain ⟨w_star, hw_inter⟩ := kkm_stdSimplex n hn1 (fun i => kkmSet v ρ γ lam eps i)
    (fun i => isClosed_kkmSet v (le_of_lt hρ_pos) hρ1 hlam i)
    (fun T hT => face_kkmSet hn2 v hγ hρ_pos hρ_ub T hT)
  have hw_all : ∀ idx : Fin n, w_star ∈ kkmSet v ρ γ lam eps idx :=
    fun idx => Set.mem_iInter.mp hw_inter idx
  have hw_simp : w_star ∈ stdSimplex ℝ (Fin n) := (hw_all ⟨0, hn1⟩).1
  choose B hB_score hB_div using fun idx => (hw_all idx).2
  exact ⟨w_star, B, hw_simp, fun idx => ⟨hB_score idx, hB_div idx⟩⟩

end KKMSelection

/-! ### §3.6 & §3.7: Consolidating Witnesses, Price Intervals (`Lemmas 9–13`), and `Theorem 1` -/

section ConsolidationAndMainProof

noncomputable def priceL {n m : ℕ} (p : Fin m → ℝ) (X : Allocation n m) (i : Fin n) : ℝ :=
  let S := ∑ g ∈ bundle X i, p g
  let M := maxBundleVal (fun _ g => p g) i (bundle X i)
  if (bundle X i).card = qSize n m then S - M else S - max 0 M

noncomputable def priceU {n m : ℕ} (ξ : Fin n → ℝ) (p : Fin m → ℝ)
    (X : Allocation n m) (i : Fin n) : ℝ :=
  let S := ∑ g ∈ bundle X i, p g
  let m_val := minBundleVal (fun _ g => p g) i (bundle X i)
  if (bundle X i).card = qSize n m ∨ ξ i < 0 then S - m_val else S - min 0 m_val

lemma real_eq_pos_sub_neg (z : ℝ) : z = max z 0 - max (- z) 0 := by
  by_cases hz : 0 ≤ z
  · rw [max_eq_left hz, max_eq_right (by linarith), sub_zero]
  · rw [max_eq_right (by linarith), max_eq_left (by linarith), sub_neg_eq_add, zero_add]

/-- Padded raw price vector of length `k` from bundle `bundle X i` (`card ≤ k`). -/
noncomputable def rawPad {n m : ℕ} (k : ℕ) (p : Fin m → ℝ) (X : Allocation n m) (i : Fin n) :
    Fin k → ℝ :=
  fun t => if h : t.val < (bundle X i).card then p ((bundle X i).equivFin.symm ⟨t.val, h⟩).1 else 0

lemma sum_rawPad {n m : ℕ} (k : ℕ) (p : Fin m → ℝ) (X : Allocation n m) (i : Fin n)
    (hcard : (bundle X i).card ≤ k) :
    ∑ t : Fin k, rawPad k p X i t = ∑ g ∈ bundle X i, p g := by
  let S := bundle X i
  let eS : Fin S.card ≃ S := S.equivFin.symm
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t : Fin k => t.val < S.card)]
  have hz : ∑ t ∈ Finset.univ.filter (fun t : Fin k => ¬ (t.val < S.card)),
      rawPad k p X i t = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have hnot := (Finset.mem_filter.mp ht).2
    unfold rawPad
    exact dif_neg hnot
  rw [hz, add_zero]
  have h1 : (∑ t ∈ Finset.univ.filter (fun t : Fin k => t.val < S.card), rawPad k p X i t) =
      ∑ u : Fin S.card, p (eS u).1 := by
    symm
    refine Finset.sum_bij (fun (u : Fin S.card) _ => (⟨u.val, lt_of_lt_of_le u.isLt hcard⟩ : Fin k))
      (fun u _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.isLt⟩)
      (fun u₁ _ u₂ _ h => by injection h with hv; exact Fin.ext hv)
      (fun t ht => ⟨⟨t.val, (Finset.mem_filter.mp ht).2⟩, Finset.mem_univ _, by ext; rfl⟩)
      (fun u _ => by
        unfold rawPad
        dsimp [eS, S]
        rw [if_pos u.isLt])
  rw [h1]
  exact Finset.sum_bij (fun (u : Fin S.card) _ => (eS u).1)
    (fun u _ => (eS u).2)
    (fun u₁ _ u₂ _ h => eS.injective (Subtype.ext h))
    (fun g hg => ⟨eS.symm ⟨g, hg⟩, Finset.mem_univ _,
      congrArg Subtype.val (eS.apply_symm_apply _)⟩)
    (fun _ _ => rfl)

/-- Key step comparing `g₁ ⟨l, _⟩ ≤ g₂ ⟨l - 1, _⟩` for padded permutations `τ₁, τ₂` under
limiting `maxSubSum` equality between `bundle X i` and `bundle Y i`. -/
lemma padded_perm_step_le {n m k : ℕ} (p : Fin m → ℝ) (X Y : Allocation n m) (i : Fin n)
    (hcX : (bundle X i).card ≤ k) (hcY : (bundle Y i).card ≤ k)
    (φ : ℝ → ℝ) (hφ0 : φ 0 = 0) (hφ_nn : ∀ z, 0 ≤ φ z)
    (τ₁ τ₂ : Equiv.Perm (Fin k))
    (hanti₁ : Antitone (fun t => φ (rawPad k p X i (τ₁ t))))
    (hanti₂ : Antitone (fun t => φ (rawPad k p Y i (τ₂ t))))
    {l : ℕ} (hl1 : 1 ≤ l) (hlk : l < k)
    (hinter : maxSubSum (bundle X i) (fun g => φ (p g)) l +
        maxSubSum (bundle Y i) (fun g => φ (p g)) l =
      maxSubSum (ownedVerts X Y i) (fun v_x => φ (p v_x.1)) (2 * l)) :
    φ (rawPad k p X i (τ₁ ⟨l, hlk⟩)) ≤ φ (rawPad k p Y i (τ₂ ⟨l - 1, by omega⟩)) := by
  let g₁ : Fin k → ℝ := fun t => φ (rawPad k p X i (τ₁ t))
  let g₂ : Fin k → ℝ := fun t => φ (rawPad k p Y i (τ₂ t))
  -- 1. Upper-bound `maxSubSum (bundle X i)` by `maxSubSum univ g₁` (and similarly for `Y, g₂`)
  have hub_single : ∀ (Z : Allocation n m) (hcZ : (bundle Z i).card ≤ k) (τ : Equiv.Perm (Fin k)),
      maxSubSum (bundle Z i) (fun g => φ (p g)) l ≤
        maxSubSum (Finset.univ : Finset (Fin k)) (fun t => φ (rawPad k p Z i (τ t))) l := by
    intro Z hcZ τ
    let S := bundle Z i
    let eS : Fin S.card ≃ S := S.equivFin.symm
    unfold maxSubSum
    refine Finset.sup'_le _ _ fun T hT => ?_
    simp only [validSubs, Finset.mem_filter, Finset.mem_powerset] at hT
    let idxOf : {g // g ∈ T} → Fin k := fun g =>
      τ.symm ⟨(eS.symm ⟨g.1, hT.1 g.2⟩).val, lt_of_lt_of_le (eS.symm ⟨g.1, hT.1 g.2⟩).isLt hcZ⟩
    have hinj_idx : Function.Injective idxOf := by
      intro a b heq
      have h1 := congrArg Fin.val (τ.symm.injective heq)
      dsimp at h1
      have h2 := eS.symm.injective (Fin.ext h1)
      injection h2 with hv
      exact Subtype.ext hv
    let T' : Finset (Fin k) := T.attach.image idxOf
    have hcard_T' : T'.card ≤ l := by
      dsimp [T']
      rw [Finset.card_image_of_injective _ hinj_idx, Finset.card_attach]
      exact hT.2
    have hsum_eq : ∑ t ∈ T', φ (rawPad k p Z i (τ t)) = ∑ g ∈ T, φ (p g) := by
      dsimp [T']
      rw [Finset.sum_image (fun a _ b _ h => hinj_idx h), ← Finset.sum_attach T (fun g => φ (p g))]
      refine Finset.sum_congr rfl fun g _ => ?_
      dsimp [idxOf]
      rw [τ.apply_symm_apply]
      unfold rawPad
      have hlt_g : (eS.symm ⟨g.1, hT.1 g.2⟩).val < (bundle Z i).card :=
        (eS.symm ⟨g.1, hT.1 g.2⟩).isLt
      rw [dif_pos hlt_g]
      have heS_eq : ((bundle Z i).equivFin.symm ⟨(eS.symm ⟨g.1, hT.1 g.2⟩).val, hlt_g⟩).1 = g.1 :=
        congrArg Subtype.val (eS.apply_symm_apply ⟨g.1, hT.1 g.2⟩)
      rw [heS_eq]
    rw [← hsum_eq]
    exact le_maxSubSum (Finset.subset_univ T') hcard_T' (fun t => φ (rawPad k p Z i (τ t)))
  have hubX : maxSubSum (bundle X i) (fun g => φ (p g)) l ≤
      ∑ t ∈ Finset.univ.filter (fun t : Fin k => t.val < l), g₁ t :=
    (hub_single X hcX τ₁).trans_eq (maxSubSum_antitone_fin hanti₁ (fun _ => hφ_nn _) l)
  have hubY : maxSubSum (bundle Y i) (fun g => φ (p g)) l ≤
      ∑ t ∈ Finset.univ.filter (fun t : Fin k => t.val < l), g₂ t :=
    (hub_single Y hcY τ₂).trans_eq (maxSubSum_antitone_fin hanti₂ (fun _ => hφ_nn _) l)
  -- 2. Construct `(l + 1) + (l - 1) = 2 * l` subset inside `ownedVerts X Y i`
  let L_l : Finset (Fin k) := Finset.univ.filter (fun t : Fin k => t.val < l)
  let L_plus : Finset (Fin k) := Finset.univ.filter (fun t : Fin k => t.val < l + 1)
  let L_minus : Finset (Fin k) := Finset.univ.filter (fun t : Fin k => t.val < l - 1)
  let idx_l : Fin k := ⟨l, hlk⟩
  let idx_lm1 : Fin k := ⟨l - 1, by omega⟩
  have hL_plus_ins : L_plus = insert idx_l L_l ∧ idx_l ∉ L_l := by
    refine ⟨?_, by simp [L_l, idx_l]⟩
    ext t; simp only [L_plus, L_l, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ht
      by_cases he : t.val = l
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (by omega)
    · rintro (rfl | ht) <;> [dsimp [idx_l]; skip] <;> omega
  have hL_l_ins : L_l = insert idx_lm1 L_minus ∧ idx_lm1 ∉ L_minus := by
    refine ⟨?_, by simp [L_minus, idx_lm1]⟩
    ext t; simp only [L_l, L_minus, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ht
      by_cases he : t.val = l - 1
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (by omega)
    · rintro (rfl | ht) <;> [dsimp [idx_lm1]; skip] <;> omega
  have hLl_card : L_l.card ≤ l := by
    rw [← Finset.card_range l]
    exact Finset.card_le_card_of_injOn Fin.val
      (fun t ht => Finset.mem_range.mpr (Finset.mem_filter.mp ht).2)
      (fun _ _ _ _ h => Fin.ext h)
  have hsum_plus : ∑ t ∈ L_plus, g₁ t = g₁ idx_l + ∑ t ∈ L_l, g₁ t := by
    rw [hL_plus_ins.1, Finset.sum_insert hL_plus_ins.2]
  have hsum_l_g₂ : ∑ t ∈ L_l, g₂ t = g₂ idx_lm1 + ∑ t ∈ L_minus, g₂ t := by
    rw [hL_l_ins.1, Finset.sum_insert hL_l_ins.2]
  have hcard_plus_minus : L_plus.card + L_minus.card ≤ 2 * l := by
    have c1 : L_plus.card = L_l.card + 1 := by
      rw [hL_plus_ins.1, Finset.card_insert_of_notMem hL_plus_ins.2]
    have c2 : L_l.card = L_minus.card + 1 := by
      rw [hL_l_ins.1, Finset.card_insert_of_notMem hL_l_ins.2]
    omega
  -- Filter positive entries of `L_plus` and `L_minus` into `ownedVerts X Y i`
  let P₁ : Finset (Fin k) := L_plus.filter (fun t => 0 < g₁ t)
  let P₂ : Finset (Fin k) := L_minus.filter (fun t => 0 < g₂ t)
  have hsum_P₁ : ∑ t ∈ L_plus, g₁ t = ∑ t ∈ P₁, g₁ t := by
    rw [← Finset.sum_filter_add_sum_filter_not L_plus (fun t => 0 < g₁ t)]
    have hz : ∑ t ∈ L_plus.filter (fun t => ¬ (0 < g₁ t)), g₁ t = 0 :=
      Finset.sum_eq_zero fun t ht =>
        le_antisymm (le_of_not_gt (Finset.mem_filter.mp ht).2) (hφ_nn _)
    rw [hz, add_zero]
  have hsum_P₂ : ∑ t ∈ L_minus, g₂ t = ∑ t ∈ P₂, g₂ t := by
    rw [← Finset.sum_filter_add_sum_filter_not L_minus (fun t => 0 < g₂ t)]
    have hz : ∑ t ∈ L_minus.filter (fun t => ¬ (0 < g₂ t)), g₂ t = 0 :=
      Finset.sum_eq_zero fun t ht =>
        le_antisymm (le_of_not_gt (Finset.mem_filter.mp ht).2) (hφ_nn _)
    rw [hz, add_zero]
  let eX : Fin (bundle X i).card ≃ bundle X i := (bundle X i).equivFin.symm
  let eY : Fin (bundle Y i).card ≃ bundle Y i := (bundle Y i).equivFin.symm
  have hlt_X : ∀ t ∈ P₁, (τ₁ t).val < (bundle X i).card := by
    intro t ht
    have hpos : 0 < g₁ t := (Finset.mem_filter.mp ht).2
    by_contra hge
    have hraw0 : rawPad k p X i (τ₁ t) = 0 := by unfold rawPad; exact dif_neg hge
    dsimp [g₁] at hpos
    rw [hraw0, hφ0] at hpos
    exact lt_irrefl 0 hpos
  have hlt_Y : ∀ t ∈ P₂, (τ₂ t).val < (bundle Y i).card := by
    intro t ht
    have hpos : 0 < g₂ t := (Finset.mem_filter.mp ht).2
    by_contra hge
    have hraw0 : rawPad k p Y i (τ₂ t) = 0 := by unfold rawPad; exact dif_neg hge
    dsimp [g₂] at hpos
    rw [hraw0, hφ0] at hpos
    exact lt_irrefl 0 hpos
  let mapX : {t // t ∈ P₁} → Fin m × Bool :=
    fun t => ((eX ⟨(τ₁ t.1).val, hlt_X t.1 t.2⟩).1, false)
  let mapY : {t // t ∈ P₂} → Fin m × Bool :=
    fun t => ((eY ⟨(τ₂ t.1).val, hlt_Y t.1 t.2⟩).1, true)
  have hinjX : Function.Injective mapX := by
    intro a b heq
    have h1 := eX.injective (Subtype.ext (congrArg Prod.fst heq))
    have hv : (τ₁ a.1).val = (τ₁ b.1).val := congrArg (fun x => x.val) h1
    have h2 : τ₁ a.1 = τ₁ b.1 := Fin.ext hv
    exact Subtype.ext (τ₁.injective h2)
  have hinjY : Function.Injective mapY := by
    intro a b heq
    have h1 := eY.injective (Subtype.ext (congrArg Prod.fst heq))
    have hv : (τ₂ a.1).val = (τ₂ b.1).val := congrArg (fun x => x.val) h1
    have h2 : τ₂ a.1 = τ₂ b.1 := Fin.ext hv
    exact Subtype.ext (τ₂.injective h2)
  let U₁ : Finset (Fin m × Bool) := P₁.attach.image mapX
  let U₂ : Finset (Fin m × Bool) := P₂.attach.image mapY
  have hdisj_U : Disjoint U₁ U₂ := by
    rw [Finset.disjoint_left]
    intro v_x hv1 hv2
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv1
    obtain ⟨b, _, heq⟩ := Finset.mem_image.mp hv2
    exact Bool.false_ne_true (congrArg Prod.snd heq).symm
  have hsub_owned : U₁ ∪ U₂ ⊆ ownedVerts X Y i := by
    intro v_x hv
    rcases Finset.mem_union.mp hv with hv1 | hv2
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv1
      have hg := (mem_bundle_iff X i _).mp (eX ⟨(τ₁ a.1).val, hlt_X a.1 a.2⟩).2
      simp [ownedVerts, mapX, hg]
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv2
      have hg := (mem_bundle_iff Y i _).mp (eY ⟨(τ₂ b.1).val, hlt_Y b.1 b.2⟩).2
      simp [ownedVerts, mapY, hg]
  have hcard_U : (U₁ ∪ U₂).card ≤ 2 * l := by
    rw [Finset.card_union_of_disjoint hdisj_U]
    dsimp [U₁, U₂]
    rw [Finset.card_image_of_injective _ hinjX, Finset.card_attach,
        Finset.card_image_of_injective _ hinjY, Finset.card_attach]
    have hp1 : P₁.card ≤ L_plus.card := Finset.card_filter_le _ _
    have hp2 : P₂.card ≤ L_minus.card := Finset.card_filter_le _ _
    omega
  have hsum_U : ∑ v_x ∈ U₁ ∪ U₂, φ (p v_x.1) = (∑ t ∈ P₁, g₁ t) + (∑ t ∈ P₂, g₂ t) := by
    rw [Finset.sum_union hdisj_U]
    congr 1
    · dsimp [U₁]
      rw [Finset.sum_image (fun a _ b _ h => hinjX h), ← Finset.sum_attach P₁ g₁]
      refine Finset.sum_congr rfl fun a _ => ?_
      dsimp [mapX, g₁, eX]
      congr 1
      unfold rawPad
      rw [dif_pos (hlt_X a.1 a.2)]
    · dsimp [U₂]
      rw [Finset.sum_image (fun a _ b _ h => hinjY h), ← Finset.sum_attach P₂ g₂]
      refine Finset.sum_congr rfl fun b _ => ?_
      dsimp [mapY, g₂, eY]
      congr 1
      unfold rawPad
      rw [dif_pos (hlt_Y b.1 b.2)]
  have hlb_owned : (∑ t ∈ L_plus, g₁ t) + (∑ t ∈ L_minus, g₂ t) ≤
      maxSubSum (ownedVerts X Y i) (fun v_x => φ (p v_x.1)) (2 * l) := by
    rw [hsum_P₁, hsum_P₂, ← hsum_U]
    exact le_maxSubSum hsub_owned hcard_U (fun v_x => φ (p v_x.1))
  linarith [hlb_owned, hinter, hubX, hubY, hsum_plus, hsum_l_g₂]

/-- Equal-length padded comparison (`Claim 1` of Lemma 9): for `1 ≤ k ≤ m / n + 1`,
`∑ a - a 0 ≤ ∑ b - b (k - 1)`. -/
lemma padded_sorted_sum_le {n m k : ℕ} (hk1 : 1 ≤ k) (hkr : k ≤ m / n + 1)
    (p : Fin m → ℝ) (X Y : Allocation n m) (i : Fin n)
    (hcX : (bundle X i).card ≤ k) (hcY : (bundle Y i).card ≤ k)
    (hXY : ∀ l ∈ Finset.Icc 1 (m / n + 1),
      maxSubSum (bundle X i) (posPrice p) l + maxSubSum (bundle Y i) (posPrice p) l =
        maxSubSum (ownedVerts X Y i) (fun v_x => posPrice p v_x.1) (2 * l))
    (hYX_neg : ∀ l ∈ Finset.Icc 1 (m / n + 1),
      maxSubSum (bundle Y i) (negPrice p) l + maxSubSum (bundle X i) (negPrice p) l =
        maxSubSum (ownedVerts Y X i) (fun v_x => negPrice p v_x.1) (2 * l)) :
    (∑ g ∈ bundle X i, p g) -
        rawPad k p X i (((revPermFin k).trans (Tuple.sort (rawPad k p X i))) ⟨0, hk1⟩) ≤
      (∑ g ∈ bundle Y i, p g) -
        rawPad k p Y i (((revPermFin k).trans (Tuple.sort (rawPad k p Y i))) ⟨k - 1, by omega⟩) := by
  let σX : Equiv.Perm (Fin k) := (revPermFin k).trans (Tuple.sort (rawPad k p X i))
  let σY : Equiv.Perm (Fin k) := (revPermFin k).trans (Tuple.sort (rawPad k p Y i))
  let a : Fin k → ℝ := fun t => rawPad k p X i (σX t)
  let b : Fin k → ℝ := fun t => rawPad k p Y i (σY t)
  have hanti_a : Antitone a :=
    (Tuple.monotone_sort (rawPad k p X i)).comp_antitone (revPermFin_antitone k)
  have hanti_b : Antitone b :=
    (Tuple.monotone_sort (rawPad k p Y i)).comp_antitone (revPermFin_antitone k)
  have hstep : ∀ l : ℕ, (hl1 : 1 ≤ l) → (hlk : l < k) →
      a ⟨l, hlk⟩ ≤ b ⟨l - 1, by omega⟩ := by
    intro l hl1 hlk
    have hl_mem : l ∈ Finset.Icc 1 (m / n + 1) := Finset.mem_Icc.mpr ⟨hl1, by omega⟩
    have hkl_mem : k - l ∈ Finset.Icc 1 (m / n + 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    -- Positive step at `l`
    have hpos_step : max (a ⟨l, hlk⟩) 0 ≤ max (b ⟨l - 1, by omega⟩) 0 := by
      refine padded_perm_step_le p X Y i hcX hcY (fun z => max z 0) (max_self 0)
        (fun _ => le_max_right _ _) σX σY
        (fun u v huv => max_le_max_right 0 (hanti_a huv))
        (fun u v huv => max_le_max_right 0 (hanti_b huv))
        hl1 hlk (hXY l hl_mem)
    -- Negative step at `l' = k - l` on `(Y, X)` with reversed permutations
    let τY_neg : Equiv.Perm (Fin k) := (revPermFin k).trans σY
    let τX_neg : Equiv.Perm (Fin k) := (revPermFin k).trans σX
    have hanti_negY : Antitone (fun t => max (- rawPad k p Y i (τY_neg t)) 0) := by
      intro u v huv
      exact max_le_max_right 0 (neg_le_neg (hanti_b (revPermFin_antitone k huv)))
    have hanti_negX : Antitone (fun t => max (- rawPad k p X i (τX_neg t)) 0) := by
      intro u v huv
      exact max_le_max_right 0 (neg_le_neg (hanti_a (revPermFin_antitone k huv)))
    have hneg_raw := padded_perm_step_le p Y X i hcY hcX (fun z => max (- z) 0)
      (by simp) (fun _ => le_max_right _ _) τY_neg τX_neg hanti_negY hanti_negX
      (show 1 ≤ k - l by omega) (show k - l < k by omega) (hYX_neg (k - l) hkl_mem)
    have hrev1 : revPermFin k ⟨k - l, by omega⟩ = ⟨l - 1, by omega⟩ := by
      ext; dsimp [revPermFin]; omega
    have hrev2 : revPermFin k ⟨k - l - 1, by omega⟩ = ⟨l, hlk⟩ := by
      ext; dsimp [revPermFin]; omega
    have hneg_step : max (- b ⟨l - 1, by omega⟩) 0 ≤ max (- a ⟨l, hlk⟩) 0 := by
      simpa [τY_neg, τX_neg, a, b, hrev1, hrev2] using hneg_raw
    have ha_decomp := real_eq_pos_sub_neg (a ⟨l, hlk⟩)
    have hb_decomp := real_eq_pos_sub_neg (b ⟨l - 1, by omega⟩)
    linarith
  -- Sum `a ⟨t + 1, _⟩ ≤ b ⟨t, _⟩` over `t : Fin (k - 1)`
  have hsum_a : ∑ t : Fin k, a t = ∑ g ∈ bundle X i, p g :=
    (Equiv.sum_comp σX (rawPad k p X i)).trans (sum_rawPad k p X i hcX)
  have hsum_b : ∑ t : Fin k, b t = ∑ g ∈ bundle Y i, p g :=
    (Equiv.sum_comp σY (rawPad k p Y i)).trans (sum_rawPad k p Y i hcY)
  have hsplit_a : (∑ t : Fin k, a t) - a ⟨0, hk1⟩ =
      ∑ u : Fin (k - 1), a ⟨u.val + 1, by have := u.isLt; omega⟩ := by
    have h1 : ∑ t : Fin k, a t = a ⟨0, hk1⟩ +
        ∑ t ∈ Finset.univ.erase (⟨0, hk1⟩ : Fin k), a t :=
      (Finset.add_sum_erase Finset.univ a (Finset.mem_univ _)).symm
    have h2 : ∑ t ∈ Finset.univ.erase (⟨0, hk1⟩ : Fin k), a t =
        ∑ u : Fin (k - 1), a ⟨u.val + 1, by have := u.isLt; omega⟩ := by
      symm
      refine Finset.sum_bij (fun (u : Fin (k - 1)) _ => (⟨u.val + 1, by have := u.isLt; omega⟩ : Fin k))
        (fun u _ => Finset.mem_erase.mpr ⟨fun h => by have := congrArg Fin.val h; dsimp at this; omega,
          Finset.mem_univ _⟩)
        (fun u₁ _ u₂ _ h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
        (fun t ht => by
          have ht0 : t.val ≠ 0 := fun h => (Finset.mem_erase.mp ht).1 (Fin.ext h)
          exact ⟨⟨t.val - 1, by have := t.isLt; omega⟩, Finset.mem_univ _,
            Fin.ext (by dsimp; omega)⟩)
        (fun _ _ => rfl)
    linarith
  have hsplit_b : (∑ t : Fin k, b t) - b ⟨k - 1, by omega⟩ =
      ∑ u : Fin (k - 1), b ⟨u.val, by have := u.isLt; omega⟩ := by
    have h1 : ∑ t : Fin k, b t = b ⟨k - 1, by omega⟩ +
        ∑ t ∈ Finset.univ.erase (⟨k - 1, by omega⟩ : Fin k), b t :=
      (Finset.add_sum_erase Finset.univ b (Finset.mem_univ _)).symm
    have h2 : ∑ t ∈ Finset.univ.erase (⟨k - 1, by omega⟩ : Fin k), b t =
        ∑ u : Fin (k - 1), b ⟨u.val, by have := u.isLt; omega⟩ := by
      symm
      refine Finset.sum_bij (fun (u : Fin (k - 1)) _ => (⟨u.val, by have := u.isLt; omega⟩ : Fin k))
        (fun u _ => Finset.mem_erase.mpr ⟨fun h => by
          have hv := congrArg Fin.val h; dsimp at hv; have := u.isLt; omega, Finset.mem_univ _⟩)
        (fun u₁ _ u₂ _ h => Fin.ext (congrArg (fun x => x.val) h))
        (fun t ht => by
          have htk : t.val ≠ k - 1 := fun h => (Finset.mem_erase.mp ht).1 (Fin.ext h)
          exact ⟨⟨t.val, by have := t.isLt; omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        (fun _ _ => rfl)
    linarith
  have hsum_le : (∑ u : Fin (k - 1), a ⟨u.val + 1, by have := u.isLt; omega⟩) ≤
      ∑ u : Fin (k - 1), b ⟨u.val, by have := u.isLt; omega⟩ :=
    Finset.sum_le_sum fun u _ => by
      have := hstep (u.val + 1) (by omega) (by have := u.isLt; omega)
      simpa using this
  change (∑ g ∈ bundle X i, p g) - a ⟨0, hk1⟩ ≤ (∑ g ∈ bundle Y i, p g) - b ⟨k - 1, by omega⟩
  linarith

/-- Evaluating the top and bottom entries of sorted `rawPad k p X i`. -/
lemma sorted_rawPad_first_last {n m k : ℕ} (hk1 : 1 ≤ k) (p : Fin m → ℝ)
    (X : Allocation n m) (i : Fin n) (hne : (bundle X i).Nonempty)
    (hcX : (bundle X i).card ≤ k) :
    let σX : Equiv.Perm (Fin k) := (revPermFin k).trans (Tuple.sort (rawPad k p X i))
    let M := maxBundleVal (fun _ g => p g) i (bundle X i)
    let m_val := minBundleVal (fun _ g => p g) i (bundle X i)
    rawPad k p X i (σX ⟨0, hk1⟩) = (if (bundle X i).card = k then M else max 0 M) ∧
    rawPad k p X i (σX ⟨k - 1, by omega⟩) = (if (bundle X i).card = k then m_val else min 0 m_val) := by
  intro σX M m_val
  let a : Fin k → ℝ := fun t => rawPad k p X i (σX t)
  have hanti : Antitone a :=
    (Tuple.monotone_sort (rawPad k p X i)).comp_antitone (revPermFin_antitone k)
  let eS : Fin (bundle X i).card ≃ bundle X i := (bundle X i).equivFin.symm
  have hM_eq : M = (bundle X i).sup' hne p := by dsimp [M]; unfold maxBundleVal; exact dif_pos hne
  have hm_eq : m_val = (bundle X i).inf' hne p := by
    dsimp [m_val]; unfold minBundleVal; exact dif_pos hne
  -- `a ⟨0, hk1⟩` is the maximum of `rawPad`, and `a ⟨k - 1, _⟩` is the minimum of `rawPad`
  have ha0_max : ∀ t : Fin k, rawPad k p X i t ≤ a ⟨0, hk1⟩ := by
    intro t
    have h1 : a (σX.symm t) ≤ a ⟨0, hk1⟩ := hanti (Nat.zero_le _)
    simpa [a] using h1
  have hak_min : ∀ t : Fin k, a ⟨k - 1, by omega⟩ ≤ rawPad k p X i t := by
    intro t
    have h1 : a ⟨k - 1, by omega⟩ ≤ a (σX.symm t) :=
      hanti (show (σX.symm t).val ≤ k - 1 by have := (σX.symm t).isLt; omega)
    simpa [a] using h1
  constructor
  · by_cases heq_k : (bundle X i).card = k
    · rw [if_pos heq_k, hM_eq]
      refine le_antisymm ?_ ?_
      · have ht := (σX ⟨0, hk1⟩).isLt
        have hlt_S : (σX ⟨0, hk1⟩).val < (bundle X i).card := by omega
        change rawPad k p X i (σX ⟨0, hk1⟩) ≤ _
        unfold rawPad
        rw [dif_pos hlt_S]
        exact Finset.le_sup' p (eS ⟨(σX ⟨0, hk1⟩).val, hlt_S⟩).2
      · refine Finset.sup'_le _ _ fun g hg => ?_
        let u := eS.symm ⟨g, hg⟩
        let t : Fin k := ⟨u.val, by have := u.isLt; omega⟩
        have hraw_t : rawPad k p X i t = p g := by
          unfold rawPad; rw [dif_pos u.isLt]
          exact congrArg (p ∘ Subtype.val) (eS.apply_symm_apply ⟨g, hg⟩)
        rw [← hraw_t]; exact ha0_max t
    · rw [if_neg heq_k, hM_eq]
      have hlt_k : (bundle X i).card < k := by omega
      refine le_antisymm ?_ ?_
      · change rawPad k p X i (σX ⟨0, hk1⟩) ≤ _
        unfold rawPad
        split_ifs with hlt_S
        · exact le_trans (Finset.le_sup' p (eS ⟨_, hlt_S⟩).2) (le_max_right 0 _)
        · exact le_max_left 0 _
      · refine max_le ?_ ?_
        · let t_pad : Fin k := ⟨k - 1, by omega⟩
          have hraw0 : rawPad k p X i t_pad = 0 := by
            unfold rawPad; exact dif_neg (by dsimp [t_pad]; omega)
          rw [← hraw0]; exact ha0_max t_pad
        · refine Finset.sup'_le _ _ fun g hg => ?_
          let u := eS.symm ⟨g, hg⟩
          let t : Fin k := ⟨u.val, lt_trans u.isLt hlt_k⟩
          have hraw_t : rawPad k p X i t = p g := by
            unfold rawPad; rw [dif_pos u.isLt]
            exact congrArg (p ∘ Subtype.val) (eS.apply_symm_apply ⟨g, hg⟩)
          rw [← hraw_t]; exact ha0_max t
  · by_cases heq_k : (bundle X i).card = k
    · rw [if_pos heq_k, hm_eq]
      refine le_antisymm ?_ ?_
      · refine Finset.le_inf' _ _ fun g hg => ?_
        let u := eS.symm ⟨g, hg⟩
        let t : Fin k := ⟨u.val, by have := u.isLt; omega⟩
        have hraw_t : rawPad k p X i t = p g := by
          unfold rawPad; rw [dif_pos u.isLt]
          exact congrArg (p ∘ Subtype.val) (eS.apply_symm_apply ⟨g, hg⟩)
        rw [← hraw_t]; exact hak_min t
      · have hlt_S : (σX ⟨k - 1, by omega⟩).val < (bundle X i).card := by
          have := (σX ⟨k - 1, by omega⟩).isLt; omega
        change _ ≤ rawPad k p X i (σX ⟨k - 1, by omega⟩)
        unfold rawPad
        rw [dif_pos hlt_S]
        exact Finset.inf'_le p (eS ⟨_, hlt_S⟩).2
    · rw [if_neg heq_k, hm_eq]
      have hlt_k : (bundle X i).card < k := by omega
      refine le_antisymm ?_ ?_
      · refine le_min ?_ ?_
        · let t_pad : Fin k := ⟨k - 1, by omega⟩
          have hraw0 : rawPad k p X i t_pad = 0 := by
            unfold rawPad; exact dif_neg (by dsimp [t_pad]; omega)
          rw [← hraw0]; exact hak_min t_pad
        · refine Finset.le_inf' _ _ fun g hg => ?_
          let u := eS.symm ⟨g, hg⟩
          let t : Fin k := ⟨u.val, lt_trans u.isLt hlt_k⟩
          have hraw_t : rawPad k p X i t = p g := by
            unfold rawPad; rw [dif_pos u.isLt]
            exact congrArg (p ∘ Subtype.val) (eS.apply_symm_apply ⟨g, hg⟩)
          rw [← hraw_t]; exact hak_min t
      · change _ ≤ rawPad k p X i (σX ⟨k - 1, by omega⟩)
        unfold rawPad
        split_ifs with hlt_S
        · exact le_trans (min_le_right 0 _) (Finset.inf'_le p (eS ⟨_, hlt_S⟩).2)
        · exact min_le_left 0 _

/-- Lemma 9 (pairwise form): `priceL p X i ≤ priceU ξ p Y i` for any two witnesses `X, Y`. -/
lemma lemma_9_priceL_le_priceU {n m : ℕ} (hr1 : 1 ≤ m / n)
    (ξ : Fin n → ℝ) (p : Fin m → ℝ) (X Y : Allocation n m) (i : Fin n)
    (hbalX : IsBalanced X) (hbalY : IsBalanced Y)
    (hshortX : ξ i < 0 → (bundle X i).card = m / n)
    (hshortY : ξ i < 0 → (bundle Y i).card = m / n)
    (hXY : ∀ l ∈ Finset.Icc 1 (m / n + 1),
      maxSubSum (bundle X i) (posPrice p) l + maxSubSum (bundle Y i) (posPrice p) l =
        maxSubSum (ownedVerts X Y i) (fun v_x => posPrice p v_x.1) (2 * l))
    (hYX_neg : ∀ l ∈ Finset.Icc 1 (m / n + 1),
      maxSubSum (bundle Y i) (negPrice p) l + maxSubSum (bundle X i) (negPrice p) l =
        maxSubSum (ownedVerts Y X i) (fun v_x => negPrice p v_x.1) (2 * l)) :
    priceL p X i ≤ priceU ξ p Y i := by
  have hneX := bundle_nonempty_of_isBalanced hr1 hbalX i
  have hneY := bundle_nonempty_of_isBalanced hr1 hbalY i
  by_cases hξ_neg : ξ i < 0
  · -- Both bundles have exact size `r = m / n`!
    have hcX_eq : (bundle X i).card = m / n := hshortX hξ_neg
    have hcY_eq : (bundle Y i).card = m / n := hshortY hξ_neg
    have hmain := padded_sorted_sum_le hr1 (by omega) p X Y i
      (le_of_eq hcX_eq) (le_of_eq hcY_eq) hXY hYX_neg
    obtain ⟨hfirstX, _⟩ := sorted_rawPad_first_last hr1 p X i hneX (le_of_eq hcX_eq)
    obtain ⟨_, hlastY⟩ := sorted_rawPad_first_last hr1 p Y i hneY (le_of_eq hcY_eq)
    rw [if_pos hcX_eq] at hfirstX
    rw [if_pos hcY_eq] at hlastY
    rw [hfirstX, hlastY] at hmain
    have hL_le : priceL p X i ≤ (∑ g ∈ bundle X i, p g) -
        maxBundleVal (fun _ g => p g) i (bundle X i) := by
      unfold priceL
      split_ifs
      · exact le_rfl
      · linarith [le_max_right 0 (maxBundleVal (fun _ g => p g) i (bundle X i))]
    have hU_eq : priceU ξ p Y i = (∑ g ∈ bundle Y i, p g) -
        minBundleVal (fun _ g => p g) i (bundle Y i) := by
      unfold priceU
      exact if_pos (Or.inr hξ_neg)
    linarith
  · -- `0 ≤ ξ i`: pad both bundles to `k = qSize n m`!
    obtain ⟨hq1, _, hqr⟩ := qSize_bounds (n := n) (m := m) hr1
    have hcX : (bundle X i).card ≤ qSize n m := card_bundle_le_qSize hbalX i
    have hcY : (bundle Y i).card ≤ qSize n m := card_bundle_le_qSize hbalY i
    have hmain := padded_sorted_sum_le hq1 hqr p X Y i hcX hcY hXY hYX_neg
    obtain ⟨hfirstX, _⟩ := sorted_rawPad_first_last hq1 p X i hneX hcX
    obtain ⟨_, hlastY⟩ := sorted_rawPad_first_last hq1 p Y i hneY hcY
    rw [hfirstX, hlastY] at hmain
    have hL_eq : priceL p X i = (∑ g ∈ bundle X i, p g) -
        (if (bundle X i).card = qSize n m then maxBundleVal (fun _ g => p g) i (bundle X i)
         else max 0 (maxBundleVal (fun _ g => p g) i (bundle X i))) := by
      unfold priceL; split_ifs <;> rfl
    have hU_eq : priceU ξ p Y i = (∑ g ∈ bundle Y i, p g) -
        (if (bundle Y i).card = qSize n m then minBundleVal (fun _ g => p g) i (bundle Y i)
         else min 0 (minBundleVal (fun _ g => p g) i (bundle Y i))) := by
      unfold priceU
      by_cases hcq : (bundle Y i).card = qSize n m
      · rw [if_pos (Or.inl hcq), if_pos hcq]
      · rw [if_neg (by tauto), if_neg hcq]
    linarith

/-- Lemma 10: `α i * resEnvy v X i j ≤ priceL p X j - priceU ξ p X i`. -/
lemma lemma_10_resEnvy_le_price_diff {n m : ℕ} (hr1 : 1 ≤ m / n)
    (v : Fin n → Fin m → ℝ) (α ξ : Fin n → ℝ) (p : Fin m → ℝ)
    (X : Allocation n m) (hbal : IsBalanced X)
    (hα_nn : ∀ k, 0 ≤ α k) (hfeas : IsDualFeasible v α ξ p)
    (htight : ∀ k : Fin n, ∀ g ∈ bundle X k, ξ k + p g = α k * v k g)
    (hshort : ∀ k : Fin n, ξ k < 0 → (bundle X k).card = m / n)
    (hlong : ∀ k : Fin n, 0 < ξ k → (bundle X k).card = m / n + 1)
    (i j : Fin n) :
    α i * resEnvy v X i j ≤ priceL p X j - priceU ξ p X i := by
  have hne_i := bundle_nonempty_of_isBalanced hr1 hbal i
  have hne_j := bundle_nonempty_of_isBalanced hr1 hbal j
  obtain ⟨g_maxP, hg_maxP_mem, hg_maxP_eq⟩ := Finset.exists_mem_eq_sup' hne_j p
  obtain ⟨h_minP, hh_minP_mem, hh_minP_eq⟩ := Finset.exists_mem_eq_inf' hne_i p
  have hMj_eq : maxBundleVal (fun _ g => p g) j (bundle X j) = p g_maxP := by
    unfold maxBundleVal; rw [dif_pos hne_j]; exact hg_maxP_eq
  have hmi_eq : minBundleVal (fun _ g => p g) i (bundle X i) = p h_minP := by
    unfold minBundleVal; rw [dif_pos hne_i]; exact hh_minP_eq
  -- 1. Upper-bound `α i * (bval v i (bundle X j) - hatMax v X i j)`
  have hj_bound : ∃ δj : ℝ, (δj = 0 ∨ δj = 1) ∧
      ((bundle X j).card = qSize n m → δj = 1) ∧
      α i * (bval v i (bundle X j) - hatMax v X i j) ≤
        priceL p X j + (((bundle X j).card : ℝ) - δj) * ξ i := by
    have hv_le_sup : v i g_maxP ≤ maxBundleVal v i (bundle X j) := by
      unfold maxBundleVal; rw [dif_pos hne_j]
      exact Finset.le_sup' (fun g => v i g) hg_maxP_mem
    have herase_j : ∀ f : Fin m → ℝ,
        ∑ g ∈ (bundle X j).erase g_maxP, f g = (∑ g ∈ bundle X j, f g) - f g_maxP := by
      intro f
      have := Finset.add_sum_erase (bundle X j) f hg_maxP_mem
      linarith
    have hcard_er_j : (((bundle X j).erase g_maxP).card : ℝ) = ((bundle X j).card : ℝ) - 1 := by
      have hc := Finset.card_erase_add_one hg_maxP_mem
      have hcr : (((bundle X j).erase g_maxP).card : ℝ) + 1 = ((bundle X j).card : ℝ) := by
        exact_mod_cast hc
      linarith
    have hrem_one : v i g_maxP ≤ hatMax v X i j →
        α i * (bval v i (bundle X j) - hatMax v X i j) ≤
          ((∑ g ∈ bundle X j, p g) - p g_maxP) + (((bundle X j).card : ℝ) - 1) * ξ i := by
      intro hv_le
      calc α i * (bval v i (bundle X j) - hatMax v X i j)
          ≤ α i * (bval v i (bundle X j) - v i g_maxP) :=
            mul_le_mul_of_nonneg_left (by linarith) (hα_nn i)
        _ = ∑ g ∈ (bundle X j).erase g_maxP, α i * v i g := by
            unfold bval; rw [herase_j, mul_sub, Finset.mul_sum]
        _ ≤ ∑ g ∈ (bundle X j).erase g_maxP, (ξ i + p g) :=
            Finset.sum_le_sum fun g _ => hfeas i g
        _ = (((bundle X j).erase g_maxP).card : ℝ) * ξ i +
              ∑ g ∈ (bundle X j).erase g_maxP, p g := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        _ = ((∑ g ∈ bundle X j, p g) - p g_maxP) + (((bundle X j).card : ℝ) - 1) * ξ i := by
            rw [hcard_er_j, herase_j]; ring
    by_cases hcj : (bundle X j).card = qSize n m
    · refine ⟨1, Or.inr rfl, fun _ => rfl, ?_⟩
      have hL : priceL p X j = (∑ g ∈ bundle X j, p g) - p g_maxP := by
        unfold priceL; rw [if_pos hcj, hMj_eq]
      have hhat : hatMax v X i j = maxBundleVal v i (bundle X j) := by
        unfold hatMax; exact if_pos hcj
      rw [hL]; exact hrem_one (hhat ▸ hv_le_sup)
    · by_cases hp_pos : 0 < p g_maxP
      · refine ⟨1, Or.inr rfl, fun h => absurd h hcj, ?_⟩
        have hL : priceL p X j = (∑ g ∈ bundle X j, p g) - p g_maxP := by
          unfold priceL; rw [if_neg hcj, hMj_eq, max_eq_right (le_of_lt hp_pos)]
        have hhat : v i g_maxP ≤ hatMax v X i j := by
          unfold hatMax; rw [if_neg hcj]; exact le_trans hv_le_sup (le_max_right 0 _)
        rw [hL]; exact hrem_one hhat
      · refine ⟨0, Or.inl rfl, fun h => absurd h hcj, ?_⟩
        have hL : priceL p X j = ∑ g ∈ bundle X j, p g := by
          unfold priceL; rw [if_neg hcj, hMj_eq, max_eq_left (by linarith), sub_zero]
        have hhat_nn : 0 ≤ hatMax v X i j := by
          unfold hatMax; rw [if_neg hcj]; exact le_max_left 0 _
        calc α i * (bval v i (bundle X j) - hatMax v X i j)
            ≤ α i * bval v i (bundle X j) :=
              mul_le_mul_of_nonneg_left (by linarith) (hα_nn i)
          _ = ∑ g ∈ bundle X j, α i * v i g := by unfold bval; rw [Finset.mul_sum]
          _ ≤ ∑ g ∈ bundle X j, (ξ i + p g) := Finset.sum_le_sum fun g _ => hfeas i g
          _ = priceL p X j + (((bundle X j).card : ℝ) - 0) * ξ i := by
              rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hL]; ring
  -- 2. Lower-bound `α i * (bval v i (bundle X i) - hatMin v X i i)` using complementary slackness
  have hi_bound : ∃ δi : ℝ, (δi = 0 ∨ δi = 1) ∧
      ((bundle X i).card = qSize n m ∨ ξ i < 0 → δi = 1) ∧
      priceU ξ p X i + (((bundle X i).card : ℝ) - δi) * ξ i ≤
        α i * (bval v i (bundle X i) - hatMin v X i i) := by
    have hv_ge_inf : minBundleVal v i (bundle X i) ≤ v i h_minP := by
      unfold minBundleVal; rw [dif_pos hne_i]
      exact Finset.inf'_le (fun g => v i g) hh_minP_mem
    have hhat_le_v : hatMin v X i i ≤ v i h_minP := by
      unfold hatMin
      split_ifs
      · exact hv_ge_inf
      · exact le_trans (min_le_right 0 _) hv_ge_inf
    have herase_i : ∀ f : Fin m → ℝ,
        ∑ g ∈ (bundle X i).erase h_minP, f g = (∑ g ∈ bundle X i, f g) - f h_minP := by
      intro f
      have := Finset.add_sum_erase (bundle X i) f hh_minP_mem
      linarith
    have hcard_er_i : (((bundle X i).erase h_minP).card : ℝ) = ((bundle X i).card : ℝ) - 1 := by
      have hc := Finset.card_erase_add_one hh_minP_mem
      have hcr : (((bundle X i).erase h_minP).card : ℝ) + 1 = ((bundle X i).card : ℝ) := by
        exact_mod_cast hc
      linarith
    have hrem_one_i : ((∑ g ∈ bundle X i, p g) - p h_minP) + (((bundle X i).card : ℝ) - 1) * ξ i ≤
        α i * (bval v i (bundle X i) - hatMin v X i i) := by
      calc ((∑ g ∈ bundle X i, p g) - p h_minP) + (((bundle X i).card : ℝ) - 1) * ξ i
          = ∑ g ∈ (bundle X i).erase h_minP, (ξ i + p g) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard_er_i, herase_i]; ring
        _ = ∑ g ∈ (bundle X i).erase h_minP, α i * v i g :=
              Finset.sum_congr rfl fun g hg => htight i g (Finset.mem_of_mem_erase hg)
        _ = α i * (bval v i (bundle X i) - v i h_minP) := by
              unfold bval; rw [herase_i, mul_sub, Finset.mul_sum]
        _ ≤ α i * (bval v i (bundle X i) - hatMin v X i i) :=
              mul_le_mul_of_nonneg_left (by linarith) (hα_nn i)
    by_cases hci : (bundle X i).card = qSize n m ∨ ξ i < 0
    · refine ⟨1, Or.inr rfl, fun _ => rfl, ?_⟩
      have hU : priceU ξ p X i = (∑ g ∈ bundle X i, p g) - p h_minP := by
        unfold priceU; rw [if_pos hci, hmi_eq]
      rw [hU]; exact hrem_one_i
    · have hci_ne : (bundle X i).card ≠ qSize n m := fun h => hci (Or.inl h)
      by_cases hp_neg : p h_minP < 0
      · refine ⟨1, Or.inr rfl, fun h => absurd h hci, ?_⟩
        have hU : priceU ξ p X i = (∑ g ∈ bundle X i, p g) - p h_minP := by
          unfold priceU; rw [if_neg hci, hmi_eq, min_eq_right (le_of_lt hp_neg)]
        rw [hU]; exact hrem_one_i
      · refine ⟨0, Or.inl rfl, fun h => absurd h hci, ?_⟩
        have hU : priceU ξ p X i = ∑ g ∈ bundle X i, p g := by
          unfold priceU; rw [if_neg hci, hmi_eq, min_eq_left (by linarith), sub_zero]
        have hhat_nonpos : hatMin v X i i ≤ 0 := by
          unfold hatMin; rw [if_neg hci_ne]; exact min_le_left 0 _
        calc priceU ξ p X i + (((bundle X i).card : ℝ) - 0) * ξ i
            = ∑ g ∈ bundle X i, (ξ i + p g) := by
                rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hU]; ring
          _ = ∑ g ∈ bundle X i, α i * v i g := Finset.sum_congr rfl fun g hg => htight i g hg
          _ = α i * bval v i (bundle X i) := by unfold bval; rw [Finset.mul_sum]
          _ ≤ α i * (bval v i (bundle X i) - hatMin v X i i) :=
                mul_le_mul_of_nonneg_left (by linarith) (hα_nn i)
  obtain ⟨δj, hδj_01, hδj_full, hj_ineq⟩ := hj_bound
  obtain ⟨δi, hδi_01, hδi_full, hi_ineq⟩ := hi_bound
  have hres_le : α i * resEnvy v X i j ≤
      α i * (bval v i (bundle X j) - hatMax v X i j) -
        α i * (bval v i (bundle X i) - hatMin v X i i) := by
    have h1 : resEnvy v X i j ≤ envy v X i j + hatMin v X i i - hatMax v X i j := min_le_right _ _
    unfold envy at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hα_nn i)
    linarith
  -- 3. Check `(((bundle X j).card - (bundle X i).card - δj + δi) * ξ i) ≤ 0`
  have hslack_nonpos :
      (((bundle X j).card : ℝ) - ((bundle X i).card : ℝ) - δj + δi) * ξ i ≤ 0 := by
    have hδj_ub : δj ≤ 1 := by rcases hδj_01 with rfl | rfl <;> norm_num
    have hδj_lb : 0 ≤ δj := by rcases hδj_01 with rfl | rfl <;> norm_num
    rcases lt_trichotomy (ξ i) 0 with hξ_lt | hξ_eq | hξ_gt
    · -- `ξ i < 0`: `bundle X i` has size `r`, `δi = 1`, `bundle X j` has size `≥ r`
      have hci_r : ((bundle X i).card : ℝ) = ((m / n : ℕ) : ℝ) := by
        exact_mod_cast hshort i hξ_lt
      have hcj_ge : ((m / n : ℕ) : ℝ) ≤ ((bundle X j).card : ℝ) := by
        have : m / n ≤ (bundle X j).card := by rcases hbal j with h | h <;> omega
        exact_mod_cast this
      have hδi_1 : δi = 1 := hδi_full (Or.inr hξ_lt)
      have hcoeff_nn : 0 ≤ ((bundle X j).card : ℝ) - ((bundle X i).card : ℝ) - δj + δi := by
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos hcoeff_nn (le_of_lt hξ_lt)
    · rw [hξ_eq, mul_zero]
    · -- `0 < ξ i`: `bundle X i` has size `r + 1 = qSize n m`, so `δi = 1`
      have hci_long : (bundle X i).card = m / n + 1 := hlong i hξ_gt
      have hnot_dvd : ¬ (n ∣ m) := by
        intro hdvd
        have := card_bundle_eq_div_of_dvd hbal hdvd i
        omega
      have hq_eq : qSize n m = m / n + 1 := by unfold qSize; exact if_neg hnot_dvd
      have hδi_1 : δi = 1 := hδi_full (Or.inl (hci_long.trans hq_eq.symm))
      have hcoeff_np : ((bundle X j).card : ℝ) - ((bundle X i).card : ℝ) - δj + δi ≤ 0 := by
        rcases hbal j with hcj_r | hcj_r1
        · have h1 : ((bundle X j).card : ℝ) = ((m / n : ℕ) : ℝ) := by exact_mod_cast hcj_r
          have h2 : ((bundle X i).card : ℝ) = ((m / n : ℕ) : ℝ) + 1 := by
            rw [hci_long]; push_cast; ring
          linarith
        · have hδj_1 : δj = 1 := hδj_full (hcj_r1.trans hq_eq.symm)
          rw [hcj_r1, hci_long, hδj_1, hδi_1]; ring_nf; exact le_rfl
      exact mul_nonpos_of_nonpos_of_nonneg hcoeff_np (le_of_lt hξ_gt)
  linarith

/-- Lemma 11 (Consolidating witnesses): algebraic potential argument without graph library! -/
lemma lemma_11_consolidate {n m : ℕ} (hn1 : 1 ≤ n) (v : Fin n → Fin m → ℝ)
    {ρ γ : ℝ} (hγ : 0 ≤ γ) (hρ_pos : 0 < ρ) (hρ1 : (n : ℝ) * ρ ≤ 1)
    {w_star : Fin n → ℝ} (hw_star : w_star ∈ stdSimplex ℝ (Fin n))
    (B : Fin n → Allocation n m)
    (hdiv_min : ∀ idx k : Fin n, divD v ρ γ (B idx) w_star idx ≤ divD v ρ γ (B idx) w_star k)
    (β : Fin n → ℝ)
    (hβ_bound : ∀ (idx i j : Fin n), alphaW ρ w_star i * resEnvy v (B idx) i j ≤ β j - β i) :
    ∃ a : Fin n, ∀ i j : Fin n, resEnvy v (B a) i j ≤ γ := by
  let α_star : Fin n → ℝ := alphaW ρ w_star
  let pot : Fin n → ℝ := fun i => β i + γ * α_star i
  -- Every flow edge satisfies `flowF ... (B idx) w_star i j ≤ max (pot j - pot i) 0`
  have hflow_pot : ∀ (idx i j : Fin n),
      0 < flowF v ρ γ (B idx) w_star i j → pot i < pot j := by
    intro idx i j hpos
    unfold flowF at hpos
    have h1 : 0 < α_star i * resEnvy v (B idx) i j + γ * (α_star j - α_star i) := by
      by_contra hnp
      push_neg at hnp
      have : max (α_star i * resEnvy v (B idx) i j + γ * (α_star j - α_star i)) 0 = 0 :=
        max_eq_right hnp
      dsimp [α_star] at this
      linarith
    have h2 := hβ_bound idx i j
    dsimp [pot, α_star] at h1 h2 ⊢
    linarith
  -- Pick `a : Fin n` minimizing `pot`
  have huniv_ne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn1⟩, Finset.mem_univ _⟩
  obtain ⟨a, _, ha_min_eq⟩ := Finset.exists_mem_eq_inf' huniv_ne pot
  have ha_le : ∀ k : Fin n, pot a ≤ pot k := by
    intro k; rw [← ha_min_eq]; exact Finset.inf'_le pot (Finset.mem_univ k)
  -- `a` has zero incoming flow in `B a`, hence `0 ≤ divD v ρ γ (B a) w_star a`
  have hin_a_zero : ∑ j ∈ Finset.univ.erase a, flowF v ρ γ (B a) w_star j a = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_contra hne
    have hpos : 0 < flowF v ρ γ (B a) w_star j a :=
      lt_of_le_of_ne (flowF_nonneg v ρ γ (B a) w_star j a) (Ne.symm hne)
    exact not_lt_of_ge (ha_le j) (hflow_pot a j a hpos)
  have hdiv_a_nn : 0 ≤ divD v ρ γ (B a) w_star a := by
    unfold divD
    rw [hin_a_zero, sub_zero]
    exact Finset.sum_nonneg fun j _ => flowF_nonneg v ρ γ (B a) w_star a j
  have hdiv_all_nn : ∀ k : Fin n, 0 ≤ divD v ρ γ (B a) w_star k :=
    fun k => le_trans hdiv_a_nn (hdiv_min a k)
  have hdiv_all_zero : ∀ k : Fin n, divD v ρ γ (B a) w_star k = 0 := fun k =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hdiv_all_nn l)).mp
      (sum_divD_eq_zero v ρ γ (B a) w_star) k (Finset.mem_univ k)
  -- Potential-weighted divergence identity:
  -- `0 = - ∑ i, pot i * divD ... i = ∑ i, ∑ j ∈ univ.erase i, (pot j - pot i) * flowF ... i j`
  have hpot_energy :
      ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
        (pot j - pot i) * flowF v ρ γ (B a) w_star i j = 0 := by
    have hlhs0 : - ∑ i : Fin n, pot i * divD v ρ γ (B a) w_star i = 0 := by
      simp [hdiv_all_zero]
    rw [← hlhs0]
    unfold divD
    simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    have her : ∀ i : Fin n, Finset.univ.erase i = Finset.univ.filter (fun j : Fin n => j ≠ i) := by
      intro i; ext j; simp
    have h1 : (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, pot i * flowF v ρ γ (B a) w_star i j) =
        ∑ i : Fin n, ∑ j : Fin n, if j ≠ i then pot i * flowF v ρ γ (B a) w_star i j else 0 := by
      refine Finset.sum_congr rfl fun i _ => by rw [her i, Finset.sum_filter]
    have h2 : (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, pot i * flowF v ρ γ (B a) w_star j i) =
        ∑ i : Fin n, ∑ j : Fin n, if i ≠ j then pot j * flowF v ρ γ (B a) w_star i j else 0 := by
      calc (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, pot i * flowF v ρ γ (B a) w_star j i)
          = ∑ i : Fin n, ∑ j : Fin n,
              if j ≠ i then pot i * flowF v ρ γ (B a) w_star j i else 0 := by
            refine Finset.sum_congr rfl fun i _ => by rw [her i, Finset.sum_filter]
        _ = ∑ j : Fin n, ∑ i : Fin n,
              if j ≠ i then pot i * flowF v ρ γ (B a) w_star j i else 0 := Finset.sum_comm
        _ = ∑ i : Fin n, ∑ j : Fin n,
              if i ≠ j then pot j * flowF v ρ γ (B a) w_star i j else 0 := rfl
    have h3 : (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
          (pot j - pot i) * flowF v ρ γ (B a) w_star i j) =
        ∑ i : Fin n, ∑ j : Fin n,
          if j ≠ i then (pot j - pot i) * flowF v ρ γ (B a) w_star i j else 0 := by
      refine Finset.sum_congr rfl fun i _ => by rw [her i, Finset.sum_filter]
    rw [h1, h2, h3]
    have h4 : (∑ i : Fin n, ∑ j : Fin n,
          if i ≠ j then pot j * flowF v ρ γ (B a) w_star i j else 0) =
        ∑ i : Fin n, ∑ j : Fin n,
          if j ≠ i then pot j * flowF v ρ γ (B a) w_star i j else 0 := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i = j
      · subst hij; simp
      · have hji : j ≠ i := fun h => hij h.symm
        simp [hij, hji]
    rw [h4]
    rw [neg_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  have hterm_nn : ∀ (i : Fin n), ∀ j ∈ Finset.univ.erase i,
      0 ≤ (pot j - pot i) * flowF v ρ γ (B a) w_star i j := by
    intro i j _
    by_cases h0 : flowF v ρ γ (B a) w_star i j = 0
    · rw [h0, mul_zero]
    · have hpos : 0 < flowF v ρ γ (B a) w_star i j :=
        lt_of_le_of_ne (flowF_nonneg v ρ γ (B a) w_star i j) (Ne.symm h0)
      have hlt := hflow_pot a i j hpos
      exact mul_nonneg (by linarith) (le_of_lt hpos)
  have hflow_all_zero : ∀ (i j : Fin n), i ≠ j → flowF v ρ γ (B a) w_star i j = 0 := by
    intro i j hij
    have hi_z : ∑ j' ∈ Finset.univ.erase i,
        (pot j' - pot i) * flowF v ρ γ (B a) w_star i j' = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i' _ => Finset.sum_nonneg (hterm_nn i'))).mp
        hpot_energy i (Finset.mem_univ i)
    have hj_z : (pot j - pot i) * flowF v ρ γ (B a) w_star i j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (hterm_nn i)).mp hi_z j
        (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
    by_contra hne
    have hpos : 0 < flowF v ρ γ (B a) w_star i j :=
      lt_of_le_of_ne (flowF_nonneg v ρ γ (B a) w_star i j) (Ne.symm hne)
    have hlt := hflow_pot a i j hpos
    have : 0 < (pot j - pot i) * flowF v ρ γ (B a) w_star i j :=
      mul_pos (by linarith) hpos
    linarith
  refine ⟨a, fun i j => ?_⟩
  by_cases hij : i = j
  · subst hij
    have h0 : envy v (B a) i i = 0 := by unfold envy; ring
    calc resEnvy v (B a) i i ≤ envy v (B a) i i := min_le_left _ _
      _ = 0 := h0
      _ ≤ γ := hγ
  · have hfz := hflow_all_zero i j hij
    unfold flowF at hfz
    have hle0 : α_star i * resEnvy v (B a) i j + γ * (α_star j - α_star i) ≤ 0 := by
      have := le_max_left (α_star i * resEnvy v (B a) i j + γ * (α_star j - α_star i)) 0
      dsimp [α_star] at this ⊢
      linarith
    have hαj_nn : 0 ≤ α_star j := by
      have := (alphaW_bounds (le_of_lt hρ_pos) hρ1 hw_star j).1
      dsimp [α_star]; linarith
    have hαi_pos : 0 < α_star i :=
      lt_of_lt_of_le hρ_pos (alphaW_bounds (le_of_lt hρ_pos) hρ1 hw_star i).1
    nlinarith

/-- Lemma 13 (`fPO` and `γ`-approximate `EF[1,1]`): taking `λ_t, ε_t → 0` and consolidating! -/
lemma exists_approx_fair_fpo {n m : ℕ} (hn2 : 2 ≤ n) (hr1 : 1 ≤ m / n)
    (v : Fin n → Fin m → ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ A : Allocation n m,
      IsBalanced A ∧ IsFPOIn v (Pbal n m) (allocMatrix A) ∧
      ∀ i j : Fin n, resEnvy v A i j ≤ γ := by
  have hn1 : 1 ≤ n := by omega
  let K : ℝ := 2 * (((m / n : ℕ) : ℝ) + 1) * vmax v
  let H : ℝ := 2 * (((m / n : ℕ) : ℝ) + 2) * vmax v
  have hV : 0 ≤ vmax v := vmax_nonneg v
  have hK_nn : 0 ≤ K := by dsimp [K]; positivity
  have hH_nn : 0 ≤ H := by dsimp [H]; positivity
  have hn_sub_nn : 0 ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  let denom : ℝ := 4 * (n : ℝ) * (γ + H + ((n : ℝ) - 1) * K)
  have hdenom_pos : 0 < denom := by dsimp [denom]; positivity
  let ρ : ℝ := γ / denom
  have hρ_pos : 0 < ρ := div_pos hγ hdenom_pos
  have hρ1 : (n : ℝ) * ρ ≤ 1 := by
    have hmul : ρ * denom = γ := div_mul_cancel₀ γ (ne_of_gt hdenom_pos)
    have hA_nn : 0 ≤ (n : ℝ) * ρ := by positivity
    have hB_ge : 4 * γ ≤ 4 * (γ + H + ((n : ℝ) - 1) * K) := by
      have := mul_nonneg hn_sub_nn hK_nn
      linarith
    have hAB : ((n : ℝ) * ρ) * (4 * (γ + H + ((n : ℝ) - 1) * K)) = γ := by
      calc ((n : ℝ) * ρ) * (4 * (γ + H + ((n : ℝ) - 1) * K))
          = ρ * denom := by dsimp [denom]; ring
        _ = γ := hmul
    have hle : ((n : ℝ) * ρ) * (4 * γ) ≤ γ :=
      le_trans (mul_le_mul_of_nonneg_left hB_ge hA_nn) (le_of_eq hAB)
    by_contra hgt
    have hlt : 1 < (n : ℝ) * ρ := lt_of_not_ge hgt
    have hmul_lt : 1 * (4 * γ) < ((n : ℝ) * ρ) * (4 * γ) :=
      mul_lt_mul_of_pos_right hlt (by positivity)
    linarith
  -- Sequence `lam_t = 1 / (t + 1)`, `eps_t = 1 / (t + 1)`
  let stepSeq : ℕ → ℝ := fun t => 1 / ((t : ℝ) + 1)
  have hstep_pos : ∀ t, 0 < stepSeq t := fun t => by dsimp [stepSeq]; positivity
  have hex_t : ∀ t : ℕ, ∃ (wt : Fin n → ℝ) (Bt : Fin n → Allocation n m),
      wt ∈ stdSimplex ℝ (Fin n) ∧
      ∀ idx : Fin n, IsScoreMax v ρ (stepSeq t) (stepSeq t) wt (Bt idx) ∧
        ∀ k : Fin n, divD v ρ γ (Bt idx) wt idx ≤ divD v ρ γ (Bt idx) wt k :=
    fun t => exists_kkm_witnesses hn2 v hγ hρ_pos le_rfl (hstep_pos t)
  choose wt Bt hwt_simp hBt_spec using hex_t
  -- Extract constant witness tuple `B` along `φ₁`, then convergent `wt` and `regDual`
  obtain ⟨B, φ₁, hφ₁_mono, hB_const⟩ := exists_const_subseq_of_finite Bt
  obtain ⟨w_star, hw_star_simp, φ₂, hφ₂_mono, hwt_tend₂⟩ :=
    (isCompact_stdSimplex ℝ (Fin n)).tendsto_subseq (fun k => hwt_simp (φ₁ k))
  have hzp_box : ∀ k, regDual v ρ (stepSeq (φ₁ (φ₂ k))) (wt (φ₁ (φ₂ k))) ∈ BoxDual v :=
    fun k => (regDual_spec v (le_of_lt hρ_pos) hρ1 (hstep_pos _) (hwt_simp _)).1.1
  obtain ⟨zp_star, _, φ₃, hφ₃_mono, hzp_tend⟩ :=
    (isCompact_BoxDual v).tendsto_subseq hzp_box
  let ψ : ℕ → ℕ := fun k => φ₁ (φ₂ (φ₃ k))
  have hψ_mono : StrictMono ψ := hφ₁_mono.comp (hφ₂_mono.comp hφ₃_mono)
  have hstep_tend : Tendsto (fun k => stepSeq (ψ k)) atTop (𝓝 0) :=
    tendsto_inv_nat_succ_comp hψ_mono
  have hwt_tend : Tendsto (fun k => wt (ψ k)) atTop (𝓝 w_star) :=
    hwt_tend₂.comp hφ₃_mono.tendsto_atTop
  have hB_ψ : ∀ k, Bt (ψ k) = B := fun k => hB_const (φ₂ (φ₃ k))
  let α_star : Fin n → ℝ := alphaW ρ w_star
  let ξ_star : Fin n → ℝ := zp_star.1
  let p_star : Fin m → ℝ := zp_star.2
  have hα_pos : ∀ i : Fin n, 0 < α_star i := fun i =>
    lt_of_lt_of_le hρ_pos (alphaW_bounds (le_of_lt hρ_pos) hρ1 hw_star_simp i).1
  have hα_nn : ∀ i : Fin n, 0 ≤ α_star i := fun i => le_of_lt (hα_pos i)
  have hα_tend : ∀ i : Fin n, Tendsto (fun k => alphaW ρ (wt (ψ k)) i) atTop (𝓝 (α_star i)) := by
    intro i
    unfold alphaW
    exact tendsto_const_nhds.add (tendsto_const_nhds.mul
      ((continuous_apply i).continuousAt.tendsto.comp hwt_tend))
  have hξ_tend : ∀ i : Fin n,
      Tendsto (fun k => (regDual v ρ (stepSeq (ψ k)) (wt (ψ k))).1 i) atTop (𝓝 (ξ_star i)) :=
    fun i => ((continuous_apply i).comp continuous_fst).continuousAt.tendsto.comp hzp_tend
  have hp_tend_all : Tendsto (fun k => (regDual v ρ (stepSeq (ψ k)) (wt (ψ k))).2) atTop
      (𝓝 p_star) :=
    continuous_snd.continuousAt.tendsto.comp hzp_tend
  -- 1. Limiting dual feasibility
  have hfeas_star : IsDualFeasible v α_star ξ_star p_star := by
    intro i g
    have hk_feas : ∀ k, alphaW ρ (wt (ψ k)) i * v i g ≤
        (regDual v ρ (stepSeq (ψ k)) (wt (ψ k))).1 i +
        (regDual v ρ (stepSeq (ψ k)) (wt (ψ k))).2 g :=
      fun k => (regDual_spec v (le_of_lt hρ_pos) hρ1 (hstep_pos (ψ k)) (hwt_simp (ψ k))).1.2 i g
    exact le_of_tendsto_of_tendsto
      ((hα_tend i).mul tendsto_const_nhds)
      ((hξ_tend i).add (((continuous_apply g).continuousAt.tendsto).comp hp_tend_all))
      (Eventually.of_forall hk_feas)
  -- 2. Balancedness, welfare optimality (`fPO`), and complementary slackness for each `B idx`
  have hB_bal : ∀ idx : Fin n, IsBalanced (B idx) := by
    intro idx
    have h0 := (hBt_spec (ψ 0) idx).1.1
    rwa [hB_ψ 0] at h0
  have hB_welf_opt : ∀ idx : Fin n,
      MaximizesWeightedWelfare v α_star (Pbal n m) (allocMatrix (B idx)) := by
    intro idx
    refine ⟨(allocMatrix_mem_Pbal_iff (B idx)).mpr (hB_bal idx), fun y hy => ?_⟩
    have hineq_k : ∀ k,
        (∑ i : Fin n, alphaW ρ (wt (ψ k)) i * fval v i y) - stepSeq (ψ k) * C_Phi n m v ≤
          ∑ i : Fin n, alphaW ρ (wt (ψ k)) i * fval v i (allocMatrix (B idx)) := by
      intro k
      have hsc : IsScoreMax v ρ (stepSeq (ψ k)) (stepSeq (ψ k)) (wt (ψ k)) (B idx) := by
        rw [← hB_ψ k]; exact (hBt_spec (ψ k) idx).1
      have hgap := scoreMax_welfare_gap hn1 v (le_of_lt hρ_pos) hρ1 (hstep_pos (ψ k))
        (le_of_lt (hstep_pos (ψ k))) (hwt_simp (ψ k)) hsc
      obtain ⟨A_opt, hA_opt_bal, hA_opt_eq⟩ :=
        exists_balAlloc_eq_wstar hn1 v (alphaW ρ (wt (ψ k)))
      -- Also `∑ i, α_k i * fval v i y ≤ wstar hn1 v α_k`!
      obtain ⟨A_max, hA_max_bal, hA_max_prop⟩ :=
        exists_balanced_maximizer hn1 (fun i g => alphaW ρ (wt (ψ k)) i * v i g)
      have hy_le_Amax : ∑ i : Fin n, alphaW ρ (wt (ψ k)) i * fval v i y ≤
          ∑ i : Fin n, alphaW ρ (wt (ψ k)) i * bval v i (bundle A_max i) := by
        have hm := hA_max_prop y hy
        have hlhs : (∑ i : Fin n, ∑ g : Fin m, alphaW ρ (wt (ψ k)) i * v i g * y i g) =
            ∑ i : Fin n, alphaW ρ (wt (ψ k)) i * fval v i y := by
          refine Finset.sum_congr rfl fun i _ => ?_
          unfold fval; rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => by ring
        have hrhs : (∑ i : Fin n, ∑ g : Fin m,
              alphaW ρ (wt (ψ k)) i * v i g * allocMatrix A_max i g) =
            ∑ i : Fin n, alphaW ρ (wt (ψ k)) i * bval v i (bundle A_max i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← fval_allocMatrix v A_max i]
          unfold fval; rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => by ring
        linarith
      have hAmax_le_wstar : ∑ i : Fin n, alphaW ρ (wt (ψ k)) i * bval v i (bundle A_max i) ≤
          wstar hn1 v (alphaW ρ (wt (ψ k))) := by
        unfold wstar
        exact Finset.le_sup' (fun X => ∑ i, alphaW ρ (wt (ψ k)) i * bval v i (bundle X i))
          (mem_balAllocFinset.mpr hA_max_bal)
      have hB_fval : ∑ i : Fin n, alphaW ρ (wt (ψ k)) i * fval v i (allocMatrix (B idx)) =
          ∑ i : Fin n, alphaW ρ (wt (ψ k)) i * bval v i (bundle (B idx) i) := by
        refine Finset.sum_congr rfl fun i _ => by rw [fval_allocMatrix]
      linarith
    have hlhs_tend : Tendsto (fun k =>
        (∑ i : Fin n, alphaW ρ (wt (ψ k)) i * fval v i y) - stepSeq (ψ k) * C_Phi n m v)
        atTop (𝓝 (∑ i : Fin n, α_star i * fval v i y)) := by
      have h1 : Tendsto (fun k => ∑ i : Fin n, alphaW ρ (wt (ψ k)) i * fval v i y)
          atTop (𝓝 (∑ i : Fin n, α_star i * fval v i y)) :=
        tendsto_finsetSum _ fun i _ => (hα_tend i).mul tendsto_const_nhds
      have h2 : Tendsto (fun k => stepSeq (ψ k) * C_Phi n m v) atTop (𝓝 0) := by
        simpa using hstep_tend.mul (tendsto_const_nhds (x := C_Phi n m v))
      simpa using h1.sub h2
    have hrhs_tend : Tendsto (fun k =>
        ∑ i : Fin n, alphaW ρ (wt (ψ k)) i * fval v i (allocMatrix (B idx)))
        atTop (𝓝 (∑ i : Fin n, α_star i * fval v i (allocMatrix (B idx)))) :=
      tendsto_finsetSum _ fun i _ => (hα_tend i).mul tendsto_const_nhds
    exact le_of_tendsto_of_tendsto hlhs_tend hrhs_tend (Eventually.of_forall hineq_k)
  have hB_slack_zero : ∀ idx : Fin n,
      (∀ i : Fin n, ∀ g ∈ bundle (B idx) i, ξ_star i + p_star g = α_star i * v i g) ∧
      (∀ i : Fin n, ξ_star i < 0 → (bundle (B idx) i).card = m / n) ∧
      (∀ i : Fin n, 0 < ξ_star i → (bundle (B idx) i).card = m / n + 1) := by
    intro idx
    let X := B idx
    have hbalX : IsBalanced X := hB_bal idx
    -- Show `dualObj n m ξ_star p_star ≤ ∑ i, α_star i * bval v i (bundle X i)`
    have hdual_le : dualObj n m ξ_star p_star ≤ ∑ i : Fin n, α_star i * bval v i (bundle X i) := by
      let C_reg : ℝ := ((n : ℝ) + (m : ℝ)) * M0 v ^ 2
      have hineq_k : ∀ k,
          dualObj n m (regDual v ρ (stepSeq (ψ k)) (wt (ψ k))).1
            (regDual v ρ (stepSeq (ψ k)) (wt (ψ k))).2 ≤
          (∑ i : Fin n, alphaW ρ (wt (ψ k)) i * bval v i (bundle X i)) +
            stepSeq (ψ k) * C_Phi n m v + stepSeq (ψ k) * C_reg := by
        intro k
        have hsc : IsScoreMax v ρ (stepSeq (ψ k)) (stepSeq (ψ k)) (wt (ψ k)) X := by
          dsimp [X]; rw [← hB_ψ k]; exact (hBt_spec (ψ k) idx).1
        have hgap := scoreMax_welfare_gap hn1 v (le_of_lt hρ_pos) hρ1 (hstep_pos (ψ k))
          (le_of_lt (hstep_pos (ψ k))) (hwt_simp (ψ k)) hsc
        have hrgap := regDual_gap hn2 hr1 v (le_of_lt hρ_pos) hρ1 (hstep_pos (ψ k))
          (hwt_simp (ψ k))
        dsimp [C_reg]
        linarith
      have hlhs_tend : Tendsto (fun k =>
          dualObj n m (regDual v ρ (stepSeq (ψ k)) (wt (ψ k))).1
            (regDual v ρ (stepSeq (ψ k)) (wt (ψ k))).2)
          atTop (𝓝 (dualObj n m ξ_star p_star)) :=
        ((continuous_dualObj n m).tendsto zp_star).comp hzp_tend
      have hrhs_tend : Tendsto (fun k =>
          (∑ i : Fin n, alphaW ρ (wt (ψ k)) i * bval v i (bundle X i)) +
            stepSeq (ψ k) * C_Phi n m v + stepSeq (ψ k) * C_reg)
          atTop (𝓝 (∑ i : Fin n, α_star i * bval v i (bundle X i))) := by
        have h1 : Tendsto (fun k => ∑ i : Fin n, alphaW ρ (wt (ψ k)) i * bval v i (bundle X i))
            atTop (𝓝 (∑ i : Fin n, α_star i * bval v i (bundle X i))) :=
          tendsto_finsetSum _ fun i _ => (hα_tend i).mul tendsto_const_nhds
        have h2 : Tendsto (fun k => stepSeq (ψ k) * C_Phi n m v) atTop (𝓝 0) := by
          simpa using hstep_tend.mul (tendsto_const_nhds (x := C_Phi n m v))
        have h3 : Tendsto (fun k => stepSeq (ψ k) * C_reg) atTop (𝓝 0) := by
          simpa using hstep_tend.mul (tendsto_const_nhds (x := C_reg))
        simpa using (h1.add h2).add h3
      exact le_of_tendsto_of_tendsto hlhs_tend hrhs_tend (Eventually.of_forall hineq_k)
    have hwd := weak_duality hfeas_star ((allocMatrix_mem_Pbal_iff X).mpr hbalX)
    have hfval_eq : ∑ i : Fin n, α_star i * fval v i (allocMatrix X) =
        ∑ i : Fin n, α_star i * bval v i (bundle X i) :=
      Finset.sum_congr rfl fun i _ => by rw [fval_allocMatrix]
    have hslack_sum_zero :
        ∑ i : Fin n, (edgeSlack v α_star ξ_star p_star X i + rowSlack ξ_star X i) = 0 := by
      have hge0 : 0 ≤ ∑ i : Fin n,
          (edgeSlack v α_star ξ_star p_star X i + rowSlack ξ_star X i) :=
        Finset.sum_nonneg fun i _ =>
          add_nonneg (edgeSlack_nonneg hfeas_star X i) (rowSlack_nonneg ξ_star hbalX i)
      have hle0 : ∑ i : Fin n,
          (edgeSlack v α_star ξ_star p_star X i + rowSlack ξ_star X i) ≤ 0 := by
        rw [primal_dual_slack_eq]
        linarith
      exact le_antisymm hle0 hge0
    have hi_slack_zero : ∀ i : Fin n,
        edgeSlack v α_star ξ_star p_star X i = 0 ∧ rowSlack ξ_star X i = 0 := by
      intro i
      have hsum_i : edgeSlack v α_star ξ_star p_star X i + rowSlack ξ_star X i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
          add_nonneg (edgeSlack_nonneg hfeas_star X k) (rowSlack_nonneg ξ_star hbalX k))).mp
          hslack_sum_zero i (Finset.mem_univ i)
      have he_nn := edgeSlack_nonneg hfeas_star X i
      have hr_nn := rowSlack_nonneg ξ_star hbalX i
      exact ⟨by linarith, by linarith⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i g hg
      have he0 := (hi_slack_zero i).1
      unfold edgeSlack at he0
      have hg0 : ξ_star i + p_star g - α_star i * v i g = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun g' _ => by linarith [hfeas_star i g'])).mp
          he0 g hg
      linarith
    · intro i hξ_neg
      have hr0 := (hi_slack_zero i).2
      unfold rowSlack zA at hr0
      rw [max_eq_right (le_of_lt hξ_neg)] at hr0
      have hz0 : ((bundle X i).card : ℝ) - ((m / n : ℕ) : ℝ) = 0 := by nlinarith
      have hcr : ((bundle X i).card : ℝ) = ((m / n : ℕ) : ℝ) := by linarith
      exact_mod_cast hcr
    · intro i hξ_pos
      have hr0 := (hi_slack_zero i).2
      unfold rowSlack zA at hr0
      rw [max_eq_left (le_of_lt hξ_pos)] at hr0
      have hz1 : ((bundle X i).card : ℝ) - ((m / n : ℕ) : ℝ) = 1 := by nlinarith
      have hcr : ((bundle X i).card : ℝ) = (((m / n + 1 : ℕ)) : ℝ) := by
        push_cast; linarith
      exact_mod_cast hcr
  -- 3. Limiting price-interlacing equalities at `p_star` for every pair `(B idx₁, B idx₂)`
  have hB_interlace : ∀ (idx₁ idx₂ i : Fin n), ∀ l ∈ Finset.Icc 1 (m / n + 1),
      (maxSubSum (bundle (B idx₁) i) (posPrice p_star) l +
        maxSubSum (bundle (B idx₂) i) (posPrice p_star) l =
        maxSubSum (ownedVerts (B idx₁) (B idx₂) i) (fun v_x => posPrice p_star v_x.1) (2 * l)) ∧
      (maxSubSum (bundle (B idx₁) i) (negPrice p_star) l +
        maxSubSum (bundle (B idx₂) i) (negPrice p_star) l =
        maxSubSum (ownedVerts (B idx₁) (B idx₂) i) (fun v_x => negPrice p_star v_x.1) (2 * l)) := by
    intro idx₁ idx₂ i l hl
    have hk_eq : ∀ k,
        let pk := (regDual v ρ (stepSeq (ψ k)) (wt (ψ k))).2
        (maxSubSum (bundle (B idx₁) i) (posPrice pk) l +
          maxSubSum (bundle (B idx₂) i) (posPrice pk) l =
          maxSubSum (ownedVerts (B idx₁) (B idx₂) i) (fun v_x => posPrice pk v_x.1) (2 * l)) ∧
        (maxSubSum (bundle (B idx₁) i) (negPrice pk) l +
          maxSubSum (bundle (B idx₂) i) (negPrice pk) l =
          maxSubSum (ownedVerts (B idx₁) (B idx₂) i) (fun v_x => negPrice pk v_x.1) (2 * l)) := by
      intro k
      have hsc₁ : IsScoreMax v ρ (stepSeq (ψ k)) (stepSeq (ψ k)) (wt (ψ k)) (B idx₁) := by
        rw [← hB_ψ k]; exact (hBt_spec (ψ k) idx₁).1
      have hsc₂ : IsScoreMax v ρ (stepSeq (ψ k)) (stepSeq (ψ k)) (wt (ψ k)) (B idx₂) := by
        rw [← hB_ψ k]; exact (hBt_spec (ψ k) idx₂).1
      exact price_interlacing_prefix_eq v (hstep_pos (ψ k)) (wt (ψ k)) hsc₁ hsc₂ i l hl
    have hcont_owned : ∀ (φ_fn : ℝ → ℝ), Continuous φ_fn →
        Continuous (fun p : Fin m → ℝ =>
          maxSubSum (ownedVerts (B idx₁) (B idx₂) i) (fun v_x => φ_fn (p v_x.1)) (2 * l)) := by
      intro φ_fn hφ
      unfold maxSubSum
      refine continuous_sup'_apply _ _ _ fun T _ => ?_
      exact continuous_finsetSum _ fun v_x _ => hφ.comp (continuous_apply v_x.1)
    constructor
    · have hc_lhs : Continuous (fun p : Fin m → ℝ =>
          maxSubSum (bundle (B idx₁) i) (posPrice p) l +
          maxSubSum (bundle (B idx₂) i) (posPrice p) l) :=
        (continuous_maxSubSum _ l _ (continuous_id.max continuous_const)).add
          (continuous_maxSubSum _ l _ (continuous_id.max continuous_const))
      have hc_rhs : Continuous (fun p : Fin m → ℝ =>
          maxSubSum (ownedVerts (B idx₁) (B idx₂) i) (fun v_x => posPrice p v_x.1) (2 * l)) :=
        hcont_owned _ (continuous_id.max continuous_const)
      refine tendsto_nhds_unique ((hc_lhs.tendsto p_star).comp hp_tend_all) ?_
      have ht2 := (hc_rhs.tendsto p_star).comp hp_tend_all
      exact ht2.congr (fun k => ((hk_eq k).1).symm)
    · have hc_lhs : Continuous (fun p : Fin m → ℝ =>
          maxSubSum (bundle (B idx₁) i) (negPrice p) l +
          maxSubSum (bundle (B idx₂) i) (negPrice p) l) :=
        (continuous_maxSubSum _ l _ (continuous_neg.max continuous_const)).add
          (continuous_maxSubSum _ l _ (continuous_neg.max continuous_const))
      have hc_rhs : Continuous (fun p : Fin m → ℝ =>
          maxSubSum (ownedVerts (B idx₁) (B idx₂) i) (fun v_x => negPrice p v_x.1) (2 * l)) :=
        hcont_owned _ (continuous_neg.max continuous_const)
      refine tendsto_nhds_unique ((hc_lhs.tendsto p_star).comp hp_tend_all) ?_
      have ht2 := (hc_rhs.tendsto p_star).comp hp_tend_all
      exact ht2.congr (fun k => ((hk_eq k).2).symm)
  -- 4. Limiting divergence minimality at `w_star`
  have hB_div_min : ∀ idx k' : Fin n,
      divD v ρ γ (B idx) w_star idx ≤ divD v ρ γ (B idx) w_star k' := by
    intro idx k'
    have hineq_k : ∀ k, divD v ρ γ (B idx) (wt (ψ k)) idx ≤
        divD v ρ γ (B idx) (wt (ψ k)) k' := by
      intro k
      have hd := (hBt_spec (ψ k) idx).2 k'
      rwa [hB_ψ k] at hd
    exact le_of_tendsto_of_tendsto
      (((continuous_divD v ρ γ (B idx) idx).tendsto w_star).comp hwt_tend)
      (((continuous_divD v ρ γ (B idx) k').tendsto w_star).comp hwt_tend)
      (Eventually.of_forall hineq_k)
  -- 5. Define `β i := max_{idx} priceL p_star (B idx) i` (Lemma 9) and apply Lemmas 10 & 11!
  have huniv_ne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn1⟩, Finset.mem_univ _⟩
  let β : Fin n → ℝ := fun i => Finset.univ.sup' huniv_ne (fun idx => priceL p_star (B idx) i)
  have hL_le_β : ∀ (idx i : Fin n), priceL p_star (B idx) i ≤ β i :=
    fun idx i => Finset.le_sup' (fun idx' => priceL p_star (B idx') i) (Finset.mem_univ idx)
  have hβ_le_U : ∀ (idx i : Fin n), β i ≤ priceU ξ_star p_star (B idx) i := by
    intro idx i
    refine Finset.sup'_le _ _ fun idx' _ => ?_
    exact lemma_9_priceL_le_priceU hr1 ξ_star p_star (B idx') (B idx) i
      (hB_bal idx') (hB_bal idx)
      ((hB_slack_zero idx').2.1 i) ((hB_slack_zero idx).2.1 i)
      (fun l hl => (hB_interlace idx' idx i l hl).1)
      (fun l hl => (hB_interlace idx idx' i l hl).2)
  have hβ_bound : ∀ (idx i j : Fin n),
      alphaW ρ w_star i * resEnvy v (B idx) i j ≤ β j - β i := by
    intro idx i j
    have h10 := lemma_10_resEnvy_le_price_diff hr1 v α_star ξ_star p_star (B idx) (hB_bal idx)
      hα_nn hfeas_star (hB_slack_zero idx).1 (hB_slack_zero idx).2.1 (hB_slack_zero idx).2.2 i j
    have hLj := hL_le_β idx j
    have hUi := hβ_le_U idx i
    dsimp [α_star] at h10
    linarith
  obtain ⟨a, ha_fair⟩ := lemma_11_consolidate hn1 v (le_of_lt hγ) hρ_pos hρ1 hw_star_simp B
    hB_div_min β hβ_bound
  have ha_fpo : IsFPOIn v (Pbal n m) (allocMatrix (B a)) :=
    maximizesWeightedWelfare_imp_isFPOIn v α_star hα_pos (Pbal n m) (allocMatrix (B a))
      (hB_welf_opt a)
  exact ⟨B a, hB_bal a, ha_fpo, ha_fair⟩

/-- Extracting `IsEF11` and `n ∣ m → IsSwapEF` from `∀ i j, resEnvy v A i j ≤ 0` (§3.7). -/
lemma resEnvy_nonpos_imp_fair {n m : ℕ} (hr1 : 1 ≤ m / n) (v : Fin n → Fin m → ℝ)
    {A : Allocation n m} (hbal : IsBalanced A)
    (hres : ∀ i j : Fin n, resEnvy v A i j ≤ 0) :
    IsEF11 v A ∧ (n ∣ m → IsSwapEF v A) := by
  constructor
  · -- `IsEF11 v A`
    intro i j
    have hne_i := bundle_nonempty_of_isBalanced hr1 hbal i
    have hne_j := bundle_nonempty_of_isBalanced hr1 hbal j
    have hle := hres i j
    unfold resEnvy at hle
    rcases min_le_iff.mp hle with henvy_np | hrem_np
    · refine ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, by simp, by simp, ?_⟩
      unfold envy at henvy_np
      simp; linarith
    · -- Choose `C ⊆ bundle A i` realizing `hatMin v A i i`, and `G ⊆ bundle A j` realizing `hatMax v A i j`
      have hex_C : ∃ C ⊆ bundle A i, C.card ≤ 1 ∧
          bval v i (bundle A i \ C) = bval v i (bundle A i) - hatMin v A i i := by
        obtain ⟨h₀, hh₀_mem, hh₀_eq⟩ := Finset.exists_mem_eq_inf' hne_i (fun g => v i g)
        have hmin_eq : minBundleVal v i (bundle A i) = v i h₀ := by
          unfold minBundleVal; rw [dif_pos hne_i]; exact hh₀_eq
        have hsdiff_h₀ : bval v i (bundle A i \ {h₀}) = bval v i (bundle A i) - v i h₀ := by
          unfold bval
          have heq_er : bundle A i \ {h₀} = (bundle A i).erase h₀ :=
            Finset.sdiff_singleton_eq_erase h₀ (bundle A i)
          rw [heq_er]
          have := Finset.add_sum_erase (bundle A i) (fun g => v i g) hh₀_mem
          linarith
        unfold hatMin
        split_ifs with hci
        · exact ⟨{h₀}, Finset.singleton_subset_iff.mpr hh₀_mem, by simp,
            by rw [hmin_eq, hsdiff_h₀]⟩
        · rw [hmin_eq]
          by_cases hv_neg : v i h₀ < 0
          · rw [min_eq_right (le_of_lt hv_neg)]
            exact ⟨{h₀}, Finset.singleton_subset_iff.mpr hh₀_mem, by simp, hsdiff_h₀⟩
          · rw [min_eq_left (by linarith)]
            exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
      have hex_G : ∃ G ⊆ bundle A j, G.card ≤ 1 ∧
          bval v i (bundle A j \ G) = bval v i (bundle A j) - hatMax v A i j := by
        obtain ⟨g₀, hg₀_mem, hg₀_eq⟩ := Finset.exists_mem_eq_sup' hne_j (fun g => v i g)
        have hmax_eq : maxBundleVal v i (bundle A j) = v i g₀ := by
          unfold maxBundleVal; rw [dif_pos hne_j]; exact hg₀_eq
        have hsdiff_g₀ : bval v i (bundle A j \ {g₀}) = bval v i (bundle A j) - v i g₀ := by
          unfold bval
          have heq_er : bundle A j \ {g₀} = (bundle A j).erase g₀ :=
            Finset.sdiff_singleton_eq_erase g₀ (bundle A j)
          rw [heq_er]
          have := Finset.add_sum_erase (bundle A j) (fun g => v i g) hg₀_mem
          linarith
        unfold hatMax
        split_ifs with hcj
        · exact ⟨{g₀}, Finset.singleton_subset_iff.mpr hg₀_mem, by simp,
            by rw [hmax_eq, hsdiff_g₀]⟩
        · rw [hmax_eq]
          by_cases hv_pos : 0 < v i g₀
          · rw [max_eq_right (le_of_lt hv_pos)]
            exact ⟨{g₀}, Finset.singleton_subset_iff.mpr hg₀_mem, by simp, hsdiff_g₀⟩
          · rw [max_eq_left (by linarith)]
            exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
      obtain ⟨C, hC_sub, hC_card, hC_val⟩ := hex_C
      obtain ⟨G, hG_sub, hG_card, hG_val⟩ := hex_G
      refine ⟨C, hC_sub, G, hG_sub, hC_card, hG_card, ?_⟩
      unfold envy at hrem_np
      linarith
  · -- `n ∣ m → IsSwapEF v A`
    intro hdvd i j
    by_cases henvy_le : bval v i (bundle A j) ≤ bval v i (bundle A i)
    · exact Or.inl henvy_le
    · right
      have henvy_pos : 0 < envy v A i j := by unfold envy; linarith
      have hij : i ≠ j := by
        intro heq; subst heq; unfold envy at henvy_pos; linarith
      have hdisj : Disjoint (bundle A i) (bundle A j) := disjoint_bundle A hij
      have hq_eq : qSize n m = m / n := by unfold qSize; exact if_pos hdvd
      have hci_q : (bundle A i).card = qSize n m :=
        (card_bundle_eq_div_of_dvd hbal hdvd i).trans hq_eq.symm
      have hcj_q : (bundle A j).card = qSize n m :=
        (card_bundle_eq_div_of_dvd hbal hdvd j).trans hq_eq.symm
      have hne_i := bundle_nonempty_of_isBalanced hr1 hbal i
      have hne_j := bundle_nonempty_of_isBalanced hr1 hbal j
      obtain ⟨h₀, hh₀_mem, hh₀_eq⟩ := Finset.exists_mem_eq_inf' hne_i (fun g => v i g)
      obtain ⟨g₀, hg₀_mem, hg₀_eq⟩ := Finset.exists_mem_eq_sup' hne_j (fun g => v i g)
      have hhat_min : hatMin v A i i = v i h₀ := by
        unfold hatMin minBundleVal
        rw [if_pos hci_q, dif_pos hne_i]; exact hh₀_eq
      have hhat_max : hatMax v A i j = v i g₀ := by
        unfold hatMax maxBundleVal
        rw [if_pos hcj_q, dif_pos hne_j]; exact hg₀_eq
      have hle := hres i j
      unfold resEnvy at hle
      have hrem_np : envy v A i j + v i h₀ - v i g₀ ≤ 0 := by
        rcases min_le_iff.mp hle with h1 | h2
        · linarith
        · rwa [hhat_min, hhat_max] at h2
      have hh₀_not_j : h₀ ∉ (bundle A j).erase g₀ := fun hm =>
        Finset.disjoint_left.mp hdisj hh₀_mem (Finset.mem_of_mem_erase hm)
      have hg₀_not_i : g₀ ∉ (bundle A i).erase h₀ := fun hm =>
        Finset.disjoint_right.mp hdisj hg₀_mem (Finset.mem_of_mem_erase hm)
      have hval_j_sw : bval v i (insert h₀ ((bundle A j).erase g₀)) =
          v i h₀ + (bval v i (bundle A j) - v i g₀) := by
        unfold bval
        rw [Finset.sum_insert hh₀_not_j]
        have := Finset.add_sum_erase (bundle A j) (fun g => v i g) hg₀_mem
        linarith
      have hval_i_sw : bval v i (insert g₀ ((bundle A i).erase h₀)) =
          v i g₀ + (bval v i (bundle A i) - v i h₀) := by
        unfold bval
        rw [Finset.sum_insert hg₀_not_i]
        have := Finset.add_sum_erase (bundle A i) (fun g => v i g) hh₀_mem
        linarith
      refine ⟨h₀, hh₀_mem, g₀, hg₀_mem, ?_⟩
      rw [hval_j_sw, hval_i_sw]
      unfold envy at henvy_pos hrem_np
      linarith

/-- Full proof of Theorem 1 (Cookson, Shah, Verma, STOC 2027). -/
theorem theorem_1_proof (n m : ℕ) (hn : 1 ≤ n) (v : Fin n → Fin m → ℝ) :
    ∃ A : Allocation n m,
      IsBalanced A ∧ IsEF11 v A ∧ IsFPOIn v (Pbal n m) (allocMatrix A) ∧
      (n ∣ m → IsSwapEF v A) := by
  by_cases hn1 : n = 1
  · exact theorem_1_one_agent n m hn1 v
  · by_cases hr0 : m / n = 0
    · exact theorem_1_small_items n m hn hr0 v
    · have hn2 : 2 ≤ n := by omega
      have hr1 : 1 ≤ m / n := Nat.pos_of_ne_zero hr0
      -- Take `γ_t = 1 / (t + 1) → 0` and extract a constant balanced fPO allocation `A`
      have hex_seq : ∀ t : ℕ, ∃ At : Allocation n m,
          IsBalanced At ∧ IsFPOIn v (Pbal n m) (allocMatrix At) ∧
          ∀ i j : Fin n, resEnvy v At i j ≤ 1 / ((t : ℝ) + 1) :=
        fun t => exists_approx_fair_fpo hn2 hr1 v (by positivity)
      choose At hAt_bal hAt_fpo hAt_res using hex_seq
      obtain ⟨A, φ, hφ_mono, hA_const⟩ := exists_const_subseq_of_finite At
      have hbalA : IsBalanced A := by rw [← hA_const 0]; exact hAt_bal (φ 0)
      have hfpoA : IsFPOIn v (Pbal n m) (allocMatrix A) := by
        rw [← hA_const 0]; exact hAt_fpo (φ 0)
      have hres_nonpos : ∀ i j : Fin n, resEnvy v A i j ≤ 0 := by
        intro i j
        have hineq : ∀ k, resEnvy v A i j ≤ 1 / ((φ k : ℝ) + 1) := by
          intro k
          rw [← hA_const k]
          exact hAt_res (φ k) i j
        exact le_of_tendsto_of_tendsto tendsto_const_nhds
          (tendsto_inv_nat_succ_comp hφ_mono)
          (Eventually.of_forall hineq)
      obtain ⟨hef11, hswap⟩ := resEnvy_nonpos_imp_fair hr1 v hbalA hres_nonpos
      exact ⟨A, hbalA, hef11, hfpoA, hswap⟩

end ConsolidationAndMainProof

end BalancedFairAlloc_Theorem1_Proof

open BalancedFairAlloc.Existence

theorem solution (n m : ℕ) (hn : 1 ≤ n) (v : Fin n → Fin m → ℝ) :
    ∃ A : Allocation n m,
      IsBalanced A ∧ IsEF11 v A ∧ IsFPOIn v (Pbal n m) (allocMatrix A) ∧
      (n ∣ m → IsSwapEF v A) :=
  BalancedFairAlloc_Theorem1_Proof.theorem_1_proof n m hn v
