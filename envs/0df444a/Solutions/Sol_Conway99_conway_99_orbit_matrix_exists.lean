-- Prove2me | solution 1 for Conway99.conway_99_orbit_matrix_exists
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T19:37:09.260478+00:00
-- url     : https://prove2.me/submissions/ab2e63b2-39bc-4ce2-be06-08cda7d3c590

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Order.Group.End
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

open SimpleGraph Finset

namespace Conway99Orbit

variable {V : Type*} {g : SimpleGraph V}

lemma pow_succ_apply (σ : g ≃g g) (n : ℕ) (y : V) : (σ ^ (n + 1)) y = σ ((σ ^ n) y) := by
  rw [pow_succ']
  rfl

lemma pow_add_apply (σ : g ≃g g) (m n : ℕ) (y : V) :
    (σ ^ (m + n)) y = (σ ^ m) ((σ ^ n) y) := by
  induction m with
  | zero => simp
  | succ k ih =>
      have hk : k + 1 + n = (k + n) + 1 := by omega
      rw [hk, pow_succ_apply, ih, pow_succ_apply]

lemma pow_apply_eq_iterate (σ : g ≃g g) (n : ℕ) (y : V) :
    (σ ^ n) y = (fun v => σ v)^[n] y := by
  induction n with
  | zero => rfl
  | succ k ih => rw [pow_succ_apply, ih, Function.iterate_succ_apply']

lemma fixed_of_pow_fixed {p : ℕ} (hp : p.Prime) (σ : g ≃g g) (hσp : σ ^ p = 1) {d : ℕ}
    (hd : ¬ p ∣ d) {y : V} (hy : (σ ^ d) y = y) : σ y = y := by
  set f : V → V := fun v => σ v with hf
  have hdp : Function.IsPeriodicPt f d y := by
    unfold Function.IsPeriodicPt Function.IsFixedPt
    rw [← pow_apply_eq_iterate]
    exact hy
  have hpp : Function.IsPeriodicPt f p y := by
    unfold Function.IsPeriodicPt Function.IsFixedPt
    rw [← pow_apply_eq_iterate, hσp]
    rfl
  have h1 : Function.minimalPeriod f y ∣ Nat.gcd p d :=
    Nat.dvd_gcd hpp.minimalPeriod_dvd hdp.minimalPeriod_dvd
  have h2 : Nat.gcd p d = 1 := (Nat.Prime.coprime_iff_not_dvd hp).2 hd
  rw [h2, Nat.dvd_one] at h1
  exact Function.minimalPeriod_eq_one_iff_isFixedPt.1 h1

lemma pow_mod_apply (σ : g ≃g g) (hσ : σ ^ 11 = 1) (n : ℕ) (y : V) :
    (σ ^ n) y = (σ ^ (n % 11)) y := by
  conv_lhs => rw [← Nat.div_add_mod n 11]
  rw [pow_add_apply, pow_mul, hσ, one_pow]
  rfl

lemma pow_adj (σ : g ≃g g) (n : ℕ) {a b : V} (hab : g.Adj a b) :
    g.Adj ((σ ^ n) a) ((σ ^ n) b) := by
  induction n with
  | zero => simpa using hab
  | succ k ih =>
      rw [pow_succ_apply, pow_succ_apply]
      exact (σ.map_adj_iff).2 ih

/-- The orbit equivalence of a graph automorphism of order dividing `11`. -/
def orbSetoid (σ : g ≃g g) (hσ : σ ^ 11 = 1) : Setoid V where
  r x y := ∃ n : ℕ, (σ ^ n) x = y
  iseqv := by
    refine ⟨fun x => ⟨0, rfl⟩, ?_, ?_⟩
    · rintro x y ⟨n, rfl⟩
      refine ⟨10 * n, ?_⟩
      rw [← pow_add_apply]
      have : 10 * n + n = 11 * n := by ring
      rw [this, pow_mul, hσ, one_pow]
      rfl
    · rintro x y z ⟨n, rfl⟩ ⟨m, rfl⟩
      exact ⟨m + n, by rw [pow_add_apply]⟩

end Conway99Orbit

namespace Conway99Orbit

section Orbits

variable {V : Type*} [Fintype V] [DecidableEq V] {g : SimpleGraph V} [DecidableRel g.Adj]

/-- The orbit of `x` under the automorphism `σ` of order dividing `11`. -/
def orbF (σ : g ≃g g) (x : V) : Finset V :=
  univ.filter (fun y => ∃ n : Fin 11, (σ ^ (n : ℕ)) x = y)

variable {σ : g ≃g g}

lemma mem_orbF (hσ : σ ^ 11 = 1) {x y : V} : y ∈ orbF σ x ↔ ∃ n : ℕ, (σ ^ n) x = y := by
  simp only [orbF, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨(n : ℕ), rfl⟩
  · rintro ⟨n, rfl⟩
    refine ⟨⟨n % 11, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    exact (pow_mod_apply σ hσ n x).symm

lemma self_mem_orbF (hσ : σ ^ 11 = 1) (x : V) : x ∈ orbF σ x :=
  (mem_orbF hσ).2 ⟨0, rfl⟩

lemma orbF_eq_of_mem (hσ : σ ^ 11 = 1) {x y : V} (hy : y ∈ orbF σ x) :
    orbF σ y = orbF σ x := by
  obtain ⟨n, rfl⟩ := (mem_orbF hσ).1 hy
  ext z
  simp only [mem_orbF hσ]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m + n, by rw [pow_add_apply]⟩
  · rintro ⟨m, rfl⟩
    refine ⟨10 * n + m, ?_⟩
    rw [← pow_add_apply]
    have h11 : 10 * n + m + n = 11 * n + m := by ring
    rw [h11, pow_add_apply, pow_mul, hσ, one_pow]
    rfl

lemma orbF_card (hσ : σ ^ 11 = 1) (hfix : ∀ v : V, σ v ≠ v) (x : V) :
    (orbF σ x).card = 11 := by
  have himg : orbF σ x = (univ : Finset (Fin 11)).image (fun n : Fin 11 => (σ ^ (n : ℕ)) x) := by
    ext y
    simp [orbF]
  rw [himg, Finset.card_image_of_injOn, Finset.card_univ, Fintype.card_fin]
  intro a _ b _ hab0
  have hab : (σ ^ (a : ℕ)) x = (σ ^ (b : ℕ)) x := hab0
  by_contra hne
  have hne' : (a : ℕ) ≠ (b : ℕ) := fun hcon => hne (Fin.ext hcon)
  have hp : Nat.Prime 11 := by norm_num
  rcases Nat.lt_or_ge (a : ℕ) (b : ℕ) with hlt | hge
  · have happ : (σ ^ (11 - (b : ℕ) + (a : ℕ))) x = x := by
      have h1 : (σ ^ (11 - (b : ℕ))) ((σ ^ (a : ℕ)) x) = (σ ^ (11 - (b : ℕ))) ((σ ^ (b : ℕ)) x) := by
        rw [hab]
      rw [← pow_add_apply, ← pow_add_apply] at h1
      have h2 : 11 - (b : ℕ) + (b : ℕ) = 11 := by omega
      rw [h2, hσ] at h1
      exact h1
    have hd : ¬ (11 : ℕ) ∣ (11 - (b : ℕ) + (a : ℕ)) := by
      intro hdvd
      have hb := b.isLt
      have h3 : 0 < 11 - (b : ℕ) + (a : ℕ) := by omega
      have h4 : 11 - (b : ℕ) + (a : ℕ) < 11 := by omega
      exact absurd (Nat.le_of_dvd h3 hdvd) (by omega)
    exact hfix x (fixed_of_pow_fixed hp σ hσ hd happ)
  · have hlt : (b : ℕ) < (a : ℕ) := by omega
    have happ : (σ ^ (11 - (a : ℕ) + (b : ℕ))) x = x := by
      have h1 : (σ ^ (11 - (a : ℕ))) ((σ ^ (b : ℕ)) x) = (σ ^ (11 - (a : ℕ))) ((σ ^ (a : ℕ)) x) := by
        rw [hab]
      rw [← pow_add_apply, ← pow_add_apply] at h1
      have h2 : 11 - (a : ℕ) + (a : ℕ) = 11 := by
        have := a.isLt; omega
      rw [h2, hσ] at h1
      exact h1
    have hd : ¬ (11 : ℕ) ∣ (11 - (a : ℕ) + (b : ℕ)) := by
      intro hdvd
      have ha := a.isLt
      have h3 : 0 < 11 - (a : ℕ) + (b : ℕ) := by omega
      have h4 : 11 - (a : ℕ) + (b : ℕ) < 11 := by omega
      exact absurd (Nat.le_of_dvd h3 hdvd) (by omega)
    exact hfix x (fixed_of_pow_fixed hp σ hσ hd happ)

/-- The set of orbits. -/
def Orbs (σ : g ≃g g) : Finset (Finset V) := univ.image (orbF σ)

lemma mem_orbs_iff (hσ : σ ^ 11 = 1) {B : Finset V} :
    B ∈ Orbs σ ↔ ∃ x : V, B = orbF σ x := by
  simp only [Orbs, mem_image, mem_univ, true_and, eq_comm]

lemma fiber_eq (hσ : σ ^ 11 = 1) (x : V) :
    univ.filter (fun v => orbF σ v = orbF σ x) = orbF σ x := by
  ext v
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro hv
    rw [← hv]
    exact self_mem_orbF hσ v
  · intro hv
    exact orbF_eq_of_mem hσ hv

lemma orbs_card (hσ : σ ^ 11 = 1) (hfix : ∀ v : V, σ v ≠ v) (hV : Fintype.card V = 99) :
    (Orbs σ).card = 9 := by
  have hsum : (univ : Finset V).card
      = ∑ B ∈ Orbs σ, (univ.filter (fun v => orbF σ v = B)).card :=
    Finset.card_eq_sum_card_image (orbF σ) univ
  have hcard : ∀ B ∈ Orbs σ, (univ.filter (fun v => orbF σ v = B)).card = 11 := by
    intro B hB
    obtain ⟨x, rfl⟩ := (mem_orbs_iff hσ).1 hB
    rw [fiber_eq hσ x, orbF_card hσ hfix x]
  rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul] at hsum
  rw [Finset.card_univ, hV] at hsum
  omega

/-- An indexing of the `9` orbits by `Fin 9`. -/
lemma exists_index (hσ : σ ^ 11 = 1) (hfix : ∀ v : V, σ v ≠ v) (hV : Fintype.card V = 99) :
    ∃ idx : V → Fin 9, (∀ v, idx (σ v) = idx v) ∧
      (∀ v w, idx v = idx w → ∃ n : ℕ, (σ ^ n) v = w) ∧
      (∀ j, (univ.filter (fun v => idx v = j)).card = 11) := by
  have hc := orbs_card hσ hfix hV
  let e : {B // B ∈ Orbs σ} ≃ Fin 9 := (Orbs σ).equivFin.trans (finCongr hc)
  have hmem : ∀ v : V, orbF σ v ∈ Orbs σ := fun v => Finset.mem_image_of_mem _ (mem_univ v)
  refine ⟨fun v => e ⟨orbF σ v, hmem v⟩, ?_, ?_, ?_⟩
  · intro v
    have h1 : orbF σ (σ v) = orbF σ v := by
      refine orbF_eq_of_mem hσ ?_
      exact (mem_orbF hσ).2 ⟨1, by rw [pow_one]⟩
    simp only [h1]
  · intro v w hvw
    have h2 : orbF σ v = orbF σ w := congrArg Subtype.val (e.injective hvw)
    have h3 : w ∈ orbF σ v := by
      rw [h2]
      exact self_mem_orbF hσ w
    exact (mem_orbF hσ).1 h3
  · intro j
    obtain ⟨⟨B, hB⟩, hBj⟩ : ∃ b : {B // B ∈ Orbs σ}, e b = j := ⟨e.symm j, e.apply_symm_apply j⟩
    have hfil : (univ.filter (fun v => e ⟨orbF σ v, hmem v⟩ = j))
        = univ.filter (fun v => orbF σ v = B) := by
      ext v
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro hv
        exact congrArg Subtype.val (e.injective (hv.trans hBj.symm))
      · intro hv
        rw [← hBj]
        congr 1
        exact Subtype.ext hv
    rw [hfil]
    obtain ⟨x, rfl⟩ := (mem_orbs_iff hσ).1 hB
    rw [fiber_eq hσ x, orbF_card hσ hfix x]

end Orbits

end Conway99Orbit

namespace Conway99Orbit

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V] {g : SimpleGraph V} [DecidableRel g.Adj]

/-- The number of neighbours of `x` lying in the block with index `j`. -/
def cnt (g : SimpleGraph V) [DecidableRel g.Adj] (idx : V → Fin 9) (x : V) (j : Fin 9) : ℕ :=
  ((g.neighborFinset x).filter (fun y => idx y = j)).card

lemma card_common (x z : V) :
    ((g.neighborFinset x).filter (fun y => g.Adj z y)).card
      = Fintype.card (g.commonNeighbors x z) := by
  rw [← Set.toFinset_card]
  congr 1
  ext y
  simp [SimpleGraph.mem_commonNeighbors, SimpleGraph.mem_neighborFinset, and_comm]

lemma cnt_eq_filter_block (idx : V → Fin 9) (x : V) (j : Fin 9) :
    cnt g idx x j = ((univ.filter (fun v => idx v = j)).filter (fun y => g.Adj x y)).card := by
  unfold cnt
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, SimpleGraph.mem_neighborFinset]
  tauto

lemma cnt_sigma (σ : g ≃g g) (idx : V → Fin 9) (h1 : ∀ v, idx (σ v) = idx v) (x : V) (j : Fin 9) :
    cnt g idx (σ x) j = cnt g idx x j := by
  unfold cnt
  have himg : (g.neighborFinset (σ x)).filter (fun y => idx y = j)
      = ((g.neighborFinset x).filter (fun y => idx y = j)).image (fun y => σ y) := by
    ext y
    simp only [mem_filter, mem_image, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hadj, hidx⟩
      refine ⟨σ.symm y, ⟨?_, ?_⟩, ?_⟩
      · have hiff := σ.map_adj_iff (v := x) (w := σ.symm y)
        rw [σ.apply_symm_apply] at hiff
        exact hiff.1 hadj
      · rw [← h1 (σ.symm y), σ.apply_symm_apply]
        exact hidx
      · exact σ.apply_symm_apply y
    · rintro ⟨z, ⟨hadj, hidx⟩, rfl⟩
      exact ⟨σ.map_adj_iff.2 hadj, by rw [h1 z]; exact hidx⟩
  rw [himg, Finset.card_image_of_injective _ (fun a b hab => σ.injective hab)]

lemma cnt_pow (σ : g ≃g g) (idx : V → Fin 9) (h1 : ∀ v, idx (σ v) = idx v) (n : ℕ) (x : V)
    (j : Fin 9) : cnt g idx ((σ ^ n) x) j = cnt g idx x j := by
  induction n with
  | zero => rfl
  | succ k ih => rw [pow_succ_apply, cnt_sigma σ idx h1, ih]

/-- From an indexing of the orbits, the orbit matrix exists. -/
lemma orbit_matrix_of_index (h : g.IsSRGWith 99 14 1 2) (σ : g ≃g g)
    (idx : V → Fin 9) (h1 : ∀ v, idx (σ v) = idx v)
    (h2 : ∀ v w, idx v = idx w → ∃ n : ℕ, (σ ^ n) v = w)
    (h3 : ∀ j, (univ.filter (fun v => idx v = j)).card = 11) :
    ∃ C : Matrix (Fin 9) (Fin 9) ℕ, (∀ i j, C i j = C j i) ∧ (∀ i, ∑ j, C i j = 14) ∧
      ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22 := by
  have hrep0 : ∀ j : Fin 9, ∃ x : V, idx x = j := by
    intro j
    have hcard := h3 j
    have hne : (univ.filter (fun v => idx v = j)).Nonempty := by
      rw [← Finset.card_pos, hcard]; norm_num
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, (mem_filter.1 hx).2⟩
  choose rep hrep using hrep0
  have hindep : ∀ (x : V) (i j : Fin 9), idx x = i → cnt g idx x j = cnt g idx (rep i) j := by
    intro x i j hx
    obtain ⟨n, hn⟩ := h2 (rep i) x (by rw [hrep i, hx])
    rw [← hn, cnt_pow σ idx h1]
  have hrow : ∀ x : V, ∑ j, cnt g idx x j = 14 := by
    intro x
    have hdeg : (g.neighborFinset x).card = 14 := h.regular x
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := idx) (s := g.neighborFinset x) (t := (univ : Finset (Fin 9)))
      (fun y _ => mem_univ (idx y))
    rw [hdeg] at hfib
    exact hfib.symm
  refine ⟨fun i j => cnt g idx (rep i) j, ?_, fun i => hrow (rep i), ?_⟩
  · -- symmetry, by counting the edges between two blocks in two ways
    intro i j
    show cnt g idx (rep i) j = cnt g idx (rep j) i
    have key : ∑ x ∈ univ.filter (fun v => idx v = i), cnt g idx x j
             = ∑ y ∈ univ.filter (fun v => idx v = j), cnt g idx y i := by
      simp only [cnt_eq_filter_block, Finset.card_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
      simp [SimpleGraph.adj_comm]
    have hL : ∑ x ∈ univ.filter (fun v => idx v = i), cnt g idx x j
        = 11 * cnt g idx (rep i) j := by
      rw [Finset.sum_congr rfl (fun x hx => hindep x i j (mem_filter.1 hx).2),
        Finset.sum_const, h3 i, smul_eq_mul]
    have hR : ∑ y ∈ univ.filter (fun v => idx v = j), cnt g idx y i
        = 11 * cnt g idx (rep j) i := by
      rw [Finset.sum_congr rfl (fun y hy => hindep y j i (mem_filter.1 hy).2),
        Finset.sum_const, h3 j, smul_eq_mul]
    rw [hL, hR] at key
    omega
  · -- the quadratic identity
    intro i j
    show (∑ k, cnt g idx (rep i) k * cnt g idx (rep k) j) + cnt g idx (rep i) j
        = (if i = j then 12 else 0) + 22
    have step1 : ∑ k, cnt g idx (rep i) k * cnt g idx (rep k) j
        = ∑ y ∈ g.neighborFinset (rep i), cnt g idx y j := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := idx) (t := (univ : Finset (Fin 9)))
          (fun y (_ : y ∈ g.neighborFinset (rep i)) => mem_univ (idx y))
          (fun y => cnt g idx y j)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_congr rfl (fun y hy => hindep y k j (mem_filter.1 hy).2),
        Finset.sum_const, smul_eq_mul]
      rfl
    have step2 : ∑ y ∈ g.neighborFinset (rep i), cnt g idx y j
        = ∑ z ∈ univ.filter (fun v => idx v = j),
            ((g.neighborFinset (rep i)).filter (fun y => g.Adj z y)).card := by
      simp only [cnt_eq_filter_block, Finset.card_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
      simp [SimpleGraph.adj_comm]
    have step3 : ∀ z ∈ univ.filter (fun v => idx v = j),
        ((g.neighborFinset (rep i)).filter (fun y => g.Adj z y)).card
          = 14 * (if z = rep i then 1 else 0) + (if g.Adj (rep i) z then 1 else 0)
            + 2 * (if z ≠ rep i ∧ ¬ g.Adj (rep i) z then 1 else 0) := by
      intro z _
      by_cases hzx : z = rep i
      · have hfil : (g.neighborFinset (rep i)).filter (fun y => g.Adj z y)
            = g.neighborFinset (rep i) := by
          apply Finset.filter_true_of_mem
          intro y hy
          rw [hzx]
          exact (SimpleGraph.mem_neighborFinset _ _ _).1 hy
        rw [hfil]
        have hd14 : (g.neighborFinset (rep i)).card = 14 := h.regular (rep i)
        simp [hd14, hzx]
      · rw [card_common]
        by_cases hadj : g.Adj (rep i) z
        · have : Fintype.card (g.commonNeighbors (rep i) z) = 1 := h.of_adj _ _ hadj
          simp [this, hzx, hadj]
        · have : Fintype.card (g.commonNeighbors (rep i) z) = 2 :=
            h.of_not_adj (fun hc => hzx hc.symm) hadj
          simp [this, hzx, hadj]
    rw [step1, step2, Finset.sum_congr rfl step3]
    -- abbreviations for the three parts of the block
    set blkj := univ.filter (fun v => idx v = j) with hblkj
    set a := (blkj.filter (fun z => z = rep i)).card with ha
    set b := (blkj.filter (fun z => g.Adj (rep i) z)).card with hb
    set c := (blkj.filter (fun z => z ≠ rep i ∧ ¬ g.Adj (rep i) z)).card with hc
    have hsum : ∑ z ∈ blkj, (14 * (if z = rep i then 1 else 0)
        + (if g.Adj (rep i) z then 1 else 0)
        + 2 * (if z ≠ rep i ∧ ¬ g.Adj (rep i) z then 1 else 0)) = 14 * a + b + 2 * c := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ha, hb, hc, Finset.card_filter, Finset.card_filter, Finset.card_filter]
    have hpart : a + b + c = 11 := by
      have hone : ∀ z ∈ blkj, (if z = rep i then 1 else 0) + (if g.Adj (rep i) z then 1 else 0)
          + (if z ≠ rep i ∧ ¬ g.Adj (rep i) z then 1 else 0) = 1 := by
        intro z _
        by_cases hzx : z = rep i
        · subst hzx; simp [g.irrefl]
        · by_cases hadj : g.Adj (rep i) z <;> simp [hzx, hadj]
      have hcalc : a + b + c = ∑ z ∈ blkj, ((if z = rep i then 1 else 0)
          + (if g.Adj (rep i) z then 1 else 0)
          + (if z ≠ rep i ∧ ¬ g.Adj (rep i) z then 1 else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ha, hb, hc,
          Finset.card_filter, Finset.card_filter, Finset.card_filter]
      rw [hcalc, Finset.sum_congr rfl hone, Finset.sum_const, hblkj, h3 j]
      simp
    have hbval : b = cnt g idx (rep i) j := by
      rw [hb, cnt_eq_filter_block]
    have haval : a = if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst hij
        have hmem : rep i ∈ blkj := by
          rw [hblkj]
          simp [hrep i]
        have : blkj.filter (fun z => z = rep i) = {rep i} := by
          ext z
          simp only [mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨_, hz⟩; exact hz
          · rintro rfl; exact ⟨hmem, rfl⟩
        rw [ha, this, Finset.card_singleton, if_pos rfl]
      · have : blkj.filter (fun z => z = rep i) = ∅ := by
          ext z
          simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
          rintro hz rfl
          rw [hblkj, mem_filter] at hz
          exact hij (by rw [← hrep i, hz.2])
        rw [ha, this, Finset.card_empty, if_neg hij]
    rw [hsum, ← hbval]
    by_cases hij : i = j
    · simp only [if_pos hij] at haval ⊢
      omega
    · simp only [if_neg hij] at haval ⊢
      omega

end Counting

end Conway99Orbit

/-- **Orbit matrix of an order-11 automorphism.**
If a `(99, 14, 1, 2)` strongly regular graph has a fixed-point-free automorphism `σ` of order
`11`, then the `9` orbits of `σ` carry an orbit matrix `C`: `C i j` is the number of neighbours
in orbit `j` of a vertex in orbit `i`.  It is symmetric, has all row sums `14`, and satisfies
`C ^ 2 + C = 12 I + 22 J`. -/
theorem solution {V : Type*} [Fintype V] {g : SimpleGraph V}
    [DecidableRel g.Adj] (h : g.IsSRGWith 99 14 1 2) (σ : g ≃g g) (hσ : orderOf σ = 11)
    (hfix : ∀ v : V, σ v ≠ v) :
    ∃ C : Matrix (Fin 9) (Fin 9) ℕ, (∀ i j, C i j = C j i) ∧ (∀ i, ∑ j, C i j = 14) ∧
      ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22 := by
  classical
  have hσ11 : σ ^ 11 = 1 := by
    rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨idx, h1, h2, h3⟩ := Conway99Orbit.exists_index hσ11 hfix h.card
  exact Conway99Orbit.orbit_matrix_of_index h σ idx h1 h2 h3
