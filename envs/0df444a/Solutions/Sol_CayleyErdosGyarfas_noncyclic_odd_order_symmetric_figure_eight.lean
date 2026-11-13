-- Prove2me | solution 1 for CayleyErdosGyarfas.noncyclic_odd_order_symmetric_figure_eight
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T02:51:48.440374+00:00
-- url     : https://prove2.me/submissions/14306120-e828-4611-85fd-5ccb13e20ebe

import Theorems.Thm_CayleyErdosGyarfas_minimal_nonabelian_case_has_symmetric_figure_eight
import Definitions.Def_CayleyErdosGyarfas_HasSymmetricFigureEight
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.ChainOfFn
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer

-- ===== from CayleyErdosGyarfas/Basic.lean =====
/-! Elementary, fully proved checks on the statement conventions. -/


namespace CayleyErdosGyarfas

/-- Mathlib's Cayley adjacency agrees with the manuscript's right-generator
convention when `S` is inverse-closed and does not contain the identity. -/
theorem cayley_adj_iff {G : Type*} [Group G] (S : Set G)
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S) (hone : (1 : G) ∉ S) (u v : G) :
    (SimpleGraph.mulCayley S).Adj u v ↔ u⁻¹ * v ∈ S := by
  rw [SimpleGraph.mulCayley_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · simpa using hinv _ h
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    exact hone (by simpa using h)

/-- Left translation preserves the right-generator Cayley graph. -/
def cayleyLeftTranslation {G : Type*} [Group G] (S : Set G) (g : G) :
    SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley S where
  toEquiv := Equiv.mulLeft g
  map_rel_iff' := SimpleGraph.mulCayley_adj_mul_iff_right

/-- Every symmetric figure-eight in the precise statement sense contains a
simple cycle of the required length. -/
theorem HasSymmetricFigureEight.contains_two_power_cycle
    {G : Type*} [Group G] {S : Set G} (h : HasSymmetricFigureEight S) :
    ∃ (n : ℕ) (v : G) (c : (SimpleGraph.mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  rcases h with ⟨n, v, α, β, hn, hα, hβ, hlen, hlenβ, htranslate, hintersect⟩
  exact ⟨n, v, α, Nat.le_trans (by decide : 1 ≤ 2) hn, hα, hlen⟩

/-- A simple cycle of power-of-two length has at least four edges. -/
theorem two_power_cycle_exponent_ge_two
    {V : Type*} {Γ : SimpleGraph V} {v : V} {c : Γ.Walk v v} {n : ℕ}
    (hcycle : c.IsCycle) (hlen : c.length = 2 ^ n) : 2 ≤ n := by
  have hthree : 3 ≤ c.length :=
    (SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mp hcycle).2
  rw [hlen] at hthree
  by_contra h
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hn with rfl | rfl <;> norm_num at hthree

/-- The quotient generating set used in both lifting statements is
inverse-closed, with the identity coset deleted. -/
theorem quotient_generators_inverse_closed
    {G : Type*} [Group G] (S : Set G)
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S) (N : Subgroup G) [N.Normal] :
    ∀ q ∈ (QuotientGroup.mk (s := N)) '' S \ {1},
      q⁻¹ ∈ (QuotientGroup.mk (s := N)) '' S \ {1} := by
  rintro q ⟨⟨s, hs, rfl⟩, hne⟩
  refine ⟨⟨s⁻¹, hinv s hs, ?_⟩, ?_⟩
  · simp
  · simpa only [Set.mem_singleton_iff, inv_eq_one] using hne

/-- A cycle and a left translate meeting at a unique vertex give the
manuscript's based symmetric figure-eight. This criterion lets constructive
proofs work with a single cycle and its translated vertex set. -/
theorem hasSymmetricFigureEight_of_cycle_translate
    {G : Type*} [Group G] {S : Set G} {v : G}
    (c : (SimpleGraph.mulCayley S).Walk v v) (n : ℕ)
    (_hn : 1 ≤ n) (hc : c.IsCycle) (hlen : c.length = 2 ^ n)
    (g w : G)
    (hintersect : ∀ x : G,
      (x ∈ c.support ∧ ∃ y ∈ c.support, g * y = x) ↔ x = w) :
    HasSymmetricFigureEight S := by
  classical
  let φ := (cayleyLeftTranslation S g).toHom
  let d := c.map φ
  have hw : w ∈ c.support := ((hintersect w).mpr rfl).1
  have hd (x : G) : x ∈ d.support ↔ ∃ y ∈ c.support, g * y = x := by
    change x ∈ (c.map φ).support ↔ _
    rw [SimpleGraph.Walk.support_map]
    change x ∈ c.support.map (g * ·) ↔ _
    exact List.mem_map
  have hwd : w ∈ d.support := (hd w).mpr ((hintersect w).mpr rfl).2
  refine ⟨n, w, c.rotate w hw, d.rotate w hwd, two_power_cycle_exponent_ge_two hc hlen,
    (SimpleGraph.Walk.isCycle_rotate hw).mpr hc, ?_,
    by simpa using hlen, ?_, ?_, ?_⟩
  · apply (SimpleGraph.Walk.isCycle_rotate hwd).mpr
    exact (SimpleGraph.Walk.isCycle_map_iff_of_injective
      (f := φ) (fun _ _ h ↦ mul_left_cancel h)).mpr hc
  · simpa [d] using hlen
  · refine ⟨g, ?_⟩
    have hr := (c.support_rotate w hw).map (g * ·)
    have hdrot := (d.support_rotate w hwd).symm
    have heq : d.support.tail = c.support.tail.map (g * ·) := by
      change (c.map φ).support.tail = _
      rw [SimpleGraph.Walk.support_map, List.map_tail]
      rfl
    rw [heq] at hdrot
    exact hr.trans hdrot
  · intro x
    simpa only [SimpleGraph.Walk.mem_support_rotate_iff, hd] using hintersect x

end CayleyErdosGyarfas

-- ===== from CayleyErdosGyarfas/Lifting.lean =====
namespace CayleyErdosGyarfas

open SimpleGraph

/-- A closed sequence of at least three pairwise distinct vertices gives a simple cycle. -/
theorem exists_cycle_of_sequence_with_support {V : Type*} {Γ : SimpleGraph V} {n : ℕ}
    (hn : 3 ≤ n) (f : ℕ → V) (hclose : f n = f 0)
    (hadj : ∀ i < n, Γ.Adj (f i) (f (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j) :
    ∃ (c : Γ.Walk (f 0) (f 0)), c.IsCycle ∧ c.length = n ∧
      c.support = List.ofFn (fun i : Fin (n + 1) ↦ f i) := by
  let l := List.ofFn (fun i : Fin (n + 1) ↦ f i)
  have hl : l ≠ [] := by simp [l]
  have hc : l.IsChain Γ.Adj := List.isChain_ofFn.mpr (by
    intro i hi
    exact hadj i (by omega))
  have hhead : l.head hl = f 0 := by simp [l]
  have hlast : l.getLast hl = f 0 := by
    change (List.ofFn (fun i : Fin (n + 1) ↦ f i)).getLast _ = f 0
    rw [List.getLast_ofFn]
    exact hclose
  let c := (Walk.ofSupport l hl hc).copy hhead hlast
  have clen : c.length = n := by simp [c, l]
  refine ⟨c, ?_, clen, by simp [c, l]⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨?_, by omega⟩
  rw [Walk.isPath_def, Walk.support_tail_of_not_nil]
  · simp only [c, Walk.support_copy, Walk.support_ofSupport]
    rw [show l.tail = List.ofFn (fun i : Fin n ↦ f (i + 1)) by simp [l, List.ofFn_succ]]
    apply List.nodup_ofFn.mpr
    intro i j hij
    apply Fin.ext
    by_cases hi : i.val + 1 = n
    · by_cases hj : j.val + 1 = n
      · omega
      · have hzero : 0 = j.val + 1 := hinj 0 (by omega) (j.val + 1) (by omega)
          (by simpa [hi, hclose] using hij)
        omega
    · by_cases hj : j.val + 1 = n
      · have hzero : i.val + 1 = 0 := hinj (i.val + 1) (by omega) 0 (by omega)
          (by simpa [hj, hclose] using hij)
        omega
      · have := hinj (i.val + 1) (by omega) (j.val + 1) (by omega) hij
        omega
  · intro hz
    have := Walk.length_eq_zero_iff.mpr hz
    omega

/-- A closed sequence of at least three pairwise distinct vertices gives a simple cycle. -/
theorem exists_cycle_of_sequence {V : Type*} {Γ : SimpleGraph V} {n : ℕ}
    (hn : 3 ≤ n) (f : ℕ → V) (hclose : f n = f 0)
    (hadj : ∀ i < n, Γ.Adj (f i) (f (i + 1)))
    (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j) :
    ∃ (v : V) (c : Γ.Walk v v), c.IsCycle ∧ c.length = n := by
  obtain ⟨c, hc, hlen, _⟩ := exists_cycle_of_sequence_with_support hn f hclose hadj hinj
  exact ⟨f 0, c, hc, hlen⟩

/-- An edge in a homomorphic image Cayley graph lifts from any prescribed initial vertex. -/
theorem cayley_adj_image_lift {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) (S : Set G) {a : G} {q : Q}
    (h : (mulCayley (φ '' S)).Adj (φ a) q) :
    ∃ b : G, (mulCayley S).Adj a b ∧ φ b = q := by
  obtain ⟨hne, t, ⟨s, hs, rfl⟩, ht⟩ := (mulCayley_adj' _ _ _).mp h
  rcases ht with ht | ht
  · have hb : φ (a * s) = q := by simpa using ht
    refine ⟨a * s, ?_, hb⟩
    apply (mulCayley_adj' _ _ _).mpr
    exact ⟨fun heq ↦ hne ((congrArg φ heq).trans hb), s, hs, Or.inl rfl⟩
  · have hb : φ (a * s⁻¹) = q := by rw [map_mul, map_inv, ht]; simp
    refine ⟨a * s⁻¹, ?_, hb⟩
    apply (mulCayley_adj' _ _ _).mpr
    exact ⟨fun heq ↦ hne ((congrArg φ heq).trans hb), s, hs, Or.inr (by group)⟩

/-- Walks in a homomorphic image Cayley graph admit length-preserving lifts. -/
theorem cayley_walk_image_lift {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) (S : Set G) {q r : Q}
    (p : (mulCayley (φ '' S)).Walk q r) (a : G) (ha : φ a = q) :
    ∃ (b : G) (w : (mulCayley S).Walk a b),
      w.length = p.length ∧ ∀ i, φ (w.getVert i) = p.getVert i := by
  induction p generalizing a with
  | nil => exact ⟨a, .nil, rfl, fun i ↦ by simpa using ha⟩
  | @cons q r t h p ih =>
    obtain ⟨b, hab, hb⟩ := cayley_adj_image_lift φ S (ha ▸ h)
    obtain ⟨c, w, hlen, hmap⟩ := ih b hb
    refine ⟨c, w.cons hab, by simpa using hlen, ?_⟩
    intro i
    cases i with
    | zero => simpa using ha
    | succ i => simpa using hmap i

/-- A simple cycle in an image Cayley graph lifts to a simple cycle whose length is
multiplied by the order of an element of the kernel. -/
theorem cayley_cycle_image_lift {G Q : Type*} [Group G] [Group Q] [Finite G]
    (φ : G →* Q) (hφ : Function.Surjective φ) (S : Set G) {q : Q}
    (p : (mulCayley (φ '' S)).Walk q q) (hp : p.IsCycle) :
    ∃ (t : G), φ t = 1 ∧ ∃ (v : G) (c : (mulCayley S).Walk v v),
      c.IsCycle ∧ c.length = p.length * orderOf t := by
  obtain ⟨a, ha⟩ := hφ q
  obtain ⟨b, w, hwlen, hwmap⟩ := cayley_walk_image_lift φ S p a ha
  let n := p.length
  let t := b * a⁻¹
  have hn : 3 ≤ n := hp.three_le_length
  have hnpos : 0 < n := by omega
  have hφb : φ b = q := calc
    φ b = φ (w.getVert w.length) := by rw [Walk.getVert_length]
    _ = p.getVert w.length := hwmap _
    _ = q := by rw [hwlen, Walk.getVert_length]
  have ht : φ t = 1 := by simp [t, hφb, ha]
  have horder : 0 < orderOf t := orderOf_pos t
  let f : ℕ → G := fun i ↦ t ^ (i / n) * w.getVert (i % n)
  have hproj (i : ℕ) : φ (f i) = p.getVert (i % n) := by
    simp [f, map_mul, map_pow, ht, hwmap]
  have hclose : f (n * orderOf t) = f 0 := by
    simp [f, Nat.mul_div_cancel_left _ hnpos, pow_orderOf_eq_one]
  have hinj : ∀ i < n * orderOf t, ∀ j < n * orderOf t, f i = f j → i = j := by
    intro i hi j hj hij
    have hmod : i % n = j % n := hp.getVert_injOn'
      (by have := Nat.mod_lt i hnpos; simp only [Set.mem_ofPred_eq]; omega)
      (by have := Nat.mod_lt j hnpos; simp only [Set.mem_ofPred_eq]; omega)
      (by simpa only [hproj] using congrArg φ hij)
    have hpow : t ^ (i / n) = t ^ (j / n) := by
      apply mul_right_cancel (b := w.getVert (j % n))
      simpa only [f, hmod] using hij
    have hdiv : i / n = j / n := pow_injOn_Iio_orderOf
      (by simpa only [Set.mem_Iio] using (Nat.div_lt_iff_lt_mul hnpos).mpr (by simpa [Nat.mul_comm] using hi))
      (by simpa only [Set.mem_Iio] using (Nat.div_lt_iff_lt_mul hnpos).mpr (by simpa [Nat.mul_comm] using hj)) hpow
    have hdi := Nat.mod_add_div i n
    have hdj := Nat.mod_add_div j n
    rw [hmod, hdiv] at hdi
    exact hdi.symm.trans hdj
  have hadj : ∀ i < n * orderOf t, (mulCayley S).Adj (f i) (f (i + 1)) := by
    intro i _
    have hir : i % n < n := Nat.mod_lt i hnpos
    have hid : i + 1 = n * (i / n) + (i % n + 1) := by
      have := Nat.mod_add_div i n
      omega
    by_cases hr : i % n + 1 < n
    · have hdiv : (i + 1) / n = i / n := by
        rw [hid, Nat.mul_add_div hnpos]
        simp [Nat.div_eq_of_lt hr]
      have hmod : (i + 1) % n = i % n + 1 := by
        rw [hid, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hr]
      simp only [f, hdiv, hmod, mulCayley_adj_mul_iff_right]
      exact w.adj_getVert_succ (by omega)
    · have hr : i % n + 1 = n := by omega
      have hdiv : (i + 1) / n = i / n + 1 := by
        rw [hid, hr, Nat.mul_add_div hnpos]
        simp [Nat.div_self hnpos]
      have hmod : (i + 1) % n = 0 := by
        rw [hid, hr, Nat.mul_add_mod_self_left, Nat.mod_self]
      have hend : t * a = b := by simp [t, mul_assoc]
      have hstep := w.adj_getVert_succ (i := i % n) (by omega)
      have hlast : w.getVert (i % n + 1) = b := by
        rw [hr]
        change w.getVert p.length = b
        rw [← hwlen]
        simp
      have hfirst : w.getVert 0 = a := by simp
      simp only [f, hdiv, hmod, hfirst, pow_succ, mul_assoc, hend]
      exact (mulCayley_adj_mul_iff_right).mpr (by simpa only [hlast] using hstep)
  obtain ⟨v, c, hc, hclen⟩ := exists_cycle_of_sequence
    (n := n * orderOf t) (by nlinarith) f hclose hadj hinj
  exact ⟨t, ht, v, c, hc, hclen⟩

/-- Lemma 1.3, in a strengthened form: generation and inverse closure are not needed
for lifting an already existing quotient cycle through a normal 2-subgroup. -/
theorem two_power_cycle_lifts
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup 2 P)
    (hcycle : ∃ (n : ℕ) (v : G ⧸ P)
      (c : (SimpleGraph.mulCayley
        ((QuotientGroup.mk (s := P)) '' S \ {1})).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n) :
    ∃ (n : ℕ) (v : G) (c : (SimpleGraph.mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  obtain ⟨n, v, p, hn, hp, hlen⟩ := hcycle
  let inclusion : mulCayley ((QuotientGroup.mk (s := P)) '' S \ {1}) →g
      mulCayley ((QuotientGroup.mk' P) '' S) :=
    SimpleGraph.Hom.ofLE (mulCayley_mono Set.sdiff_subset)
  obtain ⟨t, ht, v', c, hc, hclen⟩ := cayley_cycle_image_lift
    (QuotientGroup.mk' P) QuotientGroup.mk_surjective S (p.map inclusion)
      (hp.map Function.injective_id)
  have htP : t ∈ P := (QuotientGroup.eq_one_iff t).mp ht
  obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow (⟨t, htP⟩ : P)
  have hk' : orderOf t = 2 ^ k := by simpa using hk
  refine ⟨n + k, v', c, by omega, hc, ?_⟩
  rw [hclen, Walk.length_map, hlen, hk', pow_add]

end CayleyErdosGyarfas

-- ===== from CayleyErdosGyarfas/FigureEightLifting.lean =====
namespace CayleyErdosGyarfas

/-- Squaring is injective in any group of finite odd cardinality. -/
theorem square_injective_of_odd_natCard {G : Type*} [Group G]
    (hodd : Odd (Nat.card G)) : Function.Injective (fun a : G ↦ a ^ 2) :=
  hodd.coprime_two_right.pow_left_bijective.1

/-- In a group of odd cardinality, only the identity is conjugate to its inverse. -/
theorem eq_one_of_conjugate_inv_of_odd_natCard {G : Type*} [Group G]
    (hodd : Odd (Nat.card G)) {a g : G} (h : g⁻¹ * a * g = a⁻¹) : a = 1 := by
  have hleft : a * g = g * a⁻¹ := calc
    a * g = g * (g⁻¹ * a * g) := by group
    _ = g * a⁻¹ := by rw [h]
  have hsq : (a * g) ^ 2 = g ^ 2 := calc
    (a * g) ^ 2 = (a * g) * a * g := by simp [pow_two, mul_assoc]
    _ = (g * a⁻¹) * a * g := by rw [hleft]
    _ = g ^ 2 := by simp [pow_two, mul_assoc]
  have := square_injective_of_odd_natCard hodd hsq
  exact mul_right_cancel (by simpa using this : a * g = 1 * g)

/-- The exceptional five-element configuration in the manuscript is impossible:
a nonidentity element cannot be conjugate to the inverse of its square if its
conjugate squares back to the original element. -/
theorem eq_one_of_conjugate_inverse_square {G : Type*} [Group G]
    (hodd : Odd (Nat.card G)) {a b g : G}
    (hconj : g⁻¹ * a * g = b) (hb : b = (a * a)⁻¹) (ha : b * b = a) : a = 1 := by
  let ψ : G ≃* G := MulAut.conj g⁻¹
  have hψ : ψ a = b := by simpa [ψ, MulAut.conj_apply, mul_assoc] using hconj
  have hψψ : ψ (ψ a) = a⁻¹ := by
    rw [hψ, hb, map_inv, map_mul, hψ, ha]
  apply eq_one_of_conjugate_inv_of_odd_natCard hodd (g := g * g)
  simpa [ψ, MulAut.conj_apply, mul_inv_rev, mul_assoc] using hψψ

/-- The endpoint separation used to choose one of the two commutator figures in
Lemma 1.2. This formulation incorporates the odd-order conjugacy argument. -/
theorem conjugate_products_escape_inverse_set {G : Type*} [Group G]
    (hodd : Odd (Nat.card G)) {a b g : G} (ha : a ≠ 1) (hb : b ≠ 1)
    (hconj : g⁻¹ * a * g = b) :
    a * b ∉ ({a, a⁻¹, b, b⁻¹} : Set G) ∨
      a * b⁻¹ ∉ ({a, a⁻¹, b, b⁻¹} : Set G) := by
  by_contra! h
  rcases h with ⟨h₁, h₂⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h₁ h₂
  have h₁' : a * b = a⁻¹ ∨ a * b = b⁻¹ := by
    rcases h₁ with h | h | h | h
    · exact False.elim (hb (mul_left_cancel (by simpa using h : a * b = a * 1)))
    · exact Or.inl h
    · exact False.elim (ha (mul_right_cancel (by simpa using h : a * b = 1 * b)))
    · exact Or.inr h
  have h₂' : a * b⁻¹ = a⁻¹ ∨ a * b⁻¹ = b := by
    rcases h₂ with h | h | h | h
    · have : b⁻¹ = 1 := mul_left_cancel (by simpa using h : a * b⁻¹ = a * 1)
      exact False.elim (hb (by simpa using this))
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (ha (mul_right_cancel (by simpa using h : a * b⁻¹ = 1 * b⁻¹)))
  have h₁'' : b = (a * a)⁻¹ ∨ a = (b * b)⁻¹ := by
    rcases h₁' with h | h
    · left
      calc b = a⁻¹ * (a * b) := by group
           _ = a⁻¹ * a⁻¹ := by rw [h]
           _ = (a * a)⁻¹ := by group
    · right
      calc a = (a * b) * b⁻¹ := by group
           _ = b⁻¹ * b⁻¹ := by rw [h]
           _ = (b * b)⁻¹ := by group
  have h₂'' : b = a * a ∨ a = b * b := by
    rcases h₂' with h | h
    · left
      calc b = (a * b⁻¹)⁻¹ * a := by group
           _ = (a⁻¹)⁻¹ * a := by rw [h]
           _ = a * a := by simp
    · right
      calc a = (a * b⁻¹) * b := by group
           _ = b * b := by rw [h]
  rcases h₁'' with h₁ | h₁ <;> rcases h₂'' with h₂ | h₂
  · have hsq : a ^ 2 = (a⁻¹) ^ 2 := by simpa [pow_two, mul_inv_rev] using h₂.symm.trans h₁
    have hinv := square_injective_of_odd_natCard hodd hsq
    exact ha (eq_one_of_conjugate_inv_of_odd_natCard hodd (g := 1) (by simpa using hinv))
  · exact ha (eq_one_of_conjugate_inverse_square hodd hconj h₁ h₂.symm)
  · have hconj' : (g⁻¹)⁻¹ * b * g⁻¹ = a := by rw [← hconj]; group
    exact hb (eq_one_of_conjugate_inverse_square hodd hconj' h₁ h₂.symm)
  · have hsq : b ^ 2 = (b⁻¹) ^ 2 := by simpa [pow_two, mul_inv_rev] using h₂.symm.trans h₁
    have hinv := square_injective_of_odd_natCard hodd hsq
    exact hb (eq_one_of_conjugate_inv_of_odd_natCard hodd (g := 1) (by simpa using hinv))

/-- Distinct kernel translates of the half-open lift of a simple quotient cycle
have disjoint vertices. The endpoint is excluded to avoid counting it twice. -/
theorem translated_lift_vertex_eq_iff {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) {S : Set G} {T : Set Q} {q : Q}
    (p : (SimpleGraph.mulCayley T).Walk q q) (hp : p.IsCycle)
    {a b : G} (w : (SimpleGraph.mulCayley S).Walk a b)
    (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    {u v : G} (hu : φ u = 1) (hv : φ v = 1)
    {i j : ℕ} (hi : i < p.length) (hj : j < p.length) :
    u * w.getVert i = v * w.getVert j ↔ i = j ∧ u = v := by
  constructor
  · intro heq
    have hproj : p.getVert i = p.getVert j := by
      simpa only [map_mul, hu, hv, one_mul, hw] using congrArg φ heq
    have hij : i = j := hp.getVert_injOn' (by exact Nat.le_pred_of_lt hi)
      (by exact Nat.le_pred_of_lt hj) hproj
    refine ⟨hij, ?_⟩
    subst j
    exact mul_right_cancel heq
  · rintro ⟨rfl, rfl⟩
    rfl

/-- For two lifted quotient cycles meeting only at their basepoint, kernel
translates can meet on their half-open vertex sequences only at the starts. -/
theorem translated_disjoint_lifts_vertex_eq_iff {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) {S : Set G} {T : Set Q} {q : Q}
    (p r : (SimpleGraph.mulCayley T).Walk q q) (hp : p.IsCycle) (hr : r.IsCycle)
    (hdisj : ∀ x, (x ∈ p.support ∧ x ∈ r.support) ↔ x = q)
    {a b c : G} (w : (SimpleGraph.mulCayley S).Walk a b)
    (z : (SimpleGraph.mulCayley S).Walk a c)
    (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    (hz : ∀ i, φ (z.getVert i) = r.getVert i)
    {u v : G} (hu : φ u = 1) (hv : φ v = 1)
    {i j : ℕ} (hi : i < p.length) (hj : j < r.length) :
    u * w.getVert i = v * z.getVert j ↔ i = 0 ∧ j = 0 ∧ u = v := by
  constructor
  · intro heq
    have hproj : p.getVert i = r.getVert j := by
      simpa only [map_mul, hu, hv, one_mul, hw, hz] using congrArg φ heq
    have hqi : p.getVert i = q := (hdisj _).mp
      ⟨p.getVert_mem_support i, hproj ▸ r.getVert_mem_support j⟩
    have hqj : r.getVert j = q := hproj.symm.trans hqi
    have hi0 : i = 0 := hp.getVert_injOn' (Nat.le_pred_of_lt hi)
      (by have := hp.three_le_length; simp only [Set.mem_ofPred_eq]; omega)
      (by simpa using hqi)
    have hj0 : j = 0 := hr.getVert_injOn' (Nat.le_pred_of_lt hj)
      (by have := hr.three_le_length; simp only [Set.mem_ofPred_eq]; omega)
      (by simpa using hqj)
    refine ⟨hi0, hj0, ?_⟩
    subst i; subst j
    exact mul_right_cancel (by simpa using heq : u * a = v * a)
  · rintro ⟨rfl, rfl, rfl⟩
    simp

/-- The only vertices of a lifted simple quotient cycle lying over its basepoint
are the two endpoints of the lift. -/
theorem lifted_cycle_basepoint_iff {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) {S : Set G} {T : Set Q} {q : Q}
    (p : (SimpleGraph.mulCayley T).Walk q q) (hp : p.IsCycle)
    {a b : G} (w : (SimpleGraph.mulCayley S).Walk a b)
    (hlen : w.length = p.length) (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    {x : G} (hx : x ∈ w.support) : φ x = q ↔ x = a ∨ x = b := by
  obtain ⟨i, rfl, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  constructor
  · intro h
    have hi' : i = 0 ∨ i = p.length :=
      (hp.getVert_endpoint_iff (by omega)).mp (by simpa only [hw] using h)
    rcases hi' with rfl | hi'
    · simp
    · rw [← hlen] at hi'
      simp [hi']
  · intro h
    rcases h with h | h
    · rw [h]
      simpa using hw 0
    · rw [h]
      calc φ b = φ (w.getVert w.length) := by simp
           _ = p.getVert w.length := hw _
           _ = q := by rw [hlen]; simp

/-- A lift of a simple quotient cycle with distinct endpoints is a path. -/
theorem lifted_cycle_isPath_of_ne {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) {S : Set G} {T : Set Q} {q : Q}
    (p : (SimpleGraph.mulCayley T).Walk q q) (hp : p.IsCycle)
    {a b : G} (w : (SimpleGraph.mulCayley S).Walk a b) (hab : a ≠ b)
    (hlen : w.length = p.length) (hw : ∀ i, φ (w.getVert i) = p.getVert i) :
    w.IsPath := by
  apply (SimpleGraph.Walk.IsPath.getVert_injOn_iff w).mp
  intro i hi j hj hij
  simp only [Set.mem_ofPred_eq] at hi hj
  have hproj : p.getVert i = p.getVert j := by simpa only [hw] using congrArg φ hij
  by_cases hil : i = w.length
  · subst i
    have hj' : j = 0 ∨ j = p.length :=
      (hp.getVert_endpoint_iff (by omega)).mp (by simpa only [hlen, SimpleGraph.Walk.getVert_length] using hproj.symm)
    rcases hj' with rfl | hj'
    · exact False.elim (hab (by simpa using hij.symm))
    · omega
  · by_cases hjl : j = w.length
    · subst j
      have hi' : i = 0 ∨ i = p.length :=
        (hp.getVert_endpoint_iff (by omega)).mp (by simpa only [hlen, SimpleGraph.Walk.getVert_length] using hproj)
      rcases hi' with rfl | hi'
      · exact False.elim (hab (by simpa using hij))
      · omega
    · exact hp.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) hproj

/-- Two distinct kernel translates of a lifted lobe can meet only at endpoints. -/
theorem translated_lift_support_intersection {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) {S : Set G} {T : Set Q} {q : Q}
    (p : (SimpleGraph.mulCayley T).Walk q q) (hp : p.IsCycle)
    {a b : G} (w : (SimpleGraph.mulCayley S).Walk a b)
    (hlen : w.length = p.length) (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    {u v x y : G} (hu : φ u = 1) (hv : φ v = 1) (huv : u ≠ v)
    (hx : x ∈ w.support) (hy : y ∈ w.support) (hxy : u * x = v * y) :
    (x = a ∨ x = b) ∧ (y = a ∨ y = b) := by
  have hproj : φ x = φ y := by simpa only [map_mul, hu, hv, one_mul] using congrArg φ hxy
  have hq : φ x = q := by
    by_contra hq
    obtain ⟨i, hi, hil⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    obtain ⟨j, hj, hjl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
    have hil' : i < p.length := by
      have hne : i ≠ w.length := by
        intro heq
        apply hq
        rw [← hi, heq, hw, hlen]
        simp
      omega
    have hjl' : j < p.length := by
      have hne : j ≠ w.length := by
        intro heq
        apply hq
        rw [hproj, ← hj, heq, hw, hlen]
        simp
      omega
    have := (translated_lift_vertex_eq_iff φ p hp w hw hu hv hil' hjl').mp
      (by simpa only [hi, hj] using hxy)
    exact huv this.2
  exact ⟨(lifted_cycle_basepoint_iff φ p hp w hlen hw hx).mp hq,
    (lifted_cycle_basepoint_iff φ p hp w hlen hw hy).mp (hproj.symm.trans hq)⟩

/-- Translates of different lifted lobes of a quotient figure-eight can meet
only at endpoints. -/
theorem translated_disjoint_lifts_support_intersection {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) {S : Set G} {T : Set Q} {q : Q}
    (p r : (SimpleGraph.mulCayley T).Walk q q) (hp : p.IsCycle) (hr : r.IsCycle)
    (hdisj : ∀ x, (x ∈ p.support ∧ x ∈ r.support) ↔ x = q)
    {a b c : G} (w : (SimpleGraph.mulCayley S).Walk a b)
    (z : (SimpleGraph.mulCayley S).Walk a c)
    (hwlen : w.length = p.length) (hzlen : z.length = r.length)
    (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    (hz : ∀ i, φ (z.getVert i) = r.getVert i)
    {u v x y : G} (hu : φ u = 1) (hv : φ v = 1)
    (hx : x ∈ w.support) (hy : y ∈ z.support) (hxy : u * x = v * y) :
    (x = a ∨ x = b) ∧ (y = a ∨ y = c) := by
  have hproj : φ x = φ y := by simpa only [map_mul, hu, hv, one_mul] using congrArg φ hxy
  have hxq : φ x ∈ p.support := by
    obtain ⟨i, rfl, _⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    rw [hw]
    exact p.getVert_mem_support i
  have hyq : φ y ∈ r.support := by
    obtain ⟨i, rfl, _⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
    rw [hz]
    exact r.getVert_mem_support i
  have hq : φ x = q := (hdisj _).mp ⟨hxq, hproj ▸ hyq⟩
  exact ⟨(lifted_cycle_basepoint_iff φ p hp w hwlen hw hx).mp hq,
    (lifted_cycle_basepoint_iff φ r hr z hzlen hz hy).mp (hproj.symm.trans hq)⟩

/-- Append two paths meeting only at the common endpoint. -/
theorem isPath_append_of_support_intersection {V : Type*} {Γ : SimpleGraph V}
    {a b c : V} {p : Γ.Walk a b} {q : Γ.Walk b c}
    (hp : p.IsPath) (hq : q.IsPath)
    (h : ∀ x, x ∈ p.support → x ∈ q.support → x = b) :
    (p.append q).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  apply List.disjoint_left.mpr
  intro x hx hx'
  have hxb : x = b := h x hx (List.mem_of_mem_tail hx')
  subst x
  have hn : (b :: q.support.tail).Nodup := by
    rw [SimpleGraph.Walk.cons_tail_support]
    exact hq.support_nodup
  exact (List.nodup_cons.mp hn).1 hx'

/-- Two paths with the same endpoints and no other shared vertices form a cycle. -/
theorem isCycle_append_reverse_of_support_intersection {V : Type*} {Γ : SimpleGraph V}
    {a b : V} {p q : Γ.Walk a b} (hp : p.IsPath) (hq : q.IsPath)
    (h : ∀ x, x ∈ p.support → x ∈ q.support → x = a ∨ x = b)
    (hlen : 1 < p.length ∨ 1 < q.length) :
    (p.append q.reverse).IsCycle := by
  apply hp.isCycle_append hq.reverse _ (by simpa using hlen)
  apply List.disjoint_left.mpr
  intro x hx hx'
  have hxa : x = a ∨ x = b := h x (List.mem_of_mem_tail hx)
    (by simpa using (List.mem_of_mem_tail hx' : x ∈ q.reverse.support))
  rcases hxa with hxa | hxb
  · subst x
    have hn : (a :: p.support.tail).Nodup := by
      rw [SimpleGraph.Walk.cons_tail_support]
      exact hp.support_nodup
    exact (List.nodup_cons.mp hn).1 hx
  · subst x
    have hn : (b :: q.reverse.support.tail).Nodup := by
      rw [SimpleGraph.Walk.cons_tail_support]
      exact hq.reverse.support_nodup
    exact (List.nodup_cons.mp hn).1 hx'

/-- The equal nontrivial endpoint case of Lemma 1.2: the two lifted lobes,
followed in opposite directions, form a cycle whose inverse-endpoint translate
meets it exactly once. -/
theorem hasSymmetricFigureEight_of_equal_voltage_lifts
    {G Q : Type*} [Group G] [Group Q] (hodd : Odd (Nat.card G))
    (φ : G →* Q) {S : Set G} {T : Set Q}
    (p r : (SimpleGraph.mulCayley T).Walk 1 1) (hp : p.IsCycle) (hr : r.IsCycle)
    (hdisj : ∀ x, (x ∈ p.support ∧ x ∈ r.support) ↔ x = 1)
    {a : G} (ha : a ≠ 1) (hφa : φ a = 1)
    (w z : (SimpleGraph.mulCayley S).Walk 1 a)
    (hwlen : w.length = p.length) (hzlen : z.length = r.length)
    (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    (hz : ∀ i, φ (z.getVert i) = r.getVert i)
    (n : ℕ) (hn : 1 ≤ n) (hplen : p.length = 2 ^ n) (hrlen : r.length = 2 ^ n) :
    HasSymmetricFigureEight S := by
  have hwpath := lifted_cycle_isPath_of_ne φ p hp w (Ne.symm ha) hwlen hw
  have hzpath := lifted_cycle_isPath_of_ne φ r hr z (Ne.symm ha) hzlen hz
  let c := w.append z.reverse
  have hc : c.IsCycle := isCycle_append_reverse_of_support_intersection hwpath hzpath
    (fun x hx hz' ↦ (translated_disjoint_lifts_support_intersection φ p r hp hr hdisj
      w z hwlen hzlen hw hz (u := 1) (v := 1) (by simp) (by simp) hx hz' rfl).1)
    (Or.inl (by have := hp.three_le_length; omega))
  have hclen : c.length = 2 ^ (n + 1) := by
    simp only [c, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
      hwlen, hzlen, hplen, hrlen, pow_succ]
    omega
  apply hasSymmetricFigureEight_of_cycle_translate c (n + 1) (by omega) hc hclen a⁻¹ 1
  have hφai : φ a⁻¹ = 1 := by simp [hφa]
  have hne : (1 : G) ≠ a⁻¹ := by simpa using ha
  have hai : a⁻¹ ≠ a := by
    intro h
    exact ha (eq_one_of_conjugate_inv_of_odd_natCard hodd (g := 1) (by simpa using h.symm))
  have hsupport (x : G) : x ∈ c.support ↔ x ∈ w.support ∨ x ∈ z.support := by simp [c]
  intro x
  constructor
  · rintro ⟨hx, y, hy, hyx⟩
    rw [hsupport] at hx hy
    have he : (x = 1 ∨ x = a) ∧ (y = 1 ∨ y = a) := by
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact translated_lift_support_intersection φ p hp w hwlen hw
          (u := 1) (v := a⁻¹) (by simp) hφai hne hx hy (by simpa using hyx.symm)
      · exact translated_disjoint_lifts_support_intersection φ p r hp hr hdisj
          w z hwlen hzlen hw hz (u := 1) (v := a⁻¹) (by simp) hφai hx hy
          (by simpa using hyx.symm)
      · exact translated_disjoint_lifts_support_intersection φ r p hr hp
          (by intro x; simpa [and_comm] using hdisj x)
          z w hzlen hwlen hz hw (u := 1) (v := a⁻¹) (by simp) hφai hx hy
          (by simpa using hyx.symm)
      · exact translated_lift_support_intersection φ r hr z hzlen hz
          (u := 1) (v := a⁻¹) (by simp) hφai hne hx hy (by simpa using hyx.symm)
    rcases he with ⟨hx | hx, hy | hy⟩ <;> simp_all
  · rintro rfl
    refine ⟨by simp [c], a, ?_, by simp⟩
    rw [hsupport]
    exact Or.inl w.end_mem_support

set_option backward.isDefEq.respectTransparency false in
/-- The lifted commutator square is a simple cycle whenever its four corner
vertices are distinct. Its support is recorded for the figure-eight argument. -/
theorem commutator_cycle_of_lifts
    {G Q : Type*} [Group G] [Group Q] (φ : G →* Q) {S : Set G} {T : Set Q}
    (p r : (SimpleGraph.mulCayley T).Walk 1 1) (hp : p.IsCycle) (hr : r.IsCycle)
    (hdisj : ∀ x, (x ∈ p.support ∧ x ∈ r.support) ↔ x = 1)
    {a b : G} (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) (habi : a ≠ b⁻¹)
    (hcomm : Commute a b) (hφa : φ a = 1) (hφb : φ b = 1)
    (w : (SimpleGraph.mulCayley S).Walk 1 a)
    (z : (SimpleGraph.mulCayley S).Walk 1 b)
    (hwlen : w.length = p.length) (hzlen : z.length = r.length)
    (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    (hz : ∀ i, φ (z.getVert i) = r.getVert i) :
    ∃ c : (SimpleGraph.mulCayley S).Walk 1 1,
      c.IsCycle ∧ c.length = 2 * (w.length + z.length) ∧
      ∀ x, x ∈ c.support ↔
        (∃ u ∈ ({1, b} : Set G), ∃ y ∈ w.support, u * y = x) ∨
        (∃ u ∈ ({1, a} : Set G), ∃ y ∈ z.support, u * y = x) := by
  have hprod : a * b ≠ 1 := fun h ↦ habi (eq_inv_of_mul_eq_one_left h)
  have hprod' : b * a ≠ 1 := fun h ↦ hprod (hcomm.eq.trans h)
  have hcross {u v x y : G} := translated_disjoint_lifts_support_intersection φ p r hp hr hdisj
    w z hwlen hzlen hw hz (u := u) (v := v) (x := x) (y := y)
  have hcross' {u v x y : G} := translated_disjoint_lifts_support_intersection φ r p hr hp
    (by intro x; simpa [and_comm] using hdisj x) z w hzlen hwlen hz hw
    (u := u) (v := v) (x := x) (y := y)
  have hsamew {u v x y : G} := translated_lift_support_intersection φ p hp w hwlen hw
    (u := u) (v := v) (x := x) (y := y)
  have hsamez {u v x y : G} := translated_lift_support_intersection φ r hr z hzlen hz
    (u := u) (v := v) (x := x) (y := y)
  let az : (SimpleGraph.mulCayley S).Walk a (a * b) :=
    (z.map (cayleyLeftTranslation S a).toHom).copy (by simp [cayleyLeftTranslation]) rfl
  let bw : (SimpleGraph.mulCayley S).Walk b (a * b) :=
    (w.map (cayleyLeftTranslation S b).toHom).copy (by simp [cayleyLeftTranslation])
      (by simpa [cayleyLeftTranslation] using hcomm.eq.symm)
  have haz (x : G) : x ∈ az.support ↔ ∃ y ∈ z.support, a * y = x := by
    change x ∈ ((z.map (cayleyLeftTranslation S a).toHom).copy _ _).support ↔ _
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map]
    change x ∈ z.support.map (a * ·) ↔ _
    exact List.mem_map
  have hbw (x : G) : x ∈ bw.support ↔ ∃ y ∈ w.support, b * y = x := by
    change x ∈ ((w.map (cayleyLeftTranslation S b).toHom).copy _ _).support ↔ _
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map]
    change x ∈ w.support.map (b * ·) ↔ _
    exact List.mem_map
  have hwpath := lifted_cycle_isPath_of_ne φ p hp w (Ne.symm ha) hwlen hw
  have hzpath := lifted_cycle_isPath_of_ne φ r hr z (Ne.symm hb) hzlen hz
  have hazpath : az.IsPath := by
    apply (SimpleGraph.Walk.isPath_copy ..).mpr
    exact hzpath.map (fun _ _ h ↦ mul_left_cancel h)
  have hbwpath : bw.IsPath := by
    apply (SimpleGraph.Walk.isPath_copy ..).mpr
    exact hwpath.map (fun _ _ h ↦ mul_left_cancel h)
  let P := w.append az
  let R := z.append bw
  have hP : P.IsPath := isPath_append_of_support_intersection hwpath hazpath (by
    intro x hx hax
    obtain ⟨y, hy, hyx⟩ := (haz x).mp hax
    have he := hcross (u := 1) (v := a) (by simp) hφa hx hy (by simpa using hyx.symm)
    clear hcross hcross' hsamew hsamez
    rcases he with ⟨hx | hx, hy | hy⟩ <;> simp_all)
  have hR : R.IsPath := isPath_append_of_support_intersection hzpath hbwpath (by
    intro x hx hbx
    obtain ⟨y, hy, hyx⟩ := (hbw x).mp hbx
    have he := hcross' (u := 1) (v := b) (by simp) hφb hx hy (by simpa using hyx.symm)
    clear hcross hcross' hsamew hsamez
    rcases he with ⟨hx | hx, hy | hy⟩ <;> simp_all)
  have hPR : ∀ x, x ∈ P.support → x ∈ R.support → x = 1 ∨ x = a * b := by
    intro x hx hx'
    simp only [P, R, SimpleGraph.Walk.mem_support_append_iff, haz, hbw] at hx hx'
    rcases hx with hx | ⟨y, hy, hyx⟩ <;> rcases hx' with hx' | ⟨y', hy', hyx'⟩
    · have he := hcross (u := 1) (v := 1) (by simp) (by simp) hx hx' rfl
      clear hcross hcross' hsamew hsamez
      rcases he with ⟨hx | hx, hx' | hx'⟩ <;> simp_all
    · have he := hsamew (u := 1) (v := b) (by simp) hφb (Ne.symm hb) hx hy'
        (by simpa using hyx'.symm)
      clear hcross hcross' hsamew hsamez
      rcases he with ⟨hx | hx, hy' | hy'⟩ <;> simp_all
    · have he := hsamez (u := a) (v := 1) hφa (by simp) ha hy hx'
        (by simpa using hyx)
      clear hcross hcross' hsamew hsamez
      rcases he with ⟨hy | hy, hx' | hx'⟩ <;> simp_all
    · have he := hcross' (u := a) (v := b) hφa hφb hy hy' (hyx.trans hyx'.symm)
      clear hcross hcross' hsamew hsamez
      rcases he with ⟨hy | hy, hy' | hy'⟩ <;> simp_all
  refine ⟨P.append R.reverse, ?_, ?_, ?_⟩
  · exact isCycle_append_reverse_of_support_intersection hP hR hPR
      (Or.inl (by have := hp.three_le_length; simp [P]; omega))
  · simp [P, R, az, bw]
    omega
  · intro x
    simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse, P, R, haz, hbw, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ((hx | ⟨y, hy, rfl⟩) | (hx | ⟨y, hy, rfl⟩))
      · exact Or.inl ⟨1, Or.inl rfl, x, hx, by simp⟩
      · exact Or.inr ⟨a, Or.inr rfl, y, hy, rfl⟩
      · exact Or.inr ⟨1, Or.inl rfl, x, hx, by simp⟩
      · exact Or.inl ⟨b, Or.inr rfl, y, hy, rfl⟩
    · rintro (⟨u, hu, y, hy, rfl⟩ | ⟨u, hu, y, hy, rfl⟩) <;> rcases hu with rfl | rfl
      · simp [hy]
      · exact Or.inr (Or.inr ⟨y, hy, rfl⟩)
      · simp [hy]
      · exact Or.inl (Or.inr ⟨y, hy, rfl⟩)

/-- The corner sets of a commutator square and its opposite translate meet only
at the identity under the endpoint separation condition. -/
theorem commutator_corners_intersection {G : Type*} [Group G]
    (hodd : Odd (Nat.card G)) {a b x y : G}
    (ha : a ≠ 1) (hb : b ≠ 1) (habi : a ≠ b⁻¹) (hcomm : Commute a b)
    (hescape : a * b ∉ ({a, a⁻¹, b, b⁻¹} : Set G))
    (hx : x ∈ ({1, a, b, a * b} : Set G))
    (hy : y ∈ ({1, a, b, a * b} : Set G))
    (hxy : (a * b)⁻¹ * y = x) : x = 1 := by
  have hprod : a * b ≠ 1 := fun h ↦ habi (eq_inv_of_mul_eq_one_left h)
  have hga : (a * b)⁻¹ * a = b⁻¹ := by group
  have hgb : (a * b)⁻¹ * b = a⁻¹ := by rw [hcomm.eq]; group
  have hai : a⁻¹ ≠ a := by
    intro h
    exact ha (eq_one_of_conjugate_inv_of_odd_natCard hodd (g := 1) (by simpa using h.symm))
  have hbi : b⁻¹ ≠ b := by
    intro h
    exact hb (eq_one_of_conjugate_inv_of_odd_natCard hodd (g := 1) (by simpa using h.symm))
  have hpi : (a * b)⁻¹ ≠ a * b := by
    intro h
    exact hprod (eq_one_of_conjugate_inv_of_odd_natCard hodd (g := 1) (by simpa using h.symm))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx hy hescape
  obtain ⟨hea, heai, heb, hebi⟩ := hescape
  have hia : (a * b)⁻¹ ≠ a := by
    intro h
    apply heai
    simpa using congrArg Inv.inv h
  have hib : (a * b)⁻¹ ≠ b := by
    intro h
    apply hebi
    simpa using congrArg Inv.inv h
  have hi1 : (a * b)⁻¹ ≠ 1 := by
    intro h
    exact hprod (by simpa only [inv_inv, inv_one] using congrArg Inv.inv h)
  have hai1 : a⁻¹ ≠ 1 := by simpa using ha
  have hbi1 : b⁻¹ ≠ 1 := by simpa using hb
  have haiB : a⁻¹ ≠ b := by
    intro h
    apply habi
    simpa using congrArg Inv.inv h
  rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
    rw [hx, hy] at hxy <;> rw [hx] <;>
    simp only [mul_one, inv_mul_cancel, hga, hgb] at hxy <;> grind only

set_option backward.isDefEq.respectTransparency false in
/-- The generic commutator case of Lemma 1.2, including its translated second lobe. -/
theorem hasSymmetricFigureEight_of_commutator_lifts
    {G Q : Type*} [Group G] [Group Q] (hodd : Odd (Nat.card G))
    (φ : G →* Q) {S : Set G} {T : Set Q}
    (p r : (SimpleGraph.mulCayley T).Walk 1 1) (hp : p.IsCycle) (hr : r.IsCycle)
    (hdisj : ∀ x, (x ∈ p.support ∧ x ∈ r.support) ↔ x = 1)
    {a b : G} (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) (habi : a ≠ b⁻¹)
    (hcomm : Commute a b) (hφa : φ a = 1) (hφb : φ b = 1)
    (hescape : a * b ∉ ({a, a⁻¹, b, b⁻¹} : Set G))
    (w : (SimpleGraph.mulCayley S).Walk 1 a)
    (z : (SimpleGraph.mulCayley S).Walk 1 b)
    (hwlen : w.length = p.length) (hzlen : z.length = r.length)
    (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    (hz : ∀ i, φ (z.getVert i) = r.getVert i)
    (n : ℕ) (hn : 1 ≤ n) (hplen : p.length = 2 ^ n) (hrlen : r.length = 2 ^ n) :
    HasSymmetricFigureEight S := by
  obtain ⟨c, hc, hclen, hsupport⟩ := commutator_cycle_of_lifts φ p r hp hr hdisj
    ha hb hab habi hcomm hφa hφb w z hwlen hzlen hw hz
  have hclen' : c.length = 2 ^ (n + 2) := by
    rw [hclen, hwlen, hzlen, hplen, hrlen, pow_add]
    ring
  let g := (a * b)⁻¹
  have hprod : a * b ≠ 1 := fun h ↦ habi (eq_inv_of_mul_eq_one_left h)
  have hga : g * a = b⁻¹ := by dsimp [g]; group
  have hgb : g * b = a⁻¹ := by dsimp [g]; rw [hcomm.eq]; group
  have hφg : φ g = 1 := by simp [g, map_mul, hφa, hφb]
  have hcornerW {u x : G} (hu : u ∈ ({1, b} : Set G)) (hx : x = 1 ∨ x = a) :
      u * x ∈ ({1, a, b, a * b} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
    rcases hu with rfl | rfl <;> rcases hx with rfl | rfl <;> simp [hcomm.eq]
  have hcornerZ {u x : G} (hu : u ∈ ({1, a} : Set G)) (hx : x = 1 ∨ x = b) :
      u * x ∈ ({1, a, b, a * b} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
    rcases hu with rfl | rfl <;> rcases hx with rfl | rfl <;> simp
  have hcoeffW {u v : G} (hu : u ∈ ({1, b} : Set G)) (hv : v ∈ ({1, b} : Set G)) :
      u ≠ g * v := by
    intro heq
    have hu' : u ∈ ({1, a, b, a * b} : Set G) := by
      simpa using hcornerW hu (Or.inl rfl : (1 : G) = 1 ∨ (1 : G) = a)
    have hv' : v ∈ ({1, a, b, a * b} : Set G) := by
      simpa using hcornerW hv (Or.inl rfl : (1 : G) = 1 ∨ (1 : G) = a)
    have hu1 := commutator_corners_intersection hodd ha hb habi hcomm hescape hu' hv' heq.symm
    rw [hu1] at heq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hprod ((inv_eq_one).mp (by simpa only [mul_one] using heq.symm))
    · exact ha ((inv_eq_one).mp (hgb.symm.trans heq.symm))
  have hcoeffZ {u v : G} (hu : u ∈ ({1, a} : Set G)) (hv : v ∈ ({1, a} : Set G)) :
      u ≠ g * v := by
    intro heq
    have hu' : u ∈ ({1, a, b, a * b} : Set G) := by
      simpa using hcornerZ hu (Or.inl rfl : (1 : G) = 1 ∨ (1 : G) = b)
    have hv' : v ∈ ({1, a, b, a * b} : Set G) := by
      simpa using hcornerZ hv (Or.inl rfl : (1 : G) = 1 ∨ (1 : G) = b)
    have hu1 := commutator_corners_intersection hodd ha hb habi hcomm hescape hu' hv' heq.symm
    rw [hu1] at heq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hprod ((inv_eq_one).mp (by simpa only [mul_one] using heq.symm))
    · exact hb ((inv_eq_one).mp (hga.symm.trans heq.symm))
  have hkerW {u : G} (hu : u ∈ ({1, b} : Set G)) : φ u = 1 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl <;> simp [hφb]
  have hkerZ {u : G} (hu : u ∈ ({1, a} : Set G)) : φ u = 1 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl <;> simp [hφa]
  apply hasSymmetricFigureEight_of_cycle_translate c (n + 2) (by omega) hc hclen' g 1
  intro x
  constructor
  · rintro ⟨hx, y, hy, hxy⟩
    have hcorners : x ∈ ({1, a, b, a * b} : Set G) ∧ y ∈ ({1, a, b, a * b} : Set G) := by
      rcases (hsupport x).mp hx with ⟨u, hu, s, hs, hus⟩ | ⟨u, hu, s, hs, hus⟩ <;>
        rcases (hsupport y).mp hy with ⟨v, hv, t, ht, hvt⟩ | ⟨v, hv, t, ht, hvt⟩
      all_goals
        have heq : u * s = (g * v) * t := by rw [mul_assoc, hvt, hxy, hus]
      · have he := translated_lift_support_intersection φ p hp w hwlen hw
          (hkerW hu) (by simp [map_mul, hφg, hkerW hv]) (hcoeffW hu hv) hs ht heq
        exact ⟨hus ▸ hcornerW hu he.1, hvt ▸ hcornerW hv he.2⟩
      · have he := translated_disjoint_lifts_support_intersection φ p r hp hr hdisj
          w z hwlen hzlen hw hz (hkerW hu) (by simp [map_mul, hφg, hkerZ hv]) hs ht heq
        exact ⟨hus ▸ hcornerW hu he.1, hvt ▸ hcornerZ hv he.2⟩
      · have he := translated_disjoint_lifts_support_intersection φ r p hr hp
          (by intro q; simpa [and_comm] using hdisj q) z w hzlen hwlen hz hw
          (hkerZ hu) (by simp [map_mul, hφg, hkerW hv]) hs ht heq
        exact ⟨hus ▸ hcornerZ hu he.1, hvt ▸ hcornerW hv he.2⟩
      · have he := translated_lift_support_intersection φ r hr z hzlen hz
          (hkerZ hu) (by simp [map_mul, hφg, hkerZ hv]) (hcoeffZ hu hv) hs ht heq
        exact ⟨hus ▸ hcornerZ hu he.1, hvt ▸ hcornerZ hv he.2⟩
    exact commutator_corners_intersection hodd ha hb habi hcomm hescape hcorners.1 hcorners.2 hxy
  · rintro rfl
    refine ⟨c.start_mem_support, a * b, ?_, by simp [g]⟩
    apply (hsupport (a * b)).mpr
    exact Or.inr ⟨a, by simp, b, z.end_mem_support, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Reverse a lifted quotient lobe and translate it back to the identity. The
new endpoint is the inverse of the original endpoint. -/
theorem exists_inverse_voltage_lift {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) {S : Set G} {T : Set Q}
    (r : (SimpleGraph.mulCayley T).Walk 1 1) {b : G} (hφb : φ b = 1)
    (z : (SimpleGraph.mulCayley S).Walk 1 b)
    (hzlen : z.length = r.length) (hz : ∀ i, φ (z.getVert i) = r.getVert i) :
    ∃ z' : (SimpleGraph.mulCayley S).Walk 1 b⁻¹,
      z'.length = r.reverse.length ∧ ∀ i, φ (z'.getVert i) = r.reverse.getVert i := by
  let z' : (SimpleGraph.mulCayley S).Walk 1 b⁻¹ :=
    (z.reverse.map (cayleyLeftTranslation S b⁻¹).toHom).copy
      (by simp [cayleyLeftTranslation]) (by simp [cayleyLeftTranslation])
  refine ⟨z', by simpa [z'] using hzlen, ?_⟩
  intro i
  simp only [z', SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.getVert_map,
    SimpleGraph.Walk.getVert_reverse]
  change φ (b⁻¹ * z.getVert (z.length - i)) = r.getVert (r.length - i)
  rw [map_mul, map_inv, hφb, inv_one, one_mul, hz, hzlen]

set_option backward.isDefEq.respectTransparency false in
/-- The nontrivial-voltage part of Lemma 1.2. A compatible pair of lifted lobes
with commuting, conjugate endpoints always produces a symmetric figure-eight. -/
theorem hasSymmetricFigureEight_of_nontrivial_compatible_lifts
    {G Q : Type*} [Group G] [Group Q] (hodd : Odd (Nat.card G))
    (φ : G →* Q) {S : Set G} {T : Set Q}
    (p r : (SimpleGraph.mulCayley T).Walk 1 1) (hp : p.IsCycle) (hr : r.IsCycle)
    (hdisj : ∀ x, (x ∈ p.support ∧ x ∈ r.support) ↔ x = 1)
    {a b u : G} (ha : a ≠ 1) (hb : b ≠ 1) (hcomm : Commute a b)
    (hφa : φ a = 1) (hφb : φ b = 1) (hconj : u⁻¹ * a * u = b)
    (w : (SimpleGraph.mulCayley S).Walk 1 a)
    (z : (SimpleGraph.mulCayley S).Walk 1 b)
    (hwlen : w.length = p.length) (hzlen : z.length = r.length)
    (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    (hz : ∀ i, φ (z.getVert i) = r.getVert i)
    (n : ℕ) (hn : 1 ≤ n) (hplen : p.length = 2 ^ n) (hrlen : r.length = 2 ^ n) :
    HasSymmetricFigureEight S := by
  by_cases hab : a = b
  · clear hconj
    subst b
    exact hasSymmetricFigureEight_of_equal_voltage_lifts hodd φ p r hp hr hdisj ha hφa
      w z hwlen hzlen hw hz n hn hplen hrlen
  obtain ⟨z', hz'len, hz'⟩ := exists_inverse_voltage_lift φ r hφb z hzlen hz
  have hdisj' : ∀ x, (x ∈ p.support ∧ x ∈ r.reverse.support) ↔ x = 1 := by
    simpa using hdisj
  have hφbi : φ b⁻¹ = 1 := by simp [hφb]
  have hbi : b⁻¹ ≠ 1 := by simpa using hb
  have hrlen' : r.reverse.length = 2 ^ n := by simpa using hrlen
  by_cases habi : a = b⁻¹
  · clear hconj
    subst a
    exact hasSymmetricFigureEight_of_equal_voltage_lifts hodd φ p r.reverse hp hr.reverse
      hdisj' hbi hφbi w z' hwlen hz'len hw hz' n hn hplen hrlen'
  obtain hescape | hescape := conjugate_products_escape_inverse_set hodd ha hb hconj
  · exact hasSymmetricFigureEight_of_commutator_lifts hodd φ p r hp hr hdisj
      ha hb hab habi hcomm hφa hφb hescape w z hwlen hzlen hw hz n hn hplen hrlen
  · have hescape' : a * b⁻¹ ∉ ({a, a⁻¹, b⁻¹, (b⁻¹)⁻¹} : Set G) := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, inv_inv,
        or_assoc, or_left_comm, or_comm] using hescape
    exact hasSymmetricFigureEight_of_commutator_lifts hodd φ p r.reverse hp hr.reverse hdisj'
      ha hbi habi (by simpa using hab) hcomm.inv_right hφa hφbi hescape'
      w z' hwlen hz'len hw hz' n hn hplen hrlen'

end CayleyErdosGyarfas

-- ===== from CayleyErdosGyarfas/CompatibleLifts.lean =====
/-! Compatible lifts of translated quotient cycles. -/


namespace CayleyErdosGyarfas

open SimpleGraph
open scoped IsMulCommutative

/-- In a nonempty closed walk, deleting the repeated initial vertex does
not change the set of vertices. -/
theorem closed_walk_mem_support_tail_iff
    {V : Type*} {Γ : SimpleGraph V} {v x : V} (c : Γ.Walk v v) (hc : ¬ c.Nil) :
    x ∈ c.support.tail ↔ x ∈ c.support := by
  rw [c.mem_support_iff]
  constructor
  · exact Or.inr
  · rintro (rfl | h)
    · exact c.end_mem_tail_support hc
    · exact h

set_option backward.isDefEq.respectTransparency false in
/-- A symmetric figure-eight can be described by a single cycle based at
the identity and a translated support meeting it only at the identity. -/
theorem HasSymmetricFigureEight.exists_cycle_translate_based_one
    {Q : Type*} [Group Q] {T : Set Q} (hfigure : HasSymmetricFigureEight T) :
    ∃ (n : ℕ) (p : (mulCayley T).Walk 1 1) (g : Q),
      1 ≤ n ∧ p.IsCycle ∧ p.length = 2 ^ n ∧
      ∀ x : Q, (x ∈ p.support ∧ ∃ y ∈ p.support, g * y = x) ↔ x = 1 := by
  obtain ⟨n, v, α, β, hn, hα, hβ, hαlen, _, ⟨g, hrot⟩, hmeet⟩ := hfigure
  have hβsupport (x : Q) : x ∈ β.support ↔ ∃ y ∈ α.support, g * y = x := by
    rw [← closed_walk_mem_support_tail_iff β hβ.not_nil, ← hrot.mem_iff]
    simp only [List.mem_map, closed_walk_mem_support_tail_iff α hα.not_nil]
  have horiginal (x : Q) :
      (x ∈ α.support ∧ ∃ y ∈ α.support, g * y = x) ↔ x = v := by
    simpa only [hβsupport] using hmeet x
  let f := (cayleyLeftTranslation T v⁻¹).toHom
  let p : (mulCayley T).Walk 1 1 := (α.map f).copy (inv_mul_cancel v) (inv_mul_cancel v)
  have hpsupport (x : Q) : x ∈ p.support ↔ ∃ y ∈ α.support, v⁻¹ * y = x := by
    simp only [p, Walk.support_copy, Walk.support_map, List.mem_map]
    rfl
  refine ⟨n, p, v⁻¹ * g * v, Nat.le_trans (by decide : 1 ≤ 2) hn, ?_, by simpa [p] using hαlen, ?_⟩
  · rw [Walk.isCycle_copy]
    exact hα.map (fun _ _ h ↦ mul_left_cancel h)
  · intro x
    constructor
    · rintro ⟨hx, y, hy, heq⟩
      obtain ⟨u, hu, hux⟩ := (hpsupport x).mp hx
      obtain ⟨z, hz, hzy⟩ := (hpsupport y).mp hy
      have hgzu : g * z = u := by
        apply mul_left_cancel (a := v⁻¹)
        calc
          v⁻¹ * (g * z) = (v⁻¹ * g * v) * y := by rw [← hzy]; group
          _ = x := heq
          _ = v⁻¹ * u := hux.symm
      have huv : u = v := (horiginal u).mp ⟨hu, z, hz, hgzu⟩
      simpa [huv] using hux.symm
    · rintro rfl
      have hv := (horiginal v).mpr rfl
      obtain ⟨z, hz, hgz⟩ := hv.2
      refine ⟨p.start_mem_support, v⁻¹ * z, (hpsupport _).mpr ⟨z, hz, rfl⟩, ?_⟩
      calc
        (v⁻¹ * g * v) * (v⁻¹ * z) = v⁻¹ * (g * z) := by group
        _ = 1 := by rw [hgz]; simp

/-- A closed lift of a simple cycle is itself simple. -/
theorem closed_lift_isCycle
    {G Q : Type*} [Group G] [Group Q] (φ : G →* Q)
    {S : Set G} {T : Set Q} {v : G} {q : Q}
    (p : (mulCayley T).Walk q q) (hp : p.IsCycle)
    (w : (mulCayley S).Walk v v)
    (hlen : w.length = p.length) (hmap : ∀ i, φ (w.getVert i) = p.getVert i) :
    w.IsCycle := by
  have hthree : 3 ≤ w.length := by simpa [hlen] using hp.three_le_length
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨?_, hthree⟩
  apply (Walk.IsPath.getVert_injOn_iff w.tail).mp
  intro i hi j hj hij
  simp only [Set.mem_ofPred_eq, Walk.length_tail] at hi hj
  have heq : p.getVert (i + 1) = p.getVert (j + 1) := by
    simpa only [Walk.getVert_tail, hmap] using congrArg φ hij
  have := hp.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega) heq
  omega

/-- Concatenating two compatible lifts preserves the pointwise projection. -/
theorem append_lifts_getVert
    {G Q : Type*} [Group G] [Group Q] (φ : G →* Q)
    {S : Set G} {T : Set Q} {a b c : G} {u v w : Q}
    (p : (mulCayley T).Walk u v) (r : (mulCayley T).Walk v w)
    (α : (mulCayley S).Walk a b) (β : (mulCayley S).Walk b c)
    (hlen : α.length = p.length)
    (hα : ∀ i, φ (α.getVert i) = p.getVert i)
    (hβ : ∀ i, φ (β.getVert i) = r.getVert i) :
    ∀ i, φ ((α.append β).getVert i) = (p.append r).getVert i := by
  intro i
  simp only [Walk.getVert_append, hlen]
  split <;> simp_all

/-- A closed lifted lobe and the translate coming from its lifted change
of basepoint already give a symmetric figure-eight. -/
theorem figureEight_of_closed_compatible_lift
    {G Q : Type*} [Group G] [Group Q] (φ : G →* Q)
    {S : Set G} {T : Set Q}
    (p : (mulCayley T).Walk 1 1) (hp : p.IsCycle) (g : Q)
    (hmeet : ∀ x : Q, (x ∈ p.support ∧ ∃ y ∈ p.support, g * y = x) ↔ x = 1)
    (w : (mulCayley S).Walk 1 1)
    (hwlen : w.length = p.length) (hw : ∀ i, φ (w.getVert i) = p.getVert i)
    (u : G) (hu : u ∈ w.support) (hφu : φ u = g⁻¹)
    (n : ℕ) (hn : 1 ≤ n) (hplen : p.length = 2 ^ n) :
    HasSymmetricFigureEight S := by
  have hsupport : ∀ y ∈ w.support, φ y ∈ p.support := by
    intro y hy
    obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hy
    rw [hw]
    exact p.getVert_mem_support i
  apply hasSymmetricFigureEight_of_cycle_translate w n hn
    (closed_lift_isCycle φ p hp w hwlen hw) (hwlen.trans hplen) u⁻¹ 1
  intro x
  constructor
  · rintro ⟨hx, y, hy, hyx⟩
    have hφx : φ x = 1 := (hmeet (φ x)).mp
      ⟨hsupport x hx, φ y, hsupport y hy, by
        simpa [map_mul, map_inv, hφu] using congrArg φ hyx⟩
    obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    have hpi : p.getVert i = 1 := by rw [← hw, hix, hφx]
    rcases (hp.getVert_endpoint_iff (by omega)).mp hpi with hi0 | hil
    · simpa [hi0] using hix.symm
    · rw [← hwlen] at hil
      simpa [hil] using hix.symm
  · rintro rfl
    exact ⟨w.start_mem_support, u, hu, inv_mul_cancel u⟩

set_option backward.isDefEq.respectTransparency false in
/-- Lift the two lobes compatibly by lifting the two pieces of one lobe.
The second voltage is conjugate to the first. A trivial first voltage
already produces a symmetric figure-eight upstairs. -/
theorem compatible_lifts_or_figureEight
    {G Q : Type*} [Group G] [Group Q] (φ : G →* Q) (S : Set G)
    (p : (mulCayley (φ '' S)).Walk 1 1) (hp : p.IsCycle) (g : Q)
    (hmeet : ∀ x : Q, (x ∈ p.support ∧ ∃ y ∈ p.support, g * y = x) ↔ x = 1)
    (n : ℕ) (hn : 1 ≤ n) (hplen : p.length = 2 ^ n) :
    HasSymmetricFigureEight S ∨
    ∃ (r : (mulCayley (φ '' S)).Walk 1 1) (a b u : G)
      (w : (mulCayley S).Walk 1 a) (z : (mulCayley S).Walk 1 b),
      r.IsCycle ∧ r.length = p.length ∧
      (∀ q, (q ∈ p.support ∧ q ∈ r.support) ↔ q = 1) ∧
      a ≠ 1 ∧ b ≠ 1 ∧ φ a = 1 ∧ φ b = 1 ∧ u⁻¹ * a * u = b ∧
      w.length = p.length ∧ z.length = r.length ∧
      (∀ i, φ (w.getVert i) = p.getVert i) ∧
      (∀ i, φ (z.getVert i) = r.getVert i) := by
  classical
  have hginv : g⁻¹ ∈ p.support := by
    obtain ⟨q, hq, hgq⟩ := ((hmeet 1).mpr rfl).2
    rwa [eq_inv_of_mul_eq_one_right hgq] at hq
  let p₁ := p.takeUntil g⁻¹ hginv
  let p₂ := p.dropUntil g⁻¹ hginv
  obtain ⟨u, w₁, hw₁len, hw₁⟩ := cayley_walk_image_lift φ S p₁ 1 (map_one φ)
  have hφu : φ u = g⁻¹ := by
    have := hw₁ w₁.length
    rw [Walk.getVert_length, hw₁len, Walk.getVert_length] at this
    exact this
  obtain ⟨a, w₂, hw₂len, hw₂⟩ := cayley_walk_image_lift φ S p₂ u hφu
  have hφa : φ a = 1 := by
    have := hw₂ w₂.length
    rw [Walk.getVert_length, hw₂len, Walk.getVert_length] at this
    exact this
  let w := w₁.append w₂
  have hsplit : p₁.append p₂ = p := p.take_spec hginv
  have hwlen : w.length = p.length := by
    simp only [w, Walk.length_append, hw₁len, hw₂len]
    rw [← Walk.length_append, hsplit]
  have hw : ∀ i, φ (w.getVert i) = p.getVert i := by
    intro i
    rw [← hsplit]
    exact append_lifts_getVert φ p₁ p₂ w₁ w₂ hw₁len hw₁ hw₂ i
  by_cases ha : a = 1
  · subst a
    exact Or.inl (figureEight_of_closed_compatible_lift φ p hp g hmeet w hwlen hw
      u ((Walk.mem_support_append_iff w₁ w₂).mpr (Or.inl w₁.end_mem_support)) hφu n hn hplen)
  right
  let b := u⁻¹ * a * u
  let f := (cayleyLeftTranslation (φ '' S) g).toHom
  let r : (mulCayley (φ '' S)).Walk 1 1 :=
    ((p₂.append p₁).map f).copy (mul_inv_cancel g) (mul_inv_cancel g)
  let f₁ := (cayleyLeftTranslation S u⁻¹).toHom
  let f₂ := (cayleyLeftTranslation S (u⁻¹ * a)).toHom
  let z₁ : (mulCayley S).Walk 1 (u⁻¹ * a) :=
    (w₂.map f₁).copy (inv_mul_cancel u) rfl
  let z₂ : (mulCayley S).Walk (u⁻¹ * a) b :=
    (w₁.map f₂).copy (mul_one (u⁻¹ * a)) rfl
  let z := z₁.append z₂
  have hr : r.IsCycle := by
    change (((p.rotate g⁻¹ hginv).map f).copy _ _).IsCycle
    rw [Walk.isCycle_copy]
    exact (hp.rotate hginv).map (fun _ _ h ↦ mul_left_cancel h)
  have hrlen : r.length = p.length := by
    change (((p.rotate g⁻¹ hginv).map f).copy _ _).length = _
    simp
  have hrsupport (q : Q) : q ∈ r.support ↔ ∃ y ∈ p.support, g * y = q := by
    change q ∈ (((p.rotate g⁻¹ hginv).map f).copy _ _).support ↔ _
    simp only [Walk.support_copy, Walk.support_map, List.mem_map,
      Walk.mem_support_rotate_iff]
    rfl
  have hb : b ≠ 1 := by
    intro hb
    apply ha
    have := congrArg (fun y : G ↦ u * y * u⁻¹) hb
    simpa [b, mul_assoc] using this
  have hφb : φ b = 1 := by simp [b, map_mul, hφa]
  have hzlen : z.length = r.length := by
    simp only [z, z₁, z₂, Walk.length_append, Walk.length_copy, Walk.length_map,
      hw₁len, hw₂len]
    rw [hrlen, ← hsplit, Walk.length_append, Nat.add_comm]
  have hz : ∀ i, φ (z.getVert i) = r.getVert i := by
    intro i
    simp only [z, z₁, z₂, r, Walk.getVert_append, Walk.getVert_copy,
      Walk.getVert_map, Walk.length_copy, Walk.length_map, hw₂len,
      Walk.getVert_append]
    change φ (if i < p₂.length then u⁻¹ * w₂.getVert i
      else (u⁻¹ * a) * w₁.getVert (i - p₂.length)) =
      g * (if i < p₂.length then p₂.getVert i else p₁.getVert (i - p₂.length))
    split
    · simp only [map_mul, map_inv, hφu, inv_inv, hw₂]
    · simp only [map_mul, map_inv, hφu, hφa, inv_inv, mul_one, hw₁]
  exact ⟨r, a, b, u, w, z, hr, hrlen,
    (fun q ↦ by simpa only [hrsupport] using hmeet q),
    ha, hb, hφa, hφb, rfl, hwlen, hzlen, hw, hz⟩

set_option backward.isDefEq.respectTransparency false in
/-- Lemma 1.2, in a strengthened form: inverse closure, generation and
identity exclusion are not needed to lift an existing symmetric figure-eight. -/
theorem symmetric_figure_eight_lifts
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hodd : Odd (Nat.card G))
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hfigure : HasSymmetricFigureEight
      ((QuotientGroup.mk (s := A)) '' S \ {1})) :
    HasSymmetricFigureEight S := by
  have himage : HasSymmetricFigureEight ((QuotientGroup.mk' A) '' S) := by
    unfold HasSymmetricFigureEight at hfigure ⊢
    rw [mulCayley_erase_one] at hfigure
    exact hfigure
  obtain ⟨n, p, g, hn, hp, hplen, hmeet⟩ := himage.exists_cycle_translate_based_one
  obtain h | ⟨r, a, b, u, w, z, hr, hrlen, hdisj, ha, hb, hφa, hφb,
      hconj, hwlen, hzlen, hw, hz⟩ :=
    compatible_lifts_or_figureEight (QuotientGroup.mk' A) S p hp g hmeet n hn hplen
  · exact h
  · have haA : a ∈ A := (QuotientGroup.eq_one_iff a).mp hφa
    have hbA : b ∈ A := (QuotientGroup.eq_one_iff b).mp hφb
    have hcomm : Commute a b := by
      exact congrArg Subtype.val (mul_comm (⟨a, haA⟩ : A) (⟨b, hbA⟩ : A))
    exact hasSymmetricFigureEight_of_nontrivial_compatible_lifts hodd
      (QuotientGroup.mk' A) p r hp hr hdisj ha hb hcomm hφa hφb hconj
      w z hwlen hzlen hw hz n hn hplen (hrlen.trans hplen)

end CayleyErdosGyarfas

-- ===== from CayleyErdosGyarfas/BaseCases.lean =====
/-!
# Proved elementary cases

These results supply the abelian case mentioned in the introduction, using
Mathlib's Cayley graph and simple-cycle definitions throughout.
-/


namespace CayleyErdosGyarfas

open SimpleGraph

/-- Distinct noninverse commuting generators produce the square
`1, s, s * t, t, 1` in the Cayley graph. -/
theorem four_cycle_of_commuting_generators_with_support
    {G : Type*} [Group G] (S : Set G) {s t : G}
    (hs : s ∈ S) (ht : t ∈ S) (hs1 : s ≠ 1) (ht1 : t ≠ 1)
    (hst : s ≠ t) (hsti : t ≠ s⁻¹) (hcomm : Commute s t) :
    ∃ c : (mulCayley S).Walk 1 1, c.IsCycle ∧ c.length = 4 ∧ c.support = [1, s, s * t, t, 1] := by
  have hprod : s * t ≠ 1 := by
    intro h
    exact hsti (eq_inv_of_mul_eq_one_right h)
  have ha : (mulCayley S).Adj 1 s := by
    rw [mulCayley_adj']
    exact ⟨Ne.symm hs1, s, hs, Or.inl (one_mul s)⟩
  have hb : (mulCayley S).Adj s (s * t) := by
    rw [mulCayley_adj']
    exact ⟨by simpa using ht1, t, ht, Or.inl rfl⟩
  have hc : (mulCayley S).Adj (s * t) t := by
    rw [mulCayley_adj']
    exact ⟨by simpa using hs1, s, hs, Or.inr hcomm.eq⟩
  have hd : (mulCayley S).Adj t 1 := by
    rw [mulCayley_adj']
    exact ⟨ht1, t, ht, Or.inr (one_mul t).symm⟩
  let c : (mulCayley S).Walk 1 1 := .cons ha (.cons hb (.cons hc (.cons hd .nil)))
  refine ⟨c, ?_, rfl, rfl⟩
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · rw [Walk.isPath_def]
    simp [c, hs1, ht1, hst, hprod]
  · simp [c]

/-- The square construction, with only its simplicity and length retained. -/
theorem four_cycle_of_commuting_generators
    {G : Type*} [Group G] (S : Set G) {s t : G}
    (hs : s ∈ S) (ht : t ∈ S) (hs1 : s ≠ 1) (ht1 : t ≠ 1)
    (hst : s ≠ t) (hsti : t ≠ s⁻¹) (hcomm : Commute s t) :
    ∃ c : (mulCayley S).Walk 1 1, c.IsCycle ∧ c.length = 4 := by
  obtain ⟨c, hc, hlen, _⟩ := four_cycle_of_commuting_generators_with_support
    S hs ht hs1 ht1 hst hsti hcomm
  exact ⟨c, hc, hlen⟩

/-- Every Cayley graph of a finite abelian group with at least three
nonidentity generators contains a simple four-cycle. -/
theorem abelian_cayley_contains_four_cycle
    {G : Type*} [CommGroup G] [Finite G] (S : Set G)
    (hone : (1 : G) ∉ S) (hcard : 3 ≤ S.ncard) :
    ∃ c : (mulCayley S).Walk 1 1, c.IsCycle ∧ c.length = 4 := by
  classical
  obtain ⟨s, hs⟩ := (Set.ncard_pos (s := S)).mp (show 0 < S.ncard by omega)
  have hpair : ({s, s⁻¹} : Set G).ncard ≤ 2 := by
    simpa using Set.ncard_insert_le s ({s⁻¹} : Set G)
  obtain ⟨t, ht, htout⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show ({s, s⁻¹} : Set G).ncard < S.ncard by omega)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at htout
  exact four_cycle_of_commuting_generators S hs ht
    (fun h ↦ hone (h ▸ hs)) (fun h ↦ hone (h ▸ ht))
    (Ne.symm htout.1) htout.2 (Commute.all s t)

/-- The abelian case of the manuscript's power-of-two cycle conclusion. -/
theorem abelian_cayley_contains_two_power_cycle
    {G : Type*} [CommGroup G] [Finite G] (S : Set G)
    (hone : (1 : G) ∉ S) (hcard : 3 ≤ S.ncard) :
    ∃ (n : ℕ) (v : G) (c : (mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  obtain ⟨c, hc, hlen⟩ := abelian_cayley_contains_four_cycle S hone hcard
  exact ⟨2, 1, c, by decide, hc, hlen⟩

/-- The powers of a generator of order at least three form a simple cycle. -/
theorem generator_order_cycle
    {G : Type*} [Group G] (S : Set G) {s : G}
    (hs : s ∈ S) (horder : 3 ≤ orderOf s) :
    ∃ (v : G) (c : (mulCayley S).Walk v v), c.IsCycle ∧ c.length = orderOf s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at horder
  apply exists_cycle_of_sequence horder (s ^ ·)
  · simp
  · intro i hi
    rw [mulCayley_adj']
    refine ⟨?_, s, hs, Or.inl (pow_succ s i).symm⟩
    simpa [pow_succ] using hs1
  · intro i hi j hj heq
    exact pow_injOn_Iio_orderOf hi hj heq

/-- If a generator of a 2-group has order at least three, its own orbit
already supplies a power-of-two cycle. -/
theorem two_group_cycle_of_generator_order
    {G : Type*} [Group G] (hG : IsPGroup 2 G) (S : Set G) {s : G}
    (hs : s ∈ S) (horder : 3 ≤ orderOf s) :
    ∃ (n : ℕ) (v : G) (c : (mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  obtain ⟨n, hn⟩ := hG.exists_orderOf_eq_pow s
  obtain ⟨v, c, hc, hlen⟩ := generator_order_cycle S hs horder
  refine ⟨n, v, c, ?_, hc, hlen.trans hn⟩
  by_contra hn0
  have : n = 0 := by omega
  have horder1 : orderOf s = 1 := by simpa [this] using hn
  omega

/-- Two noncommuting generators trace a simple alternating cycle.
The vertex sequence is `(s*t)^i, (s*t)^i*s`. -/
theorem alternating_cycle_of_noncommuting_generators
    {G : Type*} [Group G] [Finite G] (S : Set G) {s t : G}
    (hs : s ∈ S) (ht : t ∈ S)
    (hnc : ¬ Commute s t) :
    ∃ (v : G) (c : (mulCayley S).Walk v v),
      c.IsCycle ∧ c.length = 2 * orderOf (s * t) := by
  have hs1 : s ≠ 1 := by intro h; apply hnc; simp [h]
  have ht1 : t ≠ 1 := by intro h; apply hnc; simp [h]
  have hpos := orderOf_pos (s * t)
  have hnot : orderOf (s * t) ≠ 1 := by
    intro h
    have htinv : t = s⁻¹ := eq_inv_of_mul_eq_one_right (orderOf_eq_one_iff.mp h)
    apply hnc
    rw [htinv]
    exact (Commute.refl s).inv_right
  have hcross : ∀ i j : ℕ, (s * t) ^ i ≠ (s * t) ^ j * s := by
    intro i j heq
    have hs_eq : s = ((s * t) ^ j)⁻¹ * (s * t) ^ i :=
      eq_inv_mul_iff_mul_eq.mpr heq.symm
    have hh : Commute (s * t) s := by
      nth_rw 2 [hs_eq]
      exact (((Commute.refl (s * t)).pow_right j).inv_right).mul_right
        ((Commute.refl (s * t)).pow_right i)
    apply hnc
    change s * t = t * s
    exact (mul_left_cancel (by simpa only [mul_assoc] using hh.eq)).symm
  let f : ℕ → G := fun i ↦
    if i % 2 = 0 then (s * t) ^ (i / 2) else (s * t) ^ (i / 2) * s
  apply exists_cycle_of_sequence (by omega) f
  · simp [f]
  · intro i hi
    by_cases hi0 : i % 2 = 0
    · have his : (i + 1) % 2 ≠ 0 := by omega
      have hid : (i + 1) / 2 = i / 2 := by omega
      simp only [f, hi0, his, hid, ite_true, ite_false]
      rw [mulCayley_adj']
      exact ⟨by simpa using hs1, s, hs, Or.inl rfl⟩
    · have his : (i + 1) % 2 = 0 := by omega
      have hid : (i + 1) / 2 = i / 2 + 1 := by omega
      simp only [f, hi0, his, hid, ite_true, ite_false, pow_succ]
      rw [mulCayley_adj']
      refine ⟨?_, t, ht, Or.inl (mul_assoc _ _ _)⟩
      simpa [← mul_assoc] using ht1
  · intro i hi j hj heq
    have hid : i / 2 < orderOf (s * t) := by omega
    have hjd : j / 2 < orderOf (s * t) := by omega
    by_cases hi0 : i % 2 = 0 <;> by_cases hj0 : j % 2 = 0
    · simp only [f, hi0, hj0, ite_true] at heq
      have := pow_injOn_Iio_orderOf hid hjd heq
      omega
    · simp only [f, hi0, hj0, ite_true, ite_false] at heq
      exact (hcross _ _ heq).elim
    · simp only [f, hi0, hj0, ite_true, ite_false] at heq
      exact (hcross _ _ heq.symm).elim
    · simp only [f, hi0, hj0, ite_false] at heq
      have heqpow := mul_right_cancel heq
      have := pow_injOn_Iio_orderOf hid hjd heqpow
      omega

/-- The pure 2-group case of Corollary 1.4.
Choose distinct noninverse generators. If they commute they give a square;
otherwise their alternating cycle has twice the order of their product. -/
theorem two_group_cayley_contains_two_power_cycle
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G) (S : Set G)
    (hone : (1 : G) ∉ S) (hcard : 3 ≤ S.ncard) :
    ∃ (n : ℕ) (v : G) (c : (mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  classical
  obtain ⟨s, hs⟩ := (Set.ncard_pos (s := S)).mp (show 0 < S.ncard by omega)
  have hpair : ({s, s⁻¹} : Set G).ncard ≤ 2 := by
    simpa using Set.ncard_insert_le s ({s⁻¹} : Set G)
  obtain ⟨t, ht, htout⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show ({s, s⁻¹} : Set G).ncard < S.ncard by omega)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at htout
  by_cases hcomm : Commute s t
  · obtain ⟨c, hc, hlen⟩ := four_cycle_of_commuting_generators S hs ht
      (fun h ↦ hone (h ▸ hs)) (fun h ↦ hone (h ▸ ht))
      (Ne.symm htout.1) htout.2 hcomm
    exact ⟨2, 1, c, by decide, hc, hlen⟩
  · obtain ⟨v, c, hc, hlen⟩ := alternating_cycle_of_noncommuting_generators S hs ht hcomm
    obtain ⟨n, hn⟩ := hG.exists_orderOf_eq_pow (s * t)
    refine ⟨n + 1, v, c, by omega, hc, ?_⟩
    rw [hlen, hn, pow_succ, Nat.mul_comm]

end CayleyErdosGyarfas

-- ===== from CayleyErdosGyarfas/CyclicCase.lean =====
/-! The commuting square construction used in the cyclic quotient case. -/


namespace CayleyErdosGyarfas

open SimpleGraph

/-- A commuting square and its diagonal translate meet only at the diagonal
vertex when the diagonal product avoids the generators and their inverses. -/
theorem symmetric_figure_eight_of_commuting_square
    {G : Type*} [CommGroup G] (hodd : Odd (Nat.card G)) (S : Set G)
    {a b : G} (ha : a ∈ S) (hb : b ∈ S) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hbinv : b ≠ a⁻¹)
    (hescape : a * b ∉ ({a, a⁻¹, b, b⁻¹} : Set G)) :
    HasSymmetricFigureEight S := by
  obtain ⟨c, hc, hlen, hsupp⟩ := four_cycle_of_commuting_generators_with_support
    S ha hb ha1 hb1 hab hbinv (Commute.all a b)
  have hsquare : Function.Injective (fun z : G ↦ z ^ 2) :=
    hodd.coprime_two_right.pow_left_bijective.1
  have hprod : a * b ≠ 1 := fun h ↦ hbinv (eq_inv_of_mul_eq_one_right h)
  have hsq (z : G) (hz : z ≠ 1) : z * z ≠ 1 := by
    intro h
    exact hz (hsquare (by simpa only [pow_two, one_mul] using h : z ^ 2 = (1 : G) ^ 2))
  have haesc : a * b ≠ a⁻¹ := fun h ↦ hescape (by simp [h])
  have hbesc : a * b ≠ b⁻¹ := fun h ↦ hescape (by simp [h])
  apply hasSymmetricFigureEight_of_cycle_translate c 2 (by decide) hc hlen (a * b) (a * b)
  intro x
  have hmem (z : G) : z ∈ c.support ↔ z = 1 ∨ z = a ∨ z = a * b ∨ z = b := by
    simp [hsupp, or_assoc, or_left_comm, or_comm]
  simp only [hmem]
  constructor
  · rintro ⟨hx, y, hy, heq⟩
    rcases hx with hx | hx | hx | hx <;> rw [hx] at heq ⊢
    · rcases hy with hy | hy | hy | hy <;> rw [hy] at heq
      · exact (hprod (by simpa using heq)).elim
      · exact (haesc (eq_inv_of_mul_eq_one_left heq)).elim
      · exact (hsq (a * b) hprod heq).elim
      · exact (hbesc (eq_inv_of_mul_eq_one_left heq)).elim
    · rcases hy with hy | hy | hy | hy <;> rw [hy] at heq
      · exact (hb1 (mul_left_cancel (by simpa using heq : a * b = a * 1))).elim
      · exact (hprod (mul_right_cancel (by simpa using heq : (a * b) * a = 1 * a))).elim
      · have h : (a * b) * b = 1 := by
          apply mul_left_cancel (a := a)
          simpa [mul_assoc, mul_left_comm, mul_comm] using heq
        exact (hbesc (eq_inv_of_mul_eq_one_left h)).elim
      · have h : b * b = 1 := by
          apply mul_left_cancel (a := a)
          simpa [mul_assoc] using heq
        exact (hsq b hb1 h).elim
    · rcases hy with hy | hy | hy | hy <;> rw [hy] at heq
      · exact (ha1 (mul_right_cancel (by simpa using heq : a * b = 1 * b))).elim
      · have h : a * a = 1 := by
          apply mul_right_cancel (b := b)
          simpa [mul_assoc, mul_left_comm, mul_comm] using heq
        exact (hsq a ha1 h).elim
      · have h : (a * b) * a = 1 := by
          apply mul_right_cancel (b := b)
          simpa [mul_assoc, mul_left_comm, mul_comm] using heq
        exact (haesc (eq_inv_of_mul_eq_one_left h)).elim
      · exact (hprod (mul_right_cancel (by simpa using heq : (a * b) * b = 1 * b))).elim
  · rintro rfl
    exact ⟨Or.inr (Or.inr (Or.inl rfl)), 1, Or.inl rfl, mul_one _⟩

/-- The simultaneous endpoint collisions force the two generators to generate a group of order five. -/
theorem card_eq_five_of_inverse_square_generators {G : Type*} [Group G]
    {a b : G} (ha1 : a ≠ 1) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hb : b = (a * a)⁻¹) (ha : a = b * b) : Nat.card G = 5 := by
  have ha5 : a ^ 5 = 1 := calc
    a ^ 5 = (a * a) * (a * a) * a := by simp [pow_succ, mul_assoc]
    _ = (b * b)⁻¹ * a := by rw [hb]; simp only [mul_inv_rev, inv_inv, mul_assoc]
    _ = 1 := by rw [← ha]; simp
  have hz : Subgroup.zpowers a = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply (Subgroup.closure_le (Subgroup.zpowers a)).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst x
      exact Subgroup.mem_zpowers a
    · subst x
      rw [hb]
      exact (Subgroup.zpowers a).inv_mem
        ((Subgroup.zpowers a).mul_mem (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers a))
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ho : orderOf a = 5 := orderOf_eq_prime_iff.mpr ⟨ha5, ha1⟩
  exact (orderOf_eq_card_of_zpowers_eq_top hz).symm.trans ho


/-- One of the two diagonal products escapes the inverse set, unless the generated group has order five. -/
theorem generating_products_escape_inverse_set {G : Type*} [Group G]
    (hodd : Odd (Nat.card G)) {a b : G} (ha : a ≠ 1) (hb : b ≠ 1)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (hcard : Nat.card G ≠ 5) :
    a * b ∉ ({a, a⁻¹, b, b⁻¹} : Set G) ∨
      a * b⁻¹ ∉ ({a, a⁻¹, b, b⁻¹} : Set G) := by
  by_contra! h
  rcases h with ⟨h₁, h₂⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h₁ h₂
  have h₁' : a * b = a⁻¹ ∨ a * b = b⁻¹ := by
    rcases h₁ with h | h | h | h
    · exact False.elim (hb (mul_left_cancel (by simpa using h : a * b = a * 1)))
    · exact Or.inl h
    · exact False.elim (ha (mul_right_cancel (by simpa using h : a * b = 1 * b)))
    · exact Or.inr h
  have h₂' : a * b⁻¹ = a⁻¹ ∨ a * b⁻¹ = b := by
    rcases h₂ with h | h | h | h
    · have : b⁻¹ = 1 := mul_left_cancel (by simpa using h : a * b⁻¹ = a * 1)
      exact False.elim (hb (by simpa using this))
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (ha (mul_right_cancel (by simpa using h : a * b⁻¹ = 1 * b⁻¹)))
  have h₁'' : b = (a * a)⁻¹ ∨ a = (b * b)⁻¹ := by
    rcases h₁' with h | h
    · left
      calc b = a⁻¹ * (a * b) := by group
           _ = a⁻¹ * a⁻¹ := by rw [h]
           _ = (a * a)⁻¹ := by group
    · right
      calc a = (a * b) * b⁻¹ := by group
           _ = b⁻¹ * b⁻¹ := by rw [h]
           _ = (b * b)⁻¹ := by group
  have h₂'' : b = a * a ∨ a = b * b := by
    rcases h₂' with h | h
    · left
      calc b = (a * b⁻¹)⁻¹ * a := by group
           _ = (a⁻¹)⁻¹ * a := by rw [h]
           _ = a * a := by simp
    · right
      calc a = (a * b⁻¹) * b := by group
           _ = b * b := by rw [h]
  rcases h₁'' with h₁ | h₁ <;> rcases h₂'' with h₂ | h₂
  · have hsq : a ^ 2 = (a⁻¹) ^ 2 := by simpa [pow_two, mul_inv_rev] using h₂.symm.trans h₁
    have hinv := square_injective_of_odd_natCard hodd hsq
    exact ha (eq_one_of_conjugate_inv_of_odd_natCard hodd (g := 1) (by simpa using hinv))
  · exact hcard (card_eq_five_of_inverse_square_generators ha hgen h₁ h₂)
  · have hgen' : Subgroup.closure ({b, a} : Set G) = ⊤ := by simpa only [Set.pair_comm b a] using hgen
    exact hcard (card_eq_five_of_inverse_square_generators hb hgen' h₁ h₂)
  · have hsq : b ^ 2 = (b⁻¹) ^ 2 := by simpa [pow_two, mul_inv_rev] using h₂.symm.trans h₁
    have hinv := square_injective_of_odd_natCard hodd hsq
    exact hb (eq_one_of_conjugate_inv_of_odd_natCard hodd (g := 1) (by simpa using hinv))

/-- The cyclic-quotient square case of the manuscript. The conclusion in fact
holds for any abelian group generated by the two chosen elements, except for
the five-element obstruction to this particular figure-eight construction. -/
theorem symmetric_figure_eight_of_two_generators_not_five
    {G : Type*} [CommGroup G] (hodd : Odd (Nat.card G)) (hcard : Nat.card G ≠ 5)
    (S : Set G) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    {a b : G} (ha : a ∈ S) (hb : b ∈ S) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hbinv : b ≠ a⁻¹)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    HasSymmetricFigureEight S := by
  obtain hescape | hescape := generating_products_escape_inverse_set hodd ha1 hb1 hgen hcard
  · exact symmetric_figure_eight_of_commuting_square hodd S ha hb ha1 hb1 hab hbinv hescape
  · have habi : a ≠ b⁻¹ := by
      intro h
      exact hbinv (by simpa only [inv_inv] using congrArg Inv.inv h.symm)
    have hbinv' : b⁻¹ ≠ a⁻¹ := fun h ↦ hab (inv_injective h).symm
    have hescape' : a * b⁻¹ ∉ ({a, a⁻¹, b⁻¹, (b⁻¹)⁻¹} : Set G) := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, inv_inv,
        or_assoc, or_left_comm, or_comm] using hescape
    exact symmetric_figure_eight_of_commuting_square hodd S ha (hinv b hb) ha1
      (by simpa using hb1) habi hbinv' hescape'

end CayleyErdosGyarfas

-- ===== from CayleyErdosGyarfas/MainReduction.lean =====
/-! Reductions for the odd-order theorem, including the noncyclic abelian base case. -/


namespace CayleyErdosGyarfas

open SimpleGraph

/-- A subgroup of an odd-order group contains the square roots of its elements. -/
theorem mem_subgroup_of_square_mem {G : Type*} [Group G]
    (hodd : Odd (Nat.card G)) (H : Subgroup G) {x : G} (hx : x ^ 2 ∈ H) : x ∈ H := by
  have hH : Odd (Nat.card H) := hodd.of_dvd_nat H.card_subgroup_dvd_card
  obtain ⟨y, hy⟩ := hH.coprime_two_right.pow_left_bijective.2 (⟨x ^ 2, hx⟩ : H)
  have hy' : (y : G) ^ 2 = x ^ 2 := congrArg Subtype.val hy
  have heq : (y : G) = x := hodd.coprime_two_right.pow_left_bijective.1 hy'
  exact heq ▸ y.property

/-- In the abelian base case, choosing the second generator outside the
cyclic subgroup generated by the first makes the two squares meet once. -/
theorem abelian_noncyclic_symmetric_figure_eight
    {G : Type*} [CommGroup G] (S : Set G) (hodd : Odd (Nat.card G))
    (hone : (1 : G) ∉ S) (hgen : Subgroup.closure S = ⊤) (hncyc : ¬ IsCyclic G) :
    HasSymmetricFigureEight S := by
  classical
  have hSne : S.Nonempty := by
    by_contra h
    have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have htop : (⊥ : Subgroup G) = ⊤ := by simpa [hempty] using hgen
    exact hncyc (isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨1, by simpa only [Subgroup.zpowers_one_eq_bot] using htop⟩)
  obtain ⟨a, ha⟩ := hSne
  have houtside : ∃ b ∈ S, b ∉ Subgroup.zpowers a := by
    by_contra! h
    have hz : Subgroup.zpowers a = ⊤ := top_unique (by
      rw [← hgen]
      exact (Subgroup.closure_le _).mpr h)
    exact hncyc (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨a, hz⟩)
  obtain ⟨b, hb, hba⟩ := houtside
  have ha1 : a ≠ 1 := fun h ↦ hone (h ▸ ha)
  have hb1 : b ≠ 1 := fun h ↦ hone (h ▸ hb)
  have ham : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
  apply symmetric_figure_eight_of_commuting_square hodd S ha hb ha1 hb1
    (fun h ↦ hba (h ▸ ham))
    (fun h ↦ hba (h ▸ (Subgroup.zpowers a).inv_mem ham))
  intro hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hab
  rcases hab with hab | hab | hab | hab
  · exact hb1 (mul_left_cancel (by simpa using hab : a * b = a * 1))
  · have h : b = a⁻¹ * a⁻¹ := eq_inv_mul_iff_mul_eq.mpr hab
    exact hba (h ▸ (Subgroup.zpowers a).mul_mem
      ((Subgroup.zpowers a).inv_mem ham) ((Subgroup.zpowers a).inv_mem ham))
  · exact ha1 (mul_right_cancel (by simpa using hab : a * b = 1 * b))
  · have h : b ^ 2 = a⁻¹ := by
      apply mul_left_cancel (a := a)
      simpa [pow_two, mul_assoc] using congrArg (· * b) hab
    exact hba (mem_subgroup_of_square_mem hodd (Subgroup.zpowers a)
      (h ▸ (Subgroup.zpowers a).inv_mem ham))

/-- Symmetric figure-eights are preserved by injective group homomorphisms
whose images of the allowed generators remain allowed generators. -/
theorem HasSymmetricFigureEight.map
    {G H : Type*} [Group G] [Group H] {S : Set G} {T : Set H}
    (h : HasSymmetricFigureEight S) (f : G →* H) (hf : Function.Injective f)
    (hST : ∀ s ∈ S, f s ∈ T) : HasSymmetricFigureEight T := by
  let φ : mulCayley S →g mulCayley T := {
    toFun := f
    map_rel' := by
      intro a b hab
      rw [mulCayley_adj] at hab ⊢
      refine ⟨fun he ↦ hab.1 (hf he), ?_⟩
      rcases hab.2 with hab | hab
      · exact Or.inl (by simpa using hST _ hab)
      · exact Or.inr (by simpa using hST _ hab) }
  obtain ⟨n, v, α, β, hn, hα, hβ, hαlen, hβlen, ⟨g, hg⟩, hinter⟩ := h
  refine ⟨n, f v, α.map φ, β.map φ, hn,
    hα.map hf, hβ.map hf, by simpa using hαlen, by simpa using hβlen, ?_, ?_⟩
  · refine ⟨f g, ?_⟩
    rw [Walk.support_map, Walk.support_map]
    change List.IsRotated ((α.support.map f).tail.map (f g * ·)) (β.support.map f).tail
    simpa only [List.map_tail, List.map_map, Function.comp_def, map_mul] using hg.map f
  · intro w
    simp only [Walk.support_map, List.mem_map]
    constructor
    · rintro ⟨⟨x, hx, hxw⟩, y, hy, hyw⟩
      have heq : x = y := hf (hxw.trans hyw.symm)
      have hxv := (hinter x).mp ⟨hx, heq ▸ hy⟩
      exact hxw.symm.trans (congrArg f hxv)
    · rintro rfl
      exact ⟨⟨v, α.start_mem_support, rfl⟩, v, β.start_mem_support, rfl⟩

/-- The original generators generate their subgroup after restricting the
ambient type to that subgroup. -/
theorem closure_preimage_subtype_eq_top
    {G : Type*} [Group G] (S : Set G) (H : Subgroup G)
    (hS : S ⊆ H) (hH : H ≤ Subgroup.closure S) :
    Subgroup.closure (H.subtype ⁻¹' S) = ⊤ := by
  apply top_unique
  intro x _
  have hx : (x : G) ∈ Subgroup.closure S := hH x.property
  have hle : Subgroup.closure S ≤
      (Subgroup.closure (H.subtype ⁻¹' S)).map H.subtype := by
    apply (Subgroup.closure_le _).mpr
    intro s hs
    exact ⟨⟨s, hS hs⟩, Subgroup.subset_closure hs, rfl⟩
  obtain ⟨y, hy, heq⟩ := hle hx
  exact (Subtype.ext heq : y = x) ▸ hy

/-- Noncommutativity is already witnessed by two members of any generating set. -/
theorem exists_noncommuting_generators
    {G : Type*} [Group G] (S : Set G) (hgen : Subgroup.closure S = ⊤)
    (hncomm : ¬ IsMulCommutative G) : ∃ s ∈ S, ∃ t ∈ S, ¬ Commute s t := by
  by_contra! h
  have : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure (fun a ha b hb ↦ (h a ha b hb).eq)
  apply hncomm
  apply IsMulCommutative.of_comm
  intro a b
  have ha : a ∈ Subgroup.closure S := by rw [hgen]; trivial
  have hb : b ∈ Subgroup.closure S := by rw [hgen]; trivial
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Subgroup.closure S) ⟨b, hb⟩)

open scoped IsMulCommutative in
/-- The minimal-counterexample argument is a strong induction on the order
of the group. It reduces the noncyclic theorem to two-generator nonabelian
groups whose nontrivial abelian normal quotients are all cyclic. -/
theorem noncyclic_figure_eight_of_minimal_case.{u}
    (hcase : ∀ {G : Type u} [Group G] [Finite G] (S : Set G),
      Odd (Nat.card G) → (∀ s ∈ S, s⁻¹ ∈ S) → (1 : G) ∉ S →
      ¬ IsMulCommutative G →
      (∀ (A : Subgroup G) [A.Normal] [IsMulCommutative A], A ≠ ⊥ → IsCyclic (G ⧸ A)) →
      ∀ {s t : G}, s ∈ S → t ∈ S → ¬ Commute s t →
        Subgroup.closure ({s, t} : Set G) = ⊤ → HasSymmetricFigureEight S)
    {G : Type u} [Group G] [Finite G] (S : Set G)
    (hodd : Odd (Nat.card G)) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hone : (1 : G) ∉ S) (hgen : Subgroup.closure S = ⊤) (hncyc : ¬ IsCyclic G) :
    HasSymmetricFigureEight S := by
  classical
  suffices h : ∀ n : ℕ, ∀ {G : Type u} [Group G] [Finite G] (S : Set G),
      Nat.card G = n → Odd (Nat.card G) → (∀ s ∈ S, s⁻¹ ∈ S) →
      (1 : G) ∉ S → Subgroup.closure S = ⊤ → ¬ IsCyclic G →
      HasSymmetricFigureEight S from h _ S rfl hodd hinv hone hgen hncyc
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ S hcard hodd hinv hone hgen hncyc
    by_contra hno
    have hncomm : ¬ IsMulCommutative G := by
      intro hc
      let := hc
      exact hno (abelian_noncyclic_symmetric_figure_eight S hodd hone hgen hncyc)
    obtain ⟨s, hs, t, ht, hnst⟩ := exists_noncommuting_generators S hgen hncomm
    let H := Subgroup.closure ({s, t} : Set G)
    have hsH : s ∈ H := Subgroup.subset_closure (by simp)
    have htH : t ∈ H := Subgroup.subset_closure (by simp)
    have hpair : H = ⊤ := by
      by_contra hproper
      have hlt : Nat.card H < n := by
        rw [← hcard]
        exact lt_of_le_of_ne H.card_le_card_group
          (fun heq ↦ hproper (H.card_eq_iff_eq_top.mp heq))
      let T : Set G := S ∩ H
      have hT : T ⊆ H := fun _ hx ↦ hx.2
      have hH : H ≤ Subgroup.closure T := by
        apply Subgroup.closure_mono
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨hs, hsH⟩
        · exact ⟨ht, htH⟩
      have hTgen := closure_preimage_subtype_eq_top T H hT hH
      have hHncyc : ¬ IsCyclic H := by
        intro hc
        let := hc
        exact hnst (congrArg Subtype.val (mul_comm (⟨s, hsH⟩ : H) ⟨t, htH⟩))
      have hfig := ih (Nat.card H) hlt (H.subtype ⁻¹' T) rfl
        (hodd.of_dvd_nat H.card_subgroup_dvd_card)
        (by intro x hx; exact ⟨hinv _ hx.1, H.inv_mem hx.2⟩)
        (fun hx ↦ hone hx.1) hTgen hHncyc
      exact hno (hfig.map H.subtype Subtype.coe_injective (fun _ hx ↦ hx.1))
    have hquot : ∀ (A : Subgroup G) [A.Normal] [IsMulCommutative A],
        A ≠ ⊥ → IsCyclic (G ⧸ A) := by
      intro A _ _ hA
      by_contra hnq
      have hlt : Nat.card (G ⧸ A) < n := by
        rw [← hcard, A.card_eq_card_quotient_mul_card_subgroup]
        exact (Nat.lt_mul_iff_one_lt_right (Nat.card_pos (α := G ⧸ A))).mpr
          (A.one_lt_card_iff_ne_bot.mpr hA)
      let T : Set (G ⧸ A) := (QuotientGroup.mk (s := A)) '' S \ {1}
      have hTgen : Subgroup.closure T = ⊤ := by
        rw [Subgroup.closure_sdiff_one]
        change Subgroup.closure ((QuotientGroup.mk' A) '' S) = ⊤
        rw [← MonoidHom.map_closure, hgen]
        exact Subgroup.map_top_of_surjective (QuotientGroup.mk' A) QuotientGroup.mk_surjective
      have hfig := ih (Nat.card (G ⧸ A)) hlt T rfl
        (hodd.of_dvd_nat A.card_quotient_dvd_card)
        (quotient_generators_inverse_closed S hinv A)
        (by simp [T]) hTgen hnq
      exact hno (symmetric_figure_eight_lifts S hodd A hfig)
    exact hno (hcase S hodd hinv hone hncomm hquot hs ht hnst hpair)

end CayleyErdosGyarfas

-- ===== platform target: CayleyErdosGyarfas.noncyclic_odd_order_symmetric_figure_eight =====
-- Reduction: the induction on |G| is proved here; the minimal nonabelian case is the imported
-- platform theorem CayleyErdosGyarfas.minimal_nonabelian_case_has_symmetric_figure_eight.
open CayleyErdosGyarfas in
theorem solution
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hodd : Odd (Nat.card G)) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hone : (1 : G) ∉ S) (hgen : Subgroup.closure S = ⊤)
    (hncyclic : ¬ IsCyclic G) : HasSymmetricFigureEight S := by
  exact noncyclic_figure_eight_of_minimal_case
    (@minimal_nonabelian_case_has_symmetric_figure_eight)
    S hodd hinv hone hgen hncyclic
