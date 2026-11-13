-- Prove2me | solution 1 for CayleyErdosGyarfas.nilpotent_cayley_contains_two_power_cycle
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T02:28:37.654681+00:00
-- url     : https://prove2.me/submissions/e8a5f831-1810-444c-9116-f7045d303792

import Theorems.Thm_CayleyErdosGyarfas_odd_order_cayley_contains_two_power_cycle
import Definitions.Def_CayleyErdosGyarfas_HasSymmetricFigureEight
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.ChainOfFn
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

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

-- ===== from CayleyErdosGyarfas/NilpotentReduction.lean =====
/-! Proved cycle constructions used in the nilpotent reduction. -/


namespace CayleyErdosGyarfas

open SimpleGraph

/-- Distinct, noninverse generators whose product has power-of-two order
produce a power-of-two cycle, whether or not they commute. -/
theorem two_power_cycle_of_generator_product
    {G : Type*} [Group G] [Finite G] (S : Set G) (hone : (1 : G) ∉ S)
    {s t : G} (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t) (htinv : t ≠ s⁻¹)
    (horder : ∃ k : ℕ, orderOf (s * t) = 2 ^ k) :
    ∃ (n : ℕ) (v : G) (c : (mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  by_cases hcomm : Commute s t
  · obtain ⟨c, hc, hlen⟩ := four_cycle_of_commuting_generators S hs ht
      (fun h ↦ hone (h ▸ hs)) (fun h ↦ hone (h ▸ ht)) hst htinv hcomm
    exact ⟨2, 1, c, by decide, hc, hlen⟩
  · obtain ⟨v, c, hc, hlen⟩ := alternating_cycle_of_noncommuting_generators S hs ht hcomm
    obtain ⟨k, hk⟩ := horder
    refine ⟨k + 1, v, c, by omega, hc, ?_⟩
    rw [hlen, hk, pow_succ, Nat.mul_comm]

/-- A square of power-of-two order forces the element itself to have
power-of-two order. -/
theorem orderOf_two_power_of_square
    {G : Type*} [Group G] {s : G} (h : ∃ k : ℕ, orderOf (s * s) = 2 ^ k) :
    ∃ k : ℕ, orderOf s = 2 ^ k := by
  obtain ⟨k, hk⟩ := h
  have hp : s ^ (2 ^ (k + 1)) = 1 := by
    rw [pow_succ', pow_mul, pow_two, ← hk]
    exact pow_orderOf_eq_one (s * s)
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
    (orderOf_dvd_of_pow_eq_one hp)
  exact ⟨j, hj⟩

/-- The generator-collision case in the manuscript's nilpotent proof.
No oddness assumption on the quotient is needed. -/
theorem two_power_cycle_of_quotient_generator_collision
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S) (hone : (1 : G) ∉ S)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup 2 P)
    {s t : G} (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t)
    (heq : (QuotientGroup.mk s : G ⧸ P) = QuotientGroup.mk t) :
    ∃ (n : ℕ) (v : G) (c : (mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  have hy : s⁻¹ * t ∈ P := by
    rw [← QuotientGroup.eq_one_iff]
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv, heq]
  have ho : ∃ k : ℕ, orderOf (s⁻¹ * t) = 2 ^ k := by
    simpa using hP.exists_orderOf_eq_pow (⟨s⁻¹ * t, hy⟩ : P)
  by_cases hti : t = s⁻¹
  · subst t
    obtain ⟨k, hk⟩ := orderOf_two_power_of_square ho
    have hpos := orderOf_pos s⁻¹
    have hge : 3 ≤ orderOf s⁻¹ := by
      by_contra h
      have hd : orderOf s⁻¹ ∣ 2 := by
        have : orderOf s⁻¹ = 1 ∨ orderOf s⁻¹ = 2 := by omega
        rcases this with h1 | h2
        · rw [h1]; exact one_dvd _
        · rw [h2]
      have hp : s⁻¹ * s⁻¹ = 1 := by
        simpa [pow_two] using (orderOf_dvd_iff_pow_eq_one.mp hd : (s⁻¹) ^ 2 = 1)
      have hi : s⁻¹ = s := by simpa using (eq_inv_of_mul_eq_one_left hp)
      exact hst hi.symm
    obtain ⟨v, c, hc, hlen⟩ := generator_order_cycle S (hinv s hs) hge
    refine ⟨k, v, c, ?_, hc, hlen.trans hk⟩
    have : k ≠ 0 := by
      intro h
      have : orderOf s⁻¹ = 1 := by simpa only [h, pow_zero] using hk
      omega
    omega
  · exact two_power_cycle_of_generator_product S hone (hinv s hs) ht
      (Ne.symm hti) (by simpa using Ne.symm hst) ho

/-- A nontrivial involution is not a translate between two powers of the
product of itself and a conjugate involution. This separates the two fibers
in the four-block construction from the manuscript. -/
theorem involution_commutator_powers_disjoint
    {G : Type*} [Group G] {s t : G} (hs1 : s ≠ 1) (hs2 : s * s = 1) :
    ∀ i j : ℕ, (s * t⁻¹ * s * t) ^ i ≠ (s * t⁻¹ * s * t) ^ j * s := by
  let c := t⁻¹ * s * t
  let x := s * t⁻¹ * s * t
  have hscx : s * c = x := by simp [x, c, mul_assoc]
  have hsxc : s * x = c := by
    rw [← hscx, ← mul_assoc, hs2, one_mul]
  have hc2 : c * c = 1 := calc
    c * c = t⁻¹ * (s * s) * t := by dsimp [c]; group
    _ = 1 := by rw [hs2]; simp
  have hc1 : c ≠ 1 := by
    intro h
    have hh : s = t * c * t⁻¹ := by dsimp [c]; group
    exact hs1 (by simpa [h] using hh)
  intro i j heq
  change x ^ i = x ^ j * s at heq
  have hs_eq : s = (x ^ j)⁻¹ * x ^ i := eq_inv_mul_iff_mul_eq.mpr heq.symm
  have hxs : Commute x s := by
    rw [hs_eq]
    exact (((Commute.refl x).pow_right j).inv_right).mul_right
      ((Commute.refl x).pow_right i)
  have hsc : Commute s c := by
    rw [← hsxc]
    exact (Commute.refl s).mul_right hxs.symm
  have hx2 : x * x = 1 := by
    have h := hsc.mul_pow 2
    rw [hscx] at h
    simpa only [pow_two, hs2, hc2, one_mul] using h
  have hxinv : x⁻¹ = x := (eq_inv_of_mul_eq_one_left hx2).symm
  have hp (n : ℕ) : x ^ n = 1 ∨ x ^ n = x := by
    induction n with
    | zero => exact Or.inl (pow_zero _)
    | succ n ih =>
      rcases ih with h | h
      · exact Or.inr (by rw [pow_succ, h, one_mul])
      · exact Or.inl (by rw [pow_succ, h, hx2])
  have hs_cases : s = 1 ∨ s = x := by
    rcases hp i with hi | hi <;> rcases hp j with hj | hj
    · exact Or.inl (by simpa only [hi, hj, inv_one, one_mul] using hs_eq)
    · exact Or.inr (by simpa only [hi, hj, hxinv, mul_one] using hs_eq)
    · exact Or.inr (by simpa only [hi, hj, inv_one, one_mul] using hs_eq)
    · exact Or.inl (by simpa only [hi, hj, hxinv, hx2] using hs_eq)
  rcases hs_cases with hs | hs
  · exact hs1 hs
  · exact hc1 (by rw [← hsxc, hs, hx2])

/-- An involution in a normal subgroup and a generator outside it produce the
cycle obtained by repeating the four-letter commutator word. -/
theorem involution_commutator_cycle
    {G : Type*} [Group G] [Finite G] (S : Set G) {s t : G}
    (hs : s ∈ S) (ht : t ∈ S) (hti : t⁻¹ ∈ S) (hs1 : s ≠ 1) (hs2 : s * s = 1)
    (P : Subgroup G) [P.Normal] (hsP : s ∈ P) (htP : t ∉ P) :
    ∃ (v : G) (c : (mulCayley S).Walk v v),
      c.IsCycle ∧ c.length = 4 * orderOf (s * t⁻¹ * s * t) := by
  let x := s * t⁻¹ * s * t
  let φ := QuotientGroup.mk' P
  have hφs : φ s = 1 := (QuotientGroup.eq_one_iff s).mpr hsP
  have hφt : φ t ≠ 1 := fun h ↦ htP ((QuotientGroup.eq_one_iff t).mp h)
  have hφti : φ t⁻¹ ≠ 1 := by
    intro h
    exact hφt (by simpa only [map_inv, inv_inv, inv_one] using congrArg Inv.inv h)
  have hφti' : (1 : G ⧸ P) ≠ φ t⁻¹ := Ne.symm hφti
  have hφx : φ x = 1 := by simp [x, map_mul, map_inv, hφs]
  have ht1 : t ≠ 1 := fun h ↦ htP (h ▸ P.one_mem)
  have hti1 : t⁻¹ ≠ 1 := by
    intro h
    exact ht1 (by simpa only [inv_inv, inv_one] using congrArg Inv.inv h)
  have hcross : ∀ i j : ℕ, x ^ i ≠ x ^ j * s := involution_commutator_powers_disjoint hs1 hs2
  have hpos := orderOf_pos x
  let f : ℕ → G := fun i ↦
    if i % 4 = 0 then x ^ (i / 4)
    else if i % 4 = 1 then x ^ (i / 4) * s
    else if i % 4 = 2 then x ^ (i / 4) * s * t⁻¹
    else x ^ (i / 4 + 1) * t⁻¹
  have hadj (v : G) {u : G} (hu : u ∈ S) (hu1 : u ≠ 1) :
      (mulCayley S).Adj v (v * u) := by
    apply (mulCayley_adj' _ _ _).mpr
    exact ⟨by simpa using hu1, u, hu, Or.inl rfl⟩
  apply exists_cycle_of_sequence (n := 4 * orderOf x) (by omega) f
  · simp [f]
  · intro i hi
    have hri : i % 4 < 4 := Nat.mod_lt _ (by decide)
    interval_cases ri : i % 4
    · have his : (i + 1) % 4 = 1 := by omega
      have hid : (i + 1) / 4 = i / 4 := by omega
      simpa [f, ri, his, hid] using hadj (x ^ (i / 4)) hs hs1
    · have his : (i + 1) % 4 = 2 := by omega
      have hid : (i + 1) / 4 = i / 4 := by omega
      simpa [f, ri, his, hid] using hadj (x ^ (i / 4) * s) hti hti1
    · have his : (i + 1) % 4 = 3 := by omega
      have hid : (i + 1) / 4 = i / 4 := by omega
      simpa [f, ri, his, hid, pow_succ, x, mul_assoc] using hadj (x ^ (i / 4) * s * t⁻¹) hs hs1
    · have his : (i + 1) % 4 = 0 := by omega
      have hid : (i + 1) / 4 = i / 4 + 1 := by omega
      simpa [f, ri, his, hid, mul_assoc] using hadj (x ^ (i / 4 + 1) * t⁻¹) ht ht1
  · intro i hi j hj heq
    have hid : i / 4 < orderOf x := by omega
    have hjd : j / 4 < orderOf x := by omega
    have hri : i % 4 < 4 := Nat.mod_lt _ (by decide)
    have hrj : j % 4 < 4 := Nat.mod_lt _ (by decide)
    interval_cases ri : i % 4 <;> interval_cases rj : j % 4
    all_goals simp [f, ri, rj] at heq
    all_goals try { have hq := congrArg φ heq
                    simp only [map_mul, map_pow, hφx, hφs, one_pow, one_mul,
                      hφti, hφti'] at hq }
    all_goals try exact (hcross _ _ heq).elim
    all_goals try exact (hcross _ _ heq.symm).elim
    all_goals
      have heqpow : x ^ (i / 4) = x ^ (j / 4) := by
        first | exact heq | exact mul_right_cancel heq |
          exact mul_right_cancel (mul_right_cancel heq) |
          exact mul_right_cancel (b := x) (by simpa only [pow_succ] using heq)
      have := pow_injOn_Iio_orderOf hid hjd heqpow
      omega


/-- A generator in a proper normal 2-subgroup gives a power-of-two cycle:
either its own order is at least four, or an involution commutator supplies one. -/
theorem two_power_cycle_of_kernel_generator
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S) (hone : (1 : G) ∉ S)
    (hgen : Subgroup.closure S = ⊤)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup 2 P) (hPtop : P ≠ ⊤)
    {s : G} (hs : s ∈ S) (hsP : s ∈ P) :
    ∃ (n : ℕ) (v : G) (c : (mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  have hs1 : s ≠ 1 := fun h ↦ hone (h ▸ hs)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, orderOf s = 2 ^ k := by
    simpa using hP.exists_orderOf_eq_pow (⟨s, hsP⟩ : P)
  by_cases hge : 3 ≤ orderOf s
  · obtain ⟨v, c, hc, hlen⟩ := generator_order_cycle S hs hge
    refine ⟨k, v, c, ?_, hc, hlen.trans hk⟩
    have : k ≠ 0 := by
      intro h
      have : orderOf s = 1 := by simpa only [h, pow_zero] using hk
      omega
    omega
  · have hpos := orderOf_pos s
    have hne : orderOf s ≠ 1 := by simpa using hs1
    have ho : orderOf s = 2 := by omega
    have hs2 : s * s = 1 := by simpa only [ho, pow_two] using pow_orderOf_eq_one s
    obtain ⟨t, ht, htP⟩ : ∃ t ∈ S, t ∉ P := by
      by_contra h
      push Not at h
      have hle : Subgroup.closure S ≤ P := (Subgroup.closure_le P).mpr h
      rw [hgen] at hle
      exact hPtop (top_le_iff.mp hle)
    obtain ⟨v, c, hc, hlen⟩ := involution_commutator_cycle S hs ht (hinv t ht)
      hs1 hs2 P hsP htP
    have hxP : s * t⁻¹ * s * t ∈ P := by
      rw [← QuotientGroup.eq_one_iff]
      have hφs : (QuotientGroup.mk s : G ⧸ P) = 1 :=
        (QuotientGroup.eq_one_iff s).mpr hsP
      simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hφs]
    obtain ⟨j, hj⟩ : ∃ j : ℕ, orderOf (s * t⁻¹ * s * t) = 2 ^ j := by
      simpa using hP.exists_orderOf_eq_pow (⟨s * t⁻¹ * s * t, hxP⟩ : P)
    refine ⟨j + 2, v, c, by omega, hc, ?_⟩
    rw [hlen, hj, pow_add]
    simp [Nat.mul_comm]


universe u

/-- The nilpotent corollary reduces to the odd-order theorem via a normal
Sylow 2-subgroup. The odd-order theorem is an explicit parameter, so this
helper records exactly the remaining dependency of the corollary. -/


theorem nilpotent_cycle_of_odd_order_theorem
    (hoddTheorem : ∀ {H : Type u} [Group H] [Finite H] (T : Set H),
      Odd (Nat.card H) → (∀ t ∈ T, t⁻¹ ∈ T) → (1 : H) ∉ T →
      Subgroup.closure T = ⊤ → 3 ≤ T.ncard →
      ∃ (n : ℕ) (v : H) (c : (mulCayley T).Walk v v),
        1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n)
    {G : Type u} [Group G] [Finite G] [Group.IsNilpotent G] (S : Set G)
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S) (hone : (1 : G) ∉ S)
    (hgen : Subgroup.closure S = ⊤) (hcard : 3 ≤ S.ncard) :
    ∃ (n : ℕ) (v : G) (c : (mulCayley S).Walk v v),
      1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  classical
  let P : Sylow 2 G := Classical.arbitrary _
  let N : Subgroup G := P
  have hN : IsPGroup 2 N := P.isPGroup'
  by_cases hNtop : N = ⊤
  · have hsurj : Function.Surjective N.subtype := by
      intro g
      exact ⟨⟨g, by rw [hNtop]; trivial⟩, rfl⟩
    exact two_group_cayley_contains_two_power_cycle (hN.of_surjective N.subtype hsurj) S hone hcard
  by_cases hkernel : ∃ s ∈ S, s ∈ N
  · obtain ⟨s, hs, hsN⟩ := hkernel
    exact two_power_cycle_of_kernel_generator S hinv hone hgen N hN hNtop hs hsN
  let φ := QuotientGroup.mk' N
  by_cases hinj : Set.InjOn φ S
  · let T : Set (G ⧸ N) := φ '' S \ {1}
    have hφone : (1 : G ⧸ N) ∉ φ '' S := by
      rintro ⟨s, hs, hsφ⟩
      exact hkernel ⟨s, hs, (QuotientGroup.eq_one_iff s).mp hsφ⟩
    have hTeq : T = φ '' S := by
      ext q
      simp only [T, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · exact And.left
      · intro hq
        exact ⟨hq, fun heq ↦ hφone (heq ▸ hq)⟩
    have hTcard : 3 ≤ T.ncard := by rw [hTeq, hinj.ncard_image]; exact hcard
    have hTgen : Subgroup.closure T = ⊤ := by
      rw [hTeq, ← MonoidHom.map_closure, hgen, ← MonoidHom.range_eq_map]
      exact φ.range_eq_top_of_surjective (QuotientGroup.mk'_surjective N)
    have hTinv : ∀ t ∈ T, t⁻¹ ∈ T := quotient_generators_inverse_closed S hinv N
    have hTone : (1 : G ⧸ N) ∉ T := by simp [T]
    have hodd : Odd (Nat.card (G ⧸ N)) := by
      apply Nat.not_even_iff_odd.mp
      rw [even_iff_two_dvd, ← Subgroup.index_eq_card]
      exact P.not_dvd_index
    exact two_power_cycle_lifts S N hN (hoddTheorem T hodd hTinv hTone hTgen hTcard)
  · have hcollision : ∃ s ∈ S, ∃ t ∈ S, s ≠ t ∧ φ s = φ t := by
      simpa only [Set.InjOn, not_forall, exists_prop, _root_.not_imp, and_assoc,
        and_left_comm, and_comm] using hinj
    obtain ⟨s, hs, t, ht, hst, heq⟩ := hcollision
    exact two_power_cycle_of_quotient_generator_collision S hinv hone N hN hs ht hst heq


end CayleyErdosGyarfas

namespace CayleyErdosGyarfas

/-- A simple cycle has at least three edges, so the two lower bounds on the
exponent are equivalent in the presence of `c.IsCycle`. -/
private theorem cycle_exponent_iff {V : Type*} (Γ : SimpleGraph V) :
    (∃ (n : ℕ) (v : V) (c : Γ.Walk v v), 1 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n) ↔
    (∃ (n : ℕ) (v : V) (c : Γ.Walk v v), 2 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n) := by
  constructor
  · rintro ⟨n, v, c, _, hc, hlen⟩
    exact ⟨n, v, c, two_power_cycle_exponent_ge_two hc hlen, hc, hlen⟩
  · rintro ⟨n, v, c, hn, hc, hlen⟩
    exact ⟨n, v, c, Nat.le_trans (by decide : 1 ≤ 2) hn, hc, hlen⟩

end CayleyErdosGyarfas

-- ===== platform target: CayleyErdosGyarfas.nilpotent_cayley_contains_two_power_cycle (Corollary 1.4) =====
-- Reduction: the Sylow 2-subgroup reduction and the 2-group base cases are proved here; the
-- odd-order quotient is handled by the imported platform theorem (Theorem 1.1).
open CayleyErdosGyarfas in
theorem solution
    {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G] (S : Set G)
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hone : (1 : G) ∉ S)
    (hgen : Subgroup.closure S = ⊤)
    (hcard : 3 ≤ S.ncard) :
    ∃ (n : ℕ) (v : G) (c : (SimpleGraph.mulCayley S).Walk v v),
      2 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by
  apply (cycle_exponent_iff _).mp
  exact nilpotent_cycle_of_odd_order_theorem
    (fun T hodd hinv hone hgen hcard ↦ (cycle_exponent_iff _).mpr
      (odd_order_cayley_contains_two_power_cycle T hodd hinv hone hgen hcard))
    S hinv hone hgen hcard
