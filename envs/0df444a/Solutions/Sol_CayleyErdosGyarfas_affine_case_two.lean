-- Prove2me | solution 1 for CayleyErdosGyarfas.affine_case_two
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T02:40:55.724784+00:00
-- url     : https://prove2.me/submissions/d22155d8-f70a-419d-9ce1-44aeab5eb693

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
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SemidirectProduct

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

-- ===== from CayleyErdosGyarfas/AffineCases.lean =====
/-! Explicit affine cycles and their translates, following Case 3 of the manuscript. -/


namespace CayleyErdosGyarfas

theorem affine_eq_coeffs {K : Type*} [Field K] {a b c d : K}
    (h : ∀ z, a*z+b = c*z+d) : a = c ∧ b = d := by
  have hzero := h 0
  have hone := h 1
  simp only [mul_zero, zero_add] at hzero
  simp only [mul_one] at hone
  exact ⟨add_right_cancel (hone.trans (congrArg (c + ·) hzero.symm)), hzero⟩

theorem affine_mul_apply {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (u v : G) (z : K) :
    φ (u*v) z = φ u (φ v z) := by simp

theorem affine_inv_apply {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) {u : G} {a b : K} (ha : a ≠ 0)
    (hu : ∀ z, φ u z = a*z+b) (z : K) :
    φ u⁻¹ z = a⁻¹ * (z-b) := by
  apply (φ u).injective
  simp only [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Equiv.Perm.one_apply]
  rw [hu]
  field_simp
  ring

private theorem caseThree_translate_plus {K : Type*} [Field K] (q : K)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hqminus : q ≠ -1)
    (hqinv : q⁻¹ ≠ q) (h2 : (2:K) ≠ 0)
    (hbad1 : q ≠ -2) (hbad2 : 2*q ≠ -1)
    (x y : K × K)
    (hx : x ∈ [(1,0), (q⁻¹,1), (1,1), (q,1), (1,1+q), (q⁻¹,1+q), (1,q), (q,0)])
    (hy : y ∈ [(1,0), (q⁻¹,1), (1,1), (q,1), (1,1+q), (q⁻¹,1+q), (1,q), (q,0)])
    (heq : (y.1, 1+q+y.2) = x) : x = (1,1+q) := by
  have hqi1 : q⁻¹ ≠ 1 := by simpa using hq1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Prod.mk.injEq] at heq ⊢ <;>
    simp only [true_and, false_and,
      hq1, hq1.symm, hqi1, hqi1.symm, hqinv, hqinv.symm] at heq <;>
    try contradiction <;> try rfl
  all_goals first
    | exact ⟨rfl, by linear_combination heq⟩
    | exact (hq0 (by linear_combination heq)).elim
    | exact (hqminus (by linear_combination heq)).elim
    | exact (h2 (by linear_combination heq)).elim
    | exact (hbad1 (by linear_combination heq)).elim
    | exact (hbad2 (by linear_combination heq)).elim
    | exact (hq0 (by linear_combination -heq)).elim
    | exact (hqminus (by linear_combination -heq)).elim
    | exact (h2 (by linear_combination -heq)).elim
    | exact (hbad1 (by linear_combination -heq)).elim
    | exact (hbad2 (by linear_combination -heq)).elim
    | exact (h2 (by linear_combination 2*heq)).elim
    | exact (hqminus (by apply mul_left_cancel₀ h2; linear_combination heq)).elim
    | exact (hq0 (by apply mul_left_cancel₀ h2; linear_combination heq)).elim

private theorem caseThree_translate_minus {K : Type*} [Field K] (q : K)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hqminus : q ≠ -1)
    (hqinv : q⁻¹ ≠ q) (h2 : (2:K) ≠ 0)
    (hbad1 : q ≠ 2) (hbad2 : 2*q ≠ 1)
    (x y : K × K)
    (hx : x ∈ [(1,0), (q⁻¹,1), (1,1), (q,1), (1,1+q), (q⁻¹,1+q), (1,q), (q,0)])
    (hy : y ∈ [(1,0), (q⁻¹,1), (1,1), (q,1), (1,1+q), (q⁻¹,1+q), (1,q), (q,0)])
    (heq : (y.1, 1-q+y.2) = x) : x = (1,1) := by
  have hqi1 : q⁻¹ ≠ 1 := by simpa using hq1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Prod.mk.injEq] at heq ⊢ <;>
    simp only [true_and, false_and,
      hq1, hq1.symm, hqi1, hqi1.symm, hqinv, hqinv.symm] at heq <;>
    try contradiction <;> try rfl
  all_goals first
    | exact ⟨rfl, by linear_combination heq⟩
    | exact (hq0 (by linear_combination heq)).elim
    | exact (hqminus (by linear_combination heq)).elim
    | exact (h2 (by linear_combination heq)).elim
    | exact (hbad1 (by linear_combination heq)).elim
    | exact (hbad2 (by linear_combination heq)).elim
    | exact (hq0 (by linear_combination -heq)).elim
    | exact (hqminus (by linear_combination -heq)).elim
    | exact (h2 (by linear_combination -heq)).elim
    | exact (hbad1 (by linear_combination -heq)).elim
    | exact (hbad2 (by linear_combination -heq)).elim
    | exact (h2 (by linear_combination 2*heq)).elim
    | exact (hqminus (by apply mul_left_cancel₀ h2; linear_combination heq)).elim
    | exact (hq0 (by apply mul_left_cancel₀ h2; linear_combination heq)).elim
    | exact (hq1 (by apply mul_left_cancel₀ h2; linear_combination -heq)).elim
    | exact (hq1 (by linear_combination -heq)).elim
    | exact (hq1 (by linear_combination heq)).elim
    | exact (hq0 (by apply mul_left_cancel₀ h2; linear_combination -heq)).elim

private theorem caseThree_good_translate {K : Type*} [Field K] (q : K)
    (h2 : (2:K) ≠ 0) (hsq : q^2 ≠ -1) :
    (q ≠ -2 ∧ 2*q ≠ -1) ∨ (q ≠ 2 ∧ 2*q ≠ 1) := by
  by_cases hplus1 : q ≠ -2
  · by_cases hplus2 : 2*q ≠ -1
    · exact Or.inl ⟨hplus1, hplus2⟩
    · push Not at hplus2
      right
      constructor
      · intro h
        apply hsq
        linear_combination q*h + hplus2
      · intro h
        apply h2
        linear_combination hplus2 - h
  · push Not at hplus1
    right
    constructor
    · intro h
      have hfour : (2:K)*2 = 0 := by linear_combination hplus1 - h
      exact (mul_ne_zero h2 h2) hfour
    · intro h
      apply hsq
      linear_combination q*hplus1 - h

set_option maxRecDepth 2000 in
private theorem caseThree_cycle {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (s t : G) (hs : s ∈ S) (ht : t ∈ S)
    (q : K) (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hqminus : q ≠ -1)
    (hqinv : q⁻¹ ≠ q)
    (hsact : ∀ z, φ s z = q⁻¹*z) (htact : ∀ z, φ t z = q⁻¹*z+1) :
    ∃ c : (SimpleGraph.mulCayley S).Walk 1 1,
      c.IsCycle ∧ c.length = 8 ∧
      c.support = [1, t, t*s⁻¹, t*s⁻¹*s⁻¹, t*s⁻¹*s⁻¹*t,
        t*s⁻¹*s⁻¹*t*s, s⁻¹*t, s⁻¹, 1] := by
  let f : ℕ → G
    | 0 => 1 | 1 => t | 2 => t*s⁻¹ | 3 => t*s⁻¹*s⁻¹
    | 4 => t*s⁻¹*s⁻¹*t | 5 => t*s⁻¹*s⁻¹*t*s
    | 6 => s⁻¹*t | 7 => s⁻¹ | _ => 1
  let v : ℕ → K × K
    | 0 => (1,0) | 1 => (q⁻¹,1) | 2 => (1,1) | 3 => (q,1)
    | 4 => (1,1+q) | 5 => (q⁻¹,1+q) | 6 => (1,q) | 7 => (q,0)
    | _ => (1,0)
  have hsinv : ∀ z, φ s⁻¹ z = q*z := by
    intro z
    simpa using affine_inv_apply φ (inv_ne_zero hq0)
      (fun z ↦ show φ s z = q⁻¹*z+0 by simpa using hsact z) z
  have htinverse : ∀ z, φ t⁻¹ z = q*(z-1) := by
    intro z
    simpa using affine_inv_apply φ (inv_ne_zero hq0) htact z
  have haction (i : ℕ) (hi : i < 9) (z : K) :
      φ (f i) z = (v i).1*z+(v i).2 := by
    interval_cases i <;>
      simp only [f, v, affine_mul_apply, hsinv, hsact, htact, map_one,
        Equiv.Perm.one_apply, one_mul, add_zero] <;>
      field_simp <;> ring
  have hinj : ∀ i < 8, ∀ j < 8, f i = f j → i = j := by
    intro i hi j hj hij
    have hh : v i = v j := by
      apply Prod.ext
      · exact (affine_eq_coeffs (fun z ↦ by rw [← haction i (by omega), hij,
          haction j (by omega)])).1
      · exact (affine_eq_coeffs (fun z ↦ by rw [← haction i (by omega), hij,
          haction j (by omega)])).2
    have hqi1 : q⁻¹ ≠ 1 := by simpa using hq1
    interval_cases i <;> interval_cases j <;> try rfl
    all_goals simp only [v, Prod.mk.injEq] at hh
    all_goals simp only [hq1, hq1.symm, hqi1, hqi1.symm, hqinv, hqinv.symm,
      false_and, true_and, and_false, zero_ne_one, one_ne_zero] at hh
    all_goals first
      | contradiction
      | exact (hq0 (by linear_combination hh)).elim
      | exact (hq0 (by linear_combination -hh)).elim
      | exact (hq1 (by linear_combination hh)).elim
      | exact (hq1 (by linear_combination -hh)).elim
      | exact (hqminus (by linear_combination hh)).elim
      | exact (hqminus (by linear_combination -hh)).elim
      | exact (zero_ne_one (by linear_combination hh)).elim
      | exact (zero_ne_one (by linear_combination -hh)).elim
  have hadj (i : ℕ) (hi : i < 8) :
      (SimpleGraph.mulCayley S).Adj (f i) (f (i+1)) := by
    have hne : f i ≠ f (i+1) := by
      intro heq
      by_cases hi7 : i = 7
      · have hh := hinj 7 (by omega) 0 (by omega) (by simpa [hi7, f] using heq)
        omega
      · have hh := hinj i hi (i+1) (by omega) heq
        omega
    rw [SimpleGraph.mulCayley_adj']
    refine ⟨hne, ?_⟩
    interval_cases i
    · exact ⟨t, ht, Or.inl (by simp [f])⟩
    · exact ⟨s, hs, Or.inr (by simp [f])⟩
    · exact ⟨s, hs, Or.inr (by simp [f])⟩
    · exact ⟨t, ht, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · refine ⟨t, ht, Or.inr ?_⟩
      apply hφ
      ext z
      simp only [f, affine_mul_apply, hsinv, hsact, htact]
      field_simp
      ring
    · exact ⟨t, ht, Or.inr rfl⟩
    · exact ⟨s, hs, Or.inl (by simp [f])⟩
  obtain ⟨c, hc, hlen, hsupport⟩ := exists_cycle_of_sequence_with_support
    (n := 8) (by decide) f rfl hadj hinj
  refine ⟨c, hc, hlen, ?_⟩
  simpa [f, List.ofFn_succ] using hsupport

theorem figureEight_of_affine_coordinate_intersection
    {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (c : (SimpleGraph.mulCayley S).Walk 1 1)
    (n : ℕ) (hn : 1 ≤ n) (hc : c.IsCycle) (hlen : c.length = 2^n)
    (L : List (K × K))
    (hvertices : ∀ x ∈ c.support, ∃ p ∈ L, ∀ z, φ x z = p.1*z+p.2)
    (g w y : G) (d b : K)
    (hg : ∀ z, φ g z = z+d) (hw : ∀ z, φ w z = z+b)
    (hwmem : w ∈ c.support) (hymem : y ∈ c.support) (hgy : g*y = w)
    (hinter : ∀ p ∈ L, ∀ q ∈ L, (q.1,d+q.2) = p → p = (1,b)) :
    HasSymmetricFigureEight S := by
  apply hasSymmetricFigureEight_of_cycle_translate c n hn hc hlen g w
  intro x
  constructor
  · rintro ⟨hx, y', hy, hxy⟩
    obtain ⟨p, hp, hpx⟩ := hvertices x hx
    obtain ⟨q, hq, hqy⟩ := hvertices y' hy
    have heq : (q.1,d+q.2) = p := by
      have hcoeff : q.1 = p.1 ∧ d+q.2 = p.2 :=
        affine_eq_coeffs (a := q.1) (b := d+q.2) (c := p.1) (d := p.2)
          (fun z ↦ by
            rw [← hpx, ← hxy, affine_mul_apply, hqy, hg]
            ring)
      exact Prod.ext hcoeff.1 hcoeff.2
    have hpval := hinter p hp q hq heq
    apply hφ
    ext z
    rw [hpx, hpval, hw]
    simp
  · rintro rfl
    exact ⟨hwmem, y, hymem, hgy⟩

/-- The manuscript's third affine case: the two generators have the same
nontrivial linear part. The eight-cycle is the word `t s⁻² t s t⁻² s`.
The two candidate translates have offsets `1+q` and `1-q`, where `q` is
the inverse of the common scalar. -/
theorem affine_case_three {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (s t : G) (hs : s ∈ S) (ht : t ∈ S)
    (q : K) (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hqminus : q ≠ -1)
    (hqinv : q⁻¹ ≠ q) (h2 : (2:K) ≠ 0) (hsq : q^2 ≠ -1)
    (hsact : ∀ z, φ s z = q⁻¹*z) (htact : ∀ z, φ t z = q⁻¹*z+1) :
    HasSymmetricFigureEight S := by
  obtain ⟨c, hc, hlen, hsupport⟩ := caseThree_cycle φ hφ S s t hs ht
    q hq0 hq1 hqminus hqinv hsact htact
  let L : List (K × K) :=
    [(1,0), (q⁻¹,1), (1,1), (q,1), (1,1+q), (q⁻¹,1+q), (1,q), (q,0)]
  have hsinv : ∀ z, φ s⁻¹ z = q*z := by
    intro z
    simpa using affine_inv_apply φ (inv_ne_zero hq0)
      (fun z ↦ show φ s z = q⁻¹*z+0 by simpa using hsact z) z
  have hvertices : ∀ x ∈ c.support, ∃ p ∈ L, ∀ z, φ x z = p.1*z+p.2 := by
    intro x hx
    rw [hsupport] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨(1,0), by simp [L], ?_⟩
      simp
    · exact ⟨(q⁻¹,1), by simp [L], htact⟩
    · refine ⟨(1,1), by simp [L], ?_⟩
      intro z; simp only [affine_mul_apply, hsinv, htact]; field_simp <;> ring
    · refine ⟨(q,1), by simp [L], ?_⟩
      intro z; simp only [affine_mul_apply, hsinv, htact]; field_simp <;> ring
    · refine ⟨(1,1+q), by simp [L], ?_⟩
      intro z; simp only [affine_mul_apply, hsinv, htact]
      field_simp <;> ring
    · refine ⟨(q⁻¹,1+q), by simp [L], ?_⟩
      intro z; simp only [affine_mul_apply, hsinv, hsact, htact]
      field_simp <;> ring
    · refine ⟨(1,q), by simp [L], ?_⟩
      intro z; simp only [affine_mul_apply, hsinv, htact]
      field_simp <;> ring
    · exact ⟨(q,0), by simp [L], fun z ↦ by simpa using hsinv z⟩
    · refine ⟨(1,0), by simp [L], ?_⟩
      simp
  rcases caseThree_good_translate q h2 hsq with hplus | hminus
  · apply figureEight_of_affine_coordinate_intersection φ hφ S c 3 (by decide) hc
      (by simpa using hlen) L hvertices
      (t*s⁻¹*s⁻¹*t) (t*s⁻¹*s⁻¹*t) 1 (1+q) (1+q)
    · intro z
      simp only [affine_mul_apply, hsinv, htact]
      field_simp <;> ring
    · intro z
      simp only [affine_mul_apply, hsinv, htact]
      field_simp <;> ring
    · simp [hsupport]
    · simp [hsupport]
    · simp
    · intro p hp y hy heq
      exact caseThree_translate_plus q hq0 hq1 hqminus hqinv h2 hplus.1 hplus.2 p y hp hy heq
  · apply figureEight_of_affine_coordinate_intersection φ hφ S c 3 (by decide) hc
      (by simpa using hlen) L hvertices
      (t*s⁻¹*(s⁻¹*t)⁻¹) (t*s⁻¹) (s⁻¹*t) (1-q) 1
    · have htranslate (z : K) : φ (s⁻¹*t) z = 1*z+q := by
        simp only [affine_mul_apply, hsinv, htact]
        field_simp <;> ring
      have htranslateinv := affine_inv_apply φ (u := s⁻¹*t) one_ne_zero htranslate
      intro z
      simp only [affine_mul_apply, htranslateinv, inv_one, one_mul, hsinv, htact]
      field_simp <;> ring
    · intro z
      simp only [affine_mul_apply, hsinv, htact]
      field_simp <;> ring
    · simp [hsupport]
    · simp [hsupport]
    · group
    · intro p hp y hy heq
      exact caseThree_translate_minus q hq0 hq1 hqminus hqinv h2 hminus.1 hminus.2 p y hp hy heq


theorem figureEight_of_affine_coordinate_intersection_general
    {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (c : (SimpleGraph.mulCayley S).Walk 1 1)
    (n : ℕ) (hn : 1 ≤ n) (hc : c.IsCycle) (hlen : c.length = 2^n)
    (L : List (K × K))
    (hvertices : ∀ x ∈ c.support, ∃ p ∈ L, ∀ z, φ x z = p.1*z+p.2)
    (g w y : G) (a d e b : K)
    (hg : ∀ z, φ g z = a*z+d) (hw : ∀ z, φ w z = e*z+b)
    (hwmem : w ∈ c.support) (hymem : y ∈ c.support) (hgy : g*y = w)
    (hinter : ∀ p ∈ L, ∀ q ∈ L, (a*q.1,d+a*q.2) = p → p = (e,b)) :
    HasSymmetricFigureEight S := by
  apply hasSymmetricFigureEight_of_cycle_translate c n hn hc hlen g w
  intro x
  constructor
  · rintro ⟨hx, y', hy, hxy⟩
    obtain ⟨p, hp, hpx⟩ := hvertices x hx
    obtain ⟨q, hq, hqy⟩ := hvertices y' hy
    have heq : (a*q.1,d+a*q.2) = p := by
      have hcoeff : a*q.1 = p.1 ∧ d+a*q.2 = p.2 :=
        affine_eq_coeffs (a := a*q.1) (b := d+a*q.2) (c := p.1) (d := p.2)
          (fun z ↦ by
            rw [← hpx, ← hxy, affine_mul_apply, hqy, hg]
            ring)
      exact Prod.ext hcoeff.1 hcoeff.2
    have hpval := hinter p hp q hq heq
    apply hφ
    ext z
    rw [hpx, hpval, hw]
  · rintro rfl
    exact ⟨hwmem, y, hymem, hgy⟩


end CayleyErdosGyarfas

-- ===== from CayleyErdosGyarfas/OddOrderReduction.lean =====
/-!
# Group-theoretic steps in the odd-order reduction

These proved lemmas isolate elementary deductions in the manuscript's
minimal-counterexample argument. They do not assume or assert the final
Cayley-cycle theorem.
-/


namespace CayleyErdosGyarfas

open scoped IsMulCommutative

/-- A nonabelian group whose quotients by nontrivial abelian normal
subgroups are cyclic has trivial center. -/
theorem center_eq_bot_of_abelian_normal_quotients_cyclic
    {G : Type*} [Group G] (hnonabelian : ¬ IsMulCommutative G)
    (hquot : ∀ (N : Subgroup G) [N.Normal] [IsMulCommutative N],
      N ≠ ⊥ → IsCyclic (G ⧸ N)) :
    Subgroup.center G = ⊥ := by
  by_contra hcenter
  let := hquot (Subgroup.center G) hcenter
  exact hnonabelian (isMulCommutative_of_isCyclic_quotient_center_self G)

/-- A minimal normal subgroup with cyclic quotient is the commutator
subgroup, provided the group is nonabelian. -/
theorem commutator_eq_of_minimal_normal_cyclic_quotient
    {G : Type*} [Group G] (V : Subgroup G) [V.Normal]
    [IsCyclic (G ⧸ V)] (hnonabelian : ¬ IsMulCommutative G)
    (hminimal : ∀ N : Subgroup G, N.Normal → N ≤ V → N = ⊥ ∨ N = V) :
    commutator G = V := by
  have hle : commutator G ≤ V :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (inferInstance : IsMulCommutative (G ⧸ V))
  rcases hminimal (commutator G) inferInstance hle with hbot | heq
  · exact (hnonabelian ((commutator_eq_bot_iff G).mp hbot)).elim
  · exact heq

/-- If an abelian normal subgroup and `x` generate a centerless group,
then a power of `x` which lies in that subgroup must be the identity. -/
theorem pow_eq_one_of_mem_abelian_normal_and_center_eq_bot
    {G : Type*} [Group G] (V : Subgroup G) [V.Normal] [IsMulCommutative V]
    (x : G) (hgenerate : Subgroup.zpowers x ⊔ V = ⊤)
    (hcenter : Subgroup.center G = ⊥) (m : ℕ) (hxm : x ^ m ∈ V) :
    x ^ m = 1 := by
  let C := Subgroup.centralizer ({x ^ m} : Set G)
  have hxC : x ∈ C := by
    change x ∈ Subgroup.centralizer ({x ^ m} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact ((Commute.refl x).pow_left m).eq
  have hVC : V ≤ C := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact congrArg Subtype.val (mul_comm (⟨x ^ m, hxm⟩ : V) ⟨v, hv⟩)
  have htop : C = ⊤ := by
    apply top_unique
    rw [← hgenerate]
    exact sup_le (Subgroup.zpowers_le.mpr hxC) hVC
  have hz : x ^ m ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ C := htop ▸ Subgroup.mem_top g
    exact ((Subgroup.mem_centralizer_iff.mp hg) (x ^ m) (by simp)).symm
  simpa [hcenter] using hz

/-- The lift of a cyclic-quotient generator has exactly its quotient
order in the centerless abelian-kernel setting used by the manuscript. -/
theorem orderOf_quotient_generator_eq
    {G : Type*} [Group G] [Finite G]
    (V : Subgroup G) [V.Normal] [IsMulCommutative V]
    (x : G) (hgenerate : Subgroup.zpowers x ⊔ V = ⊤)
    (hcenter : Subgroup.center G = ⊥) :
    orderOf x = orderOf (QuotientGroup.mk x : G ⧸ V) := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    apply pow_eq_one_of_mem_abelian_normal_and_center_eq_bot V x hgenerate hcenter
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_pow, pow_orderOf_eq_one]
  · exact orderOf_dvd_of_pow_eq_one (by
      change (QuotientGroup.mk' V) x ^ orderOf x = 1
      rw [← map_pow (QuotientGroup.mk' V), pow_orderOf_eq_one, map_one])

/-- The cyclic subgroup generated by such a quotient lift intersects the
abelian kernel trivially. -/
theorem zpowers_disjoint_abelian_kernel
    {G : Type*} [Group G] [Finite G]
    (V : Subgroup G) [V.Normal] [IsMulCommutative V]
    (x : G) (hgenerate : Subgroup.zpowers x ⊔ V = ⊤)
    (hcenter : Subgroup.center G = ⊥) :
    Disjoint (Subgroup.zpowers x) V := by
  rw [disjoint_iff_inf_le]
  intro g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg.1
  rw [Subgroup.mem_bot]
  apply orderOf_dvd_iff_zpow_eq_one.mp
  rw [orderOf_quotient_generator_eq V x hgenerate hcenter]
  apply orderOf_dvd_iff_zpow_eq_one.mpr
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]
  exact hg.2

/-- Thus the kernel and the cyclic lift are complementary subgroups. -/
theorem cyclic_lift_isCompl_abelian_kernel
    {G : Type*} [Group G] [Finite G]
    (V : Subgroup G) [V.Normal] [IsMulCommutative V]
    (x : G) (hgenerate : Subgroup.zpowers x ⊔ V = ⊤)
    (hcenter : Subgroup.center G = ⊥) :
    IsCompl (Subgroup.zpowers x) V :=
  ⟨zpowers_disjoint_abelian_kernel V x hgenerate hcenter,
    codisjoint_iff.mpr hgenerate⟩

/-- Inside a minimal abelian normal kernel, invariance under the cyclic
complement already forces a subgroup to be trivial or the whole kernel.
This is the subgroup form of irreducibility used in the field-model step. -/
theorem invariant_subgroup_eq_bot_or_eq_kernel
    {G : Type*} [Group G] (V : Subgroup G) [V.Normal] [IsMulCommutative V]
    (x : G) (hgenerate : Subgroup.zpowers x ⊔ V = ⊤)
    (hminimal : ∀ N : Subgroup G, N.Normal → N ≤ V → N = ⊥ ∨ N = V)
    (N : Subgroup G) (hNV : N ≤ V)
    (hxN : x ∈ Subgroup.normalizer (N : Set G)) :
    N = ⊥ ∨ N = V := by
  have hVnorm : V ≤ Subgroup.normalizer (N : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer (N : Set G))
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact congrArg Subtype.val (mul_comm (⟨n, hNV hn⟩ : V) ⟨v, hv⟩)
  have hnormtop : Subgroup.normalizer (N : Set G) = ⊤ := by
    apply top_unique
    rw [← hgenerate]
    exact sup_le (Subgroup.zpowers_le.mpr hxN) hVnorm
  exact hminimal N (Subgroup.normalizer_eq_top_iff.mp hnormtop) hNV

/-- Conjugation on an abelian normal subgroup, viewed as a linear
representation over its prime field. The module structure is Mathlib's
standard `AddCommGroup.zmodModule`. -/
noncomputable def normalConjugationRepresentation
    {G : Type*} [Group G] (p : ℕ)
    (V : Subgroup G) [V.Normal] [IsMulCommutative V]
    [Module (ZMod p) (Additive V)] (C : Subgroup G) :
    Representation (ZMod p) C (Additive V) where
  toFun c := ((MulAut.conjNormal (H := V) (c : G)).toMonoidHom.toAdditive).toZModLinearMap p
  map_one' := by
    ext v
    change (1 : G) * (v.toMul : G) * (1 : G)⁻¹ = (v.toMul : G)
    simp
  map_mul' c d := by
    ext v
    change ((c : G) * (d : G)) * (v.toMul : G) * ((c : G) * (d : G))⁻¹ =
      (c : G) * ((d : G) * (v.toMul : G) * (d : G)⁻¹) * (c : G)⁻¹
    group

@[simp] theorem normalConjugationRepresentation_apply
    {G : Type*} [Group G] (p : ℕ)
    (V : Subgroup G) [V.Normal] [IsMulCommutative V]
    [Module (ZMod p) (Additive V)] (C : Subgroup G)
    (c : C) (v : Additive V) :
    ((normalConjugationRepresentation p V C c v).toMul : G) =
      (c : G) * (v.toMul : G) * (c : G)⁻¹ := rfl

/-- Every subrepresentation of the cyclic conjugation action on a
minimal abelian normal subgroup is trivial or the whole representation. -/
theorem normalConjugation_subrepresentation_eq_bot_or_top
    {G : Type*} [Group G] (p : ℕ)
    (V : Subgroup G) [V.Normal] [IsMulCommutative V]
    [Module (ZMod p) (Additive V)]
    (x : G) (hgenerate : Subgroup.zpowers x ⊔ V = ⊤)
    (hminimal : ∀ N : Subgroup G, N.Normal → N ≤ V → N = ⊥ ∨ N = V)
    (W : Subrepresentation (normalConjugationRepresentation p V (Subgroup.zpowers x))) :
    W = ⊥ ∨ W = ⊤ := by
  let K : Subgroup V := {
    carrier := {v | Additive.ofMul v ∈ W}
    one_mem' := W.toSubmodule.zero_mem
    mul_mem' := fun ha hb ↦ W.toSubmodule.add_mem ha hb
    inv_mem' := fun ha ↦ W.toSubmodule.neg_mem ha }
  let N : Subgroup G := K.map V.subtype
  have hNV : N ≤ V := Subgroup.map_subtype_le K
  have hstable : ∀ c : Subgroup.zpowers x, ∀ n ∈ N,
      (c : G) * n * (c : G)⁻¹ ∈ N := by
    intro c n hn
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hn
    apply Subgroup.mem_map.mpr
    refine ⟨MulAut.conjNormal (H := V) (c : G) v, ?_, rfl⟩
    exact W.apply_mem_toSubmodule c hv
  have hxN : x ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hstable ⟨x, Subgroup.mem_zpowers x⟩ n
    · intro hn
      have hh := hstable ⟨x⁻¹, (Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x)⟩
        (x * n * x⁻¹) hn
      simpa [mul_assoc] using hh
  rcases invariant_subgroup_eq_bot_or_eq_kernel V x hgenerate hminimal N hNV hxN
    with hN | hN
  · left
    apply SetLike.ext
    intro v
    constructor
    · intro hv
      have hn : (v.toMul : G) ∈ N := Subgroup.mem_map.mpr ⟨v.toMul, hv, rfl⟩
      have hv1 : (v.toMul : G) = 1 := by simpa [hN] using hn
      change v = 0
      apply Additive.toMul.injective
      exact Subtype.ext hv1
    · intro hv
      change v = 0 at hv
      subst v
      exact W.toSubmodule.zero_mem
  · right
    apply top_unique
    intro v hv
    have hn : (v.toMul : G) ∈ N := hN.symm ▸ v.toMul.property
    obtain ⟨u, hu, heu⟩ := Subgroup.mem_map.mp hn
    have huv : u = v.toMul := Subtype.ext heu
    change Additive.ofMul u ∈ W at hu
    simpa [huv] using hu

/-- Minimal normality gives the irreducible prime-field representation
required by the finite-field (Singer) construction. -/
theorem normalConjugation_isIrreducible
    {G : Type*} [Group G] (p : ℕ) [Fact p.Prime]
    (V : Subgroup G) [V.Normal] [IsMulCommutative V] [Nontrivial V]
    [Module (ZMod p) (Additive V)]
    (x : G) (hgenerate : Subgroup.zpowers x ⊔ V = ⊤)
    (hminimal : ∀ N : Subgroup G, N.Normal → N ≤ V → N = ⊥ ∨ N = V) :
    (normalConjugationRepresentation p V (Subgroup.zpowers x)).IsIrreducible where
  exists_pair_ne := by
    refine ⟨⊥, ⊤, ?_⟩
    intro heq
    obtain ⟨v, hv⟩ := exists_ne (0 : Additive V)
    have hmem : v ∈ (⊥ : Subrepresentation
        (normalConjugationRepresentation p V (Subgroup.zpowers x))) := by
      rw [heq]
      trivial
    change v = 0 at hmem
    exact hv hmem
  eq_bot_or_eq_top := normalConjugation_subrepresentation_eq_bot_or_top p V x hgenerate hminimal

/-- Mathlib's prime-field module structure on an abelian subgroup of
exponent dividing `p`, with no replacement notion of elementary abelianity. -/
abbrev abelianKernelZModModule
    {G : Type*} [Group G] (p : ℕ)
    (V : Subgroup G) [IsMulCommutative V] (hpow : ∀ v : V, v ^ p = 1) :
    Module (ZMod p) (Additive V) :=
  AddCommGroup.zmodModule (fun v ↦ congrArg Additive.ofMul (hpow v.toMul))

/-- In the centerless case the cyclic complement acts faithfully on the
abelian kernel. -/
theorem normalConjugation_injective
    {G : Type*} [Group G] (p : ℕ)
    (V : Subgroup G) [V.Normal] [IsMulCommutative V]
    [Module (ZMod p) (Additive V)]
    (x : G) (hgenerate : Subgroup.zpowers x ⊔ V = ⊤)
    (hcenter : Subgroup.center G = ⊥) :
    Function.Injective (normalConjugationRepresentation p V (Subgroup.zpowers x)) := by
  let ρ := normalConjugationRepresentation p V (Subgroup.zpowers x)
  change Function.Injective ρ
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro c hc
  have hcV : ∀ v : V, (c : G) * (v : G) = (v : G) * (c : G) := by
    intro v
    have heq : ρ c = 1 := hc
    have heval := congrArg (fun f : Module.End (ZMod p) (Additive V) ↦
      ((f (Additive.ofMul v)).toMul : G)) heq
    change (c : G) * (v : G) * (c : G)⁻¹ = (v : G) at heval
    exact mul_inv_eq_iff_eq_mul.mp heval
  have hcx : Commute (c : G) x := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp c.property
    rw [← hk]
    exact (Commute.refl x).zpow_left k
  let C := Subgroup.centralizer ({(c : G)} : Set G)
  have hxC : x ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact hcx.eq
  have hVC : V ≤ C := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact hcV ⟨v, hv⟩
  have hCtop : C = ⊤ := by
    apply top_unique
    rw [← hgenerate]
    exact sup_le (Subgroup.zpowers_le.mpr hxC) hVC
  have hcz : (c : G) ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ C := hCtop ▸ Subgroup.mem_top g
    exact ((Subgroup.mem_centralizer_iff.mp hg) (c : G) (by simp)).symm
  change c = 1
  apply Subtype.ext
  simpa [hcenter] using hcz

/-- The exact simple-module hypothesis consumed by the Singer field
construction, obtained from the preceding group-theoretic assumptions. -/
theorem normalConjugation_asModule_isSimple
    {G : Type*} [Group G] (p : ℕ) [Fact p.Prime]
    (V : Subgroup G) [V.Normal] [IsMulCommutative V] [Nontrivial V]
    [Module (ZMod p) (Additive V)]
    (x : G) (hgenerate : Subgroup.zpowers x ⊔ V = ⊤)
    (hminimal : ∀ N : Subgroup G, N.Normal → N ≤ V → N = ⊥ ∨ N = V) :
    IsSimpleModule (MonoidAlgebra (ZMod p) (Subgroup.zpowers x))
      (normalConjugationRepresentation p V (Subgroup.zpowers x)).asModule :=
  (Representation.irreducible_iff_isSimpleModule_asModule _).mp
    (normalConjugation_isIrreducible p V x hgenerate hminimal)

/-- The stronger complement statement needed by Mathlib's
`SemidirectProduct.mulEquivSubgroup`. -/
theorem cyclic_lift_isComplement_abelian_kernel
    {G : Type*} [Group G] [Finite G]
    (V : Subgroup G) [V.Normal] [IsMulCommutative V]
    (x : G) (hgenerate : Subgroup.zpowers x ⊔ V = ⊤)
    (hcenter : Subgroup.center G = ⊥) :
    (Subgroup.zpowers x).IsComplement' V := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    (zpowers_disjoint_abelian_kernel V x hgenerate hcenter)
  rw [← Subgroup.mul_normal, hgenerate]
  rfl

end CayleyErdosGyarfas

-- ===== from CayleyErdosGyarfas/AffineModel.lean =====
/-! Faithful affine coordinates for a group with an abelian complement. -/


namespace CayleyErdosGyarfas

open scoped IsMulCommutative

set_option backward.isDefEq.respectTransparency false in
/-- A scalar realization of the action on an abelian normal subgroup gives
faithful affine coordinates for the whole split extension. -/
theorem exists_faithful_affine_action
    {G K : Type*} [Group G] [Field K]
    (V C : Subgroup G) [V.Normal] [IsMulCommutative V]
    (hcomp : V.IsComplement' C)
    (e : Additive V ≃+ K) (μ : C →* Kˣ) (hμ : Function.Injective μ)
    (hequiv : ∀ (c : C) (v : Additive V),
      e (Additive.ofMul (MulAut.conjNormal (H := V) (c : G) v.toMul)) =
        (μ c : K) * e v) :
    ∃ φ : G →* Equiv.Perm K, Function.Injective φ ∧
      (∀ (c : C) (z : K), φ (c : G) z = (μ c : K) * z) ∧
      (∀ (v : V) (z : K), φ (v : G) z = z + e (Additive.ofMul v)) ∧
      ∀ g : G, ∃ (r : Kˣ) (a : K), ∀ z : K, φ g z = (r : K) * z + a := by
  let σ : C →* MulAut V :=
    V.normalizerMonoidHom.comp (Subgroup.inclusion (V.normalizer_eq_top ▸ le_top))
  have hσ (c : C) (v : V) :
      e (Additive.ofMul (σ c v)) = (μ c : K) * e (Additive.ofMul v) :=
    hequiv c (Additive.ofMul v)
  let ψ : V ⋊[σ] C →* Equiv.Perm K := {
    toFun d := {
      toFun z := (μ d.right : K) * z + e (Additive.ofMul d.left)
      invFun z := ((μ d.right)⁻¹ : Kˣ) * (z - e (Additive.ofMul d.left))
      left_inv := by intro z; simp
      right_inv := by intro z; simp }
    map_one' := by ext z; simp
    map_mul' := by
      intro a b
      ext z
      change (μ (a.right * b.right) : K) * z +
        e (Additive.ofMul (a.left * σ a.right b.left)) =
        (μ a.right : K) * ((μ b.right : K) * z + e (Additive.ofMul b.left)) +
          e (Additive.ofMul a.left)
      rw [map_mul, Units.val_mul]
      change _ + e (Additive.ofMul a.left + Additive.ofMul (σ a.right b.left)) = _
      rw [map_add, hσ]
      ring }
  have hψ (d : V ⋊[σ] C) (z : K) :
      ψ d z = (μ d.right : K) * z + e (Additive.ofMul d.left) := rfl
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have hleft : a.left = b.left := by
      have h0 := congrArg (fun f : Equiv.Perm K ↦ f 0) hab
      simp only [hψ, mul_zero, zero_add] at h0
      exact e.injective h0
    have hright : a.right = b.right := by
      apply hμ
      apply Units.ext
      have h1 := congrArg (fun f : Equiv.Perm K ↦ f 1) hab
      simp only [hψ, mul_one, hleft] at h1
      exact add_right_cancel h1
    exact SemidirectProduct.ext hleft hright
  let E : V ⋊[σ] C ≃* G := SemidirectProduct.mulEquivSubgroup hcomp
  let φ := ψ.comp E.symm.toMonoidHom
  refine ⟨φ, hψinj.comp E.symm.injective, ?_, ?_, ?_⟩
  · intro c z
    have hc : E (SemidirectProduct.inr c) = (c : G) := by
      change (1 : G) * (c : G) = (c : G)
      simp
    change ψ (E.symm (c : G)) z = _
    rw [← hc, E.symm_apply_apply, hψ]
    simp
  · intro v z
    have hv : E (SemidirectProduct.inl v) = (v : G) := by
      change (v : G) * (1 : G) = (v : G)
      simp
    change ψ (E.symm (v : G)) z = _
    rw [← hv, E.symm_apply_apply, hψ]
    simp
  · intro g
    exact ⟨μ (E.symm g).right, e (Additive.ofMul (E.symm g).left), fun _ ↦ rfl⟩

/-- Translate a fixed point of the first generator to zero and rescale the
nonzero translation part of the second generator to one. Noncommutation is
exactly what prevents that translation part from vanishing. -/
theorem normalize_two_affine_generators
    {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (s t : G) (r q : Kˣ) (a b : K)
    (hs : ∀ z : K, φ s z = (r : K) * z + a)
    (ht : ∀ z : K, φ t z = (q : K) * z + b)
    (hr : (r : K) ≠ 1) (hnoncomm : ¬ Commute s t) :
    ∃ ψ : G →* Equiv.Perm K, Function.Injective ψ ∧
      (∀ z : K, ψ s z = (r : K) * z) ∧
      ∀ z : K, ψ t z = (q : K) * z + 1 := by
  let c : K := a / (1 - (r : K))
  have hrc : (r : K) * c + a = c := by
    dsimp [c]
    field_simp
    ring
  let d : K := (q : K) * c + b - c
  have hd : d ≠ 0 := by
    intro hd
    have hqc : (q : K) * c + b = c := sub_eq_zero.mp hd
    have ha : a = c - (r : K) * c := by linear_combination hrc
    have hb : b = c - (q : K) * c := by linear_combination hqc
    apply hnoncomm
    apply hφ
    ext z
    simp only [map_mul, Equiv.Perm.mul_apply, hs, ht]
    rw [ha, hb]
    ring
  let E : Equiv.Perm K := {
    toFun z := d * z + c
    invFun z := d⁻¹ * (z - c)
    left_inv := by intro z; simp [hd]
    right_inv := by intro z; simp [hd] }
  let ψ := (MulAut.conj E⁻¹).toMonoidHom.comp φ
  have hψ (g : G) (z : K) : ψ g z = d⁻¹ * (φ g (d * z + c) - c) := rfl
  refine ⟨ψ, (MulAut.conj E⁻¹).injective.comp hφ, ?_, ?_⟩
  · intro z
    rw [hψ, hs]
    have hcalc : (r : K) * (d * z + c) + a - c = d * ((r : K) * z) := by
      linear_combination hrc
    rw [hcalc]
    simp [hd]
  · intro z
    rw [hψ, ht]
    have hcalc : (q : K) * (d * z + c) + b - c = d * ((q : K) * z + 1) := by
      dsimp [d]
      ring
    rw [hcalc]
    simp [hd]

/-- Powers of a generator acting by a scalar act by the corresponding scalar
power. -/
theorem scalar_action_pow
    {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (s : G) (r : K)
    (hs : ∀ z : K, φ s z = r * z) (n : ℕ) (z : K) :
    φ (s ^ n) z = r ^ n * z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', map_mul, Equiv.Perm.mul_apply, hs, ih, pow_succ']
    exact (mul_assoc _ _ _).symm

/-- A nonidentity scalar in a faithful action has no order coprime to the
order of the acting group. -/
theorem scalar_action_pow_ne_one
    {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (s : G) (r : K) (hs : ∀ z : K, φ s z = r * z)
    (hr : r ≠ 1) (n : ℕ) (hn : (Nat.card G).Coprime n) : r ^ n ≠ 1 := by
  intro hrn
  have hsn : s ^ n = 1 := by
    apply hφ
    ext z
    rw [scalar_action_pow φ s r hs, hrn]
    simp
  have hsone : s = 1 := hn.pow_left_bijective.1 (by simpa using hsn)
  have := hs 1
  rw [hsone, φ.map_one] at this
  exact hr (by simpa using this.symm)

/-- The scalar exclusions used by the explicit eight-cycle constructions. -/
theorem scalar_action_square_and_fourth_ne_one
    {G K : Type*} [Group G] [Field K]
    (hodd : Odd (Nat.card G))
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (s : G) (r : K) (hs : ∀ z : K, φ s z = r * z)
    (hr : r ≠ 1) : r ^ 2 ≠ 1 ∧ r ^ 4 ≠ 1 := by
  refine ⟨scalar_action_pow_ne_one φ hφ s r hs hr 2 hodd.coprime_two_right, ?_⟩
  exact scalar_action_pow_ne_one φ hφ s r hs hr 4
    (by simpa using hodd.coprime_two_right.pow_right 2)

/-- Extract the scalar homomorphism from faithful affine coordinates. Its
kernel is exactly the normal translation subgroup. -/
theorem exists_scalar_hom_of_affine_action
    {G K : Type*} [Group G] [Field K]
    (V : Subgroup G) [IsMulCommutative V]
    (e : Additive V ≃+ K)
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (hV : ∀ (v : V) (z : K), φ (v : G) z = z + e (Additive.ofMul v))
    (haffine : ∀ g : G, ∃ (r : Kˣ) (a : K), ∀ z : K, φ g z = (r : K) * z + a) :
    ∃ χ : G →* Kˣ, χ.ker = V ∧
      ∀ g : G, ∃ a : K, ∀ z : K, φ g z = (χ g : K) * z + a := by
  classical
  choose r a h using haffine
  have hcoeff (g : G) : (r g : K) = φ g 1 - φ g 0 := by
    rw [h, h]
    ring
  let χ : G →* Kˣ := {
    toFun := r
    map_one' := by
      apply Units.ext
      rw [hcoeff, φ.map_one]
      simp
    map_mul' := by
      intro g k
      apply Units.ext
      rw [hcoeff, φ.map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        h, h, h, h, Units.val_mul]
      ring }
  refine ⟨χ, ?_, fun g ↦ ⟨a g, h g⟩⟩
  ext g
  change χ g = 1 ↔ g ∈ V
  constructor
  · intro hg
    obtain ⟨v, hv⟩ := e.surjective (a g)
    have hgv : g = (v.toMul : G) := by
      apply hφ
      ext z
      rw [h, hV]
      change (r g : K) * z + a g = z + e v
      rw [hv]
      have hr : (r g : K) = 1 := congrArg Units.val hg
      rw [hr]
      simp
    rw [hgv]
    exact v.toMul.property
  · intro hg
    apply Units.ext
    change (r g : K) = 1
    rw [hcoeff, hV ⟨g, hg⟩, hV ⟨g, hg⟩]
    ring

/-- No power of a scalar coming from an odd-order group can equal minus one
in characteristic different from two. -/
theorem scalar_action_pow_ne_neg_one
    {G K : Type*} [Group G] [Field K]
    (hodd : Odd (Nat.card G))
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (s : G) (r : K) (hs : ∀ z : K, φ s z = r * z)
    (h2 : (2 : K) ≠ 0) (n : ℕ) : r ^ n ≠ -1 := by
  intro hn
  have hscalar (z : K) : φ (s ^ n) z = -z := by
    rw [scalar_action_pow φ s r hs, hn]
    simp
  have hsq : (s ^ n) ^ 2 = 1 := by
    apply hφ
    ext z
    simp only [pow_two, map_mul, Equiv.Perm.mul_apply, hscalar,
      neg_neg, map_one, Equiv.Perm.one_apply]
  have hsn : s ^ n = 1 := hodd.coprime_two_right.pow_left_bijective.1
    (by simpa using hsq)
  have h1 := hscalar 1
  rw [hsn, φ.map_one] at h1
  have hbad : (1 : K) = -1 := by simpa using h1
  apply h2
  linear_combination hbad

end CayleyErdosGyarfas

-- ===== from CayleyErdosGyarfas/CaseTwoCoordinates.lean =====
/-! Finite coordinate checks for the two sixteen-cycles in affine Case 2.
The scalar exclusions below are explicit polynomial identities checked by
`linear_combination`; every finite case is checked by the Lean kernel. -/

namespace CayleyErdosGyarfas

def caseTwoExponent : ℕ → ℕ
    | 0 => 0
    | 1 => 1
    | 2 => 3
    | 3 => 4
    | 4 => 0
    | 5 => 1
    | 6 => 4
    | 7 => 0
    | 8 => 2
    | 9 => 3
    | 10 => 1
    | 11 => 2
    | 12 => 3
    | 13 => 4
    | 14 => 1
    | 15 => 2
    | _ => 0
def caseTwoOffset {K : Type*} [Field K] (r : K) : ℕ → K
    | 0 => 0
    | 1 => 0
    | 2 => r
    | 3 => r
    | 4 => r
    | 5 => r
    | 6 => -r^4 + r
    | 7 => -r^4 + r
    | 8 => -r^4 + r + 1
    | 9 => -r^4 + r + 1
    | 10 => 1 - r^4
    | 11 => 1 - r^4
    | 12 => 1 - r^4
    | 13 => 1 - r^4
    | 14 => 1
    | 15 => 1
    | _ => 0

set_option maxHeartbeats 2000000 in
/-- The sixteen affine coordinates are distinct and their translate by one
meets them only at the coordinate `(r,1)`. -/
theorem caseTwo_coordinates {K : Type*} [Field K] (r : K)
    (horder : orderOf r = 5)
    (hC : r^4+r^3+r^2+r+1 = 0) (h2 : (2:K) ≠ 0) (h5 : (5:K) ≠ 0)
    (hP : 19*r^2-r+19 ≠ 0) :
    Function.Injective (fun i : Fin 16 ↦ (r ^ caseTwoExponent i, caseTwoOffset r i)) ∧
    ∀ i j : Fin 16,
      (r ^ caseTwoExponent j, 1 + caseTwoOffset r j) =
        (r ^ caseTwoExponent i, caseTwoOffset r i) →
      (r ^ caseTwoExponent i, caseTwoOffset r i) = (r, 1) := by
  have hd0 : (-r : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (1)*hC + (r^3 + r^2 + r + 1)*h
  have hd1 : (r^4 - r : K) ≠ 0 := by
    intro h
    apply h5
    linear_combination (-3*r^3 + 2*r^2 - 3*r + 5)*hC + (3*r^3 + r^2 + 4*r + 2)*h
  have hd2 : (r^4 - 1 : K) ≠ 0 := by
    intro h
    apply h5
    linear_combination (-r^3 - r^2 - r + 4)*hC + (r^3 + 2*r^2 + 3*r - 1)*h
  have hd3 : (-1 : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (0)*hC + (-1)*h
  have hd4 : (r^4 + r - 1 : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (-r^3 + r)*hC + (r^3 + r^2 - 1)*h
  have hd5 : (r^4 : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (1 - r)*hC + (r)*h
  have hd6 : (r : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (1)*hC + (-r^3 - r^2 - r - 1)*h
  have hd7 : (r - 1 : K) ≠ 0 := by
    intro h
    apply h5
    linear_combination (1)*hC + (-r^3 - 2*r^2 - 3*r - 4)*h
  have hd8 : (-r^4 : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (1 - r)*hC + (-r)*h
  have hd9 : (-r^4 + r : K) ≠ 0 := by
    intro h
    apply h5
    linear_combination (-3*r^3 + 2*r^2 - 3*r + 5)*hC + (-3*r^3 - r^2 - 4*r - 2)*h
  have hd10 : (1 - r^4 : K) ≠ 0 := by
    intro h
    apply h5
    linear_combination (-r^3 - r^2 - r + 4)*hC + (-r^3 - 2*r^2 - 3*r + 1)*h
  have hd11 : (-r^4 - r + 1 : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (-r^3 + r)*hC + (-r^3 - r^2 + 1)*h
  have hd12 : (1 - r : K) ≠ 0 := by
    intro h
    apply h5
    linear_combination (1)*hC + (r^3 + 2*r^2 + 3*r + 4)*h
  have hd13 : (1 : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (0)*hC + (1)*h
  have hd14 : (-r - 1 : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (1)*hC + (r^3 + r)*h
  have hd15 : (r^4 - r - 1 : K) ≠ 0 := by
    intro h
    apply hP
    linear_combination (-14*r^3 + 16*r^2 - 11*r + 21)*hC + (14*r^3 - 2*r^2 + 9*r + 2)*h
  have hd16 : (r^4 - 2 : K) ≠ 0 := by
    intro h
    apply hP
    linear_combination (-3*r^3 + 8*r^2 - 6*r + 7)*hC + (3*r^3 - 5*r^2 + r - 6)*h
  have hd17 : (-2 : K) ≠ 0 := by
    intro h
    apply h2
    linear_combination (0)*hC + (-1)*h
  have hd18 : (r^4 + r - 2 : K) ≠ 0 := by
    intro h
    apply h5
    linear_combination (-r^3 + r + 1)*hC + (r^3 + r^2 - 2)*h
  have hd19 : (r - 2 : K) ≠ 0 := by
    intro h
    apply hP
    linear_combination (3)*hC + (-3*r^3 - 9*r^2 - 2*r - 8)*h
  have hd20 : (-r^4 - 1 : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (-r^3 + r^2 - r)*hC + (-r^3 - r - 1)*h
  have hd21 : (-r^4 + r - 1 : K) ≠ 0 := by
    intro h
    apply hP
    linear_combination (-14*r^3 + 2*r^2 + 7*r + 3)*hC + (-14*r^3 - 12*r^2 - 5*r - 16)*h
  have hd22 : (-r^4 - r : K) ≠ 0 := by
    intro h
    apply (one_ne_zero : (1:K) ≠ 0)
    linear_combination (r^3 - r + 1)*hC + (r^3 + r^2)*h

  let e := caseTwoExponent
  let b := caseTwoOffset r
  have he_bound (i : ℕ) (hi : i < 16) : e i < 5 := by
    interval_cases i <;> norm_num [e, caseTwoExponent]
  constructor
  · intro i j hh
    change (r ^ e i, b i) = (r ^ e j, b j) at hh
    have hh := Prod.mk.inj hh
    have hexp : e i = e j := pow_injOn_Iio_orderOf
      (by simpa [horder] using he_bound i i.isLt)
      (by simpa [horder] using he_bound j j.isLt) hh.1
    have hoff := hh.2
    fin_cases i <;> fin_cases j <;> try norm_num [e, caseTwoExponent] at hexp
    all_goals try norm_num
    all_goals simp only [b, caseTwoOffset] at hoff
    all_goals first
      | (guard_hyp hoff : (0 : K) = (r : K)
         exact (hd0 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (0 : K) = (-r^4 + r : K)
         exact (hd1 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (0 : K) = (1 - r^4 : K)
         exact (hd2 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (0 : K) = (1 : K)
         exact (hd3 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (r : K) = (-r^4 + r + 1 : K)
         exact (hd2 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (r : K) = (1 - r^4 : K)
         exact (hd4 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (r : K) = (-r^4 + r : K)
         exact (hd5 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (r : K) = (0 : K)
         exact (hd6 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (r : K) = (1 : K)
         exact (hd7 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (-r^4 + r : K) = (r : K)
         exact (hd8 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (-r^4 + r : K) = (1 - r^4 : K)
         exact (hd7 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (-r^4 + r : K) = (0 : K)
         exact (hd9 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (-r^4 + r + 1 : K) = (1 - r^4 : K)
         exact (hd6 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (-r^4 + r + 1 : K) = (1 : K)
         exact (hd9 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (-r^4 + r + 1 : K) = (r : K)
         exact (hd10 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 - r^4 : K) = (0 : K)
         exact (hd10 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 - r^4 : K) = (r : K)
         exact (hd11 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 - r^4 : K) = (1 : K)
         exact (hd8 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 - r^4 : K) = (-r^4 + r + 1 : K)
         exact (hd0 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 - r^4 : K) = (-r^4 + r : K)
         exact (hd12 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 : K) = (0 : K)
         exact (hd13 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 : K) = (r : K)
         exact (hd12 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 : K) = (1 - r^4 : K)
         exact (hd5 (by linear_combination hoff)).elim)
      | (guard_hyp hoff : (1 : K) = (-r^4 + r + 1 : K)
         exact (hd1 (by linear_combination hoff)).elim)

  · intro i j heq
    change (r ^ e j, 1 + b j) = (r ^ e i, b i) at heq
    change (r ^ e i, b i) = (r, 1)
    simp only [Prod.mk.injEq] at heq
    have hexp : e i = e j := pow_injOn_Iio_orderOf
      (by simpa [horder] using he_bound i i.isLt)
      (by simpa [horder] using he_bound j j.isLt) heq.1.symm
    have hoff := heq.2
    fin_cases i <;> fin_cases j <;> try norm_num [e, caseTwoExponent] at hexp
    all_goals try norm_num [e, b, caseTwoExponent, caseTwoOffset]
    all_goals simp only [b, caseTwoOffset] at hoff
    all_goals first
      | (guard_hyp hoff : (1 : K) + (0 : K) = (0 : K)
         exact (hd3 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (r : K) = (0 : K)
         exact (hd14 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (-r^4 + r : K) = (0 : K)
         exact (hd15 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 - r^4 : K) = (0 : K)
         exact (hd16 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 : K) = (0 : K)
         exact (hd17 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (r : K) = (r : K)
         exact (hd3 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (-r^4 + r + 1 : K) = (r : K)
         exact (hd16 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 - r^4 : K) = (r : K)
         exact (hd18 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (-r^4 + r : K) = (r : K)
         exact (hd2 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (0 : K) = (r : K)
         exact (hd7 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 : K) = (r : K)
         exact (hd19 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (r : K) = (-r^4 + r : K)
         exact (hd20 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (-r^4 + r : K) = (-r^4 + r : K)
         exact (hd3 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 - r^4 : K) = (-r^4 + r : K)
         exact (hd19 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (0 : K) = (-r^4 + r : K)
         exact (hd21 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (-r^4 + r + 1 : K) = (-r^4 + r + 1 : K)
         exact (hd3 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 - r^4 : K) = (-r^4 + r + 1 : K)
         exact (hd7 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 : K) = (-r^4 + r + 1 : K)
         exact (hd21 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (r : K) = (-r^4 + r + 1 : K)
         exact (hd8 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (0 : K) = (1 - r^4 : K)
         exact (hd8 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (r : K) = (1 - r^4 : K)
         exact (hd22 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 - r^4 : K) = (1 - r^4 : K)
         exact (hd3 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 : K) = (1 - r^4 : K)
         exact (hd20 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (-r^4 + r + 1 : K) = (1 - r^4 : K)
         exact (hd14 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (-r^4 + r : K) = (1 - r^4 : K)
         exact (hd0 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 - r^4 : K) = (1 : K)
         exact (hd2 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (1 : K) = (1 : K)
         exact (hd3 (by linear_combination -hoff)).elim)
      | (guard_hyp hoff : (1 : K) + (-r^4 + r + 1 : K) = (1 : K)
         exact (hd15 (by linear_combination -hoff)).elim)

end CayleyErdosGyarfas

-- ===== from CayleyErdosGyarfas/AffineCaseTwo.lean =====
/-!
# The exceptional cyclic quotient of order five

The sixteen letters below are exactly the manuscript's word for `β`.
`CaseTwoCoordinates` verifies its vertex coordinates and their intersections.
The polynomial `19*r^2-r+19` records the possible extra intersections; explicit
integer identities show that at least one of the scalars `r` and `r^2` avoids
these intersections. The latter corresponds to the manuscript's replacement
of `(s,t)` by `(t,s⁻¹)`.
-/


namespace CayleyErdosGyarfas

private theorem fifth_scalar_data {K : Type*} [Field K] (r : K)
    (hr : r ≠ 1) (hr5 : r^5 = 1) :
    orderOf r = 5 ∧ r ≠ 0 ∧ r^4+r^3+r^2+r+1 = 0 ∧ (5:K) ≠ 0 := by
  have hord : orderOf r = 5 := by
    have hd := orderOf_dvd_of_pow_eq_one hr5
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h | h
    · exact (hr (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr5
  have hC : r^4+r^3+r^2+r+1 = 0 := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hr)
    linear_combination hr5
  refine ⟨hord, hr0, hC, ?_⟩
  intro hfive
  have hzero : (r-1)^4 = 0 := by
    linear_combination hC - r*(r^2-r+1)*hfive
  exact hr (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero))

private theorem fifth_scalar_indicator_alternative {K : Type*} [Field K] (r : K)
    (hC : r^4+r^3+r^2+r+1 = 0) :
    19*r^2-r+19 ≠ 0 ∨ 19*(r^2)^2-r^2+19 ≠ 0 := by
  by_contra! h
  have hP := h.1
  have hQ : -19*r^3-20*r^2-19*r = 0 := by linear_combination h.2 - 19*hC
  have ha : (341:K) = 0 := by
    linear_combination (19*r+360)*hC + (-r^3-20*r^2-20*r-1)*hP
  have hb : (7581:K) = 0 := by
    linear_combination (19*r^2+381*r+399)*hP + (19*r+360)*hQ
  have hfalse : (1:K) = 0 := by linear_combination 1823*ha - 82*hb
  exact one_ne_zero hfalse

set_option maxHeartbeats 2000000 in
private theorem affine_case_two_good_scalar {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (s t : G) (hs : s ∈ S) (ht : t ∈ S)
    (r : K) (hr : r ≠ 1) (hr5 : r^5 = 1) (h2 : (2:K) ≠ 0)
    (hP : 19*r^2-r+19 ≠ 0)
    (hsact : ∀ z, φ s z = r*z) (htact : ∀ z, φ t z = r^2*z+1) :
    HasSymmetricFigureEight S := by
  obtain ⟨horder, hr0, hC, h5⟩ := fifth_scalar_data r hr hr5
  obtain ⟨hcoords_inj, hcoords_inter⟩ := caseTwo_coordinates r horder hC h2 h5 hP
  have hir : r⁻¹ = r^4 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_succ'] using hr5
  have hir2 : (r^2)⁻¹ = r^3 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [← pow_add] using hr5
  have hsinv : ∀ z, φ s⁻¹ z = r^4*z := by
    intro z
    simpa [hir] using affine_inv_apply φ hr0
      (fun z ↦ show φ s z = r*z+0 by simpa using hsact z) z
  have htinv : ∀ z, φ t⁻¹ z = r^3*(z-1) := by
    intro z
    simpa [hir2] using affine_inv_apply φ (pow_ne_zero 2 hr0) htact z
  have hp5 : r^5 = 1 := by
    simpa [horder] using (pow_mod_orderOf r 5).symm
  have hp6 : r^6 = r := by
    simpa [horder] using (pow_mod_orderOf r 6).symm
  have hp10 : r^10 = 1 := by
    simpa [horder] using (pow_mod_orderOf r 10).symm
  have hp11 : r^11 = r := by
    simpa [horder] using (pow_mod_orderOf r 11).symm
  let letters : ℕ → G
    | 0 => s
    | 1 => t
    | 2 => s
    | 3 => s
    | 4 => s
    | 5 => t⁻¹
    | 6 => s
    | 7 => t
    | 8 => s
    | 9 => t⁻¹
    | 10 => s
    | 11 => s
    | 12 => s
    | 13 => t
    | 14 => s
    | 15 => t⁻¹
    | _ => 1
  let f (i : ℕ) : G := (List.ofFn (fun j : Fin i ↦ letters j)).prod
  let e : ℕ → ℕ := caseTwoExponent
  let b : ℕ → K := caseTwoOffset r
  have hstep (i : ℕ) : f (i+1) = f i * letters i := by
    simp only [f, List.ofFn_succ', List.prod_concat]
    rfl
  have haction : ∀ i < 17, ∀ z : K, φ (f i) z = r^(e i)*z+b i := by
    intro i
    induction i with
    | zero =>
      intro hi z
      simp [f, e, b, caseTwoExponent, caseTwoOffset]
    | succ i ih =>
      intro hi z
      rw [hstep, affine_mul_apply, ih (by omega)]
      have hi16 : i < 16 := by omega
      interval_cases i <;>
        simp only [letters, e, b, caseTwoExponent, caseTwoOffset,
          hsact, htact, htinv] <;> ring_nf
      all_goals (try simp only [hp5, hp6])
      all_goals ring
  have hinj : ∀ i < 16, ∀ j < 16, f i = f j → i = j := by
    intro i hi j hj hij
    have hh : r^(e i) = r^(e j) ∧ b i = b j :=
      affine_eq_coeffs (a := r^(e i)) (b := b i) (c := r^(e j)) (d := b j)
        (fun z ↦ by rw [← haction i (by omega), hij, haction j (by omega)])
    exact congrArg Fin.val (hcoords_inj (a₁ := ⟨i,hi⟩) (a₂ := ⟨j,hj⟩)
      (Prod.ext hh.1 hh.2))
  have hclose : f 16 = f 0 := by
    apply hφ
    ext z
    simp [haction, e, b, caseTwoExponent, caseTwoOffset]
  have hadj (i : ℕ) (hi : i < 16) :
      (SimpleGraph.mulCayley S).Adj (f i) (f (i+1)) := by
    have hne : f i ≠ f (i+1) := by
      intro h
      by_cases hi15 : i = 15
      · have hh := hinj 15 (by omega) 0 (by omega) (by simpa [hi15, hclose] using h)
        omega
      · have hh := hinj i hi (i+1) (by omega) h
        omega
    have hstep : f (i+1) = f i * letters i := by
      simp only [f, List.ofFn_succ', List.prod_concat]
      rfl
    rw [SimpleGraph.mulCayley_adj']
    refine ⟨hne, ?_⟩
    rw [hstep]
    interval_cases i <;> simp only [letters]
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inr (by simp)⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inr (by simp)⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inr (by simp)⟩
  obtain ⟨c, hc, hlen, hsupport⟩ := exists_cycle_of_sequence_with_support
    (n := 16) (by decide) f hclose hadj hinj
  let L : List (K × K) := List.ofFn (fun i : Fin 16 ↦ (r^(e i),b i))
  have hvertices : ∀ x ∈ c.support, ∃ p ∈ L, ∀ z, φ x z = p.1*z+p.2 := by
    intro x hx
    rw [hsupport, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    by_cases hi : i.val < 16
    · exact ⟨(r^(e i),b i), List.mem_ofFn.mpr ⟨⟨i,hi⟩,rfl⟩,
        haction i (by omega)⟩
    · have hi16 : i.val = 16 := by omega
      refine ⟨(1,0), List.mem_ofFn.mpr ⟨⟨0,by decide⟩,by simp [e,b,caseTwoExponent,caseTwoOffset]⟩, ?_⟩
      intro z
      rw [haction i i.isLt, hi16]
      simp [e,b,caseTwoExponent,caseTwoOffset]
  have hmember (i : ℕ) (hi : i < 17) : f i ∈ c.support := by
    rw [hsupport]
    exact List.mem_ofFn.mpr ⟨⟨i,hi⟩,rfl⟩
  have hf0 : f 0 = 1 := by simp [f]
  let c' := c.copy hf0 hf0
  have hc' : c'.IsCycle := by simpa [c'] using hc
  have hlen' : c'.length = 2^4 := by simpa [c'] using hlen
  apply figureEight_of_affine_coordinate_intersection_general φ hφ S c' 4
    (by decide) hc' hlen' L
    (by simpa [c'] using hvertices)
    (t*s⁻¹*s⁻¹) (f 14) (f 1) 1 1 r 1
  · intro z
    simp only [affine_mul_apply, hsinv, htact]
    ring_nf
    simp only [hp10]
    ring
  · intro z
    rw [haction 14 (by decide)]
    simp [e,b,caseTwoExponent,caseTwoOffset]
  · simpa [c'] using hmember 14 (by decide)
  · simpa [c'] using hmember 1 (by decide)
  · apply hφ
    ext z
    simp only [affine_mul_apply, hsinv, htact]
    rw [haction 1 (by decide), haction 14 (by decide)]
    simp only [e,b,caseTwoExponent,caseTwoOffset]
    ring_nf
    simp only [hp11]
  · intro p hp q hq heq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact hcoords_inter i j (by simpa only [one_mul] using heq)

/-- The manuscript's second affine case, where the two images in the
cyclic quotient of order five are distinct and not inverse. The two candidate
sixteen-cycles are the stated word and the word obtained by replacing
`(s,t)` with `(t,s⁻¹)`. -/
theorem affine_case_two {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (s t : G) (hs : s ∈ S) (ht : t ∈ S) (hsi : s⁻¹ ∈ S)
    (r : Kˣ) (hr : (r:K) ≠ 1) (hr5 : (r:K)^5 = 1) (h2 : (2:K) ≠ 0)
    (hsact : ∀ z, φ s z = (r:K)*z)
    (htact : ∀ z, φ t z = (r:K)^2*z+1) :
    HasSymmetricFigureEight S := by
  obtain ⟨horder, hr0, hC, h5⟩ := fifth_scalar_data (r:K) hr hr5
  rcases fifth_scalar_indicator_alternative (r:K) hC with hP | hP
  · exact affine_case_two_good_scalar φ hφ S s t hs ht (r:K) hr hr5 h2 hP hsact htact
  · have hr2 : (r:K)^2 ≠ 1 := by
      intro h
      have hd := orderOf_dvd_of_pow_eq_one h
      rw [horder] at hd
      norm_num at hd
    have hsinv : ∀ z, φ s⁻¹ z = (r:K)⁻¹*z := by
      intro z
      simpa using affine_inv_apply φ hr0
        (fun z ↦ show φ s z = (r:K)*z+0 by simpa using hsact z) z
    have hnoncomm : ¬ Commute t s⁻¹ := by
      intro h
      have hh := congrArg (fun g ↦ φ g 0) h.eq
      simp only [affine_mul_apply, htact, hsinv, mul_zero, zero_add,
        mul_one] at hh
      exact hr (inv_eq_one.mp hh.symm)
    obtain ⟨ψ, hψ, hsnew, htnew⟩ := normalize_two_affine_generators
      φ hφ t s⁻¹ (r^2) r⁻¹ 1 0
      (by simpa using htact) (by simpa using hsinv)
      (by simpa using hr2) hnoncomm
    have hrnew5 : ((r:K)^2)^5 = 1 := by
      calc
        ((r:K)^2)^5 = ((r:K)^5)^2 := by ring
        _ = 1 := by rw [hr5]; simp
    have hir : (r:K)⁻¹ = (r:K)^4 := by
      apply inv_eq_of_mul_eq_one_right
      simpa [pow_succ'] using hr5
    apply affine_case_two_good_scalar ψ hψ S t s⁻¹ ht hsi ((r:K)^2)
      hr2 hrnew5 h2 hP
    · simpa using hsnew
    · intro z
      simpa only [Units.val_inv_eq_inv_val, hir, ← pow_mul] using htnew z

end CayleyErdosGyarfas

-- ===== platform target: CayleyErdosGyarfas.affine_case_two (case (2) of the proof of Theorem 1.1) =====
open CayleyErdosGyarfas in
theorem solution {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (s t : G) (hs : s ∈ S) (ht : t ∈ S) (hsi : s⁻¹ ∈ S)
    (r : Kˣ) (hr : (r:K) ≠ 1) (hr5 : (r:K)^5 = 1) (h2 : (2:K) ≠ 0)
    (hsact : ∀ z, φ s z = (r:K)*z)
    (htact : ∀ z, φ t z = (r:K)^2*z+1) :
    HasSymmetricFigureEight S :=
  affine_case_two φ hφ S s t hs ht hsi r hr hr5 h2 hsact htact
