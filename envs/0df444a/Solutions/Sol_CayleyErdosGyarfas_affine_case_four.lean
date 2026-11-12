-- Prove2me | solution 1 for CayleyErdosGyarfas.affine_case_four
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T02:46:25.591379+00:00
-- url     : https://prove2.me/submissions/41f9062d-360f-4f7e-8235-c134964f7f59

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

-- ===== from CayleyErdosGyarfas/AffineCaseFour.lean =====
/-! The fourth affine case: one generator is a translation. -/


namespace CayleyErdosGyarfas


theorem caseFour_good_translate {K : Type*} [Field K] (r : K)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (h2 : (2 : K) ≠ 0)
    (hneg : ∀ k : ℕ, r ^ k ≠ -1) :
    (2*r ≠ 1 ∧ r ≠ -2 ∧ r^2+r ≠ 1 ∧ r^2+2*r ≠ 1) ∨
    (2*r ≠ -1 ∧ r ≠ 2 ∧ r^2-r ≠ 1 ∧ r^2-2*r ≠ 1) ∨
    ((7 : K) = 0 ∧ (r = 2 ∨ 2*r = 1)) := by
  by_cases hplus : 2*r ≠ 1 ∧ r ≠ -2 ∧ r^2+r ≠ 1 ∧ r^2+2*r ≠ 1
  · exact Or.inl hplus
  by_cases hminus : 2*r ≠ -1 ∧ r ≠ 2 ∧ r^2-r ≠ 1 ∧ r^2-2*r ≠ 1
  · exact Or.inr (Or.inl hminus)
  right; right
  simp only [not_and_or, not_not] at hplus hminus
  rcases hplus with hp | hp | hp | hp <;>
    rcases hminus with hm | hm | hm | hm
  · exact (h2 (by linear_combination hm-hp)).elim
  · exact (hneg 1 (by linear_combination hp-hm)).elim
  · exact (hneg 2 (by linear_combination r*hp-hm)).elim
  · exact ⟨by linear_combination (2*r-3)*hp-4*hm, Or.inr hp⟩
  · exact (hr1 (by linear_combination hm-hp)).elim
  · have h4 : (2 : K)*2 = 0 := by linear_combination hp-hm
    exact (mul_ne_zero h2 h2 h4).elim
  · exact (hneg 2 (by linear_combination hp+hm)).elim
  · exact (hneg 3 (by linear_combination (r^2-r)*hp-hm)).elim
  · exact (hneg 2 (by linear_combination -hp+r*hm)).elim
  · exact (hneg 2 (by linear_combination hp-hm)).elim
  · have h : (2 : K)*r = 0 := by linear_combination hp-hm
    exact (mul_ne_zero h2 hr0 h).elim
  · exact (hneg 4 (by linear_combination (r^2-1)*hp-r*hm)).elim
  · exact (hneg 3 (by linear_combination r*hp+(1-r)*hm)).elim
  · exact ⟨by linear_combination hp-(r+4)*hm, Or.inl hm⟩
  · exact (hneg 4 (by linear_combination (r^2-1)*hp-2*r*hm)).elim
  · have h : (2 : K)*2*r = 0 := by linear_combination hp-hm
    exact (mul_ne_zero (mul_ne_zero h2 h2) hr0 h).elim


set_option maxRecDepth 2000 in
theorem caseFour_translate_plus {K : Type*} [Field K] (r : K)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hrminus : r ≠ -1)
    (hrsq : r^2 ≠ 1) (h2 : (2:K) ≠ 0)
    (hbad1 : 2*r ≠ 1) (hbad2 : r ≠ -2)
    (hbad3 : r^2+r ≠ 1) (hbad4 : r^2+2*r ≠ 1)
    (x y : K × K)
    (hx : x ∈ [(1,0),(1,1),(r,1),(r,1+r),(1,1+r),(1,r),(r,r),(r,0)])
    (hy : y ∈ [(1,0),(1,1),(r,1),(r,1+r),(1,1+r),(1,r),(r,r),(r,0)])
    (heq : (r*y.1,r+r*y.2) = x) : x = (r,r) := by
  have hrsqr : r*r ≠ r := by
    intro h
    exact hr1 (mul_left_cancel₀ hr0 (by simpa using h))
  have hrsq' : r*r ≠ 1 := by simpa [pow_two] using hrsq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Prod.mk.injEq, mul_one, mul_zero] at heq ⊢ <;>
    simp only [true_and, false_and, hr1, hrsq', hrsqr] at heq
  all_goals first
    | rfl
    | exact (hr0 (by linear_combination heq)).elim
    | exact (hr0 (by linear_combination -heq)).elim
    | exact (hr1 (by linear_combination heq)).elim
    | exact (hr1 (by linear_combination -heq)).elim
    | exact (hbad1 (by linear_combination heq)).elim
    | exact (hbad3 (by linear_combination heq)).elim
    | exact (hbad4 (by linear_combination heq)).elim
    | exact (hrsq (by linear_combination heq)).elim
    | exact (hrminus (by apply mul_left_cancel₀ hr0; linear_combination heq)).elim
    | exact (hr0 (by apply mul_left_cancel₀ hr0; linear_combination heq)).elim
    | exact (hrminus (by apply mul_left_cancel₀ hr0; linear_combination -heq)).elim
    | exact (hr0 (by apply mul_left_cancel₀ hr0; linear_combination -heq)).elim
    | exact (hbad2 (by apply mul_left_cancel₀ hr0; linear_combination heq)).elim
    | exact (hr0 (by apply mul_left_cancel₀ h2; linear_combination heq)).elim
    | exact (zero_ne_one (by linear_combination heq)).elim
set_option maxRecDepth 2000 in
theorem caseFour_translate_minus {K : Type*} [Field K] (r : K)
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hrminus : r ≠ -1)
    (hrsq : r^2 ≠ 1) (h2 : (2:K) ≠ 0)
    (hbad1 : 2*r ≠ -1) (hbad2 : r ≠ 2)
    (hbad3 : r^2-r ≠ 1) (hbad4 : r^2-2*r ≠ 1)
    (x y : K × K)
    (hx : x ∈ [(1,0),(1,1),(r,1),(r,1+r),(1,1+r),(1,r),(r,r),(r,0)])
    (hy : y ∈ [(1,0),(1,1),(r,1),(r,1+r),(1,1+r),(1,r),(r,r),(r,0)])
    (heq : (r*y.1,-r+r*y.2) = x) : x = (r,0) := by
  have hrsqr : r*r ≠ r := by
    intro h
    exact hr1 (mul_left_cancel₀ hr0 (by simpa using h))
  have hrsq' : r*r ≠ 1 := by simpa [pow_two] using hrsq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Prod.mk.injEq, mul_one, mul_zero] at heq ⊢ <;>
    simp only [true_and, false_and, hr1, hrsq', hrsqr] at heq
  all_goals first
    | rfl
    | exact (hr0 (by linear_combination heq)).elim
    | exact (hr0 (by linear_combination -heq)).elim
    | exact (hr1 (by linear_combination heq)).elim
    | exact (hr1 (by linear_combination -heq)).elim
    | exact (hbad1 (by linear_combination heq)).elim
    | exact (hbad3 (by linear_combination heq)).elim
    | exact (hbad4 (by linear_combination heq)).elim
    | exact (hrsq (by linear_combination heq)).elim
    | exact (hrminus (by apply mul_left_cancel₀ hr0; linear_combination heq)).elim
    | exact (hr0 (by apply mul_left_cancel₀ hr0; linear_combination heq)).elim
    | exact (hrminus (by apply mul_left_cancel₀ hr0; linear_combination -heq)).elim
    | exact (hr0 (by apply mul_left_cancel₀ hr0; linear_combination -heq)).elim
    | exact (hbad2 (by apply mul_left_cancel₀ hr0; linear_combination heq)).elim
    | exact (hr0 (by apply mul_left_cancel₀ h2; linear_combination heq)).elim
    | exact (zero_ne_one (by linear_combination heq)).elim
    | exact (zero_ne_one (by linear_combination -heq)).elim
    | exact (hbad1 (by linear_combination -heq)).elim
    | exact (hbad2 (by apply mul_left_cancel₀ hr0; linear_combination -heq)).elim
    | exact (hr1 (by apply mul_left_cancel₀ hr0; linear_combination heq)).elim
    | exact (hrminus (by linear_combination heq)).elim
    | exact (hrminus (by linear_combination -heq)).elim
    | exact (hr0 (by apply mul_left_cancel₀ h2; linear_combination -heq)).elim

set_option maxRecDepth 2000 in
theorem caseFour_cycle {G K : Type*} [Group G] [Field K]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (s t : G) (hs : s ∈ S) (ht : t ∈ S)
    (r : K) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hrminus : r ≠ -1)
    (hsact : ∀ z, φ s z = r*z) (htact : ∀ z, φ t z = z+1) :
    ∃ c : (SimpleGraph.mulCayley S).Walk 1 1,
      c.IsCycle ∧ c.length = 8 ∧
      c.support = [1,t,t*s,t*s*t,t*s*t*s⁻¹,s*t*s⁻¹,s*t,s,1] := by
  let f : ℕ → G
    | 0 => 1 | 1 => t | 2 => t*s | 3 => t*s*t
    | 4 => t*s*t*s⁻¹ | 5 => s*t*s⁻¹
    | 6 => s*t | 7 => s | _ => 1
  let v : ℕ → K × K
    | 0 => (1,0) | 1 => (1,1) | 2 => (r,1) | 3 => (r,1+r)
    | 4 => (1,1+r) | 5 => (1,r) | 6 => (r,r) | 7 => (r,0)
    | _ => (1,0)
  have hsinv : ∀ z, φ s⁻¹ z = r⁻¹*z := by
    intro z
    simpa using affine_inv_apply φ hr0
      (fun z ↦ show φ s z = r*z+0 by simpa using hsact z) z
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
    interval_cases i <;> interval_cases j <;> try rfl
    all_goals simp only [v, Prod.mk.injEq] at hh
    all_goals simp only [hr1, hr1.symm,
      false_and, true_and, and_false, zero_ne_one, one_ne_zero] at hh
    all_goals first
      | contradiction
      | exact (hr0 (by linear_combination hh)).elim
      | exact (hr0 (by linear_combination -hh)).elim
      | exact (hr1 (by linear_combination hh)).elim
      | exact (hr1 (by linear_combination -hh)).elim
      | exact (hrminus (by linear_combination hh)).elim
      | exact (hrminus (by linear_combination -hh)).elim
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
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inl rfl⟩
    · exact ⟨s, hs, Or.inr (by simp [f])⟩
    · refine ⟨t, ht, Or.inr ?_⟩
      apply hφ
      ext z
      simp only [f, affine_mul_apply, hsinv, hsact, htact]
      field_simp
      ring
    · exact ⟨s, hs, Or.inl (by simp [f, mul_assoc])⟩
    · exact ⟨t, ht, Or.inr rfl⟩
    · exact ⟨s, hs, Or.inr (by simp [f])⟩
  obtain ⟨c, hc, hlen, hsupport⟩ := exists_cycle_of_sequence_with_support
    (n := 8) (by decide) f rfl hadj hinj
  refine ⟨c, hc, hlen, ?_⟩
  simpa [f, List.ofFn_succ] using hsupport






set_option maxRecDepth 2000 in
theorem caseFour_exception {G K : Type*} [Group G] [Field K] [CharP K 7]
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (s t : G) (hs : s ∈ S) (ht : t ∈ S)
    (hsact : ∀ z, φ s z = 2*z) (htact : ∀ z, φ t z = z+1) :
    HasSymmetricFigureEight S := by
  have h2 : (2:K) ≠ 0 := fun h ↦ by
    have hh := (CharP.cast_eq_zero_iff K 7 2).mp h
    norm_num at hh
  have h2inv : (2:K)⁻¹ = 4 := by
    apply inv_eq_of_mul_eq_one_right
    reduce_mod_char!
  have hsinv : ∀ z, φ s⁻¹ z = 4*z := by
    intro z
    simpa [h2inv] using affine_inv_apply φ h2
      (fun z ↦ show φ s z = 2*z+0 by simpa using hsact z) z
  have htrans (n : ℕ) (z : K) : φ (t^n) z = z+n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', affine_mul_apply, htact, ih, Nat.cast_add, Nat.cast_one]
      ring
  let f : ℕ → G
    | 0 => 1 | 1 => t | 2 => t^2 | 3 => t^3 | 4 => t^4 | 5 => t^5
    | 6 => t^5*s | 7 => t^5*s*t | _ => 1
  let v : ℕ → K × K
    | 0 => (1,0) | 1 => (1,1) | 2 => (1,2) | 3 => (1,3) | 4 => (1,4)
    | 5 => (1,5) | 6 => (2,5) | 7 => (2,0) | _ => (1,0)
  have haction (i : ℕ) (hi : i < 9) (z : K) :
      φ (f i) z = (v i).1*z+(v i).2 := by
    interval_cases i
    all_goals simp only [f, v, affine_mul_apply, hsact, htact, htrans, map_one,
      Equiv.Perm.one_apply, one_mul, add_zero, Nat.cast_ofNat]
    all_goals ring_nf
    all_goals reduce_mod_char!
  have hinj : ∀ i < 8, ∀ j < 8, f i = f j → i = j := by
    intro i hi j hj hij
    have hh : v i = v j := by
      apply Prod.ext
      · exact (affine_eq_coeffs (fun z ↦ by rw [← haction i (by omega), hij,
          haction j (by omega)])).1
      · exact (affine_eq_coeffs (fun z ↦ by rw [← haction i (by omega), hij,
          haction j (by omega)])).2
    interval_cases i <;> interval_cases j <;> try rfl
    all_goals simp only [v, Prod.mk.injEq] at hh
    all_goals obtain ⟨hha, hhb⟩ := hh
    all_goals solve
      | have hz := sub_eq_zero.mpr hha
        reduce_mod_char! at hz
        first
        | exact (one_ne_zero hz).elim
        | have hn := (CharP.cast_eq_zero_iff K 7 _).mp hz
          norm_num at hn
      | have hz := sub_eq_zero.mpr hhb
        reduce_mod_char! at hz
        first
        | exact (one_ne_zero hz).elim
        | have hn := (CharP.cast_eq_zero_iff K 7 _).mp hz
          norm_num at hn
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
    · exact ⟨t, ht, Or.inl (by simp [f, pow_succ])⟩
    · exact ⟨t, ht, Or.inl (by simp [f, pow_succ])⟩
    · exact ⟨t, ht, Or.inl (by simp [f, pow_succ])⟩
    · exact ⟨t, ht, Or.inl (by simp [f, pow_succ])⟩
    · exact ⟨s, hs, Or.inl rfl⟩
    · exact ⟨t, ht, Or.inl rfl⟩
    · refine ⟨s, hs, Or.inr ?_⟩
      apply hφ
      ext z
      simp only [f, affine_mul_apply, hsact, htact, htrans, map_one,
        Equiv.Perm.one_apply, Nat.cast_ofNat]
      ring_nf
      reduce_mod_char!
  obtain ⟨c, hc, hlen, hsupport⟩ := exists_cycle_of_sequence_with_support
    (n := 8) (by decide) f rfl hadj hinj
  have hsupp : c.support = [1,t,t^2,t^3,t^4,t^5,t^5*s,t^5*s*t,1] := by
    simpa [f, List.ofFn_succ] using hsupport
  let L : List (K × K) := [(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,0)]
  have hvertices : ∀ x ∈ c.support, ∃ p ∈ L, ∀ z, φ x z = p.1*z+p.2 := by
    intro x hx
    rw [hsupp] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact ⟨v 0, by simp [v, L], haction 0 (by decide)⟩
      | exact ⟨v 1, by simp [v, L], haction 1 (by decide)⟩
      | exact ⟨v 2, by simp [v, L], haction 2 (by decide)⟩
      | exact ⟨v 3, by simp [v, L], haction 3 (by decide)⟩
      | exact ⟨v 4, by simp [v, L], haction 4 (by decide)⟩
      | exact ⟨v 5, by simp [v, L], haction 5 (by decide)⟩
      | exact ⟨v 6, by simp [v, L], haction 6 (by decide)⟩
      | exact ⟨v 7, by simp [v, L], haction 7 (by decide)⟩
  have hs_eq : t^5*s*t = s := by
    apply hφ
    ext z
    rw [hsact]
    simpa only [f, v, add_zero] using haction 7 (by decide) z
  apply figureEight_of_affine_coordinate_intersection_general φ hφ S c 3 (by decide)
    hc (by simpa using hlen) L hvertices s s 1 2 0 2 0
  · simpa using hsact
  · simpa using hsact
  · rw [← hs_eq]; simp [hsupp]
  · simp [hsupp]
  · simp
  · intro p hp q hq heq
    simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try rfl
    all_goals simp only [Prod.mk.injEq] at heq
    all_goals obtain ⟨hha, hhb⟩ := heq
    all_goals solve
      | have hz := sub_eq_zero.mpr hha
        reduce_mod_char! at hz
        first
        | exact (one_ne_zero hz).elim
        | have hn := (CharP.cast_eq_zero_iff K 7 _).mp hz
          norm_num at hn
      | have hz := sub_eq_zero.mpr hhb
        reduce_mod_char! at hz
        first
        | exact (one_ne_zero hz).elim
        | have hn := (CharP.cast_eq_zero_iff K 7 _).mp hz
          norm_num at hn



/-- The manuscript’s fourth affine case. The commutator of a translation
and its scalar conjugate gives an eight-cycle. Two explicit translates work
unless the scalar is 2 or its inverse in characteristic 7; the exceptional
word `t⁵ s t s⁻¹` then supplies a symmetric figure-eight. -/
theorem affine_case_four {G K : Type*} [Group G] [Field K]
    (hodd : Odd (Nat.card G))
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (s t : G) (hs : s ∈ S) (ht : t ∈ S)
    (r : K) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (h2 : (2:K) ≠ 0)
    (hsact : ∀ z, φ s z = r*z) (htact : ∀ z, φ t z = z+1) :
    HasSymmetricFigureEight S := by
  have hneg := scalar_action_pow_ne_neg_one hodd φ hφ s r hsact h2
  have hrminus : r ≠ -1 := by simpa only [pow_one] using hneg 1
  have hrsq : r^2 ≠ 1 :=
    (scalar_action_square_and_fourth_ne_one hodd φ hφ s r hsact hr1).1
  have hsinv : ∀ z, φ s⁻¹ z = r⁻¹*z := by
    intro z
    simpa using affine_inv_apply φ hr0
      (fun z ↦ show φ s z = r*z+0 by simpa using hsact z) z
  rcases caseFour_good_translate r hr0 hr1 h2 hneg with hplus | hminus | ⟨h7, hexc⟩
  case inr.inr =>
    have : CharP K 7 := (CharP.charP_iff_prime_eq_zero (by decide : Nat.Prime 7)).mpr h7
    rcases hexc with hr | hr
    · exact caseFour_exception φ hφ S s t hs ht (by simpa only [hr] using hsact) htact
    · have hri : r⁻¹ = 2 := inv_eq_of_mul_eq_one_right (by simpa only [mul_comm] using hr)
      exact caseFour_exception φ hφ S s⁻¹ t (hinv s hs) ht
        (by simpa only [hri] using hsinv) htact
  all_goals
    obtain ⟨c, hc, hlen, hsupport⟩ := caseFour_cycle φ hφ S s t hs ht
      r hr0 hr1 hrminus hsact htact
    let L : List (K × K) := [(1,0),(1,1),(r,1),(r,1+r),(1,1+r),(1,r),(r,r),(r,0)]
    have hvertices : ∀ x ∈ c.support, ∃ p ∈ L, ∀ z, φ x z = p.1*z+p.2 := by
      intro x hx
      rw [hsupport] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨(1,0), by simp [L], ?_⟩; simp
      · exact ⟨(1,1), by simp [L], fun z ↦ by simpa using htact z⟩
      · refine ⟨(r,1), by simp [L], ?_⟩
        intro z; simp only [affine_mul_apply, hsact, htact]
      · refine ⟨(r,1+r), by simp [L], ?_⟩
        intro z; simp only [affine_mul_apply, hsact, htact]; ring
      · refine ⟨(1,1+r), by simp [L], ?_⟩
        intro z; simp only [affine_mul_apply, hsact, htact, hsinv]
        field_simp; ring
      · refine ⟨(1,r), by simp [L], ?_⟩
        intro z; simp only [affine_mul_apply, hsact, htact, hsinv]
        field_simp
      · refine ⟨(r,r), by simp [L], ?_⟩
        intro z; simp only [affine_mul_apply, hsact, htact]; ring
      · exact ⟨(r,0), by simp [L], fun z ↦ by simpa using hsact z⟩
      · refine ⟨(1,0), by simp [L], ?_⟩; simp
  · apply figureEight_of_affine_coordinate_intersection_general φ hφ S c 3 (by decide)
      hc (by simpa using hlen) L hvertices (s*t) (s*t) 1 r r r r
    · intro z; simp only [affine_mul_apply, hsact, htact]; ring
    · intro z; simp only [affine_mul_apply, hsact, htact]; ring
    · simp [hsupport]
    · simp [hsupport]
    · simp
    · exact fun p hp q hq heq ↦ caseFour_translate_plus r hr0 hr1 hrminus hrsq h2
        hplus.1 hplus.2.1 hplus.2.2.1 hplus.2.2.2 p q hp hq heq
  · have htinverse : ∀ z, φ t⁻¹ z = z-1 := by
      intro z
      simpa using affine_inv_apply φ one_ne_zero
        (fun z ↦ show φ t z = 1*z+1 by simpa using htact z) z
    apply figureEight_of_affine_coordinate_intersection_general φ hφ S c 3 (by decide)
      hc (by simpa using hlen) L hvertices (s*t⁻¹) s t r (-r) r 0
    · intro z; simp only [affine_mul_apply, hsact, htinverse]; ring
    · intro z; simpa using hsact z
    · simp [hsupport]
    · simp [hsupport]
    · group
    · exact fun p hp q hq heq ↦ caseFour_translate_minus r hr0 hr1 hrminus hrsq h2
        hminus.1 hminus.2.1 hminus.2.2.1 hminus.2.2.2 p q hp hq heq


end CayleyErdosGyarfas

-- ===== platform target: CayleyErdosGyarfas.affine_case_four (case (4) of the proof of Theorem 1.1) =====
open CayleyErdosGyarfas in
theorem solution {G K : Type*} [Group G] [Field K]
    (hodd : Odd (Nat.card G))
    (φ : G →* Equiv.Perm K) (hφ : Function.Injective φ)
    (S : Set G) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (s t : G) (hs : s ∈ S) (ht : t ∈ S)
    (r : K) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (h2 : (2:K) ≠ 0)
    (hsact : ∀ z, φ s z = r*z) (htact : ∀ z, φ t z = z+1) :
    HasSymmetricFigureEight S :=
  affine_case_four hodd φ hφ S hinv s t hs ht r hr0 hr1 h2 hsact htact
