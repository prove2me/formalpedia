-- Prove2me | solution 1 for BunkbedTM.profile_indicator
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T16:06:10.937333+00:00
-- url     : https://prove2.me/submissions/30e8c5f4-ca35-4b67-bbc7-902468fd02fb

import Definitions.Def_BunkbedTransfer
import Theorems.Thm_BunkbedAux_wzProb_pair_sum

/-!
# Bunkbed connectivity on Hollom's hypergraph depends only on the two level profiles

Two reductions of the `5 ^ 12`-term Wierman--Ziff sum.

`wzProb_split` — the two levels are conditionally independent (each hyperedge draws its state
independently on each level, and the posts over `T = {1,6,8}` are always present), so the sum
factors into a double sum over a level-0 and a level-1 configuration.

`profile_determines` and `fold_represents` — whether `0` on level `0` reaches `9` on level `l`
depends on the two configurations only through the partitions they induce on the five special
vertices `{0,1,6,8,9}`, and the transfer matrix `step` computes exactly those partitions. A walk
can change level only at a post, and the posts stand over `T`, which is part of the recorded
boundary; that is why nothing else about the configuration matters.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

/-!
# M2 — turning `wzProb` into transfer-matrix bookkeeping

Three purely combinatorial rearrangements, no graph theory:

* `wzProb_split` — the `5 ^ 12`-term sum defining `wzProb` factors as a double sum over the two
  *level configurations* `c₀, c₁ : Fin 6 → WZ`, with weight `(∏ i, P (c₀ i)) * (∏ i, P (c₁ i))`.
  Built on the published `BunkbedAux.wzProb_pair_sum` together with the equivalence
  `(ι → WZ × WZ) ≃ (ι → WZ) × (ι → WZ)`.
* `nested` — a single sum over `Fin 6 → WZ` unrolled into six nested sums over `WZ`, with the
  profile written as six explicit applications of `Bunkbed.TM.step`. This is the shape the
  dynamic program consumes.
* `fiberwise` — one dynamic-programming step: a sum over (state, hyperedge-state) pairs
  regrouped by the resulting state.
-/


open Bunkbed Bunkbed.Hyper Bunkbed.TM SimpleGraph Finset

/-! ## Splitting `wzProb` into two independent levels -/

/-- Assemble a pair configuration from the two level configurations. -/
private def levelPair {ι : Type*} : ((ι → WZ) × (ι → WZ)) ≃ (ι → WZ × WZ) where
  toFun c := fun i => (c.1 i, c.2 i)
  invFun φ := (fun i => (φ i).1, fun i => (φ i).2)
  left_inv c := rfl
  right_inv φ := rfl

/-- The level-split form of `wzProb`, as a sum over *pairs* of level configurations. -/
private lemma wzProb_pair {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → (V × V × V)) (T : Finset V) (P : WZ → ℚ) (x y : V × Fin 2) :
    wzProb t T P x y
      = ∑ c : (ι → WZ) × (ι → WZ),
          (if (wzGraph t T (fun p => if p.2 = 0 then c.1 p.1 else c.2 p.1)).Reachable x y
            then (1 : ℚ) else 0) * ((∏ i, P (c.1 i)) * (∏ i, P (c.2 i))) := by
  rw [BunkbedAux.wzProb_pair_sum, ← Equiv.sum_comp levelPair]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [mul_comm]
  congr 1
  simp only [levelPair, Equiv.coe_fn_mk]
  rw [Finset.prod_mul_distrib]

/-- `wzProb` as a product of two independent level sums. -/
theorem wzProb_split (P : WZ → ℚ) (x y : Fin 10 × Fin 2) :
    wzProb hollomTriple hollomT P x y
      = ∑ c₀ : Fin 6 → WZ, ∑ c₁ : Fin 6 → WZ,
          (if (wzGraph hollomTriple hollomT
                (fun p => if p.2 = 0 then c₀ p.1 else c₁ p.1)).Reachable x y then (1 : ℚ) else 0)
            * ((∏ i, P (c₀ i)) * (∏ i, P (c₁ i))) := by
  rw [wzProb_pair]
  simp only [Fintype.sum_prod_type]

/-! ## Unrolling a level sum into six nested sums -/

/-- `(Fin 6 → WZ)` as a sixfold product. -/
private def vec6 : (WZ × WZ × WZ × WZ × WZ × WZ) ≃ (Fin 6 → WZ) where
  toFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2]
  invFun c := (c 0, c 1, c 2, c 3, c 4, c 5)
  left_inv p := rfl
  right_inv c := by funext i; fin_cases i <;> rfl

private lemma vec6_apply (p : WZ × WZ × WZ × WZ × WZ × WZ) :
    (vec6 p : Fin 6 → WZ)
      = ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2] := rfl

/-- `prof`, i.e. `fold 6`, written out as six `step`s. -/
private lemma prof_eq (c : Fin 6 → WZ) :
    prof c
      = step 5 (c 5) (step 4 (c 4) (step 3 (c 3)
          (step 2 (c 2) (step 1 (c 1) (step 0 (c 0) stInit))))) := rfl

/-- A sum over level configurations, unrolled into six nested sums over the six hyperedges. -/
theorem nested (P : WZ → ℚ) (g : St → ℚ) :
    (∑ c : Fin 6 → WZ, g (prof c) * ∏ i, P (c i))
      = ∑ t₀ : WZ, ∑ t₁ : WZ, ∑ t₂ : WZ, ∑ t₃ : WZ, ∑ t₄ : WZ, ∑ t₅ : WZ,
          (P t₀ * P t₁ * P t₂ * P t₃ * P t₄ * P t₅)
            * g (step 5 t₅ (step 4 t₄ (step 3 t₃ (step 2 t₂ (step 1 t₁ (step 0 t₀ stInit)))))) := by
  rw [← Equiv.sum_comp vec6]
  rw [show (fun p : WZ × WZ × WZ × WZ × WZ × WZ => g (prof (vec6 p)) * ∏ i, P (vec6 p i))
        = (fun p : WZ × WZ × WZ × WZ × WZ × WZ =>
            (P p.1 * P p.2.1 * P p.2.2.1 * P p.2.2.2.1 * P p.2.2.2.2.1 * P p.2.2.2.2.2)
              * g (step 5 p.2.2.2.2.2 (step 4 p.2.2.2.2.1 (step 3 p.2.2.2.1
                  (step 2 p.2.2.1 (step 1 p.2.1 (step 0 p.1 stInit))))))) from ?_]
  · simp only [Fintype.sum_prod_type]
  · funext p
    rw [vec6_apply, prof_eq, Fin.prod_univ_six]
    exact mul_comm _ _

/-! ## One dynamic-programming step -/

/-- Regroup a sum over (state, hyperedge-state) pairs by the resulting state. -/
theorem fiberwise {β : Type*} [AddCommMonoid β] (i : Fin 6) (S T : Finset St)
    (hST : ∀ s ∈ S, ∀ t : WZ, step i t s ∈ T) (F : St → WZ → β) :
    (∑ s ∈ S, ∑ t : WZ, F s t)
      = ∑ s' ∈ T, ∑ p ∈ (S ×ˢ (Finset.univ : Finset WZ)).filter (fun p => step i p.2 p.1 = s'),
          F p.1 p.2 := by
  rw [← Finset.sum_product']
  refine (Finset.sum_fiberwise_of_maps_to (g := fun p : St × WZ => step i p.2 p.1) ?_ _).symm
  intro p hp
  exact hST p.1 (Finset.mem_product.1 hp).1 p.2

/-!
# M3 — the profile reduction

Connectivity of the WZ bunkbed between `0@0` and `9@l` depends only on the two partitions that
the levels induce on the five special vertices `sp = ![0, 1, 6, 8, 9]`.

The proof needs no walk surgery.  The only graph-theoretic input is that a set of vertices closed
under passing to a neighbour is closed under reachability (`mem_of_reachable`).  Applied to the
*explicitly described* set

`K = {x | x lies on level 0 and is level-0-reachable from 0} ∪ {x | x is level-reachable from an
open post}`

it yields the hard direction; the easy direction is an induction over the post closure
`closeStep`, whose three rounds are shown to reach a fixed point by a counting argument (a
strictly growing subset of the three post slots stabilises in at most three rounds).
-/


namespace Bunkbed.M3

open Bunkbed Bunkbed.Hyper Bunkbed.TM SimpleGraph Finset

/-! ## Generic reachability tools -/

/-- A set closed under passing to adjacent vertices is closed under reachability. -/
lemma mem_of_reachable {W : Type*} {G : SimpleGraph W} {K : Set W}
    (hK : ∀ u v, G.Adj u v → u ∈ K → v ∈ K) :
    ∀ {x y : W}, G.Reachable x y → x ∈ K → y ∈ K := by
  intro x y h
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact id
  | cons hadj _ ih => exact fun hx => ih (hK _ _ hadj hx)

/-- An edge of `ofEdges S` really is a member of `S`. -/
lemma mem_of_adj {W : Type*} {S : Finset (Sym2 W)} {u v : W} (h : (ofEdges S).Adj u v) :
    s(u, v) ∈ S := by
  simpa using ((fromEdgeSet_adj (s := (S : Set (Sym2 W)))).mp h).1

/-- A member of `S` with distinct endpoints is an edge of `ofEdges S`. -/
lemma adj_of_mem {W : Type*} {S : Finset (Sym2 W)} {u v : W} (h : s(u, v) ∈ S)
    (hne : u ≠ v) : (ofEdges S).Adj u v :=
  (fromEdgeSet_adj (s := (S : Set (Sym2 W)))).mpr ⟨by simpa using h, hne⟩

/-- **The bridging lemma.**  Two graphs each of whose edges is a reachability of the other have
the same reachability relation.  Both directions are the walk induction above. -/
lemma reach_congr {V : Type*} {G H : SimpleGraph V}
    (h1 : ∀ u v, G.Adj u v → H.Reachable u v) (h2 : ∀ u v, H.Adj u v → G.Reachable u v)
    {x y : V} : G.Reachable x y ↔ H.Reachable x y :=
  ⟨fun h => mem_of_reachable (K := {z | H.Reachable x z})
      (fun u v huv hu => (show H.Reachable x u from hu).trans (h1 u v huv)) h (Reachable.refl x),
   fun h => mem_of_reachable (K := {z | G.Reachable x z})
      (fun u v huv hu => (show G.Reachable x u from hu).trans (h2 u v huv)) h (Reachable.refl x)⟩

/-! ## The WZ edge sets are confined to one level -/

/-- Every vertex touched by `WZ.edges s t l` sits on level `l`. -/
lemma edges_level {V : Type*} [DecidableEq V] (s : WZ) (t : V × V × V) (l : Fin 2)
    {e : Sym2 (V × Fin 2)} (he : e ∈ WZ.edges s t l) {v : V × Fin 2} (hv : v ∈ e) : v.2 = l := by
  cases s <;>
    simp only [WZ.edges, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] at he
  · rcases he with rfl | rfl | rfl <;> rw [Sym2.mem_iff] at hv <;>
      rcases hv with rfl | rfl <;> rfl
  · subst he; rw [Sym2.mem_iff] at hv; rcases hv with rfl | rfl <;> rfl
  · subst he; rw [Sym2.mem_iff] at hv; rcases hv with rfl | rfl <;> rfl
  · subst he; rw [Sym2.mem_iff] at hv; rcases hv with rfl | rfl <;> rfl

/-! ## The post closure `closeStep` reaches its fixed point in three rounds -/

section Close

variable (r0 r1 : St)

/-- The `n`-th round of post closure. -/
private def itA (n : ℕ) : Fin 5 → Bool :=
  (closeStep r0 r1)^[n] (fun t => postSlots.contains t && (r0 0 = r0 t))

private lemma postSet_eq_itA : postSet r0 r1 = itA r0 r1 3 := rfl

private lemma itA_succ (n : ℕ) : itA r0 r1 (n + 1) = closeStep r0 r1 (itA r0 r1 n) := by
  simp only [itA, Function.iterate_succ_apply']

private lemma itA_zero_iff (t : Fin 5) :
    itA r0 r1 0 t = true ↔ (t ∈ postSlots ∧ r0 0 = r0 t) := by
  simp [itA]

private lemma closeStep_iff (A : Fin 5 → Bool) (t : Fin 5) :
    closeStep r0 r1 A t = true ↔
      (A t = true ∨ ∃ s ∈ postSlots, A s = true ∧ (r0 s = r0 t ∨ r1 s = r1 t)) := by
  simp [closeStep]

private lemma itA_mono (n : ℕ) (t : Fin 5) (h : itA r0 r1 n t = true) :
    itA r0 r1 (n + 1) t = true := by
  rw [itA_succ, closeStep_iff]
  exact Or.inl h

private lemma itA_le : ∀ (m k : ℕ) (t : Fin 5), itA r0 r1 m t = true →
    itA r0 r1 (m + k) t = true := by
  intro m k t h
  induction k with
  | zero => exact h
  | succ k ih => exact itA_mono r0 r1 (m + k) t ih

private lemma bool_of_iff : ∀ X Y : Bool, (X = true ↔ Y = true) → X = Y := by decide

/-- On the post slots, one round of closure depends only on the previous round's post slots. -/
private lemma closeStep_congr (A B : Fin 5 → Bool) (h : ∀ s ∈ postSlots, A s = B s)
    (t : Fin 5) (ht : t ∈ postSlots) : closeStep r0 r1 A t = closeStep r0 r1 B t := by
  refine bool_of_iff _ _ ?_
  rw [closeStep_iff, closeStep_iff]
  constructor
  · rintro (h1 | ⟨s, hs, h2, h3⟩)
    · exact Or.inl (by rw [← h t ht]; exact h1)
    · exact Or.inr ⟨s, hs, by rw [← h s hs]; exact h2, h3⟩
  · rintro (h1 | ⟨s, hs, h2, h3⟩)
    · exact Or.inl (by rw [h t ht]; exact h1)
    · exact Or.inr ⟨s, hs, by rw [h s hs]; exact h2, h3⟩

private lemma stab_prop (n : ℕ)
    (h : ∀ t ∈ postSlots, itA r0 r1 (n + 1) t = true → itA r0 r1 n t = true) :
    ∀ t ∈ postSlots, itA r0 r1 (n + 1 + 1) t = true → itA r0 r1 (n + 1) t = true := by
  have hEq : ∀ s ∈ postSlots, itA r0 r1 (n + 1) s = itA r0 r1 n s := fun s hs =>
    bool_of_iff _ _ ⟨h s hs, itA_mono r0 r1 n s⟩
  intro t ht hmem
  rw [itA_succ r0 r1 (n + 1)] at hmem
  rw [itA_succ r0 r1 n]
  rwa [closeStep_congr r0 r1 _ _ hEq t ht] at hmem

/-- How many of the three post slots are open. -/
private def cnt (A : Fin 5 → Bool) : ℕ :=
  (if A 1 = true then 1 else 0) + (if A 2 = true then 1 else 0) + (if A 3 = true then 1 else 0)

private lemma cnt_le (A : Fin 5 → Bool) : cnt A ≤ 3 := by
  unfold cnt; split_ifs <;> omega

private lemma cnt6 : ∀ a1 a2 a3 b1 b2 b3 : Bool, (a1 = true → b1 = true) →
    (a2 = true → b2 = true) → (a3 = true → b3 = true) →
    ((a1 ≠ true ∧ b1 = true) ∨ (a2 ≠ true ∧ b2 = true) ∨ (a3 ≠ true ∧ b3 = true)) →
    ((if a1 = true then 1 else 0) + (if a2 = true then 1 else 0)
        + (if a3 = true then 1 else 0) : ℕ)
      < (if b1 = true then 1 else 0) + (if b2 = true then 1 else 0)
        + (if b3 = true then 1 else 0) := by decide

private lemma cnt_lt (A B : Fin 5 → Bool) (h1 : A 1 = true → B 1 = true)
    (h2 : A 2 = true → B 2 = true) (h3 : A 3 = true → B 3 = true)
    (t : Fin 5) (ht : t ∈ postSlots) (hA : A t ≠ true) (hB : B t = true) : cnt A < cnt B := by
  have htc : t = 1 ∨ t = 2 ∨ t = 3 := by simpa [postSlots] using ht
  unfold cnt
  refine cnt6 (A 1) (A 2) (A 3) (B 1) (B 2) (B 3) h1 h2 h3 ?_
  rcases htc with rfl | rfl | rfl
  · exact Or.inl ⟨hA, hB⟩
  · exact Or.inr (Or.inl ⟨hA, hB⟩)
  · exact Or.inr (Or.inr ⟨hA, hB⟩)

private lemma stab_or_grow : ∀ n : ℕ,
    (∀ t ∈ postSlots, itA r0 r1 (n + 1) t = true → itA r0 r1 n t = true)
      ∨ n < cnt (itA r0 r1 (n + 1)) := by
  intro n
  induction n with
  | zero =>
    by_cases h : ∀ t ∈ postSlots, itA r0 r1 (0 + 1) t = true → itA r0 r1 0 t = true
    · exact Or.inl h
    · right
      show 0 < cnt (itA r0 r1 1)
      push Not at h
      obtain ⟨t, ht, h1, h2⟩ := h
      have hlt := cnt_lt (itA r0 r1 0) (itA r0 r1 1) (itA_mono r0 r1 0 1) (itA_mono r0 r1 0 2)
        (itA_mono r0 r1 0 3) t ht h2 h1
      omega
  | succ n ih =>
    by_cases h : ∀ t ∈ postSlots, itA r0 r1 (n + 1 + 1) t = true → itA r0 r1 (n + 1) t = true
    · exact Or.inl h
    · right
      have hn : n < cnt (itA r0 r1 (n + 1)) := by
        rcases ih with h0 | h0
        · exact absurd (stab_prop r0 r1 n h0) h
        · exact h0
      push Not at h
      obtain ⟨t, ht, h1, h2⟩ := h
      have hlt := cnt_lt (itA r0 r1 (n + 1)) (itA r0 r1 (n + 1 + 1)) (itA_mono r0 r1 (n + 1) 1)
        (itA_mono r0 r1 (n + 1) 2) (itA_mono r0 r1 (n + 1) 3) t ht h2 h1
      omega

private lemma stab3 : ∀ t ∈ postSlots, itA r0 r1 (3 + 1) t = true → itA r0 r1 3 t = true := by
  rcases stab_or_grow r0 r1 3 with h | h
  · exact h
  · exact absurd (cnt_le (itA r0 r1 (3 + 1))) (by omega)

/-- **The post set is closed.**  A post joined on either level to an open post is itself open. -/
lemma postSet_close (t : Fin 5) (ht : t ∈ postSlots) (s : Fin 5) (hs : s ∈ postSlots)
    (hA : postSet r0 r1 s = true) (hrel : r0 s = r0 t ∨ r1 s = r1 t) :
    postSet r0 r1 t = true := by
  rw [postSet_eq_itA] at hA ⊢
  refine stab3 r0 r1 t ht ?_
  rw [itA_succ, closeStep_iff]
  exact Or.inr ⟨s, hs, hA, hrel⟩

/-- The post set contains every post lying in vertex `0`'s level-`0` block. -/
lemma postSet_init (t : Fin 5) (ht : t ∈ postSlots) (h : r0 0 = r0 t) :
    postSet r0 r1 t = true := by
  rw [postSet_eq_itA]
  exact itA_le r0 r1 0 3 t ((itA_zero_iff r0 r1 t).mpr ⟨ht, h⟩)

end Close

/-! ## The graphs -/

section Graphs

variable (C : Fin 2 → (Fin 6 → WZ))

/-- The edges contributed by all six hyperedges on both levels. -/
abbrev bigE : Finset (Sym2 (Fin 10 × Fin 2)) :=
  Finset.univ.biUnion (fun p : Fin 6 × Fin 2 => (C p.2 p.1).edges (hollomTriple p.1) p.2)

/-- The full WZ bunkbed graph, in the level-indexed presentation. -/
abbrev Gg : SimpleGraph (Fin 10 × Fin 2) := ofEdges (bigE C ∪ posts hollomT)

/-- The graph of a single level. -/
abbrev Lg (a : Fin 2) : SimpleGraph (Fin 10 × Fin 2) := ofEdges (levelEdges (C a) a)

lemma levelEdges_sub (a : Fin 2) : levelEdges (C a) a ⊆ bigE C ∪ posts hollomT := by
  intro e he
  have he' : ∃ i ∈ (Finset.univ : Finset (Fin 6)), e ∈ (C a i).edges (hollomTriple i) a :=
    Finset.mem_biUnion.mp he
  obtain ⟨i, -, hi⟩ := he'
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(i, a), Finset.mem_univ _, hi⟩)

lemma Lg_le (a : Fin 2) : Lg C a ≤ Gg C :=
  fromEdgeSet_mono (Finset.coe_subset.mpr (levelEdges_sub C a))

lemma post_adj (t : Fin 10) (ht : t ∈ hollomT) : (Gg C).Adj (t, 0) (t, 1) := by
  have hm : s((t, (0 : Fin 2)), (t, (1 : Fin 2))) ∈ posts hollomT :=
    Finset.mem_image.mpr ⟨t, ht, rfl⟩
  exact adj_of_mem (Finset.mem_union_right _ hm) (by simp)

lemma bigE_mem {x y : Fin 10 × Fin 2} (h : s(x, y) ∈ bigE C) :
    x.2 = y.2 ∧ s(x, y) ∈ levelEdges (C x.2) x.2 := by
  have h' : ∃ p ∈ (Finset.univ : Finset (Fin 6 × Fin 2)),
      s(x, y) ∈ (C p.2 p.1).edges (hollomTriple p.1) p.2 := Finset.mem_biUnion.mp h
  obtain ⟨p, -, hp⟩ := h'
  have hx : x.2 = p.2 := edges_level _ _ _ hp (by simp)
  have hy : y.2 = p.2 := edges_level _ _ _ hp (by simp)
  refine ⟨hx.trans hy.symm, ?_⟩
  rw [hx]
  exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_univ _, hp⟩

lemma posts_mem {x y : Fin 10 × Fin 2} (h : s(x, y) ∈ posts hollomT) :
    ∃ t ∈ hollomT, (x = (t, 0) ∧ y = (t, 1)) ∨ (x = (t, 1) ∧ y = (t, 0)) := by
  have h' : ∃ t ∈ hollomT, s((t, (0 : Fin 2)), (t, (1 : Fin 2))) = s(x, y) :=
    Finset.mem_image.mp h
  obtain ⟨t, ht, hte⟩ := h'
  refine ⟨t, ht, ?_⟩
  rw [Sym2.eq_iff] at hte
  rcases hte with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h2.symm, h1.symm⟩

/-- Every edge of the bunkbed graph is either a level edge or a post. -/
lemma adj_cases {x y : Fin 10 × Fin 2} (h : (Gg C).Adj x y) :
    (x.2 = y.2 ∧ (Lg C x.2).Adj x y) ∨
      ∃ t ∈ hollomT, (x = (t, 0) ∧ y = (t, 1)) ∨ (x = (t, 1) ∧ y = (t, 0)) := by
  have hne : x ≠ y := h.ne
  have hmem : s(x, y) ∈ bigE C ∪ posts hollomT := mem_of_adj h
  rcases Finset.mem_union.mp hmem with h1 | h2
  · obtain ⟨hl, hle⟩ := bigE_mem C h1
    exact Or.inl ⟨hl, adj_of_mem hle hne⟩
  · exact Or.inr (posts_mem h2)

end Graphs

/-! ## Special vertices and levels -/

lemma sp0 : sp 0 = (0 : Fin 10) := by decide

lemma sp4 : sp 4 = (9 : Fin 10) := by decide

lemma sp_mem_hollomT : ∀ t ∈ postSlots, sp t ∈ hollomT := by decide

lemma exists_slot : ∀ t : Fin 10, t ∈ hollomT → ∃ tt ∈ postSlots, sp tt = t := by decide

lemma fin2_cases : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide

/-! ## The tracked set of vertices -/

section Main

variable (C : Fin 2 → (Fin 6 → WZ)) (R : Fin 2 → St)

lemma rel_iff (hR : ∀ a, Represents (R a) (levelRel (C a) a)) (a : Fin 2) (u v : Fin 5) :
    R a u = R a v ↔ (Lg C a).Reachable (sp u, a) (sp v, a) := hR a u v

/-- The vertices the argument tracks: those level-`0`-reachable from `0@0`, and those
level-reachable from an open post. -/
def Kset : Set (Fin 10 × Fin 2) :=
  {x | (x.2 = 0 ∧ (Lg C 0).Reachable ((0 : Fin 10), (0 : Fin 2)) x) ∨
      ∃ t ∈ postSlots, postSet (R 0) (R 1) t = true ∧ (Lg C x.2).Reachable (sp t, x.2) x}

lemma mem_Kset {x : Fin 10 × Fin 2} : x ∈ Kset C R ↔
    ((x.2 = 0 ∧ (Lg C 0).Reachable ((0 : Fin 10), (0 : Fin 2)) x) ∨
      ∃ t ∈ postSlots, postSet (R 0) (R 1) t = true ∧ (Lg C x.2).Reachable (sp t, x.2) x) :=
  Iff.rfl

lemma start_mem_Kset : ((0 : Fin 10), (0 : Fin 2)) ∈ Kset C R :=
  (mem_Kset C R).mpr (Or.inl ⟨rfl, Reachable.refl _⟩)

/-- A tracked post is an open post. -/
lemma post_of_mem_Kset (hR : ∀ a, Represents (R a) (levelRel (C a) a))
    (tt : Fin 5) (htt : tt ∈ postSlots) (a : Fin 2) (hu : (sp tt, a) ∈ Kset C R) :
    postSet (R 0) (R 1) tt = true := by
  rcases (mem_Kset C R).mp hu with ⟨h0, hre⟩ | ⟨s, hs, hAs, hre⟩
  · have ha : a = 0 := h0
    subst ha
    have hre' : (Lg C 0).Reachable (sp 0, (0 : Fin 2)) (sp tt, (0 : Fin 2)) := by
      rw [sp0]; exact hre
    exact postSet_init _ _ tt htt ((rel_iff C R hR 0 0 tt).mpr hre')
  · have hrel : R a s = R a tt := (rel_iff C R hR a s tt).mpr hre
    refine postSet_close _ _ tt htt s hs hAs ?_
    rcases fin2_cases a with rfl | rfl
    · exact Or.inl hrel
    · exact Or.inr hrel

/-- `K` is closed under adjacency in the bunkbed graph. -/
lemma Kset_closed (hR : ∀ a, Represents (R a) (levelRel (C a) a)) :
    ∀ u v, (Gg C).Adj u v → u ∈ Kset C R → v ∈ Kset C R := by
  intro u v hadj hu
  rcases adj_cases C hadj with ⟨hlvl, hA⟩ | ⟨t, ht, hcase⟩
  · rcases (mem_Kset C R).mp hu with ⟨h0, hre⟩ | ⟨s, hs, hAs, hre⟩
    · refine (mem_Kset C R).mpr (Or.inl ⟨hlvl.symm.trans h0, ?_⟩)
      rw [h0] at hA
      exact hre.trans hA.reachable
    · refine (mem_Kset C R).mpr (Or.inr ⟨s, hs, hAs, ?_⟩)
      rw [← hlvl]
      exact hre.trans hA.reachable
  · obtain ⟨tt, htt, hsp⟩ := exists_slot t ht
    subst hsp
    rcases hcase with ⟨hu1, hv1⟩ | ⟨hu1, hv1⟩
    · rw [hu1] at hu
      have hAtt := post_of_mem_Kset C R hR tt htt 0 hu
      exact (mem_Kset C R).mpr (Or.inr ⟨tt, htt, hAtt, by rw [hv1]⟩)
    · rw [hu1] at hu
      have hAtt := post_of_mem_Kset C R hR tt htt 1 hu
      exact (mem_Kset C R).mpr (Or.inr ⟨tt, htt, hAtt, by rw [hv1]⟩)

/-- Both copies of an open post are connected to `0@0`. -/
lemma both_levels (tt : Fin 5) (htt : tt ∈ postSlots) (a b : Fin 2)
    (h : (Gg C).Reachable ((0 : Fin 10), (0 : Fin 2)) (sp tt, a)) :
    (Gg C).Reachable ((0 : Fin 10), (0 : Fin 2)) (sp tt, b) := by
  have hp : (Gg C).Reachable (sp tt, (0 : Fin 2)) (sp tt, (1 : Fin 2)) :=
    (post_adj C (sp tt) (sp_mem_hollomT tt htt)).reachable
  rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl
  · exact h
  · exact h.trans hp
  · exact h.trans hp.symm
  · exact h

/-- Every post opened after `n` rounds of closure is connected to `0@0`, on both levels. -/
lemma reach_of_itA (hR : ∀ a, Represents (R a) (levelRel (C a) a)) :
    ∀ (n : ℕ) (t : Fin 5), t ∈ postSlots → itA (R 0) (R 1) n t = true →
      ∀ a : Fin 2, (Gg C).Reachable ((0 : Fin 10), (0 : Fin 2)) (sp t, a) := by
  intro n
  induction n with
  | zero =>
    intro t ht h a
    rw [itA_zero_iff] at h
    have hre : (Lg C 0).Reachable (sp 0, (0 : Fin 2)) (sp t, (0 : Fin 2)) :=
      (rel_iff C R hR 0 0 t).mp h.2
    rw [sp0] at hre
    exact both_levels C t ht 0 a (hre.mono (Lg_le C 0))
  | succ n ih =>
    intro t ht h a
    rw [itA_succ, closeStep_iff] at h
    rcases h with h | ⟨s, hs, hAs, hrel⟩
    · exact ih t ht h a
    · rcases hrel with hr | hr
      · have hre : (Lg C 0).Reachable (sp s, (0 : Fin 2)) (sp t, (0 : Fin 2)) :=
          (rel_iff C R hR 0 s t).mp hr
        exact both_levels C t ht 0 a ((ih s hs hAs 0).trans (hre.mono (Lg_le C 0)))
      · have hre : (Lg C 1).Reachable (sp s, (1 : Fin 2)) (sp t, (1 : Fin 2)) :=
          (rel_iff C R hR 1 s t).mp hr
        exact both_levels C t ht 1 a ((ih s hs hAs 1).trans (hre.mono (Lg_le C 1)))

lemma reach_of_postSet (hR : ∀ a, Represents (R a) (levelRel (C a) a))
    (t : Fin 5) (ht : t ∈ postSlots) (h : postSet (R 0) (R 1) t = true) (a : Fin 2) :
    (Gg C).Reachable ((0 : Fin 10), (0 : Fin 2)) (sp t, a) := by
  rw [postSet_eq_itA] at h
  exact reach_of_itA C R hR 3 t ht h a

end Main

/-! ## `glueConn`, unfolded -/

lemma glueConn_zero (r0 r1 : St) :
    glueConn r0 r1 0 = true ↔
      (r0 0 = r0 4 ∨ ∃ t ∈ postSlots, postSet r0 r1 t = true ∧ r0 t = r0 4) := by
  simp [glueConn]

lemma glueConn_one (r0 r1 : St) :
    glueConn r0 r1 1 = true ↔ ∃ t ∈ postSlots, postSet r0 r1 t = true ∧ r1 t = r1 4 := by
  simp [glueConn]

/-! ## The reduction -/

section Final

variable (C : Fin 2 → (Fin 6 → WZ)) (R : Fin 2 → St)

lemma forward (hR : ∀ a, Represents (R a) (levelRel (C a) a)) (l : Fin 2)
    (h : (Gg C).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), l)) :
    glueConn (R 0) (R 1) l = true := by
  have hK : ((9 : Fin 10), l) ∈ Kset C R :=
    mem_of_reachable (Kset_closed C R hR) h (start_mem_Kset C R)
  rcases fin2_cases l with rfl | rfl
  · rw [glueConn_zero]
    rcases (mem_Kset C R).mp hK with ⟨-, hre⟩ | ⟨s, hs, hAs, hre⟩
    · refine Or.inl ((rel_iff C R hR 0 0 4).mpr ?_)
      rw [sp0, sp4]; exact hre
    · refine Or.inr ⟨s, hs, hAs, (rel_iff C R hR 0 s 4).mpr ?_⟩
      rw [sp4]; exact hre
  · rw [glueConn_one]
    rcases (mem_Kset C R).mp hK with ⟨h0, -⟩ | ⟨s, hs, hAs, hre⟩
    · exact absurd h0 (by decide)
    · refine ⟨s, hs, hAs, (rel_iff C R hR 1 s 4).mpr ?_⟩
      rw [sp4]; exact hre

lemma backward (hR : ∀ a, Represents (R a) (levelRel (C a) a)) (l : Fin 2)
    (h : glueConn (R 0) (R 1) l = true) :
    (Gg C).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), l) := by
  rcases fin2_cases l with rfl | rfl
  · rw [glueConn_zero] at h
    rcases h with h | ⟨s, hs, hAs, hrel⟩
    · have hre : (Lg C 0).Reachable (sp 0, (0 : Fin 2)) (sp 4, (0 : Fin 2)) :=
        (rel_iff C R hR 0 0 4).mp h
      rw [sp0, sp4] at hre
      exact hre.mono (Lg_le C 0)
    · have hre : (Lg C 0).Reachable (sp s, (0 : Fin 2)) (sp 4, (0 : Fin 2)) :=
        (rel_iff C R hR 0 s 4).mp hrel
      rw [sp4] at hre
      exact (reach_of_postSet C R hR s hs hAs 0).trans (hre.mono (Lg_le C 0))
  · rw [glueConn_one] at h
    obtain ⟨s, hs, hAs, hrel⟩ := h
    have hre : (Lg C 1).Reachable (sp s, (1 : Fin 2)) (sp 4, (1 : Fin 2)) :=
      (rel_iff C R hR 1 s 4).mp hrel
    rw [sp4] at hre
    exact (reach_of_postSet C R hR s hs hAs 1).trans (hre.mono (Lg_le C 1))

lemma main (hR : ∀ a, Represents (R a) (levelRel (C a) a)) (l : Fin 2) :
    (Gg C).Reachable ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), l)
      ↔ glueConn (R 0) (R 1) l = true :=
  ⟨forward C R hR l, backward C R hR l⟩

end Final

end Bunkbed.M3

/-! ## The requested statement, verbatim -/

open Bunkbed Bunkbed.Hyper Bunkbed.TM SimpleGraph Finset

theorem profile_determines (c₀ c₁ : Fin 6 → WZ) (r₀ r₁ : St) (l : Fin 2)
    (h₀ : Represents r₀ (levelRel c₀ 0)) (h₁ : Represents r₁ (levelRel c₁ 1)) :
    (wzGraph hollomTriple hollomT (fun p => if p.2 = 0 then c₀ p.1 else c₁ p.1)).Reachable
        ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), l)
      ↔ glueConn r₀ r₁ l = true := by
  have hR : ∀ a : Fin 2,
      Represents ((fun a : Fin 2 => if a = 0 then r₀ else r₁) a)
        (levelRel ((fun (a : Fin 2) (i : Fin 6) => if a = 0 then c₀ i else c₁ i) a) a) := by
    intro a
    rcases Bunkbed.M3.fin2_cases a with rfl | rfl
    · exact h₀
    · exact h₁
  exact Bunkbed.M3.main (fun (a : Fin 2) (i : Fin 6) => if a = 0 then c₀ i else c₁ i)
    (fun a : Fin 2 => if a = 0 then r₀ else r₁) hR l

/-!
# The transfer-matrix fold computes the level partition

`Bunkbed.TM.step` processes one hyperedge of Hollom's hypergraph: it opens a slot for the
incoming path vertex, performs the merges dictated by the WZ state of that hyperedge, and then
forgets the outgoing path vertex.  Folding all six hyperedges gives `prof c`.  The theorem
`fold_represents` says that `prof c` names exactly the partition that the level-`l` edges of the
configuration `c` induce on the five special vertices `{0, 1, 6, 8, 9}`.

The engine of the proof is the pair of *generic* lemmas

* `reach_closure` — a reflexive transitive relation containing `G.Adj` contains `G.Reachable`;
* `reach_insert` — adding one edge `s(p,q)` to an edge set merges exactly the components of `p`
  and of `q`,

which between them replace any reasoning about walk surgery or union-find.  `reach_insert`
matches the purely arithmetic identity `uni6_key` about `uni6`, so a single merge is correct;
`step` is at most three merges followed by a recanonicalisation, and the recanonicalisation is
correct because taking the least element of a fibre is injective on fibres (`canonF_iff`).

The structural input is that each intermediate path vertex of `ρ = 0 → 2 → 5 → 4 → 3 → 7 → 9`
lies in exactly two consecutive hyperedges: `pathN_not_in_earlier` says the *incoming* vertex of
hyperedge `k` occurs in none of the hyperedges `0, …, k-1`, so it is isolated in the graph built
so far and `embed5` may open a fresh slot for it (`isolated`).
-/


namespace Bunkbed.TMFold

open Bunkbed Bunkbed.Hyper Bunkbed.TM SimpleGraph Finset

/-! ## Generic reachability tools -/

section Generic

variable {W : Type*}

/-- An edge of `ofEdges S` really is a member of `S`. -/
private lemma mem_of_adj {S : Finset (Sym2 W)} {u v : W} (h : (ofEdges S).Adj u v) :
    s(u, v) ∈ S := by
  simpa using ((fromEdgeSet_adj (s := (S : Set (Sym2 W)))).mp h).1

/-- A member of `S` joining distinct endpoints is an edge of `ofEdges S`. -/
private lemma adj_of_mem {S : Finset (Sym2 W)} {u v : W} (h : s(u, v) ∈ S) (hne : u ≠ v) :
    (ofEdges S).Adj u v :=
  (fromEdgeSet_adj (s := (S : Set (Sym2 W)))).mpr ⟨by simpa using h, hne⟩

/-- **M1.** A reflexive, transitive relation containing `G.Adj` contains `G.Reachable`.  This is
the only induction on walks in the whole file. -/
private lemma reach_closure {G : SimpleGraph W} {R : W → W → Prop}
    (hrefl : ∀ x, R x x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (hadj : ∀ u v, G.Adj u v → R u v) {x y : W} (h : G.Reachable x y) : R x y := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hrefl _
  | cons hxy _ ih => exact htrans _ _ _ (hadj _ _ hxy) ih

private lemma reach_mono {S T : Finset (Sym2 W)} (h : S ⊆ T) {u v : W}
    (hr : (ofEdges S).Reachable u v) : (ofEdges T).Reachable u v :=
  hr.mono (fromEdgeSet_mono (by exact_mod_cast h))

private lemma reach_empty {u v : W} :
    (ofEdges (∅ : Finset (Sym2 W))).Reachable u v ↔ u = v := by
  refine ⟨fun h => ?_, fun h => h ▸ Reachable.refl _⟩
  refine reach_closure (R := fun x y => x = y) (fun _ => rfl)
    (fun _ _ _ h1 h2 => h1.trans h2) (fun u v hadj => ?_) h
  exact absurd (mem_of_adj hadj) (by simp)

/-- **Adding one edge.**  In `ofEdges (insert s(p,q) S)` two vertices are connected iff they were
already connected in `ofEdges S`, or each of them was connected to one of `p`, `q`. -/
private lemma reach_insert [DecidableEq W] (S : Finset (Sym2 W)) (p q u v : W) :
    (ofEdges (insert s(p, q) S)).Reachable u v ↔
      ((ofEdges S).Reachable u v ∨
        (((ofEdges S).Reachable u p ∨ (ofEdges S).Reachable u q) ∧
         ((ofEdges S).Reachable v p ∨ (ofEdges S).Reachable v q))) := by
  have hMtr : ∀ x y : W, (ofEdges S).Reachable x y →
      ((ofEdges S).Reachable x p ∨ (ofEdges S).Reachable x q) →
      ((ofEdges S).Reachable y p ∨ (ofEdges S).Reachable y q) :=
    fun _ _ hxy hx => hx.imp (fun h => hxy.symm.trans h) (fun h => hxy.symm.trans h)
  constructor
  · refine reach_closure
      (R := fun x y => (ofEdges S).Reachable x y ∨
        (((ofEdges S).Reachable x p ∨ (ofEdges S).Reachable x q) ∧
         ((ofEdges S).Reachable y p ∨ (ofEdges S).Reachable y q)))
      (fun x => Or.inl (Reachable.refl x)) (fun x y z hxy hyz => ?_) (fun x y hadj => ?_)
    · rcases hxy with h1 | ⟨h1a, h1b⟩ <;> rcases hyz with h2 | ⟨h2a, h2b⟩
      · exact Or.inl (h1.trans h2)
      · exact Or.inr ⟨hMtr _ _ h1.symm h2a, h2b⟩
      · exact Or.inr ⟨h1a, hMtr _ _ h2 h1b⟩
      · exact Or.inr ⟨h1a, h2b⟩
    · have hx := mem_of_adj hadj
      rcases Finset.mem_insert.mp hx with he | he
      · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr ⟨Or.inl (Reachable.refl _), Or.inr (Reachable.refl _)⟩
        · exact Or.inr ⟨Or.inr (Reachable.refl _), Or.inl (Reachable.refl _)⟩
      · exact Or.inl (adj_of_mem he hadj.ne).reachable
  · intro h
    have hsub : S ⊆ insert s(p, q) S := Finset.subset_insert _ _
    have hpq : (ofEdges (insert s(p, q) S)).Reachable p q := by
      by_cases he : p = q
      · exact he ▸ Reachable.refl _
      · exact (adj_of_mem (Finset.mem_insert_self _ _) he).reachable
    rcases h with h | ⟨h1, h2⟩
    · exact reach_mono hsub h
    · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact (reach_mono hsub h1).trans (reach_mono hsub h2).symm
      · exact ((reach_mono hsub h1).trans hpq).trans (reach_mono hsub h2).symm
      · exact ((reach_mono hsub h1).trans hpq.symm).trans (reach_mono hsub h2).symm
      · exact (reach_mono hsub h1).trans (reach_mono hsub h2).symm

end Generic

/-! ## Representations -/

/-- `s` names the partition that `G` induces on the vertices `g 0, …, g (n-1)`. -/
private def Rep {W : Type*} {n : ℕ} {β : Type*} (s : Fin n → β) (G : SimpleGraph W)
    (g : Fin n → W) : Prop := ∀ x y, s x = s y ↔ G.Reachable (g x) (g y)

/-! ### Arithmetic of `uni6` and of the recanonicalising fold -/

private lemma uni6_key : ∀ a b c d : Fin 6,
    ((if a = max c d then min c d else a) = (if b = max c d then min c d else b)) ↔
      (a = b ∨ ((a = c ∨ a = d) ∧ (b = c ∨ b = d))) := by decide

private lemma fin5_cases : ∀ a : Fin 5, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by decide

private lemma fin6_split : ∀ x : Fin 6, (∃ a : Fin 5, x = a.castSucc) ∨ x = 5 := by decide

private lemma castSucc_ne_five : ∀ x : Fin 5, x.castSucc ≠ (5 : Fin 6) := by decide

private lemma finRange5 : List.finRange 5 = [0, 1, 2, 3, 4] := by decide

/-- The recanonicalising fold of `step`, in isolation: `canonF v a` is the least slot in the
fibre of `v` through `a`. -/
private def canonF (v : Fin 5 → Fin 6) (a : Fin 5) : Fin 5 :=
  (List.finRange 5).foldl (fun acc b => if v b = v a then min acc b else acc) 4

private lemma foldl_min5 (p : Fin 5 → Prop) [DecidablePred p] :
    (List.finRange 5).foldl (fun acc j => if p j then min acc j else acc) 4
      = (if p 0 then 0 else if p 1 then 1 else if p 2 then 2 else if p 3 then 3 else 4) := by
  rw [finRange5]
  by_cases h0 : p 0 <;> by_cases h1 : p 1 <;> by_cases h2 : p 2 <;> by_cases h3 : p 3 <;>
    by_cases h4 : p 4 <;>
    simp only [List.foldl_cons, List.foldl_nil, h0, h1, h2, h3, h4, if_pos, if_neg,
      not_false_eq_true] <;> decide

private lemma canonF_explicit (v : Fin 5 → Fin 6) (a : Fin 5) :
    canonF v a = (if v 0 = v a then 0 else if v 1 = v a then 1 else if v 2 = v a then 2
      else if v 3 = v a then 3 else 4) :=
  foldl_min5 (fun j => v j = v a)

private lemma canonF_val (v : Fin 5 → Fin 6) (a : Fin 5) : v (canonF v a) = v a := by
  rw [canonF_explicit]
  split_ifs with h0 h1 h2 h3
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · rcases fin5_cases a with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact absurd rfl h3
    · rfl

private lemma canonF_iff (v : Fin 5 → Fin 6) (a b : Fin 5) :
    canonF v a = canonF v b ↔ v a = v b := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · calc v a = v (canonF v a) := (canonF_val v a).symm
      _ = v (canonF v b) := by rw [h]
      _ = v b := canonF_val v b
  · rw [canonF_explicit, canonF_explicit, h]

/-! ### The three moves of `step` -/

private lemma embed5_cast (r : St) (a : Fin 5) : embed5 r a.castSucc = (r a).castSucc :=
  dif_pos (show (a.castSucc).val < 5 from a.isLt)

private lemma embed5_five (r : St) : embed5 r 5 = 5 := dif_neg (by decide)

/-- **Opening a slot.**  If the new vertex `g 5` is isolated in `G`, then `embed5` extends a
representation of five slots to one of six. -/
private lemma rep_embed5 {W : Type*} {G : SimpleGraph W} {r : St} {f : Fin 5 → W} {g : Fin 6 → W}
    (hr : Rep r G f) (hgc : ∀ a : Fin 5, g a.castSucc = f a)
    (hiso : ∀ a : Fin 5, ¬ G.Reachable (f a) (g 5)) : Rep (embed5 r) G g := by
  intro x y
  rcases fin6_split x with ⟨a, rfl⟩ | rfl
  · rcases fin6_split y with ⟨b, rfl⟩ | rfl
    · rw [embed5_cast, embed5_cast, hgc, hgc, Fin.castSucc_inj]
      exact hr a b
    · rw [embed5_cast, embed5_five, hgc]
      exact iff_of_false (castSucc_ne_five (r a)) (hiso a)
  · rcases fin6_split y with ⟨b, rfl⟩ | rfl
    · rw [embed5_cast, embed5_five, hgc]
      exact iff_of_false (fun h => castSucc_ne_five (r b) h.symm) (fun h => hiso b h.symm)
    · exact iff_of_true rfl (Reachable.refl _)

/-- **One merge.**  `uni6` is correct for a single added edge. -/
private lemma rep_uni6 {W : Type*} [DecidableEq W] {g : Fin 6 → W} {S : Finset (Sym2 W)}
    {s : St6} (hs : Rep s (ofEdges S) g) (p q : Fin 6) :
    Rep (uni6 s p q) (ofEdges (insert s(g p, g q) S)) g := by
  intro x y
  rw [show uni6 s p q x = (if s x = max (s p) (s q) then min (s p) (s q) else s x) from rfl,
    show uni6 s p q y = (if s y = max (s p) (s q) then min (s p) (s q) else s y) from rfl,
    uni6_key, reach_insert, hs x y, hs x p, hs x q, hs y p, hs y q]

/-- **Dropping the spent slot.**  Passing to least fibre representatives is faithful. -/
private lemma rep_drop {W : Type*} {G : SimpleGraph W} {g : Fin 6 → W} {s : St6}
    (h : Rep s G g) : Rep (canonF (fun x => s (newSlot x))) G (fun a => g (newSlot a)) := by
  intro a b
  rw [canonF_iff]
  exact h (newSlot a) (newSlot b)

/-! ### The merges of one hyperedge -/

/-- The edge set a WZ state contributes, with the three lifted vertices given explicitly. -/
private def wzE {W : Type*} [DecidableEq W] (t : WZ) (A B C : W) : Finset (Sym2 W) :=
  match t with
  | .abc => {s(A, B), s(B, C), s(A, C)}
  | .ab_c => {s(A, B)}
  | .ac_b => {s(A, C)}
  | .a_bc => {s(B, C)}
  | .a_b_c => ∅

private lemma wzE_eq {V : Type*} [DecidableEq V] (t : WZ) (tr : V × V × V) (l : Fin 2) :
    WZ.edges t tr l = wzE t (tr.1, l) (tr.2.1, l) (tr.2.2, l) := by
  cases t <;> rfl

/-- **The merge phase of `step`.**  Folding `uni6` over `wzPairs t` adds exactly the edges of
the WZ state `t` inside hyperedge `i`. -/
private lemma rep_stepS {W : Type*} [DecidableEq W] {g : Fin 6 → W} {S S' : Finset (Sym2 W)}
    {s0 : St6} (i : Fin 6) (t : WZ) (h : Rep s0 (ofEdges S) g)
    (hS : S ∪ wzE t (g (triplePos i 0)) (g (triplePos i 1)) (g (triplePos i 2)) = S') :
    Rep ((wzPairs t).foldl (fun acc pq => uni6 acc (triplePos i pq.1) (triplePos i pq.2)) s0)
      (ofEdges S') g := by
  subst hS
  cases t
  case abc =>
    have h3 := rep_uni6 (rep_uni6 (rep_uni6 h (triplePos i 0) (triplePos i 1))
      (triplePos i 1) (triplePos i 2)) (triplePos i 0) (triplePos i 2)
    have hset : insert s(g (triplePos i 0), g (triplePos i 2))
        (insert s(g (triplePos i 1), g (triplePos i 2))
          (insert s(g (triplePos i 0), g (triplePos i 1)) S))
        = S ∪ wzE WZ.abc (g (triplePos i 0)) (g (triplePos i 1)) (g (triplePos i 2)) := by
      ext e; simp only [wzE, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]; tauto
    rw [← hset]; exact h3
  case ab_c =>
    have hset : insert s(g (triplePos i 0), g (triplePos i 1)) S
        = S ∪ wzE WZ.ab_c (g (triplePos i 0)) (g (triplePos i 1)) (g (triplePos i 2)) := by
      ext e; simp only [wzE, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]; tauto
    rw [← hset]; exact rep_uni6 h (triplePos i 0) (triplePos i 1)
  case ac_b =>
    have hset : insert s(g (triplePos i 0), g (triplePos i 2)) S
        = S ∪ wzE WZ.ac_b (g (triplePos i 0)) (g (triplePos i 1)) (g (triplePos i 2)) := by
      ext e; simp only [wzE, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]; tauto
    rw [← hset]; exact rep_uni6 h (triplePos i 0) (triplePos i 2)
  case a_bc =>
    have hset : insert s(g (triplePos i 1), g (triplePos i 2)) S
        = S ∪ wzE WZ.a_bc (g (triplePos i 0)) (g (triplePos i 1)) (g (triplePos i 2)) := by
      ext e; simp only [wzE, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]; tauto
    rw [← hset]; exact rep_uni6 h (triplePos i 1) (triplePos i 2)
  case a_b_c =>
    have hset : S ∪ wzE WZ.a_b_c (g (triplePos i 0)) (g (triplePos i 1))
        (g (triplePos i 2)) = S := by simp [wzE]
    rw [hset]; exact h

/-! ## The combinatorics of Hollom's hypergraph -/

/-- The path `ρ` as a function of a natural number. -/
private def pathN : ℕ → Fin 10
  | 0 => 0
  | 1 => 2
  | 2 => 5
  | 3 => 4
  | 4 => 3
  | 5 => 7
  | _ => 9

/-- The five tracked vertices after `k` hyperedges. -/
private def slotN (k : ℕ) : Fin 5 → Fin 10 := ![0, 1, 6, 8, pathN k]

/-- The six vertices live during the `k`-th transfer step. -/
private def slotN6 (k : ℕ) : Fin 6 → Fin 10 := ![0, 1, 6, 8, pathN k, pathN (k + 1)]

private def nth3 (t : Fin 10 × Fin 10 × Fin 10) : Fin 3 → Fin 10 := ![t.1, t.2.1, t.2.2]

private lemma slotN6_castSucc (k : ℕ) : ∀ a : Fin 5, slotN6 k a.castSucc = slotN k a := by
  intro a; rcases fin5_cases a with rfl | rfl | rfl | rfl | rfl <;> rfl

private lemma slotN6_five (k : ℕ) : slotN6 k 5 = pathN (k + 1) := rfl

private lemma slotN6_newSlot (k : ℕ) : ∀ a : Fin 5, slotN6 k (newSlot a) = slotN (k + 1) a := by
  intro a; rcases fin5_cases a with rfl | rfl | rfl | rfl | rfl <;> rfl

private lemma slotN6_triplePos : ∀ (i : Fin 6) (j : Fin 3),
    slotN6 i.val (triplePos i j) = nth3 (hollomTriple i) j := by decide

/-- **The key structural fact.**  The path vertex entering at hyperedge `j` occurs in none of
the hyperedges `0, …, j-1`; equivalently, each intermediate path vertex lies in exactly the two
consecutive hyperedges that meet it. -/
private lemma pathN_not_in_earlier : ∀ i j : Fin 6, i.val < j.val →
    (pathN (j.val + 1) ≠ (hollomTriple i).1 ∧ pathN (j.val + 1) ≠ (hollomTriple i).2.1 ∧
      pathN (j.val + 1) ≠ (hollomTriple i).2.2) := by decide

private lemma slotN_ne_pathN : ∀ (i : Fin 6) (a : Fin 5), slotN i.val a ≠ pathN (i.val + 1) := by
  decide

private lemma stInit_iff : ∀ a b : Fin 5, stInit a = stInit b ↔ slotN 0 a = slotN 0 b := by
  decide

private lemma slotN_six : ∀ a : Fin 5, slotN 6 a = sp a := by decide

/-- Every edge a WZ state contributes lies inside the three lifted vertices of its hyperedge. -/
private lemma edges_support {V : Type*} [DecidableEq V] (tr : V × V × V) (l : Fin 2) (t : WZ)
    (e : Sym2 (V × Fin 2)) (he : e ∈ WZ.edges t tr l) (v : V × Fin 2) (hv : v ∈ e) :
    v = (tr.1, l) ∨ v = (tr.2.1, l) ∨ v = (tr.2.2, l) := by
  cases t <;>
    simp only [WZ.edges, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] at he
  · rcases he with rfl | rfl | rfl <;> (simp only [Sym2.mem_iff] at hv; tauto)
  · subst he; simp only [Sym2.mem_iff] at hv; tauto
  · subst he; simp only [Sym2.mem_iff] at hv; tauto
  · subst he; simp only [Sym2.mem_iff] at hv; tauto

/-! ## The partial edge sets -/

/-- The level-`l` edges contributed by the first `k` hyperedges. -/
private def pEdges (c : Fin 6 → WZ) (l : Fin 2) (k : ℕ) : Finset (Sym2 (Fin 10 × Fin 2)) :=
  (Finset.univ.filter (fun i : Fin 6 => i.val < k)).biUnion
    (fun i => (c i).edges (hollomTriple i) l)

private lemma pEdges_zero (c : Fin 6 → WZ) (l : Fin 2) : pEdges c l 0 = ∅ := by
  simp [pEdges]

private lemma pEdges_succ (c : Fin 6 → WZ) (l : Fin 2) (i : Fin 6) :
    pEdges c l (i.val + 1) = pEdges c l i.val ∪ (c i).edges (hollomTriple i) l := by
  ext e
  simp only [pEdges, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union]
  constructor
  · rintro ⟨j, hj, he⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact Or.inl ⟨j, h, he⟩
    · exact Or.inr (by rwa [Fin.ext h] at he)
  · rintro (⟨j, hj, he⟩ | he)
    · exact ⟨j, by omega, he⟩
    · exact ⟨i, by omega, he⟩

private lemma pEdges_six (c : Fin 6 → WZ) (l : Fin 2) : pEdges c l 6 = levelEdges c l := by
  have h : (Finset.univ.filter (fun i : Fin 6 => i.val < 6)) = Finset.univ :=
    Finset.filter_true_of_mem (fun i _ => i.isLt)
  rw [pEdges, h, levelEdges]

private lemma pEdges_avoid (c : Fin 6 → WZ) (l : Fin 2) (i : Fin 6)
    {e : Sym2 (Fin 10 × Fin 2)} (he : e ∈ pEdges c l i.val) :
    ((pathN (i.val + 1), l) : Fin 10 × Fin 2) ∉ e := by
  intro hv
  simp only [pEdges, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at he
  obtain ⟨j, hj, hej⟩ := he
  have hs := edges_support (hollomTriple j) l (c j) e hej _ hv
  have hne := pathN_not_in_earlier j i hj
  rcases hs with h | h | h <;> rw [Prod.mk.injEq] at h
  · exact hne.1 h.1
  · exact hne.2.1 h.1
  · exact hne.2.2 h.1

/-- **Isolation.**  The incoming path vertex of hyperedge `i` is untouched by the edges of the
earlier hyperedges, hence is its own component. -/
private lemma isolated (c : Fin 6 → WZ) (l : Fin 2) (i : Fin 6) (a : Fin 5) :
    ¬ (ofEdges (pEdges c l i.val)).Reachable (slotN i.val a, l) (pathN (i.val + 1), l) := by
  intro hr
  have key : ∀ x y : Fin 10 × Fin 2, (ofEdges (pEdges c l i.val)).Reachable x y →
      x ≠ (pathN (i.val + 1), l) → y ≠ (pathN (i.val + 1), l) := by
    intro x y h
    refine reach_closure
      (R := fun x y => x ≠ ((pathN (i.val + 1), l) : Fin 10 × Fin 2) →
        y ≠ ((pathN (i.val + 1), l) : Fin 10 × Fin 2))
      (fun _ h => h) (fun _ _ _ h1 h2 h3 => h2 (h1 h3)) (fun u v hadj _ => ?_) h
    have hm := pEdges_avoid c l i (mem_of_adj hadj)
    simp only [Sym2.mem_iff, not_or] at hm
    exact fun hc => hm.2 hc.symm
  refine key _ _ hr (fun hc => ?_) rfl
  exact slotN_ne_pathN i a (by simpa using congrArg Prod.fst hc)

/-! ## The induction over the six hyperedges -/

private lemma wzE_hollom (c : Fin 6 → WZ) (l : Fin 2) (i : Fin 6) :
    wzE (c i) (slotN6 i.val (triplePos i 0), l) (slotN6 i.val (triplePos i 1), l)
        (slotN6 i.val (triplePos i 2), l) = (c i).edges (hollomTriple i) l := by
  rw [slotN6_triplePos, slotN6_triplePos, slotN6_triplePos]
  exact (wzE_eq (c i) (hollomTriple i) l).symm

/-- **One transfer step is correct.** -/
private lemma rep_step (c : Fin 6 → WZ) (l : Fin 2) (i : Fin 6) (r : St)
    (ih : Rep r (ofEdges (pEdges c l i.val)) (fun a => (slotN i.val a, l))) :
    Rep (step i (c i) r) (ofEdges (pEdges c l (i.val + 1)))
      (fun a => (slotN (i.val + 1) a, l)) := by
  have h1 : Rep (embed5 r) (ofEdges (pEdges c l i.val))
      (fun x : Fin 6 => (slotN6 i.val x, l)) := by
    refine rep_embed5 ih (fun a => ?_) (fun a => ?_)
    · show ((slotN6 i.val a.castSucc, l) : Fin 10 × Fin 2) = (slotN i.val a, l)
      rw [slotN6_castSucc]
    · show ¬ (ofEdges (pEdges c l i.val)).Reachable (slotN i.val a, l) (slotN6 i.val 5, l)
      rw [slotN6_five]
      exact isolated c l i a
  have h2 := rep_stepS (g := fun x : Fin 6 => (slotN6 i.val x, l)) (S := pEdges c l i.val)
    (S' := pEdges c l (i.val + 1)) i (c i) h1 (by
      show pEdges c l i.val ∪ wzE (c i) (slotN6 i.val (triplePos i 0), l)
        (slotN6 i.val (triplePos i 1), l) (slotN6 i.val (triplePos i 2), l)
        = pEdges c l (i.val + 1)
      rw [wzE_hollom, pEdges_succ])
  have h3 := rep_drop h2
  have hgf : (fun a : Fin 5 => ((slotN6 i.val (newSlot a), l) : Fin 10 × Fin 2))
      = (fun a : Fin 5 => ((slotN (i.val + 1) a, l) : Fin 10 × Fin 2)) := by
    funext a; rw [slotN6_newSlot]
  rw [show (fun a : Fin 5 => ((fun x : Fin 6 => (slotN6 i.val x, l)) (newSlot a)))
      = (fun a : Fin 5 => ((slotN (i.val + 1) a, l) : Fin 10 × Fin 2)) from hgf] at h3
  exact h3

private lemma fold_inv (c : Fin 6 → WZ) (l : Fin 2) : ∀ (k : ℕ) (h : k ≤ 6),
    Rep (fold k h c) (ofEdges (pEdges c l k)) (fun a => (slotN k a, l)) := by
  intro k
  induction k with
  | zero =>
    intro h a b
    rw [show fold 0 h c = stInit from rfl, pEdges_zero, reach_empty, Prod.mk.injEq]
    simp only [and_true]
    exact stInit_iff a b
  | succ k ih =>
    intro h
    have hk : k < 6 := by omega
    exact rep_step c l ⟨k, hk⟩ (fold k (by omega) c) (ih (by omega))

end Bunkbed.TMFold

/-! ## The requested statement, verbatim -/

open Bunkbed Bunkbed.Hyper Bunkbed.TM SimpleGraph Finset

/-- **M4.**  Six iterations of the combinatorial `step` compute exactly the partition that one
level of a WZ configuration induces on the five special vertices `{0, 1, 6, 8, 9}`. -/
theorem fold_represents (c : Fin 6 → WZ) (l : Fin 2) : Represents (prof c) (levelRel c l) := by
  intro a b
  have h := Bunkbed.TMFold.fold_inv c l 6 le_rfl a b
  rw [Bunkbed.TMFold.pEdges_six] at h
  simp only [Bunkbed.TMFold.slotN_six] at h
  exact h

open Bunkbed Bunkbed.Hyper Bunkbed.TM SimpleGraph Finset in
/-- The reachability indicator is the glued connectivity of the two induced profiles. -/
private theorem ind_eq (c₀ c₁ : Fin 6 → WZ) (l : Fin 2) :
    (if (wzGraph hollomTriple hollomT (fun p => if p.2 = 0 then c₀ p.1 else c₁ p.1)).Reachable
          ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), l) then (1 : ℚ) else 0)
      = (if glueConn (prof c₀) (prof c₁) l then (1 : ℚ) else 0) := by
  by_cases h : glueConn (prof c₀) (prof c₁) l = true
  · rw [if_pos ((profile_determines c₀ c₁ _ _ l (fold_represents c₀ 0) (fold_represents c₁ 1)).mpr h),
      if_pos (by simpa using h)]
  · rw [if_neg (fun hr => h ((profile_determines c₀ c₁ _ _ l (fold_represents c₀ 0)
        (fold_represents c₁ 1)).mp hr)), if_neg (by simpa using h)]

open Bunkbed Bunkbed.Hyper Bunkbed.TM SimpleGraph Finset in
/-- **Connectivity depends only on the two level profiles.** -/
theorem solution (P : WZ → ℚ) :
    wzProb hollomTriple hollomT P ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2))
      - wzProb hollomTriple hollomT P ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2))
      = ∑ c₀ : Fin 6 → WZ, ∑ c₁ : Fin 6 → WZ,
          ((if glueConn (prof c₀) (prof c₁) 1 then (1 : ℚ) else 0)
            - (if glueConn (prof c₀) (prof c₁) 0 then (1 : ℚ) else 0))
            * ((∏ i, P (c₀ i)) * (∏ i, P (c₁ i))) := by
  rw [wzProb_split, wzProb_split, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun c₀ _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun c₁ _ => ?_)
  rw [ind_eq c₀ c₁ 1, ind_eq c₀ c₁ 0]
  ring

#print axioms solution
