-- Prove2me | solution 1 for CountingLLL.DetCount.tree_event_far_independence
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:29:06.209042+00:00
-- url     : https://prove2.me/submissions/c04bf297-9a79-4f37-8db6-416ccf20b851

import Theorems.Thm_CountingLLL_DetCount_lemma_3_2

set_option autoImplicit false

namespace CountingLLL.DetCount
open CSP

private theorem step_subset (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) :
    st.1 ⊆ (Φ.treeStep E D st).1 ∧ st.2 ⊆ (Φ.treeStep E D st).2 := by
  classical
  unfold CSP.treeStep
  dsimp only
  split_ifs <;> simp_all [Finset.subset_insert]

private theorem step_inv (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m))
    (ha : st.1 ⊆ D) (hr : st.2 ⊆ E \ D) :
    (Φ.treeStep E D st).1 ⊆ D ∧ (Φ.treeStep E D st).2 ⊆ E \ D := by
  classical
  unfold CSP.treeStep
  dsimp only
  split_ifs with h hD
  · simp only [Prod.fst, Prod.snd, Finset.insert_subset_iff]
    exact ⟨⟨hD, ha⟩, hr⟩
  · simp only [Prod.fst, Prod.snd, Finset.insert_subset_iff]
    refine ⟨ha, ⟨?_, hr⟩⟩
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp (Finset.min'_mem _ h)).1, hD⟩
  · exact ⟨ha, hr⟩

private theorem run_inv (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m))
    (ha : st.1 ⊆ D) (hr : st.2 ⊆ E \ D) (n : ℕ) :
    ((Φ.treeStep E D)^[n] st).1 ⊆ D ∧ ((Φ.treeStep E D)^[n] st).2 ⊆ E \ D := by
  induction n with
  | zero => simpa using And.intro ha hr
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact step_inv Φ E D _ ih.1 ih.2

private theorem run_monotone (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) (n : ℕ) :
    st.1 ⊆ ((Φ.treeStep E D)^[n] st).1 ∧ st.2 ⊆ ((Φ.treeStep E D)^[n] st).2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨ih.1.trans (step_subset Φ E D _).1, ih.2.trans (step_subset Φ E D _).2⟩

private theorem distSet_mem_zero {V : Type} (G : SimpleGraph V) (S : Finset V) (v : V)
    (hv : v ∈ S) : distSet G v S = 0 := by
  apply le_antisymm
  · exact (Finset.inf_le hv).trans_eq SimpleGraph.edist_self
  · exact bot_le

private theorem step_active_growth (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m))
    (h : (E.filter (fun c => c ∉ st.2 ∧ distSet (Φ.depGraph E) c st.1 = 2)).Nonempty) :
    (st.1 ∪ st.2).card < (((Φ.treeStep E D st).1) ∪ ((Φ.treeStep E D st).2)).card := by
  classical
  let cand := E.filter (fun c => c ∉ st.2 ∧ distSet (Φ.depGraph E) c st.1 = 2)
  let c := cand.min' h
  have hc : c ∈ cand := Finset.min'_mem cand h
  have hmem := Finset.mem_filter.mp hc
  have hn1 : c ∉ st.1 := by
    intro hc1
    have hz := distSet_mem_zero (Φ.depGraph E) st.1 c hc1
    rw [hmem.2.2] at hz
    norm_num at hz
  have hn2 : c ∉ st.2 := hmem.2.1
  have hn : c ∉ st.1 ∪ st.2 := by simp [hn1, hn2]
  unfold CSP.treeStep
  dsimp only
  simp only [dif_pos h]
  split_ifs with hd
  · simp only [Prod.fst, Prod.snd, Finset.insert_union]
    rw [Finset.card_insert_of_notMem hn]
    omega
  · simp only [Prod.fst, Prod.snd, Finset.union_insert]
    rw [Finset.card_insert_of_notMem hn]
    omega

private def Active (Φ : CSP) (E : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) : Prop :=
  (E.filter (fun c => c ∉ st.2 ∧ distSet (Φ.depGraph E) c st.1 = 2)).Nonempty

private theorem step_inactive (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) (h : ¬ Active Φ E st) :
    Φ.treeStep E D st = st := by
  classical
  unfold Active at h
  simpa only [CSP.treeStep, dif_neg h]

private theorem active_iterate_growth (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) (n : ℕ)
    (h : Active Φ E ((Φ.treeStep E D)^[n] st)) :
    (st.1 ∪ st.2).card + n ≤
      (((Φ.treeStep E D)^[n] st).1 ∪ ((Φ.treeStep E D)^[n] st).2).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    let prev := (Φ.treeStep E D)^[n] st
    have hp : Active Φ E prev := by
      by_contra hn
      have he := step_inactive Φ E D prev hn
      rw [Function.iterate_succ_apply', he] at h
      exact hn h
    have hi := ih hp
    have hs := step_active_growth Φ E D prev hp
    dsimp [prev] at hs
    rw [Function.iterate_succ_apply']
    omega

private theorem treeRun_terminal (Φ : CSP) (E D : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (hc : c₀ ∈ D) (hDE : D ⊆ E) : ¬ Active Φ E (Φ.treeRun E c₀ D) := by
  classical
  intro h
  have hg := active_iterate_growth Φ E D ({c₀}, ∅) E.card h
  have hi := run_inv Φ E D ({c₀}, ∅) (by simpa using hc) (by simp) E.card
  have hs : (Φ.treeRun E c₀ D).1 ∪ (Φ.treeRun E c₀ D).2 ⊆ E :=
    Finset.union_subset (hi.1.trans hDE) (hi.2.trans (Finset.sdiff_subset))
  have hb := Finset.card_le_card hs
  simp only [Finset.union_empty, Finset.card_singleton] at hg
  change 1 + E.card ≤ ((Φ.treeRun E c₀ D).1 ∪ (Φ.treeRun E c₀ D).2).card at hg
  omega


private theorem distSet_zero_mem {V : Type} (G : SimpleGraph V) (S : Finset V) (v : V)
    (h : distSet G v S = 0) : v ∈ S := by
  classical
  have hmin : distSet G v S ≤ 0 := h.le
  obtain ⟨w, hw, hd⟩ := (Finset.inf_le_iff (ENat.natCast_lt_top 0)).mp hmin
  have heq : G.edist v w = 0 := le_antisymm hd bot_le
  have heq' := SimpleGraph.edist_eq_zero_iff.mp heq
  simpa [heq'] using hw

private theorem free_no_two (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hT : T ∈ Φ.twoTrees E r) (c : Fin Φ.m) (hc : c ∈ Φ.free E r T) :
    distSet (Φ.depGraph E) c T ≠ 2 := by
  classical
  have ht : T ⊆ E ∧ r ∈ T := by
    have hh := Finset.mem_filter.mp hT
    exact ⟨Finset.mem_powerset.mp hh.1, hh.2.1⟩
  have hterminal := treeRun_terminal Φ E T r ht.2 ht.1
  have hfix := (lemma_3_2 Φ E r).2 T hT
  intro he
  apply hterminal
  unfold Active
  have hf := Finset.mem_sdiff.mp hc
  have hnot : c ∉ (Φ.treeRun E r T).2 := by
    intro hR
    exact hf.2 (Finset.mem_union.mpr (Or.inr hR))
  refine ⟨c, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨hf.1, hnot, ?_⟩
  change distSet (Φ.depGraph E) c (Φ.Tree E r T) = 2
  rw [hfix]
  exact he

private theorem far_free_distance (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hT : T ∈ Φ.twoTrees E r) (c : Fin Φ.m)
    (hc : c ∈ Φ.free E r T \ Φ.free1 E r T) :
    (2 : ℕ∞) < distSet (Φ.depGraph E) c T := by
  classical
  have hh := Finset.mem_sdiff.mp hc
  have hf := Finset.mem_sdiff.mp hh.1
  have hnotT : c ∉ T := fun h => hf.2 (Finset.mem_union.mpr (Or.inl h))
  have hnot0 : distSet (Φ.depGraph E) c T ≠ 0 := fun h => hnotT (distSet_zero_mem _ _ _ h)
  have hnot1 : distSet (Φ.depGraph E) c T ≠ 1 := by
    intro h
    apply hh.2
    exact Finset.mem_filter.mpr ⟨hh.1, h⟩
  have hnot2 := free_no_two Φ E T r hT c hh.1
  have hgt1 : (1 : ℕ∞) < distSet (Φ.depGraph E) c T := by
    apply lt_of_not_ge
    intro hle
    rcases Order.le_one_iff.mp hle with hz | ho
    · exact hnot0 hz
    · exact hnot1 ho
  have hge2 : (2 : ℕ∞) ≤ distSet (Φ.depGraph E) c T :=
    (ENat.natCast_add_one_le_iff (m := 1)).2 hgt1
  exact lt_of_le_of_ne hge2 (Ne.symm hnot2)

private theorem adjacent_to_near_le_two (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    {c u : Fin Φ.m} (hu : u ∈ T ∪ Φ.free1 E r T) (hadj : (Φ.depGraph E).Adj c u) :
    distSet (Φ.depGraph E) c T ≤ 2 := by
  classical
  have hcu : (Φ.depGraph E).edist c u = 1 := SimpleGraph.edist_eq_one_iff_adj.mpr hadj
  rcases Finset.mem_union.mp hu with hT | hF
  · have h := Finset.inf_le (f := fun t => (Φ.depGraph E).edist c t) hT
    change distSet (Φ.depGraph E) c T ≤ (Φ.depGraph E).edist c u at h
    rw [hcu] at h
    exact h.trans (by norm_num)
  · have hu1 : distSet (Φ.depGraph E) u T = 1 := (Finset.mem_filter.mp hF).2
    have hle : distSet (Φ.depGraph E) u T ≤ 1 := hu1.le
    obtain ⟨t, ht, hut⟩ := (Finset.inf_le_iff (ENat.natCast_lt_top 1)).mp hle
    have hct := @SimpleGraph.edist_triangle _ (Φ.depGraph E) c u t
    have hdist : (Φ.depGraph E).edist c t ≤ 2 := by
      calc
        _ ≤ (Φ.depGraph E).edist c u + (Φ.depGraph E).edist u t := hct
        _ ≤ 1 + 1 := add_le_add hcu.le hut
        _ = 2 := by norm_num
    have hmin := Finset.inf_le (f := fun t => (Φ.depGraph E).edist c t) ht
    exact hmin.trans hdist

/-- Distant free constraints share no variables with the tree or nearby free constraints. -/
theorem far_free_scopes_disjoint (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hT : T ∈ Φ.twoTrees E r) :
    Disjoint ((T ∪ Φ.free1 E r T).biUnion Φ.scope)
      ((Φ.free E r T \ Φ.free1 E r T).biUnion Φ.scope) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvnear hvfar
  obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp hvnear
  obtain ⟨c, hc, hvc⟩ := Finset.mem_biUnion.mp hvfar
  have hfar := far_free_distance Φ E T r hT c hc
  have hc' := Finset.mem_sdiff.mp hc
  have hcE : c ∈ E := (Finset.mem_sdiff.mp hc'.1).1
  have huE : u ∈ E := by
    rcases Finset.mem_union.mp hu with hTmem | hfree
    · exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1) hTmem
    · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hfree).1).1
  have hne : c ≠ u := by
    intro he
    subst c
    rcases Finset.mem_union.mp hu with hTmem | hfree
    · exact (Finset.mem_sdiff.mp hc'.1).2 (Finset.mem_union.mpr (Or.inl hTmem))
    · exact hc'.2 hfree
  have hover : Φ.Overlap c u := by
    apply Finset.not_disjoint_iff.mpr
    exact ⟨v, hvc, hvu⟩
  have hadj : (Φ.depGraph E).Adj c u := ⟨hcE, huE, hne, hover⟩
  exact (not_le_of_gt hfar) (adjacent_to_near_le_two Φ E T r hu hadj)

end CountingLLL.DetCount

open CountingLLL.DetCount
open CountingLLL.DetCount.CSP
open scoped Classical

namespace CountingLLL.DetCount
private noncomputable def swapCoords {V : Type} [DecidableEq V] (Q : V → Type)
    (S : Finset V) (z : ((v : V) → Q v) × ((v : V) → Q v)) :
    ((v : V) → Q v) × ((v : V) → Q v) :=
  (fun v => if v ∈ S then z.1 v else z.2 v,
   fun v => if v ∈ S then z.2 v else z.1 v)

private theorem swapCoords_inv {V : Type} [DecidableEq V] (Q : V → Type)
    (S : Finset V) : Function.Involutive (swapCoords Q S) := by
  intro z
  apply Prod.ext <;> funext u <;> by_cases hu : u ∈ S <;> simp [swapCoords, hu]

/-- Finite-product counting independence for heterogeneous coordinate domains.
The swap-bijection argument adapts the accepted platform proof of
`OAI.MetricEntropyDuality.FiniteProductCounting.card_inter_mul_card_sample`
(https://prove2.me), generalized here to dependent coordinate domains. -/
theorem audit_dependent_disjoint_card {V : Type} [Fintype V] [DecidableEq V]
    (Q : V → Type) [∀ v, Fintype (Q v)] [∀ v, DecidableEq (Q v)]
    (S T : Finset V) (A B : Finset ((v : V) → Q v))
    (hA : ∀ x y, (∀ v ∈ S, x v = y v) → (x ∈ A ↔ y ∈ A))
    (hB : ∀ x y, (∀ v ∈ T, x v = y v) → (x ∈ B ↔ y ∈ B))
    (hST : Disjoint S T) :
    (A ∩ B).card * Fintype.card ((v : V) → Q v) = A.card * B.card := by
  classical
  have hforward : ∀ z ∈ (A ∩ B).product (Finset.univ : Finset ((v : V) → Q v)),
      swapCoords Q S z ∈ A.product B := by
    rintro ⟨x, y⟩ hz
    have hxA := (Finset.mem_inter.mp (Finset.mem_product.mp hz).1).1
    have hxB := (Finset.mem_inter.mp (Finset.mem_product.mp hz).1).2
    apply Finset.mem_product.mpr
    constructor
    · apply (hA _ x ?_).mpr hxA
      intro u hu
      simp [swapCoords, hu]
    · apply (hB _ x ?_).mpr hxB
      intro u huT
      have huS : u ∉ S := fun huS => Finset.disjoint_left.mp hST huS huT
      simp [swapCoords, huS]
  have hreverse : ∀ z ∈ A.product B,
      swapCoords Q S z ∈ (A ∩ B).product (Finset.univ : Finset ((v : V) → Q v)) := by
    rintro ⟨x, y⟩ hz
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_inter.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
    · apply (hA _ x ?_).mpr hx
      intro u hu
      simp [swapCoords, hu]
    · apply (hB _ y ?_).mpr hy
      intro u huT
      have huS : u ∉ S := fun huS => Finset.disjoint_left.mp hST huS huT
      simp [swapCoords, huS]
  have hc := Finset.card_nbij' (swapCoords Q S) (swapCoords Q S)
    hforward hreverse (fun z _ => swapCoords_inv Q S z) (fun z _ => swapCoords_inv Q S z)
  simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ] using hc


end CountingLLL.DetCount

private theorem independent_events (Φ : CSP) (A B : Φ.Config → Prop)
    (S T : Finset (Fin Φ.n))
    (hA : ∀ x y : Φ.Config, (∀ v ∈ S, x v = y v) → (A x ↔ A y))
    (hB : ∀ x y : Φ.Config, (∀ v ∈ T, x v = y v) → (B x ↔ B y))
    (hST : Disjoint S T) :
    Φ.prob (fun σ => A σ ∧ B σ) = Φ.prob A * Φ.prob B := by
  classical
  let P : Finset Φ.Config := Finset.univ.filter A
  let Q : Finset Φ.Config := Finset.univ.filter B
  have hP : ∀ x y : Φ.Config, (∀ v ∈ S, x v = y v) → (x ∈ P ↔ y ∈ P) := by
    intro x y h
    simpa [P] using hA x y h
  have hQ : ∀ x y : Φ.Config, (∀ v ∈ T, x v = y v) → (x ∈ Q ↔ y ∈ Q) := by
    intro x y h
    simpa [Q] using hB x y h
  have hc := CountingLLL.DetCount.audit_dependent_disjoint_card (fun v => Fin (Φ.q v)) S T P Q hP hQ hST
  letI : Nonempty Φ.Config := ⟨fun v => ⟨0, lt_of_lt_of_le (by decide) (Φ.two_le_q v)⟩⟩
  have hC : (Fintype.card Φ.Config : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card Φ.Config))
  have hcR : ((P ∩ Q).card : ℝ) * (Fintype.card Φ.Config : ℝ) =
      (P.card : ℝ) * (Q.card : ℝ) := by exact_mod_cast hc
  letI : DecidablePred (fun σ : Φ.Config => A σ ∧ B σ) := fun _ => Classical.propDecidable _
  have hab : P ∩ Q = Finset.univ.filter (fun σ => A σ ∧ B σ) := by
    ext σ
    simp [P, Q]
  have hPQ : ((P ∩ Q).card : ℝ) / (Fintype.card Φ.Config : ℝ) =
      ((P.card : ℝ) / (Fintype.card Φ.Config : ℝ)) * ((Q.card : ℝ) / (Fintype.card Φ.Config : ℝ)) := by
    field_simp
    nlinarith
  unfold CSP.prob
  rw [← hab]
  exact hPQ


private theorem satall_depend (Φ : CSP) (S : Finset (Fin Φ.m)) :
    ∀ σ σ' : Φ.Config, (∀ v ∈ S.biUnion Φ.scope, σ v = σ' v) →
      (Φ.SatAll S σ ↔ Φ.SatAll S σ') := by
  classical
  intro σ σ' h
  unfold CSP.SatAll
  apply forall_congr'
  intro c
  apply forall_congr'
  intro hc
  have heq : (fun v : ↥(Φ.scope c) => σ v.1) = (fun v : ↥(Φ.scope c) => σ' v.1) := by
    funext v
    exact h v.1 (Finset.mem_biUnion.mpr ⟨c, hc, v.2⟩)
  simp only [CSP.Sat, heq]

private theorem violall_depend (Φ : CSP) (S : Finset (Fin Φ.m)) :
    ∀ σ σ' : Φ.Config, (∀ v ∈ S.biUnion Φ.scope, σ v = σ' v) →
      (Φ.ViolAll S σ ↔ Φ.ViolAll S σ') := by
  classical
  intro σ σ' h
  unfold CSP.ViolAll
  apply forall_congr'
  intro c
  apply forall_congr'
  intro hc
  have heq : (fun v : ↥(Φ.scope c) => σ v.1) = (fun v : ↥(Φ.scope c) => σ' v.1) := by
    funext v
    exact h v.1 (Finset.mem_biUnion.mpr ⟨c, hc, v.2⟩)
  simp only [CSP.Sat, heq]

private theorem satall_union (Φ : CSP) (S T : Finset (Fin Φ.m)) (σ : Φ.Config) :
    Φ.SatAll (S ∪ T) σ ↔ Φ.SatAll S σ ∧ Φ.SatAll T σ := by
  classical
  simp [CSP.SatAll, or_imp, forall_and]

/-- Lemma 4.2's conditional-probability identity, assuming its stated positive denominator. -/
theorem solution (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hT : T ∈ Φ.twoTrees E r) :
    Φ.prob (fun σ => Φ.SatAll (Φ.free E r T \ Φ.free1 E r T) σ ∧
      (Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free1 E r T) σ)) =
      Φ.prob (Φ.SatAll (Φ.free E r T \ Φ.free1 E r T)) *
      Φ.prob (fun σ => Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free1 E r T) σ) := by
  classical
  let N := Φ.free1 E r T
  let H := Φ.free E r T \ N
  let W := (T ∪ N).biUnion Φ.scope
  let Z := H.biUnion Φ.scope
  have hdis : Disjoint W Z := far_free_scopes_disjoint Φ E T r hT
  have hdepA : ∀ σ σ' : Φ.Config, (∀ v ∈ W, σ v = σ' v) →
      ((Φ.ViolAll T σ ∧ Φ.SatAll N σ) ↔ (Φ.ViolAll T σ' ∧ Φ.SatAll N σ')) := by
    intro σ σ' h
    have hTdep : Φ.ViolAll T σ ↔ Φ.ViolAll T σ' := by
      apply violall_depend Φ T σ σ'
      intro v hv
      obtain ⟨c, hc, hv⟩ := Finset.mem_biUnion.mp hv
      apply h v
      exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_union_left _ hc, hv⟩
    have hNdep : Φ.SatAll N σ ↔ Φ.SatAll N σ' := by
      apply satall_depend Φ N σ σ'
      intro v hv
      obtain ⟨c, hc, hv⟩ := Finset.mem_biUnion.mp hv
      apply h v
      exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_union_right _ hc, hv⟩
    exact and_congr hTdep hNdep
  have hdepH : ∀ σ σ' : Φ.Config, (∀ v ∈ Z, σ v = σ' v) →
      (Φ.SatAll H σ ↔ Φ.SatAll H σ') := satall_depend Φ H
  have h := independent_events Φ (Φ.SatAll H) (fun σ => Φ.ViolAll T σ ∧ Φ.SatAll N σ)
    Z W hdepH hdepA hdis.symm
  exact h
