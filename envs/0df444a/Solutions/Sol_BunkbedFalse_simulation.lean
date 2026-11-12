-- Prove2me | solution 1 for BunkbedFalse.simulation
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T13:16:54.576984+00:00
-- url     : https://prove2.me/submissions/aaee51d1-968f-453d-9bb7-a6cb94ceda6b

import Definitions.Def_BunkbedSubstituted

/-!
# Bunkbed percolation at `1/2` on the substituted graph IS the Wierman-Ziff model

This is the `simulation` stub of Theorem 1.2 of Gladkov-Pak-Zimin, *The bunkbed conjecture is
false*, PNAS 122 (2025) e2420725122: writing `Pgad` for the tuple of the five partition
probabilities of the gadget `G₁₂₀₄` at `P = 1/2`,

`bbProb subEdges (fun _ => 1/2) subT (iota x, 0) (iota y, l)
   = wzProb hollomTriple hollomT Pgad (x, 0) (y, l)`.

The proof is the following chain.

1. `bbfactor` (edge-disjoint factorisation of `bbProb`, copied from
   `Solutions/Sub2_bbfactor.lean`) turns the left-hand side into a double sum over *tuples*
   `S₀, S₁ : Fin 6 → Finset (Sym2 (Fin 7222))` of subconfigurations of the six copies, using that
   the copies are pairwise disjoint (`SimA.copies_disjoint`, copied from
   `Solutions/Sub2_count.lean`).
2. `SimA.stOf` classifies each copy of such a tuple by the `WZ` state it induces on its
   attachment triple.
3. `SimA.reach_iff_wz`: the bunkbed reachability indicator depends only on the pair of induced
   state tuples.  This is `bbreduce` (the boundary reduction, copied from
   `Solutions/Sub3_bbreduce.lean`) applied to `ψ = SimA.mk2 (stOf S₀) (stOf S₁)`, whose matching
   hypothesis is supplied by `SimA.reach_pairs` (each attachment pair is connected iff the state
   is one of two values -- a consequence of reachability being an equivalence relation).
4. `SimA.fibre_eq`: the fibre of `stOf` over a state tuple is cut out coordinatewise, hence is
   again a `Fintype.piFinset`.
5. `SimA.weight_sum_fibre`: therefore the weight sum over a fibre factorises
   (`Finset.prod_univ_sum`) into a product of the per-copy state probabilities, each of which is
   the corresponding partition probability of `G₁₂₀₄` (`BunkbedRelabel.copy_P*`, copied from
   `Solutions/Sub3_relabel.lean`).  `SimA.key` packages steps 4-5.
6. `SimA.wz_pair`: the currying bijection `((Fin 6 → WZ) × (Fin 6 → WZ)) ≃ (Fin 6 × Fin 2 → WZ)`
   identifies the resulting double sum over state tuples with `wzProb`.

Parts 1-3 are verbatim copies of accepted results (`Solutions/Sub3_relabel.lean`,
`Solutions/Sub2_bbfactor.lean`, `Solutions/Sub3_bbreduce.lean`), whose `theorem solution` is
renamed to `relabel_solution`, `bbfactor` and `bbreduce` respectively; nothing in them is
changed.  Parts 4-7 are new.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
-- the `constructorNameAsVariable` linter `whnf`s the type of every local hypothesis, which for a
-- hypothesis `S ∈ Fintype.piFinset (fun i => (cop i).powerset)` tries to *evaluate* the gadget
set_option linter.constructorNameAsVariable false

open Bunkbed Bunkbed.Hyper SimpleGraph Finset


/-! PART 1: copied from Solutions/Sub3_relabel.lean -/
set_option maxRecDepth 100000

open Bunkbed Bunkbed.Hyper SimpleGraph Finset Function

/-! ## The state classifier of `Solutions/Sub_states.lean` (copied verbatim) -/

namespace GadgetStates

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The five partition events of the triple `(a, b, c)`, written **exactly** as the predicates
occurring in the definitions of `Pabc`, `Pab_c`, `Pac_b`, `Pa_bc`, `Pa_b_c`, and indexed by the
`WZ` state each one describes. -/
def PartEvent (s : WZ) (S : Finset (Sym2 V)) (a b c : V) : Prop :=
  match s with
  | WZ.abc   => (ofEdges S).Reachable a b ∧ (ofEdges S).Reachable b c
  | WZ.ab_c  => (ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable a c
  | WZ.ac_b  => (ofEdges S).Reachable a c ∧ ¬ (ofEdges S).Reachable a b
  | WZ.a_bc  => (ofEdges S).Reachable b c ∧ ¬ (ofEdges S).Reachable a b
  | WZ.a_b_c => ¬ (ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable b c ∧
                  ¬ (ofEdges S).Reachable a c

/-- The `WZ` state that the configuration `S` induces on the triple `(a, b, c)`. -/
def wzStateOf (S : Finset (Sym2 V)) (a b c : V) : WZ :=
  if (ofEdges S).Reachable a b then
    (if (ofEdges S).Reachable b c then WZ.abc else WZ.ab_c)
  else
    if (ofEdges S).Reachable b c then WZ.a_bc
    else if (ofEdges S).Reachable a c then WZ.ac_b else WZ.a_b_c

/-- The tuple of the five partition probabilities, read as a law on `WZ`. -/
def partProb (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) : WZ → ℚ
  | WZ.abc   => Pabc E w a b c
  | WZ.ab_c  => Pab_c E w a b c
  | WZ.ac_b  => Pac_b E w a b c
  | WZ.a_bc  => Pa_bc E w a b c
  | WZ.a_b_c => Pa_b_c E w a b c

/-- The five partition events, as literally written in `Def_BunkbedPercolation`, are exactly the
fibres of the induced-state map. -/
theorem partEvent_iff_state (s : WZ) (S : Finset (Sym2 V)) (a b c : V) :
    PartEvent s S a b c ↔ wzStateOf S a b c = s := by
  by_cases hab : (ofEdges S).Reachable a b
  · by_cases hbc : (ofEdges S).Reachable b c
    · have hac : (ofEdges S).Reachable a c := hab.trans hbc
      cases s <;> simp +decide [PartEvent, wzStateOf, hab, hbc, hac]
    · have hac : ¬ (ofEdges S).Reachable a c := fun h => hbc (hab.symm.trans h)
      cases s <;> simp +decide [PartEvent, wzStateOf, hab, hbc, hac]
  · by_cases hbc : (ofEdges S).Reachable b c
    · have hac : ¬ (ofEdges S).Reachable a c := fun h => hab (h.trans hbc.symm)
      cases s <;> simp +decide [PartEvent, wzStateOf, hab, hbc, hac]
    · by_cases hac : (ofEdges S).Reachable a c
      · cases s <;> simp +decide [PartEvent, wzStateOf, hab, hbc, hac]
      · cases s <;> simp +decide [PartEvent, wzStateOf, hab, hbc, hac]

omit [Fintype V] in
private theorem probOf_congr (E : Finset (Sym2 V)) (w : Sym2 V → ℚ)
    {ev₁ ev₂ : Finset (Sym2 V) → Prop} [DecidablePred ev₁] [DecidablePred ev₂]
    (h : ∀ S, ev₁ S ↔ ev₂ S) : probOf E w ev₁ = probOf E w ev₂ :=
  Finset.sum_congr rfl fun S _ => if_congr (h S) rfl rfl

/-- **The state distribution.** The probability that a configuration induces the state `s` on
`(a, b, c)` is exactly the corresponding partition probability. -/
theorem prob_state_eq (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) (s : WZ) :
    probOf E w (fun S => wzStateOf S a b c = s) = partProb E w a b c s := by
  cases s
  · exact probOf_congr E w fun S => ((partEvent_iff_state WZ.abc S a b c).symm)
  · exact probOf_congr E w fun S => ((partEvent_iff_state WZ.ab_c S a b c).symm)
  · exact probOf_congr E w fun S => ((partEvent_iff_state WZ.ac_b S a b c).symm)
  · exact probOf_congr E w fun S => ((partEvent_iff_state WZ.a_bc S a b c).symm)
  · exact probOf_congr E w fun S => ((partEvent_iff_state WZ.a_b_c S a b c).symm)

end GadgetStates

namespace BunkbedRelabel

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-! ## Edges transport along an injective relabelling -/

omit [Fintype V] [DecidableEq V] [Fintype W] in
/-- Membership in a relabelled edge set is membership in the original one. -/
lemma mem_image_map_iff (f : V → W) (hf : Injective f) (S : Finset (Sym2 V)) (u v : V) :
    s(f u, f v) ∈ S.image (Sym2.map f) ↔ s(u, v) ∈ S := by
  refine ⟨fun h => ?_, fun h => Finset.mem_image.2 ⟨s(u, v), h, by simp⟩⟩
  obtain ⟨e, he, hfe⟩ := Finset.mem_image.1 h
  have : e = s(u, v) := Sym2.map.injective hf (by rw [hfe]; simp)
  exact this ▸ he

omit [Fintype V] [DecidableEq V] [Fintype W] in
/-- Every edge of a relabelled edge set is the relabelling of an edge. -/
lemma exists_of_mem_image_map (f : V → W) (S : Finset (Sym2 V)) {z : Sym2 W}
    (h : z ∈ S.image (Sym2.map f)) : ∃ p q : V, s(p, q) ∈ S ∧ z = s(f p, f q) := by
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
  induction e using Sym2.ind with
  | _ p q => exact ⟨p, q, he, rfl⟩

omit [Fintype V] [DecidableEq V] [Fintype W] in
/-- Adjacency transports along an injective relabelling. -/
lemma adj_image_map (f : V → W) (hf : Injective f) (S : Finset (Sym2 V)) (u v : V) :
    (ofEdges (S.image (Sym2.map f))).Adj (f u) (f v) ↔ (ofEdges S).Adj u v := by
  simp only [ofEdges, fromEdgeSet_adj, Finset.mem_coe]
  rw [mem_image_map_iff f hf, hf.ne_iff]

/-- The relabelling is a graph homomorphism from the original graph to the relabelled one. -/
def imageHom (f : V → W) (hf : Injective f) (S : Finset (Sym2 V)) :
    ofEdges S →g ofEdges (S.image (Sym2.map f)) :=
  ⟨f, fun {_ _} h => (adj_image_map f hf S _ _).2 h⟩

omit [Fintype V] [DecidableEq V] [Fintype W] in
/-- Conversely, the inverse relabelling is a graph homomorphism the other way: this works because
every edge of a relabelled edge set has both endpoints in the range of the relabelling. -/
lemma adj_of_adj_image (f : V → W) (hf : Injective f) (S : Finset (Sym2 V)) [Nonempty V]
    {x y : W} (h : (ofEdges (S.image (Sym2.map f))).Adj x y) :
    (ofEdges S).Adj (invFun f x) (invFun f y) := by
  have hinv : ∀ z : V, invFun f (f z) = z := leftInverse_invFun hf
  simp only [ofEdges, fromEdgeSet_adj, Finset.mem_coe] at h ⊢
  obtain ⟨hmem, hne⟩ := h
  obtain ⟨p, q, hpq, hz⟩ := exists_of_mem_image_map f S hmem
  rcases Sym2.eq_iff.1 hz with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · subst hx; subst hy
    rw [hinv, hinv]
    exact ⟨hpq, fun hh => hne (by rw [hh])⟩
  · subst hx; subst hy
    rw [hinv, hinv]
    exact ⟨by rwa [Sym2.eq_swap], fun hh => hne (by rw [hh])⟩

omit [Fintype V] [DecidableEq V] [Fintype W] in
/-- **Reachability transports along an injective relabelling.**  For injective `f`, the vertices
`u` and `v` are connected in `ofEdges S` if and only if `f u` and `f v` are connected in the
relabelled graph `ofEdges (S.image (Sym2.map f))`. -/
theorem reach_image_map (f : V → W) (hf : Injective f) (S : Finset (Sym2 V)) (u v : V) :
    (ofEdges (S.image (Sym2.map f))).Reachable (f u) (f v) ↔ (ofEdges S).Reachable u v := by
  refine ⟨fun h => ?_, fun h => h.map (imageHom f hf S)⟩
  have : Nonempty V := ⟨u⟩
  have hinv : ∀ z : V, invFun f (f z) = z := leftInverse_invFun hf
  have key : ∀ x y : W, (ofEdges (S.image (Sym2.map f))).Reachable x y →
      (ofEdges S).Reachable (invFun f x) (invFun f y) := fun _ _ hxy =>
    Reachable.map (⟨invFun f, fun {_ _} hab => adj_of_adj_image f hf S hab⟩ :
      ofEdges (S.image (Sym2.map f)) →g ofEdges S) hxy
  have h2 := key (f u) (f v) h
  rwa [hinv, hinv] at h2

/-- The induced `WZ` state of a triple is unchanged by an injective relabelling. -/
theorem wzStateOf_image (f : V → W) (hf : Injective f) (S : Finset (Sym2 V)) (a b c : V) :
    GadgetStates.wzStateOf (S.image (Sym2.map f)) (f a) (f b) (f c)
      = GadgetStates.wzStateOf S a b c := by
  unfold GadgetStates.wzStateOf
  simp only [reach_image_map f hf]

/-! ## Constant weights are unchanged by an injective relabelling -/

omit [Fintype V] in
/-- A constant weight is `c ^ |S| * (1-c) ^ |E \ S|`. -/
lemma weight_const (E S : Finset (Sym2 V)) (c : ℚ) :
    weight E (fun _ => c) S = c ^ S.card * (1 - c) ^ (E \ S).card := by
  unfold weight
  rw [Finset.prod_const, Finset.prod_const]

omit [Fintype V] [Fintype W] in
/-- Constant weights are preserved by an injective relabelling, because an injective image
preserves both `|S|` and `|E \ S|`. -/
lemma weight_image_map (f : V → W) (hf : Injective f) (E S : Finset (Sym2 V)) (c : ℚ) :
    weight (E.image (Sym2.map f)) (fun _ => c) (S.image (Sym2.map f))
      = weight E (fun _ => c) S := by
  have hmi : Injective (Sym2.map f) := Sym2.map.injective hf
  rw [weight_const, weight_const, Finset.card_image_of_injective _ hmi,
    ← Finset.image_sdiff E S hmi, Finset.card_image_of_injective _ hmi]

/-! ## Relabelling invariance of `probOf` -/

omit [Fintype V] [Fintype W] in
/-- **Percolation is invariant under an injective relabelling of the vertices** (constant edge
weight).  The bijection `S ↦ S.image (Sym2.map f)` between `E.powerset` and
`(E.image (Sym2.map f)).powerset` matches the events by hypothesis and the weights by
`weight_image_map`. -/
theorem probOf_image_map (f : V → W) (hf : Injective f) (E : Finset (Sym2 V)) (c : ℚ)
    (ev : Finset (Sym2 V) → Prop) [DecidablePred ev]
    (ev' : Finset (Sym2 W) → Prop) [DecidablePred ev']
    (hev : ∀ S, S ⊆ E → (ev S ↔ ev' (S.image (Sym2.map f)))) :
    probOf E (fun _ => c) ev = probOf (E.image (Sym2.map f)) (fun _ => c) ev' := by
  have hmi : Injective (Sym2.map f) := Sym2.map.injective hf
  unfold probOf
  refine Finset.sum_nbij' (fun S => S.image (Sym2.map f))
    (fun T => E.filter (fun e => Sym2.map f e ∈ T)) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    exact Finset.mem_powerset.2 (Finset.image_subset_image (Finset.mem_powerset.1 hS))
  · intro T _
    exact Finset.mem_powerset.2 (Finset.filter_subset _ _)
  · intro S hS
    have hSE : S ⊆ E := Finset.mem_powerset.1 hS
    ext e
    simp only [Finset.mem_filter, Finset.mem_image]
    refine ⟨fun ⟨_, a, ha, hae⟩ => (hmi hae) ▸ ha, fun h => ⟨hSE h, e, h, rfl⟩⟩
  · intro T hT
    have hTE : T ⊆ E.image (Sym2.map f) := Finset.mem_powerset.1 hT
    ext z
    simp only [Finset.mem_image, Finset.mem_filter]
    refine ⟨fun ⟨e, ⟨_, hez⟩, hze⟩ => hze ▸ hez, fun h => ?_⟩
    obtain ⟨e, heE, rfl⟩ := Finset.mem_image.1 (hTE h)
    exact ⟨e, ⟨heE, h⟩, rfl⟩
  · intro S hS
    rw [weight_image_map f hf E S c, if_congr (hev S (Finset.mem_powerset.1 hS)) rfl rfl]

end BunkbedRelabel

/-- **Percolation is invariant under an injective relabelling of the vertices.**  If the weight
function is the constant `c` and the event `ev` on subconfigurations of `E` corresponds, under the
relabelling `f`, to the event `ev'` on their images, then the two probabilities agree. -/
theorem relabel_solution {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (E : Finset (Sym2 V)) (c : ℚ)
    (ev : Finset (Sym2 V) → Prop) [DecidablePred ev]
    (ev' : Finset (Sym2 W) → Prop) [DecidablePred ev']
    (hev : ∀ S, S ⊆ E → (ev S ↔ ev' (S.image (Sym2.map f)))) :
    probOf E (fun _ => c) ev = probOf (E.image (Sym2.map f)) (fun _ => c) ev' :=
  BunkbedRelabel.probOf_image_map f hf E c ev ev' hev

namespace BunkbedRelabel

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Connection probabilities are invariant under an injective relabelling. -/
theorem connProb_image_map (f : V → W) (hf : Injective f) (E : Finset (Sym2 V)) (c : ℚ)
    (u v : V) :
    connProb E (fun _ => c) u v = connProb (E.image (Sym2.map f)) (fun _ => c) (f u) (f v) :=
  probOf_image_map f hf E c _ _ fun S _ => (reach_image_map f hf S u v).symm

/-- Each of the five partition probabilities is invariant under an injective relabelling. -/
theorem partProb_image_map (f : V → W) (hf : Injective f) (E : Finset (Sym2 V)) (c : ℚ)
    (a b c' : V) (s : WZ) :
    GadgetStates.partProb E (fun _ => c) a b c' s
      = GadgetStates.partProb (E.image (Sym2.map f)) (fun _ => c) (f a) (f b) (f c') s := by
  rw [← GadgetStates.prob_state_eq, ← GadgetStates.prob_state_eq]
  refine probOf_image_map f hf E c _ _ fun S _ => ?_
  rw [wzStateOf_image f hf S a b c']

end BunkbedRelabel

/-! ## Application: a gadget copy of the substituted graph

The copy glued in at hyperedge `i` is the image of `gadgetE 1204` under `Sym2.map (Sub.emb i)`,
and `Sub.emb i` is injective (the injectivity proof is copied from `Solutions/Sub2_count.lean`,
which is not importable as a library).  So by `probOf_image_map` the five partition probabilities
of the copy at its attachment triple are those of `G₁₂₀₄` at `(0, 1, Fin.last 1204)`.
-/

namespace BunkbedRelabel

/-- The attachment table of Hollom's hypergraph (copied from `Solutions/Sub2_count.lean`). -/
lemma tri_val (i : Fin 6) :
    (i.val = 0 ∧ (hollomTr i).val = 1 ∧ (hollomPath i.castSucc).val = 0 ∧
        (hollomPath i.succ).val = 2) ∨
    (i.val = 1 ∧ (hollomTr i).val = 8 ∧ (hollomPath i.castSucc).val = 2 ∧
        (hollomPath i.succ).val = 5) ∨
    (i.val = 2 ∧ (hollomTr i).val = 6 ∧ (hollomPath i.castSucc).val = 5 ∧
        (hollomPath i.succ).val = 4) ∨
    (i.val = 3 ∧ (hollomTr i).val = 1 ∧ (hollomPath i.castSucc).val = 4 ∧
        (hollomPath i.succ).val = 3) ∨
    (i.val = 4 ∧ (hollomTr i).val = 6 ∧ (hollomPath i.castSucc).val = 3 ∧
        (hollomPath i.succ).val = 7) ∨
    (i.val = 5 ∧ (hollomTr i).val = 8 ∧ (hollomPath i.castSucc).val = 7 ∧
        (hollomPath i.succ).val = 9) := by
  fin_cases i
  · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))))

/-- The transversal vertices are `1`, `6`, `8`. -/
lemma trv (i : Fin 6) : (hollomTr i).val = 1 ∨ (hollomTr i).val = 8 ∨ (hollomTr i).val = 6 := by
  rcases tri_val i with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ <;>
    omega

/-- The path vertices are `0, 2, 5, 4, 3, 7, 9`. -/
lemma pathv (j : Fin 7) : (hollomPath j).val = 0 ∨ (hollomPath j).val = 2 ∨
    (hollomPath j).val = 5 ∨ (hollomPath j).val = 4 ∨ (hollomPath j).val = 3 ∨
    (hollomPath j).val = 7 ∨ (hollomPath j).val = 9 := by
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

lemma tr_ne_path : ∀ (i : Fin 6) (j : Fin 7), hollomTr i ≠ hollomPath j := by
  intro i j h
  have hv : (hollomTr i).val = (hollomPath j).val := by rw [h]
  have h1 := trv i
  have h2 := pathv j
  omega

lemma cs_ne_succ : ∀ i : Fin 6, hollomPath i.castSucc ≠ hollomPath i.succ := by
  intro i h
  have hv : (hollomPath i.castSucc).val = (hollomPath i.succ).val := by rw [h]
  rcases tri_val i with ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ |
    ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ <;> omega

lemma embN_zero (i : Fin 6) : Sub.embN i 0 = (hollomTr i).val := by simp [Sub.embN]
lemma embN_one (i : Fin 6) : Sub.embN i 1 = (hollomPath i.castSucc).val := by simp [Sub.embN]
lemma embN_last (i : Fin 6) : Sub.embN i 1204 = (hollomPath i.succ).val := by simp [Sub.embN]

lemma embN_interior (i : Fin 6) (k : ℕ) (h2 : 2 ≤ k) (h3 : k ≤ 1203) :
    Sub.embN i k = 10 + 1202 * i.val + (k - 2) := by
  unfold Sub.embN; split_ifs <;> omega

lemma embN_bdry (i : Fin 6) (k : ℕ) (h : k = 0 ∨ k = 1 ∨ k = 1204) : Sub.embN i k < 10 := by
  have h3 : (hollomTr i).val < 10 := (hollomTr i).isLt
  have h4 : (hollomPath i.castSucc).val < 10 := (hollomPath i.castSucc).isLt
  have h5 : (hollomPath i.succ).val < 10 := (hollomPath i.succ).isLt
  rcases h with rfl | rfl | rfl <;> (unfold Sub.embN; split_ifs <;> omega)

lemma embN_bdry_inj (i : Fin 6) (k l : ℕ) (hk : k = 0 ∨ k = 1 ∨ k = 1204)
    (hl : l = 0 ∨ l = 1 ∨ l = 1204) (h : Sub.embN i k = Sub.embN i l) : k = l := by
  have n1 : (hollomTr i).val ≠ (hollomPath i.castSucc).val :=
    fun hh => tr_ne_path i i.castSucc (Fin.ext hh)
  have n2 : (hollomTr i).val ≠ (hollomPath i.succ).val :=
    fun hh => tr_ne_path i i.succ (Fin.ext hh)
  have n3 : (hollomPath i.castSucc).val ≠ (hollomPath i.succ).val :=
    fun hh => cs_ne_succ i (Fin.ext hh)
  rcases hk with rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl <;>
    simp only [embN_zero, embN_one, embN_last] at h <;> omega

/-- Every gadget index is one of the three attachment indices, or interior. -/
lemma idx_cases (k : Fin 1205) :
    (k.val = 0 ∨ k.val = 1 ∨ k.val = 1204) ∨ (2 ≤ k.val ∧ k.val ≤ 1203) := by
  have := k.isLt; omega

/-- **The embedding of a gadget copy is injective** (copied from `Solutions/Sub2_count.lean`). -/
lemma emb_inj (i : Fin 6) : Function.Injective (Sub.emb i) := by
  intro k l h
  have hv : Sub.embN i k.val = Sub.embN i l.val := congrArg Fin.val h
  rcases idx_cases k with hk | hk <;> rcases idx_cases l with hl | hl
  · exact Fin.ext (embN_bdry_inj i k.val l.val hk hl hv)
  · have h1 := embN_bdry i k.val hk
    have h2 := embN_interior i l.val hl.1 hl.2
    omega
  · have h1 := embN_bdry i l.val hl
    have h2 := embN_interior i k.val hk.1 hk.2
    omega
  · have h1 := embN_interior i k.val hk.1 hk.2
    have h2 := embN_interior i l.val hl.1 hl.2
    exact Fin.ext (by omega)

/-- The numeral `1204` is the last index of `Fin 1205`. -/
lemma last_eq : (1204 : Fin 1205) = Fin.last 1204 := rfl

/-- At `P = 1/2` the gadget weight function is the constant `1/2`: both branches of the `if`
in `gadgetW` are `1/2`. -/
lemma gadgetW_half (n : ℕ) : gadgetW n (1/2 : ℚ) = fun _ => (1/2 : ℚ) := by
  funext e
  unfold gadgetW
  split_ifs <;> norm_num

/-- **The partition probabilities of a gadget copy are those of the gadget.**  For each of the six
hyperedges `i` and each of the five `WZ` states `s`, the probability that the copy glued in at `i`
puts its attachment triple `(Sub.emb i 0, Sub.emb i 1, Sub.emb i 1204)` in state `s` equals the
corresponding partition probability of `G₁₂₀₄` at `(0, 1, Fin.last 1204)`. -/
theorem copy_partProb (i : Fin 6) (s : WZ) :
    probOf ((gadgetE 1204).image (Sym2.map (Sub.emb i))) (fun _ => (1/2 : ℚ))
        (fun S => GadgetStates.wzStateOf S (Sub.emb i 0) (Sub.emb i 1) (Sub.emb i 1204) = s)
      = GadgetStates.partProb (gadgetE 1204) (fun _ => (1/2 : ℚ)) 0 1 (Fin.last 1204) s := by
  rw [← GadgetStates.prob_state_eq]
  refine (probOf_image_map (Sub.emb i) (emb_inj i) (gadgetE 1204) (1/2) _ _ fun S _ => ?_).symm
  rw [last_eq, wzStateOf_image (Sub.emb i) (emb_inj i) S 0 1 (Fin.last 1204)]

/-! ### The five partition probabilities of a copy, spelled out with `gadgetW` -/

theorem copy_Pabc (i : Fin 6) :
    probOf ((gadgetE 1204).image (Sym2.map (Sub.emb i))) (fun _ => (1/2 : ℚ))
        (fun S => GadgetStates.wzStateOf S (Sub.emb i 0) (Sub.emb i 1) (Sub.emb i 1204) = WZ.abc)
      = Pabc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204) := by
  rw [gadgetW_half 1204]; exact copy_partProb i WZ.abc

theorem copy_Pab_c (i : Fin 6) :
    probOf ((gadgetE 1204).image (Sym2.map (Sub.emb i))) (fun _ => (1/2 : ℚ))
        (fun S => GadgetStates.wzStateOf S (Sub.emb i 0) (Sub.emb i 1) (Sub.emb i 1204) = WZ.ab_c)
      = Pab_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204) := by
  rw [gadgetW_half 1204]; exact copy_partProb i WZ.ab_c

theorem copy_Pac_b (i : Fin 6) :
    probOf ((gadgetE 1204).image (Sym2.map (Sub.emb i))) (fun _ => (1/2 : ℚ))
        (fun S => GadgetStates.wzStateOf S (Sub.emb i 0) (Sub.emb i 1) (Sub.emb i 1204) = WZ.ac_b)
      = Pac_b (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204) := by
  rw [gadgetW_half 1204]; exact copy_partProb i WZ.ac_b

theorem copy_Pa_bc (i : Fin 6) :
    probOf ((gadgetE 1204).image (Sym2.map (Sub.emb i))) (fun _ => (1/2 : ℚ))
        (fun S => GadgetStates.wzStateOf S (Sub.emb i 0) (Sub.emb i 1) (Sub.emb i 1204) = WZ.a_bc)
      = Pa_bc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204) := by
  rw [gadgetW_half 1204]; exact copy_partProb i WZ.a_bc

theorem copy_Pa_b_c (i : Fin 6) :
    probOf ((gadgetE 1204).image (Sym2.map (Sub.emb i))) (fun _ => (1/2 : ℚ))
        (fun S => GadgetStates.wzStateOf S (Sub.emb i 0) (Sub.emb i 1) (Sub.emb i 1204) = WZ.a_b_c)
      = Pa_b_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204) := by
  rw [gadgetW_half 1204]; exact copy_partProb i WZ.a_b_c

end BunkbedRelabel

/-! PART 2: copied from Solutions/Sub2_bbfactor.lean -/
open Bunkbed Finset

set_option linter.unusedSectionVars false

namespace Sub2BBFactor

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {iota : Type*} [Fintype iota] [DecidableEq iota]

/-! ## Set-level lemmas (copied from `Solutions/Sub_factor.lean`) -/

/-- If the `E i` are pairwise disjoint and `S i ⊆ E i`, then removing `⋃ S` from `⋃ E` can be
done part by part. -/
lemma sdiff_biUnion (E S : iota → Finset (Sym2 V))
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j)) (hsub : ∀ i, S i ⊆ E i) :
    (univ.biUnion E) \ (univ.biUnion S) = univ.biUnion (fun i => E i \ S i) := by
  ext e
  simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, hi⟩, hno⟩
    exact ⟨i, hi, fun h => hno ⟨i, h⟩⟩
  · rintro ⟨i, hi, hni⟩
    refine ⟨⟨i, hi⟩, ?_⟩
    rintro ⟨j, hj⟩
    by_cases hij : j = i
    · rw [hij] at hj; exact hni hj
    · exact (Finset.disjoint_left.mp (hdisj i j (Ne.symm hij)) hi) (hsub j hj)

/-- Forward-backward: a tuple of parts is recovered from its union. -/
lemma biUnion_inter (E S : iota → Finset (Sym2 V))
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j)) (hsub : ∀ i, S i ⊆ E i) (i : iota) :
    (univ.biUnion S) ∩ E i = S i := by
  ext e
  simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨j, hj⟩, hEi⟩
    by_cases hij : j = i
    · rw [hij] at hj; exact hj
    · exact absurd (hsub j hj) (Finset.disjoint_left.mp (hdisj i j (Ne.symm hij)) hEi)
  · intro h
    exact ⟨⟨i, h⟩, hsub i h⟩

/-- Backward-forward: a subset of `⋃ E` is recovered from its intersections with the parts. -/
lemma biUnion_inter_eq_self (E : iota → Finset (Sym2 V)) (T : Finset (Sym2 V))
    (hT : T ⊆ univ.biUnion E) :
    univ.biUnion (fun i => T ∩ E i) = T := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · rintro ⟨i, h, -⟩; exact h
  · intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (hT h)
    exact ⟨i, h, hi⟩

/-- `⋃ S ⊆ ⋃ E` when `S i ⊆ E i`. -/
lemma biUnion_mono_pointwise (E S : iota → Finset (Sym2 V)) (hsub : ∀ i, S i ⊆ E i) :
    univ.biUnion S ⊆ univ.biUnion E := by
  intro e he
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp he
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hsub i hi⟩

/-- The percolation weight of a configuration assembled from pairwise disjoint parts is the
product of the weights of the parts. -/
lemma weight_biUnion (E S : iota → Finset (Sym2 V))
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j)) (hsub : ∀ i, S i ⊆ E i) (w : Sym2 V → ℚ) :
    weight (univ.biUnion E) w (univ.biUnion S) = ∏ i, weight (E i) w (S i) := by
  have hSd : (↑(univ : Finset iota) : Set iota).PairwiseDisjoint S := by
    intro i _ j _ hij
    simp only [Function.onFun]
    exact Finset.disjoint_of_subset_left (hsub i)
      (Finset.disjoint_of_subset_right (hsub j) (hdisj i j hij))
  have hEd : (↑(univ : Finset iota) : Set iota).PairwiseDisjoint (fun i => E i \ S i) := by
    intro i _ j _ hij
    simp only [Function.onFun]
    exact Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset (hdisj i j hij))
  simp only [weight]
  rw [sdiff_biUnion E S hdisj hsub, Finset.prod_biUnion hSd, Finset.prod_biUnion hEd,
    ← Finset.prod_mul_distrib]

/-! ## The reusable one-variable sub-lemma -/

/-- **Reusable engine.**  A weighted sum over all subsets of a disjoint union `⋃ i, E i`
reindexes as a sum over *tuples* of subsets of the parts, with the weight factoring as a
product.  `F` is an arbitrary coefficient function. -/
lemma sum_weight_biUnion (E : iota → Finset (Sym2 V))
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j)) (w : Sym2 V → ℚ)
    (F : Finset (Sym2 V) → ℚ) :
    (∑ S ∈ (univ.biUnion E).powerset, F S * weight (univ.biUnion E) w S)
      = ∑ S ∈ Fintype.piFinset (fun i => (E i).powerset),
          F (univ.biUnion S) * ∏ i, weight (E i) w (S i) := by
  refine Finset.sum_nbij' (i := fun T i => T ∩ E i) (j := fun S => univ.biUnion S)
    ?_ ?_ ?_ ?_ ?_
  · intro T _
    exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_powerset.mpr Finset.inter_subset_right)
  · intro S hS
    have hsub : ∀ i, S i ⊆ E i := fun i =>
      Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hS i)
    exact Finset.mem_powerset.mpr (biUnion_mono_pointwise E S hsub)
  · intro T hT
    exact biUnion_inter_eq_self E T (Finset.mem_powerset.mp hT)
  · intro S hS
    have hsub : ∀ i, S i ⊆ E i := fun i =>
      Finset.mem_powerset.mp (Fintype.mem_piFinset.mp hS i)
    funext i
    exact biUnion_inter E S hdisj hsub i
  · intro T hT
    have hTsub : T ⊆ univ.biUnion E := Finset.mem_powerset.mp hT
    have hsub : ∀ i, T ∩ E i ⊆ E i := fun _ => Finset.inter_subset_right
    have hrec : univ.biUnion (fun i => T ∩ E i) = T := biUnion_inter_eq_self E T hTsub
    rw [hrec, ← weight_biUnion E (fun i => T ∩ E i) hdisj hsub w, hrec]

/-! ## The two-variable version -/

/-- Two independent percolations on a disjoint union reindex simultaneously. -/
lemma sum_sum_weight_biUnion (E : iota → Finset (Sym2 V))
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j)) (w : Sym2 V → ℚ)
    (G : Finset (Sym2 V) → Finset (Sym2 V) → ℚ) :
    (∑ S₀ ∈ (univ.biUnion E).powerset, ∑ S₁ ∈ (univ.biUnion E).powerset,
        G S₀ S₁ * weight (univ.biUnion E) w S₀ * weight (univ.biUnion E) w S₁)
      = ∑ S₀ ∈ Fintype.piFinset (fun i => (E i).powerset),
          ∑ S₁ ∈ Fintype.piFinset (fun i => (E i).powerset),
            G (univ.biUnion S₀) (univ.biUnion S₁)
              * (∏ i, weight (E i) w (S₀ i)) * ∏ i, weight (E i) w (S₁ i) := by
  have inner : ∀ S₀ : Finset (Sym2 V),
      (∑ S₁ ∈ (univ.biUnion E).powerset,
          G S₀ S₁ * weight (univ.biUnion E) w S₀ * weight (univ.biUnion E) w S₁)
        = (∑ S₁ ∈ (univ.biUnion E).powerset, G S₀ S₁ * weight (univ.biUnion E) w S₁)
            * weight (univ.biUnion E) w S₀ := by
    intro S₀
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun S₁ _ => by ring)
  have step1 :
      (∑ S₀ ∈ (univ.biUnion E).powerset, ∑ S₁ ∈ (univ.biUnion E).powerset,
          G S₀ S₁ * weight (univ.biUnion E) w S₀ * weight (univ.biUnion E) w S₁)
        = ∑ S₀ ∈ (univ.biUnion E).powerset,
            (∑ S₁ ∈ (univ.biUnion E).powerset, G S₀ S₁ * weight (univ.biUnion E) w S₁)
              * weight (univ.biUnion E) w S₀ :=
    Finset.sum_congr rfl (fun S₀ _ => inner S₀)
  have step2 :
      (∑ S₀ ∈ (univ.biUnion E).powerset,
          (∑ S₁ ∈ (univ.biUnion E).powerset, G S₀ S₁ * weight (univ.biUnion E) w S₁)
            * weight (univ.biUnion E) w S₀)
        = ∑ S₀ ∈ Fintype.piFinset (fun i => (E i).powerset),
            (∑ S₁ ∈ (univ.biUnion E).powerset,
                G (univ.biUnion S₀) S₁ * weight (univ.biUnion E) w S₁)
              * ∏ i, weight (E i) w (S₀ i) :=
    sum_weight_biUnion E hdisj w
      (fun S₀ => ∑ S₁ ∈ (univ.biUnion E).powerset, G S₀ S₁ * weight (univ.biUnion E) w S₁)
  rw [step1, step2]
  refine Finset.sum_congr rfl (fun S₀ _ => ?_)
  rw [sum_weight_biUnion E hdisj w (fun S₁ => G (univ.biUnion S₀) S₁), Finset.sum_mul]
  exact Finset.sum_congr rfl (fun S₁ _ => by ring)

end Sub2BBFactor

open Sub2BBFactor

theorem bbfactor {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → Finset (Sym2 V)) (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (w : Sym2 V → ℚ) (T : Finset V) (x y : V × Fin 2) :
    bbProb (Finset.univ.biUnion E) w T x y
      = ∑ S₀ ∈ Fintype.piFinset (fun i => (E i).powerset),
          ∑ S₁ ∈ Fintype.piFinset (fun i => (E i).powerset),
            (if (bbGraph T (Finset.univ.biUnion (fun i => S₀ i))
                  (Finset.univ.biUnion (fun i => S₁ i))).Reachable x y then (1 : ℚ) else 0)
              * (∏ i, weight (E i) w (S₀ i)) * (∏ i, weight (E i) w (S₁ i)) := by
  rw [bbProb]
  exact sum_sum_weight_biUnion E hdisj w
    (fun S₀ S₁ => if (bbGraph T S₀ S₁).Reachable x y then (1 : ℚ) else 0)


/-! PART 3: copied from Solutions/Sub3_bbreduce.lean -/
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

open Bunkbed Bunkbed.Hyper SimpleGraph Finset

namespace Bunkbed.Sub3

open Bunkbed.Sub

/-! ## Generic facts about `ofEdges` -/

section Generic

variable {W : Type*}

lemma mem_of_adj {S : Finset (Sym2 W)} {u v : W} (h : (ofEdges S).Adj u v) : s(u, v) ∈ S := by
  simpa using ((fromEdgeSet_adj (s := (S : Set (Sym2 W)))).mp h).1

lemma adj_of_mem {S : Finset (Sym2 W)} {u v : W} (h : s(u, v) ∈ S) (hne : u ≠ v) :
    (ofEdges S).Adj u v :=
  (fromEdgeSet_adj (s := (S : Set (Sym2 W)))).mpr ⟨by simpa using h, hne⟩

lemma reachable_of_mem {S : Finset (Sym2 W)} {u v : W} (h : s(u, v) ∈ S) (hne : u ≠ v) :
    (ofEdges S).Reachable u v := (adj_of_mem h hne).reachable

/-- A predicate closed under passing to adjacent vertices is closed under reachability. -/
lemma prop_transport {G : SimpleGraph W} {P : W → Prop} (hstep : ∀ u v, G.Adj u v → P u → P v) :
    ∀ {x y : W}, G.Reachable x y → P x → P y := by
  intro x y h
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact id
  | cons hadj _ ih => exact fun hx => ih (hstep _ _ hadj hx)

lemma mem_of_reachable {G : SimpleGraph W} {K : Set W}
    (hK : ∀ u v, G.Adj u v → u ∈ K → v ∈ K) : ∀ {x y : W}, G.Reachable x y → x ∈ K → y ∈ K :=
  prop_transport hK

/-- If no edge of `S` crosses the boundary of `K`, no vertex of `K` reaches a vertex outside. -/
lemma not_reachable_of_sep {S : Finset (Sym2 W)} {K : Set W} {x y : W}
    (hK : ∀ u v : W, s(u, v) ∈ S → (u ∈ K ↔ v ∈ K)) (hx : x ∈ K) (hy : y ∉ K) :
    ¬ (ofEdges S).Reachable x y := fun h =>
  hy (mem_of_reachable (fun _ _ hadj hu => (hK _ _ (mem_of_adj hadj)).mp hu) h hx)

/-- If `u` is reachable from some *other* vertex, then `u` is covered by an edge. -/
lemma exists_edge_of_reachable_ne {T : Finset (Sym2 W)} {b u : W}
    (h : (ofEdges T).Reachable b u) (hne : b ≠ u) : ∃ f ∈ T, u ∈ f := by
  obtain ⟨p⟩ := h.symm
  cases p with
  | nil => exact absurd rfl hne
  | cons hadj q =>
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    exact ⟨_, Finset.mem_coe.1 hadj.1, by simp⟩

lemma flipIff {G₁ G₂ : SimpleGraph W} {u v : W} (h : G₁.Reachable u v ↔ G₂.Reachable u v) :
    G₁.Reachable v u ↔ G₂.Reachable v u :=
  ⟨fun hh => (h.1 hh.symm).symm, fun hh => (h.2 hh.symm).symm⟩

end Generic

/-! ## Relabelling along an injective vertex map -/

section Relabel

variable {A B : Type*} [DecidableEq B] {f : A → B}

lemma map_eq_pair : ∀ (g : Sym2 A) (p q : B), Sym2.map f g = s(p, q) →
    ∃ a b : A, g = s(a, b) ∧ f a = p ∧ f b = q := by
  intro g
  induction g using Sym2.ind with
  | _ a b =>
    intro p q h
    rw [Sym2.map_mk, Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨a, b, rfl, h1, h2⟩
    · exact ⟨b, a, Sym2.eq_swap, h2, h1⟩

lemma adj_map (hf : Function.Injective f) {E : Finset (Sym2 A)} {u v : A}
    (h : (ofEdges E).Adj u v) : (ofEdges (E.image (Sym2.map f))).Adj (f u) (f v) := by
  refine adj_of_mem ?_ (fun hh => h.ne (hf hh))
  have h2 := Finset.mem_image_of_mem (Sym2.map f) (mem_of_adj h)
  simpa using h2

lemma reach_map (hf : Function.Injective f) {E : Finset (Sym2 A)} :
    ∀ {u v : A}, (ofEdges E).Reachable u v →
      (ofEdges (E.image (Sym2.map f))).Reachable (f u) (f v) := by
  intro u v h
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj _ ih => exact ((adj_map hf hadj).reachable).trans ih

lemma reach_of_map (hf : Function.Injective f) {E : Finset (Sym2 A)} {u v : A}
    (h : (ofEdges (E.image (Sym2.map f))).Reachable (f u) (f v)) : (ofEdges E).Reachable u v := by
  have step : ∀ p q : B, (ofEdges (E.image (Sym2.map f))).Adj p q →
      (∃ a, f a = p ∧ (ofEdges E).Reachable u a) → ∃ a, f a = q ∧ (ofEdges E).Reachable u a := by
    intro p q hadj hp
    obtain ⟨a, hfa, hra⟩ := hp
    obtain ⟨g, hg, hgpq⟩ := Finset.mem_image.1 (mem_of_adj hadj)
    obtain ⟨b, c, rfl, hb, hc⟩ := map_eq_pair g p q hgpq
    have hba : b = a := hf (by rw [hb, hfa])
    have hrb : (ofEdges E).Reachable u b := by rw [hba]; exact hra
    refine ⟨c, hc, hrb.trans (reachable_of_mem hg ?_)⟩
    intro hbc
    exact hadj.ne (by rw [← hb, ← hc, hbc])
  obtain ⟨a, hfa, hra⟩ := prop_transport step h ⟨u, rfl, Reachable.refl u⟩
  rw [← hf hfa]
  exact hra

/-- **Relabelling.**  Reachability is invariant under an injective relabelling of the vertices. -/
lemma reach_map_iff (hf : Function.Injective f) (E : Finset (Sym2 A)) (u v : A) :
    (ofEdges (E.image (Sym2.map f))).Reachable (f u) (f v) ↔ (ofEdges E).Reachable u v :=
  ⟨reach_of_map hf, reach_map hf⟩

end Relabel

/-! ## Boundary congruence (a copy of the accepted `BunkbedAux.boundary_congr`) -/

section Boundary

variable {V : Type*} [DecidableEq V] {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma reachable_union (S : ι → Finset (Sym2 V)) (i : ι) {p q : V}
    (h : (ofEdges (S i)).Reachable p q) : (ofEdges (univ.biUnion S)).Reachable p q :=
  h.mono (fromEdgeSet_mono
    (Finset.coe_subset.2 (Finset.subset_biUnion_of_mem S (mem_univ i))))

lemma adj_union_part {S : ι → Finset (Sym2 V)} {u v : V}
    (h : (ofEdges (univ.biUnion S)).Adj u v) :
    ∃ i, (ofEdges (S i)).Adj u v ∧ s(u, v) ∈ S i := by
  rw [SimpleGraph.fromEdgeSet_adj] at h
  obtain ⟨hmem, hne⟩ := h
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hmem)
  exact ⟨i, (SimpleGraph.fromEdgeSet_adj _).2 ⟨Finset.mem_coe.2 hi, hne⟩, hi⟩

/-- The walk invariant: the current vertex is reached from `x` by travelling in the *new* union
to a boundary vertex and then inside a **single** part of the *old* family. -/
def Good (S S' : ι → Finset (Sym2 V)) (Bd : Finset V) (x v : V) : Prop :=
  ∃ b ∈ Bd, (ofEdges (univ.biUnion S')).Reachable x b ∧
    (b = v ∨ ∃ i, (ofEdges (S i)).Reachable b v)

lemma good_step {S S' : ι → Finset (Sym2 V)} {Bd : Finset V}
    (hsame : ∀ i, ∀ p ∈ Bd, ∀ q ∈ Bd,
      (ofEdges (S i)).Reachable p q → (ofEdges (S' i)).Reachable p q)
    (hsupp : ∀ i, ∀ e ∈ S i, ∀ v ∈ e, v ∉ Bd → ∀ j, j ≠ i → ∀ f ∈ S j, v ∉ f)
    {x u v : V} (hu : Good S S' Bd x u)
    (hadj : (ofEdges (univ.biUnion S)).Adj u v) : Good S S' Bd x v := by
  obtain ⟨b, hbB, hxb, hbu⟩ := hu
  obtain ⟨i, hadji, hi⟩ := adj_union_part hadj
  by_cases huB : u ∈ Bd
  · refine ⟨u, huB, ?_, Or.inr ⟨i, hadji.reachable⟩⟩
    rcases hbu with rfl | ⟨j, hj⟩
    · exact hxb
    · exact hxb.trans (reachable_union S' j (hsame j b hbB u huB hj))
  · rcases hbu with rfl | ⟨j, hj⟩
    · exact absurd hbB huB
    · have hbne : b ≠ u := by rintro rfl; exact huB hbB
      have hji : j = i := by
        by_contra hjne
        obtain ⟨f, hf, huf⟩ := exists_edge_of_reachable_ne hj hbne
        exact hsupp i s(u, v) hi u (by simp) huB j hjne f hf huf
      have hj' : (ofEdges (S i)).Reachable b u := by rw [← hji]; exact hj
      exact ⟨b, hbB, hxb, Or.inr ⟨i, hj'.trans hadji.reachable⟩⟩

lemma good_transport {S S' : ι → Finset (Sym2 V)} {Bd : Finset V}
    (hsame : ∀ i, ∀ p ∈ Bd, ∀ q ∈ Bd,
      (ofEdges (S i)).Reachable p q → (ofEdges (S' i)).Reachable p q)
    (hsupp : ∀ i, ∀ e ∈ S i, ∀ v ∈ e, v ∉ Bd → ∀ j, j ≠ i → ∀ f ∈ S j, v ∉ f)
    {x u v : V} (W : (ofEdges (univ.biUnion S)).Walk u v) :
    Good S S' Bd x u → Good S S' Bd x v := by
  induction W with
  | nil => exact id
  | cons hadj _ ih => exact fun h => ih (good_step hsame hsupp h hadj)

lemma bc_reachable_of_reachable {S S' : ι → Finset (Sym2 V)} {Bd : Finset V}
    (hsame : ∀ i, ∀ p ∈ Bd, ∀ q ∈ Bd,
      (ofEdges (S i)).Reachable p q → (ofEdges (S' i)).Reachable p q)
    (hsupp : ∀ i, ∀ e ∈ S i, ∀ v ∈ e, v ∉ Bd → ∀ j, j ≠ i → ∀ f ∈ S j, v ∉ f)
    {x y : V} (hx : x ∈ Bd) (hy : y ∈ Bd)
    (h : (ofEdges (univ.biUnion S)).Reachable x y) :
    (ofEdges (univ.biUnion S')).Reachable x y := by
  obtain ⟨W⟩ := h
  obtain ⟨b, hbB, hxb, hby⟩ :=
    good_transport hsame hsupp W ⟨x, hx, SimpleGraph.Reachable.refl x, Or.inl rfl⟩
  rcases hby with rfl | ⟨j, hj⟩
  · exact hxb
  · exact hxb.trans (reachable_union S' j (hsame j b hbB y hy hj))

/-- **Connectivity depends only on the boundary partitions.** -/
theorem bc_boundary_congr (S S' : ι → Finset (Sym2 V)) (Bd : Finset V)
    (hsame : ∀ i, ∀ p ∈ Bd, ∀ q ∈ Bd,
      ((ofEdges (S i)).Reachable p q ↔ (ofEdges (S' i)).Reachable p q))
    (hsupp : ∀ i, ∀ e ∈ S i, ∀ v ∈ e, v ∉ Bd → ∀ j, j ≠ i → ∀ f ∈ S j, v ∉ f)
    (hsupp' : ∀ i, ∀ e ∈ S' i, ∀ v ∈ e, v ∉ Bd → ∀ j, j ≠ i → ∀ f ∈ S' j, v ∉ f)
    (x y : V) (hx : x ∈ Bd) (hy : y ∈ Bd) :
    ((ofEdges (Finset.univ.biUnion S)).Reachable x y
      ↔ (ofEdges (Finset.univ.biUnion S')).Reachable x y) :=
  ⟨bc_reachable_of_reachable (fun i p hp q hq => (hsame i p hp q hq).1) hsupp hx hy,
   bc_reachable_of_reachable (fun i p hp q hq => (hsame i p hp q hq).2) hsupp' hx hy⟩

end Boundary

/-! ## The canonical WZ edge sets (copies of the accepted `BunkbedAux.wzEdges_*`) -/

section WZStates

variable {V : Type*} [DecidableEq V]

theorem edges_support (a b c : V) (l : Fin 2) (s : WZ) (e : Sym2 (V × Fin 2))
    (he : e ∈ WZ.edges s (a, b, c) l) (v : V × Fin 2) (hv : v ∈ e) :
    v = (a, l) ∨ v = (b, l) ∨ v = (c, l) := by
  cases s <;>
    simp only [WZ.edges, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] at he
  · rcases he with rfl | rfl | rfl <;> (simp only [Sym2.mem_iff] at hv; tauto)
  · subst he; simp only [Sym2.mem_iff] at hv; tauto
  · subst he; simp only [Sym2.mem_iff] at hv; tauto
  · subst he; simp only [Sym2.mem_iff] at hv; tauto

private lemma lift_ne {x y : V} (h : x ≠ y) (l : Fin 2) : ((x, l) : V × Fin 2) ≠ (y, l) := by
  simp [Prod.ext_iff, h]

theorem reach_iff (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (l : Fin 2) (s : WZ) :
    ((ofEdges (WZ.edges s (a, b, c) l)).Reachable (a, l) (b, l) ↔ (s = WZ.abc ∨ s = WZ.ab_c))
    ∧ ((ofEdges (WZ.edges s (a, b, c) l)).Reachable (b, l) (c, l) ↔ (s = WZ.abc ∨ s = WZ.a_bc))
    ∧ ((ofEdges (WZ.edges s (a, b, c) l)).Reachable (a, l) (c, l) ↔
        (s = WZ.abc ∨ s = WZ.ac_b)) := by
  have hab' : ((a, l) : V × Fin 2) ≠ (b, l) := lift_ne hab l
  have hbc' : ((b, l) : V × Fin 2) ≠ (c, l) := lift_ne hbc l
  have hac' : ((a, l) : V × Fin 2) ≠ (c, l) := lift_ne hac l
  cases s
  · refine ⟨?_, ?_, ?_⟩
    · exact iff_of_true (reachable_of_mem (by simp [WZ.edges]) hab') (Or.inl rfl)
    · exact iff_of_true (reachable_of_mem (by simp [WZ.edges]) hbc') (Or.inl rfl)
    · exact iff_of_true (reachable_of_mem (by simp [WZ.edges]) hac') (Or.inl rfl)
  · have key : ∀ u v : V × Fin 2, s(u, v) ∈ WZ.edges WZ.ab_c (a, b, c) l →
        (u ∈ ({(a, l), (b, l)} : Set (V × Fin 2)) ↔ v ∈ ({(a, l), (b, l)} : Set (V × Fin 2))) := by
      intro u v hu
      simp only [WZ.edges, Finset.mem_singleton, Sym2.eq_iff] at hu
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> simp
    refine ⟨?_, ?_, ?_⟩
    · exact iff_of_true (reachable_of_mem (by simp [WZ.edges]) hab') (Or.inr rfl)
    · exact iff_of_false
        (not_reachable_of_sep key (by simp) (by simp [hac.symm, hbc.symm])) (by decide)
    · exact iff_of_false
        (not_reachable_of_sep key (by simp) (by simp [hac.symm, hbc.symm])) (by decide)
  · have key : ∀ u v : V × Fin 2, s(u, v) ∈ WZ.edges WZ.ac_b (a, b, c) l →
        (u ∈ ({(b, l)} : Set (V × Fin 2)) ↔ v ∈ ({(b, l)} : Set (V × Fin 2))) := by
      intro u v hu
      simp only [WZ.edges, Finset.mem_singleton, Sym2.eq_iff] at hu
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> simp [hab, hbc.symm]
    have key2 : ∀ u v : V × Fin 2, s(u, v) ∈ WZ.edges WZ.ac_b (a, b, c) l →
        (u ∈ ({(a, l), (c, l)} : Set (V × Fin 2)) ↔ v ∈ ({(a, l), (c, l)} : Set (V × Fin 2))) := by
      intro u v hu
      simp only [WZ.edges, Finset.mem_singleton, Sym2.eq_iff] at hu
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> simp
    refine ⟨?_, ?_, ?_⟩
    · exact iff_of_false
        (not_reachable_of_sep key2 (by simp) (by simp [hab.symm, hbc])) (by decide)
    · exact iff_of_false (not_reachable_of_sep key (by simp) (by simp [hbc.symm])) (by decide)
    · exact iff_of_true (reachable_of_mem (by simp [WZ.edges]) hac') (Or.inr rfl)
  · have key : ∀ u v : V × Fin 2, s(u, v) ∈ WZ.edges WZ.a_bc (a, b, c) l →
        (u ∈ ({(a, l)} : Set (V × Fin 2)) ↔ v ∈ ({(a, l)} : Set (V × Fin 2))) := by
      intro u v hu
      simp only [WZ.edges, Finset.mem_singleton, Sym2.eq_iff] at hu
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;>
        simp [hab.symm, hac.symm]
    refine ⟨?_, ?_, ?_⟩
    · exact iff_of_false (not_reachable_of_sep key (by simp) (by simp [hab.symm])) (by decide)
    · exact iff_of_true (reachable_of_mem (by simp [WZ.edges]) hbc') (Or.inr rfl)
    · exact iff_of_false (not_reachable_of_sep key (by simp) (by simp [hac.symm])) (by decide)
  · have key : ∀ (K : Set (V × Fin 2)) (u v : V × Fin 2),
        s(u, v) ∈ WZ.edges WZ.a_b_c (a, b, c) l → (u ∈ K ↔ v ∈ K) := by
      intro K u v hu
      simp [WZ.edges] at hu
    refine ⟨?_, ?_, ?_⟩
    · exact iff_of_false (not_reachable_of_sep (K := {((a, l) : V × Fin 2)}) (key _)
        (by simp) (by simp [hab.symm])) (by decide)
    · exact iff_of_false (not_reachable_of_sep (K := {((b, l) : V × Fin 2)}) (key _)
        (by simp) (by simp [hbc.symm])) (by decide)
    · exact iff_of_false (not_reachable_of_sep (K := {((a, l) : V × Fin 2)}) (key _)
        (by simp) (by simp [hac.symm])) (by decide)

end WZStates

/-! ## Facts about Hollom's hypergraph and the substituted graph -/

lemma fin2_cases : ∀ l : Fin 2, l = 0 ∨ l = 1 := by decide

lemma tr_ne_path : ∀ (i : Fin 6) (j : Fin 7), hollomTr i ≠ hollomPath j := by decide

lemma cs_ne_succ : ∀ i : Fin 6, hollomPath i.castSucc ≠ hollomPath i.succ := by decide

lemma hollomTriple_eq : ∀ i : Fin 6,
    hollomTriple i = (hollomTr i, hollomPath i.castSucc, hollomPath i.succ) := by decide

lemma iota_inj : Function.Injective iota := by
  intro a b h
  have hv : (iota a).val = (iota b).val := by rw [h]
  exact Fin.ext hv

lemma iota_val (v : Fin 10) : (iota v).val = v.val := rfl

lemma emb_val (i : Fin 6) (k : Fin 1205) : (emb i k).val = embN i k.val := rfl

lemma embN_zero (i : Fin 6) : embN i 0 = (hollomTr i).val := by simp [embN]
lemma embN_one (i : Fin 6) : embN i 1 = (hollomPath i.castSucc).val := by simp [embN]
lemma embN_last (i : Fin 6) : embN i 1204 = (hollomPath i.succ).val := by simp [embN]

lemma embN_interior (i : Fin 6) (k : ℕ) (h2 : 2 ≤ k) (h3 : k ≤ 1203) :
    embN i k = 10 + 1202 * i.val + (k - 2) := by
  unfold embN; split_ifs <;> omega

lemma embN_bdry (i : Fin 6) (k : ℕ) (h : k = 0 ∨ k = 1 ∨ k = 1204) : embN i k < 10 := by
  have h3 : (hollomTr i).val < 10 := (hollomTr i).isLt
  have h4 : (hollomPath i.castSucc).val < 10 := (hollomPath i.castSucc).isLt
  have h5 : (hollomPath i.succ).val < 10 := (hollomPath i.succ).isLt
  rcases h with rfl | rfl | rfl <;> (unfold embN; split_ifs <;> omega)

lemma one_val : (1 : Fin 1205).val = 1 := rfl
lemma last_val : (1204 : Fin 1205).val = 1204 := rfl

lemma emb_zero (i : Fin 6) : emb i 0 = iota (hollomTr i) :=
  Fin.ext (by rw [emb_val, iota_val]; exact embN_zero i)

lemma emb_one (i : Fin 6) : emb i 1 = iota (hollomPath i.castSucc) :=
  Fin.ext (by rw [emb_val, iota_val, one_val]; exact embN_one i)

lemma emb_last (i : Fin 6) : emb i 1204 = iota (hollomPath i.succ) :=
  Fin.ext (by rw [emb_val, iota_val, last_val]; exact embN_last i)

lemma idx_cases (k : Fin 1205) :
    k.val = 0 ∨ k.val = 1 ∨ k.val = 1204 ∨ (2 ≤ k.val ∧ k.val ≤ 1203) := by
  have := k.isLt; omega

lemma emb_val_eq {i j : Fin 6} {k l : Fin 1205} (h : emb i k = emb j l) :
    embN i k.val = embN j l.val := by
  rw [← emb_val i k, ← emb_val j l, h]

/-- An interior index pins down the copy *and* the index. -/
lemma emb_eq_block {i j : Fin 6} {k l : Fin 1205}
    (hk : 2 ≤ k.val) (hk' : k.val ≤ 1203) (h : emb i k = emb j l) : i = j ∧ k = l := by
  have hv : embN i k.val = embN j l.val := emb_val_eq h
  have h2 : embN i k.val = 10 + 1202 * i.val + (k.val - 2) := embN_interior i k.val hk hk'
  have hi6 : i.val < 6 := i.isLt
  have hj6 : j.val < 6 := j.isLt
  have hl : 2 ≤ l.val ∧ l.val ≤ 1203 := by
    rcases idx_cases l with hl | hl | hl | hl
    · have := embN_bdry j l.val (by omega); omega
    · have := embN_bdry j l.val (by omega); omega
    · have := embN_bdry j l.val (by omega); omega
    · exact hl
  have h3 : embN j l.val = 10 + 1202 * j.val + (l.val - 2) := embN_interior j l.val hl.1 hl.2
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

/-- A gadget index whose image is a hypergraph vertex is an attachment index. -/
lemma bdry_idx (i : Fin 6) (k : Fin 1205) (h : (emb i k).val < 10) :
    k = 0 ∨ k = 1 ∨ k = 1204 := by
  have hv : (emb i k).val = embN i k.val := rfl
  rcases idx_cases k with hk | hk | hk | hk
  · exact Or.inl (Fin.ext (by rw [hk]; rfl))
  · exact Or.inr (Or.inl (Fin.ext (by rw [hk, one_val])))
  · exact Or.inr (Or.inr (Fin.ext (by rw [hk, last_val])))
  · exfalso
    have h2 : embN i k.val = 10 + 1202 * i.val + (k.val - 2) := embN_interior i k.val hk.1 hk.2
    omega

/-- A gadget index whose image is not a hypergraph vertex is interior. -/
lemma nonbdry_interior (i : Fin 6) (k : Fin 1205) (h : ¬ (emb i k).val < 10) :
    2 ≤ k.val ∧ k.val ≤ 1203 := by
  rcases idx_cases k with hk | hk | hk | hk
  · exact absurd (show (emb i k).val < 10 from embN_bdry i k.val (Or.inl hk)) h
  · exact absurd (show (emb i k).val < 10 from embN_bdry i k.val (Or.inr (Or.inl hk))) h
  · exact absurd (show (emb i k).val < 10 from embN_bdry i k.val (Or.inr (Or.inr hk))) h
  · exact hk

/-! ## The two families of parts, on the common vertex type `Fin 7222 × Fin 2` -/

/-- The index type of the parts: six copies on each of the two levels, plus the posts. -/
abbrev Idx : Type := Fin 6 × Fin 2 ⊕ Unit

/-- The lift of the ten hypergraph vertices to the bunkbed over the substituted graph. -/
def gmap (p : Fin 10 × Fin 2) : Fin 7222 × Fin 2 := (iota p.1, p.2)

lemma gmap_inj : Function.Injective gmap := by
  rintro ⟨a, l⟩ ⟨b, m⟩ h
  simp only [gmap, Prod.mk.injEq] at h
  rw [iota_inj h.1, h.2]

/-- The boundary: the ten lifted hypergraph vertices on each of the two levels. -/
def bdryB : Finset (Fin 7222 × Fin 2) := Finset.univ.image gmap

lemma mem_bdryB {w : Fin 7222 × Fin 2} : w ∈ bdryB ↔ w.1.val < 10 := by
  constructor
  · intro hw
    obtain ⟨p, -, hp⟩ := Finset.mem_image.1 hw
    rw [← hp]
    exact p.1.isLt
  · intro hw
    exact Finset.mem_image.2 ⟨(⟨w.1.val, hw⟩, w.2), Finset.mem_univ _, rfl⟩

/-- The posts over the substituted transversal set, as a single part. -/
def postPart : Finset (Sym2 (Fin 7222 × Fin 2)) := subT.image (fun x => s((x, 0), (x, 1)))

lemma postPart_bdry : ∀ e ∈ postPart, ∀ v : Fin 7222 × Fin 2, v ∈ e → v ∈ bdryB := by
  intro e he v hv
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 he
  have ht' : t ∈ hollomT.image iota := ht
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 ht'
  rw [Sym2.mem_iff] at hv
  rcases hv with rfl | rfl <;> exact mem_bdryB.2 u.isLt

/-- The parts of the bunkbed graph: copy `i` on level `l`, plus the posts. -/
def bbFam (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222))) : Idx → Finset (Sym2 (Fin 7222 × Fin 2)) :=
  Sum.elim (fun p => (if p.2 = 0 then S₀ p.1 else S₁ p.1).image (liftLvl p.2))
    (fun _ => postPart)

/-- The parts of the Wierman-Ziff graph, transported along `iota`. -/
def wzFam (ψ : Fin 6 × Fin 2 → WZ) : Idx → Finset (Sym2 (Fin 7222 × Fin 2)) :=
  Sum.elim (fun p => (ψ p).edges
      (iota (hollomTr p.1), iota (hollomPath p.1.castSucc), iota (hollomPath p.1.succ)) p.2)
    (fun _ => postPart)

lemma bbFam_inl (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222))) (i : Fin 6) (l : Fin 2) :
    bbFam S₀ S₁ (Sum.inl (i, l)) = (if l = 0 then S₀ i else S₁ i).image (liftLvl l) := rfl

lemma wzFam_inl (ψ : Fin 6 × Fin 2 → WZ) (i : Fin 6) (l : Fin 2) :
    wzFam ψ (Sum.inl (i, l)) = (ψ (i, l)).edges
      (iota (hollomTr i), iota (hollomPath i.castSucc), iota (hollomPath i.succ)) l := rfl

/-! ## Decomposing the two edge sets as `biUnion`s over `Idx` -/

lemma biUnion_sum {V' κ : Type*} [DecidableEq V'] [Fintype κ] [DecidableEq κ]
    (F : κ → Finset V') (P : Finset V') :
    Finset.univ.biUnion (Sum.elim F (fun _ : Unit => P)) = Finset.univ.biUnion F ∪ P := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union, Sum.exists,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro (⟨i, h⟩ | ⟨u, h⟩)
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr h
  · rintro (⟨i, h⟩ | h)
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr ⟨(), h⟩

lemma biUnion_fin2 {V' κ : Type*} [DecidableEq V'] [Fintype κ] [DecidableEq κ]
    (F : κ × Fin 2 → Finset V') :
    Finset.univ.biUnion F
      = Finset.univ.biUnion (fun i => F (i, 0)) ∪ Finset.univ.biUnion (fun i => F (i, 1)) := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union, Prod.exists]
  constructor
  · rintro ⟨i, l, h⟩
    rcases fin2_cases l with rfl | rfl
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr ⟨i, h⟩
  · rintro (⟨i, h⟩ | ⟨i, h⟩)
    · exact ⟨i, 0, h⟩
    · exact ⟨i, 1, h⟩

lemma bbFam_biUnion (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222))) :
    Finset.univ.biUnion (bbFam S₀ S₁)
      = (Finset.univ.biUnion S₀).image (liftLvl 0) ∪ (Finset.univ.biUnion S₁).image (liftLvl 1)
        ∪ postPart := by
  have h1 : Finset.univ.biUnion (bbFam S₀ S₁)
      = Finset.univ.biUnion (fun p : Fin 6 × Fin 2 =>
          (if p.2 = 0 then S₀ p.1 else S₁ p.1).image (liftLvl p.2)) ∪ postPart :=
    biUnion_sum _ _
  rw [h1]
  congr 1
  rw [biUnion_fin2 (fun p : Fin 6 × Fin 2 => (if p.2 = 0 then S₀ p.1 else S₁ p.1).image
    (liftLvl p.2)), Finset.biUnion_image, Finset.biUnion_image]
  simp

lemma edges_transport (s : WZ) (i : Fin 6) (l : Fin 2) :
    (s.edges (hollomTriple i) l).image (Sym2.map gmap)
      = s.edges (iota (hollomTr i), iota (hollomPath i.castSucc), iota (hollomPath i.succ)) l := by
  rw [hollomTriple_eq i]
  cases s <;> simp [WZ.edges, gmap]

lemma postPart_transport :
    (posts hollomT).image (Sym2.map gmap) = postPart := by
  simp only [postPart, posts, subT, Finset.image_image]
  refine Finset.image_congr ?_
  intro t _
  simp [gmap]

/-- The edge set of the Wierman-Ziff graph on `Fin 10 × Fin 2`. -/
def wzE (ψ : Fin 6 × Fin 2 → WZ) : Finset (Sym2 (Fin 10 × Fin 2)) :=
  (Finset.univ.biUnion (fun p : Fin 6 × Fin 2 => (ψ p).edges (hollomTriple p.1) p.2))
    ∪ posts hollomT

lemma wzFam_biUnion (ψ : Fin 6 × Fin 2 → WZ) :
    Finset.univ.biUnion (wzFam ψ) = (wzE ψ).image (Sym2.map gmap) := by
  have h1 : Finset.univ.biUnion (wzFam ψ)
      = Finset.univ.biUnion (fun p : Fin 6 × Fin 2 => (ψ p).edges
          (iota (hollomTr p.1), iota (hollomPath p.1.castSucc), iota (hollomPath p.1.succ)) p.2)
        ∪ postPart := biUnion_sum _ _
  have h2 : (wzE ψ).image (Sym2.map gmap)
      = Finset.univ.biUnion (fun p : Fin 6 × Fin 2 =>
          ((ψ p).edges (hollomTriple p.1) p.2).image (Sym2.map gmap))
        ∪ (posts hollomT).image (Sym2.map gmap) := by
    simp only [wzE, Finset.image_union, Finset.biUnion_image]
  rw [h1, h2, postPart_transport]
  congr 1
  refine Finset.biUnion_congr rfl (fun p _ => ?_)
  exact (edges_transport (ψ p) p.1 p.2).symm

/-! ## Support of the parts -/

lemma bb_part_support (i : Fin 6) (l : Fin 2) (E : Finset (Sym2 (Fin 7222)))
    (hE : E ⊆ (gadgetE 1204).image (Sym2.map (emb i))) :
    ∀ e ∈ E.image (liftLvl l), ∀ v : Fin 7222 × Fin 2, v ∈ e →
      ∃ k : Fin 1205, v = (emb i k, l) := by
  intro e he v hv
  obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 (hE he')
  have hmm : liftLvl l (Sym2.map (emb i) g)
      = Sym2.map (fun k : Fin 1205 => (emb i k, l)) g := by
    simp [liftLvl, Sym2.map_map, Function.comp]
  rw [hmm] at hv
  obtain ⟨k, -, hk⟩ := Sym2.mem_map.1 hv
  exact ⟨k, hk.symm⟩

/-! ## The parts agree on the boundary -/

/-- **The heart of the argument.**  On the boundary, a lifted copy of the gadget induces exactly
the reachability relation of the canonical edge set of the state `ψ (i, l)`. -/
lemma hsame_part (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222))) (ψ : Fin 6 × Fin 2 → WZ)
    (hsubL : ∀ (i : Fin 6) (l : Fin 2),
      (if l = 0 then S₀ i else S₁ i) ⊆ (gadgetE 1204).image (Sym2.map (emb i)))
    (hmatch : ∀ (i : Fin 6) (l : Fin 2),
        ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable (emb i 0) (emb i 1)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.ab_c))
      ∧ ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable (emb i 1) (emb i 1204)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.a_bc))
      ∧ ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable (emb i 0) (emb i 1204)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.ac_b)))
    (i : Fin 6) (l : Fin 2) (p : Fin 7222 × Fin 2) (hp : p ∈ bdryB)
    (q : Fin 7222 × Fin 2) (hq : q ∈ bdryB) :
    ((ofEdges (bbFam S₀ S₁ (Sum.inl (i, l)))).Reachable p q
      ↔ (ofEdges (wzFam ψ (Sum.inl (i, l)))).Reachable p q) := by
  rw [bbFam_inl, wzFam_inl]
  obtain ⟨m1, m2, m3⟩ := hmatch i l
  -- lift reachability inside the copy up to level `l`
  have hinj : Function.Injective (fun w : Fin 7222 => (w, l)) := fun a b h => congrArg Prod.fst h
  have himg : (if l = 0 then S₀ i else S₁ i).image (liftLvl l)
      = (if l = 0 then S₀ i else S₁ i).image (Sym2.map (fun w : Fin 7222 => (w, l))) := rfl
  have hlift : ∀ u v : Fin 1205,
      (ofEdges ((if l = 0 then S₀ i else S₁ i).image (liftLvl l))).Reachable
          (emb i u, l) (emb i v, l)
        ↔ (ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable (emb i u) (emb i v) := by
    intro u v
    rw [himg]
    exact reach_map_iff hinj _ (emb i u) (emb i v)
  have L1 := (hlift 0 1).trans m1
  have L2 := (hlift 1 1204).trans m2
  have L3 := (hlift 0 1204).trans m3
  rw [emb_zero, emb_one] at L1
  rw [emb_one, emb_last] at L2
  rw [emb_zero, emb_last] at L3
  -- the three attachment vertices are distinct
  have hab : iota (hollomTr i) ≠ iota (hollomPath i.castSucc) := fun h =>
    tr_ne_path i i.castSucc (iota_inj h)
  have hbc : iota (hollomPath i.castSucc) ≠ iota (hollomPath i.succ) := fun h =>
    cs_ne_succ i (iota_inj h)
  have hac : iota (hollomTr i) ≠ iota (hollomPath i.succ) := fun h =>
    tr_ne_path i i.succ (iota_inj h)
  obtain ⟨R1, R2, R3⟩ := reach_iff (iota (hollomTr i)) (iota (hollomPath i.castSucc))
    (iota (hollomPath i.succ)) hab hbc hac l (ψ (i, l))
  have I1 := L1.trans R1.symm
  have I2 := L2.trans R2.symm
  have I3 := L3.trans R3.symm
  -- both parts touch the boundary only in the three attachment vertices
  have hLsup : ∀ w : Fin 7222 × Fin 2, w ∈ bdryB →
      (∃ e ∈ (if l = 0 then S₀ i else S₁ i).image (liftLvl l), w ∈ e) →
      (w = (iota (hollomTr i), l) ∨ w = (iota (hollomPath i.castSucc), l)
        ∨ w = (iota (hollomPath i.succ), l)) := by
    intro w hw hex
    obtain ⟨e, he, hwe⟩ := hex
    obtain ⟨k, rfl⟩ := bb_part_support i l _ (hsubL i l) e he w hwe
    have hk10 : (emb i k).val < 10 := mem_bdryB.1 hw
    rcases bdry_idx i k hk10 with rfl | rfl | rfl
    · exact Or.inl (by rw [emb_zero])
    · exact Or.inr (Or.inl (by rw [emb_one]))
    · exact Or.inr (Or.inr (by rw [emb_last]))
  have hRsup : ∀ w : Fin 7222 × Fin 2,
      (∃ e ∈ WZ.edges (ψ (i, l))
          (iota (hollomTr i), iota (hollomPath i.castSucc), iota (hollomPath i.succ)) l, w ∈ e) →
      (w = (iota (hollomTr i), l) ∨ w = (iota (hollomPath i.castSucc), l)
        ∨ w = (iota (hollomPath i.succ), l)) := by
    intro w hex
    obtain ⟨e, he, hwe⟩ := hex
    exact edges_support _ _ _ l (ψ (i, l)) e he w hwe
  -- the nine cases
  have pair : ∀ u v : Fin 7222 × Fin 2,
      (u = (iota (hollomTr i), l) ∨ u = (iota (hollomPath i.castSucc), l)
        ∨ u = (iota (hollomPath i.succ), l)) →
      (v = (iota (hollomTr i), l) ∨ v = (iota (hollomPath i.castSucc), l)
        ∨ v = (iota (hollomPath i.succ), l)) →
      ((ofEdges ((if l = 0 then S₀ i else S₁ i).image (liftLvl l))).Reachable u v
        ↔ (ofEdges (WZ.edges (ψ (i, l))
            (iota (hollomTr i), iota (hollomPath i.castSucc), iota (hollomPath i.succ))
              l)).Reachable u v) := by
    intro u v hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact iff_of_true (Reachable.refl _) (Reachable.refl _)
    · exact I1
    · exact I3
    · exact flipIff I1
    · exact iff_of_true (Reachable.refl _) (Reachable.refl _)
    · exact I2
    · exact flipIff I3
    · exact flipIff I2
    · exact iff_of_true (Reachable.refl _) (Reachable.refl _)
  by_cases hpq : p = q
  · subst hpq
    exact iff_of_true (Reachable.refl _) (Reachable.refl _)
  · constructor
    · intro h
      exact (pair p q (hLsup p hp (exists_edge_of_reachable_ne h.symm (Ne.symm hpq)))
        (hLsup q hq (exists_edge_of_reachable_ne h hpq))).1 h
    · intro h
      exact (pair p q (hRsup p (exists_edge_of_reachable_ne h.symm (Ne.symm hpq)))
        (hRsup q (exists_edge_of_reachable_ne h hpq))).2 h

/-! ## Interior vertices are private to their part -/

lemma hsupp_bb (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222)))
    (hsubL : ∀ (i : Fin 6) (l : Fin 2),
      (if l = 0 then S₀ i else S₁ i) ⊆ (gadgetE 1204).image (Sym2.map (emb i))) :
    ∀ z : Idx, ∀ e ∈ bbFam S₀ S₁ z, ∀ v ∈ e, v ∉ bdryB →
      ∀ z', z' ≠ z → ∀ f ∈ bbFam S₀ S₁ z', v ∉ f := by
  intro z
  rcases z with ⟨i, l⟩ | u
  · intro e he v hv hvB z' hz' f hf hvf
    rw [bbFam_inl] at he
    obtain ⟨k, rfl⟩ := bb_part_support i l _ (hsubL i l) e he v hv
    have hint := nonbdry_interior i k (fun hlt => hvB (mem_bdryB.2 hlt))
    rcases z' with ⟨j, l'⟩ | u'
    · rw [bbFam_inl] at hf
      obtain ⟨k', hk'⟩ := bb_part_support j l' _ (hsubL j l') f hf _ hvf
      have h1 : emb i k = emb j k' := congrArg Prod.fst hk'
      have h2 : l = l' := congrArg Prod.snd hk'
      obtain ⟨hij, -⟩ := emb_eq_block hint.1 hint.2 h1
      exact hz' (by rw [← hij, ← h2])
    · exact hvB (postPart_bdry f hf _ hvf)
  · intro e he v hv hvB
    exact absurd (postPart_bdry e he v hv) hvB

lemma hsupp_wz (ψ : Fin 6 × Fin 2 → WZ) :
    ∀ z : Idx, ∀ e ∈ wzFam ψ z, ∀ v ∈ e, v ∉ bdryB →
      ∀ z', z' ≠ z → ∀ f ∈ wzFam ψ z', v ∉ f := by
  intro z
  rcases z with ⟨i, l⟩ | u
  · intro e he v hv hvB
    rw [wzFam_inl] at he
    rcases edges_support _ _ _ l (ψ (i, l)) e he v hv with rfl | rfl | rfl
    · exact absurd (mem_bdryB.2 (hollomTr i).isLt) hvB
    · exact absurd (mem_bdryB.2 (hollomPath i.castSucc).isLt) hvB
    · exact absurd (mem_bdryB.2 (hollomPath i.succ).isLt) hvB
  · intro e he v hv hvB
    exact absurd (postPart_bdry e he v hv) hvB

end Bunkbed.Sub3

/-! ## The requested statement -/

open Bunkbed Bunkbed.Hyper Bunkbed.Sub3 SimpleGraph Finset

/-- **Bunkbed reachability depends only on the per-copy boundary partitions.**

If, for every copy `i` and every level `l`, the open edges of that copy on that level connect its
three attachment vertices `emb i 0`, `emb i 1`, `emb i 1204` exactly as the Wierman-Ziff state
`ψ (i, l)` prescribes, then reachability between lifted hypergraph vertices in the bunkbed graph
over the substituted graph agrees with reachability in the Wierman-Ziff graph. -/
theorem bbreduce (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222)))
    (hsub : ∀ i, S₀ i ⊆ (gadgetE 1204).image (Sym2.map (Bunkbed.Sub.emb i)))
    (hsub' : ∀ i, S₁ i ⊆ (gadgetE 1204).image (Sym2.map (Bunkbed.Sub.emb i)))
    (ψ : Fin 6 × Fin 2 → WZ)
    (hmatch : ∀ (i : Fin 6) (l : Fin 2),
        ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable
              (Bunkbed.Sub.emb i 0) (Bunkbed.Sub.emb i 1)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.ab_c))
      ∧ ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable
              (Bunkbed.Sub.emb i 1) (Bunkbed.Sub.emb i 1204)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.a_bc))
      ∧ ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable
              (Bunkbed.Sub.emb i 0) (Bunkbed.Sub.emb i 1204)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.ac_b)))
    (x y : Fin 10) (l : Fin 2) :
    (bbGraph Bunkbed.Sub.subT (Finset.univ.biUnion S₀) (Finset.univ.biUnion S₁)).Reachable
        (Bunkbed.Sub.iota x, 0) (Bunkbed.Sub.iota y, l)
      ↔ (wzGraph hollomTriple hollomT ψ).Reachable (x, 0) (y, l) := by
  have hsubL : ∀ (i : Fin 6) (m : Fin 2),
      (if m = 0 then S₀ i else S₁ i) ⊆ (gadgetE 1204).image (Sym2.map (Bunkbed.Sub.emb i)) := by
    intro i m
    rcases fin2_cases m with rfl | rfl
    · simpa using hsub i
    · simpa using hsub' i
  have hx : ((Bunkbed.Sub.iota x, 0) : Fin 7222 × Fin 2) ∈ bdryB := mem_bdryB.2 x.isLt
  have hy : ((Bunkbed.Sub.iota y, l) : Fin 7222 × Fin 2) ∈ bdryB := mem_bdryB.2 y.isLt
  have e1 : bbGraph Bunkbed.Sub.subT (Finset.univ.biUnion S₀) (Finset.univ.biUnion S₁)
      = ofEdges (Finset.univ.biUnion (bbFam S₀ S₁)) := by
    rw [bbFam_biUnion]
    rfl
  have hsame : ∀ z : Idx, ∀ p ∈ bdryB, ∀ q ∈ bdryB,
      ((ofEdges (bbFam S₀ S₁ z)).Reachable p q ↔ (ofEdges (wzFam ψ z)).Reachable p q) := by
    intro z
    rcases z with ⟨i, m⟩ | u
    · exact fun p hp q hq => hsame_part S₀ S₁ ψ hsubL hmatch i m p hp q hq
    · exact fun _ _ _ _ => Iff.rfl
  have hcong := bc_boundary_congr (bbFam S₀ S₁) (wzFam ψ) bdryB hsame
    (hsupp_bb S₀ S₁ hsubL) (hsupp_wz ψ) (Bunkbed.Sub.iota x, 0) (Bunkbed.Sub.iota y, l) hx hy
  rw [e1, hcong, wzFam_biUnion]
  exact reach_map_iff gmap_inj (wzE ψ) (x, 0) (y, l)

/-! ## PART 4: the six copies are pairwise disjoint

Copied from `Solutions/Sub2_count.lean`, with `tri_val` taken from `BunkbedRelabel` and the
`embN`/`emb` facts from `Bunkbed.Sub3`. -/

namespace SimA

open Bunkbed Bunkbed.Hyper Bunkbed.Sub Bunkbed.Sub3 SimpleGraph Finset

/-- Two distinct hyperedges sharing a transversal vertex share no path end. -/
lemma bdry_val (i j : Fin 6) (hij : i.val ≠ j.val)
    (h : (hollomTr i).val = (hollomTr j).val) :
    (hollomPath i.castSucc).val ≠ (hollomPath j.castSucc).val ∧
    (hollomPath i.castSucc).val ≠ (hollomPath j.succ).val ∧
    (hollomPath i.succ).val ≠ (hollomPath j.castSucc).val ∧
    (hollomPath i.succ).val ≠ (hollomPath j.succ).val := by
  rcases BunkbedRelabel.tri_val i with hi | hi | hi | hi | hi | hi <;>
    rcases BunkbedRelabel.tri_val j with hj | hj | hj | hj | hj | hj <;> omega

lemma bdry : ∀ i j : Fin 6, i ≠ j →
    ¬ (hollomTr i = hollomTr j ∧ hollomPath i.castSucc = hollomPath j.castSucc) ∧
    ¬ (hollomTr i = hollomTr j ∧ hollomPath i.castSucc = hollomPath j.succ) ∧
    ¬ (hollomTr i = hollomTr j ∧ hollomPath i.succ = hollomPath j.castSucc) ∧
    ¬ (hollomTr i = hollomTr j ∧ hollomPath i.succ = hollomPath j.succ) := by
  intro i j hij
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro ⟨h1, h2⟩ <;>
    · have e1 : (hollomTr i).val = (hollomTr j).val := by rw [h1]
      obtain ⟨b1, b2, b3, b4⟩ := bdry_val i j hne e1
      have e2 := congrArg Fin.val h2
      omega

lemma mem_gadgetE_iff {n : ℕ} (e : Sym2 (Fin (n + 1))) :
    e ∈ gadgetE n ↔ ∃ p : Fin (n + 1) × Fin (n + 1),
      ((p.1 = 0 ∧ p.2 ≠ 0) ∨ (1 ≤ p.1.val ∧ p.2.val = p.1.val + 1)) ∧ s(p.1, p.2) = e := by
  simp only [gadgetE, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

lemma mem_copy_iff (i : Fin 6) (e : Sym2 (Fin 7222)) :
    e ∈ (gadgetE 1204).image (Sym2.map (emb i)) ↔
      ∃ p : Fin 1205 × Fin 1205,
        ((p.1 = 0 ∧ p.2 ≠ 0) ∨ (1 ≤ p.1.val ∧ p.2.val = p.1.val + 1)) ∧
        s(emb i p.1, emb i p.2) = e := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨p, hp, rfl⟩ := (mem_gadgetE_iff (n := 1204) a).1 ha
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨s(p.1, p.2), (mem_gadgetE_iff (n := 1204) _).2 ⟨p, hp, rfl⟩, rfl⟩

/-- Every gadget edge either has an interior endpoint, or is one of the two edges joining the
apex to a path end. -/
lemma cond_cases {p : Fin 1205 × Fin 1205}
    (hp : (p.1 = 0 ∧ p.2 ≠ 0) ∨ (1 ≤ p.1.val ∧ p.2.val = p.1.val + 1)) :
    (2 ≤ p.1.val ∧ p.1.val ≤ 1203) ∨ (2 ≤ p.2.val ∧ p.2.val ≤ 1203) ∨
      (p.1.val = 0 ∧ (p.2.val = 1 ∨ p.2.val = 1204)) := by
  have h1 := p.1.isLt
  have h2 := p.2.isLt
  rcases hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have ha' : p.1.val = 0 := by rw [ha]; rfl
    have hb' : p.2.val ≠ 0 := fun hh => hb (Fin.ext hh)
    omega
  · omega

lemma emb_bdry_cross {i j : Fin 6} (hij : i ≠ j) {p1 p2 q1 q2 : Fin 1205}
    (hp1 : p1.val = 0) (hp2 : p2.val = 1 ∨ p2.val = 1204)
    (hq1 : q1.val = 0) (hq2 : q2.val = 1 ∨ q2.val = 1204)
    (key : s(emb i p1, emb i p2) = s(emb j q1, emb j q2)) : False := by
  obtain ⟨b1, b2, b3, b4⟩ := bdry i j hij
  rcases Sym2.eq_iff.mp key with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have f1 := emb_val_eq e1
    have f2 := emb_val_eq e2
    rw [hp1, hq1, embN_zero, embN_zero] at f1
    rcases hp2 with h | h <;> rcases hq2 with h' | h' <;>
      rw [h, h'] at f2 <;> simp only [embN_one, embN_last] at f2
    · exact b1 ⟨Fin.ext f1, Fin.ext f2⟩
    · exact b2 ⟨Fin.ext f1, Fin.ext f2⟩
    · exact b3 ⟨Fin.ext f1, Fin.ext f2⟩
    · exact b4 ⟨Fin.ext f1, Fin.ext f2⟩
  · have f1 := emb_val_eq e1
    rw [hp1, embN_zero] at f1
    rcases hq2 with h' | h' <;> rw [h'] at f1 <;> simp only [embN_one, embN_last] at f1
    · exact tr_ne_path i j.castSucc (Fin.ext f1)
    · exact tr_ne_path i j.succ (Fin.ext f1)

/-- **The six gadget copies are pairwise disjoint.** -/
lemma copies_disjoint : ∀ i j : Fin 6, i ≠ j →
    Disjoint ((gadgetE 1204).image (Sym2.map (emb i)))
      ((gadgetE 1204).image (Sym2.map (emb j))) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro e hei hej
  obtain ⟨p, hp, hpe⟩ := (mem_copy_iff i e).1 hei
  obtain ⟨q, hq, hqe⟩ := (mem_copy_iff j e).1 hej
  have key : s(emb i p.1, emb i p.2) = s(emb j q.1, emb j q.2) := by rw [hpe, hqe]
  have noint : ∀ k : Fin 1205, 2 ≤ k.val → k.val ≤ 1203 →
      (emb i k = emb j q.1 ∨ emb i k = emb j q.2) → False := by
    intro k h1 h2 hor
    rcases hor with h | h
    · exact hij (emb_eq_block h1 h2 h).1
    · exact hij (emb_eq_block h1 h2 h).1
  have noint' : ∀ k : Fin 1205, 2 ≤ k.val → k.val ≤ 1203 →
      (emb j k = emb i p.1 ∨ emb j k = emb i p.2) → False := by
    intro k h1 h2 hor
    rcases hor with h | h
    · exact hij (emb_eq_block h1 h2 h).1.symm
    · exact hij (emb_eq_block h1 h2 h).1.symm
  have hmem1 : emb i p.1 = emb j q.1 ∨ emb i p.1 = emb j q.2 := by
    rcases Sym2.eq_iff.mp key with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hmem2 : emb i p.2 = emb j q.1 ∨ emb i p.2 = emb j q.2 := by
    rcases Sym2.eq_iff.mp key with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr h
    · exact Or.inl h
  have hmem1' : emb j q.1 = emb i p.1 ∨ emb j q.1 = emb i p.2 := by
    rcases Sym2.eq_iff.mp key with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hmem2' : emb j q.2 = emb i p.1 ∨ emb j q.2 = emb i p.2 := by
    rcases Sym2.eq_iff.mp key with ⟨-, h⟩ | ⟨h, -⟩
    · exact Or.inr h.symm
    · exact Or.inl h.symm
  rcases cond_cases hp with h | h | h
  · exact noint p.1 h.1 h.2 hmem1
  · exact noint p.2 h.1 h.2 hmem2
  · rcases cond_cases hq with h' | h' | h'
    · exact noint' q.1 h'.1 h'.2 hmem1'
    · exact noint' q.2 h'.1 h'.2 hmem2'
    · exact emb_bdry_cross hij h.1 h.2 h'.1 h'.2 key

end SimA
/-! ## PART 5: the five gadget partition probabilities as a `WZ`-distribution -/

noncomputable def Pgad : WZ → ℚ
  | .abc   => Pabc   (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
  | .a_b_c => Pa_b_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
  | .a_bc  => Pa_bc  (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
  | .ab_c  => Pab_c  (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
  | .ac_b  => Pac_b  (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)

namespace SimA

open Bunkbed Bunkbed.Hyper Bunkbed.Sub Bunkbed.Sub3 SimpleGraph Finset

/-- The gadget copy glued in at hyperedge `i`. -/
def cop (i : Fin 6) : Finset (Sym2 (Fin 7222)) :=
  (gadgetE 1204).image (Sym2.map (emb i))

lemma subEdges_eq : subEdges = Finset.univ.biUnion cop := rfl

/-- The `WZ` state that each copy of a tuple of configurations induces on its attachment
triple. -/
def stOf (S : Fin 6 → Finset (Sym2 (Fin 7222))) : Fin 6 → WZ :=
  fun i => GadgetStates.wzStateOf (S i) (emb i 0) (emb i 1) (emb i 1204)

/-- Assemble a lower-level and an upper-level `WZ` configuration into one. -/
def mk2 (φ₀ φ₁ : Fin 6 → WZ) : Fin 6 × Fin 2 → WZ :=
  fun p => if p.2 = 0 then φ₀ p.1 else φ₁ p.1

/-- The probability of each of the five states in a copy is the corresponding gadget
partition probability. -/
lemma copy_prob (i : Fin 6) (s : WZ) :
    probOf (cop i) (fun _ => (1 / 2 : ℚ))
        (fun S => GadgetStates.wzStateOf S (emb i 0) (emb i 1) (emb i 1204) = s)
      = Pgad s := by
  cases s
  · exact BunkbedRelabel.copy_Pabc i
  · exact BunkbedRelabel.copy_Pab_c i
  · exact BunkbedRelabel.copy_Pac_b i
  · exact BunkbedRelabel.copy_Pa_bc i
  · exact BunkbedRelabel.copy_Pa_b_c i

/-! ### Step 3: the three attachment-pair reachabilities are read off the state -/

/-- For a general configuration and a general triple, each of the three pair-reachabilities is
equivalent to the state being one of two values.  This uses that reachability is an equivalence
relation: e.g. in state `ab|c` one has `a ~ b` and `¬ a ~ c`, so `b ~ c` would give `a ~ c`. -/
lemma reach_pairs {V : Type*} [Fintype V] [DecidableEq V] (S : Finset (Sym2 V)) (a b c : V) :
    ((ofEdges S).Reachable a b ↔ (GadgetStates.wzStateOf S a b c = WZ.abc
        ∨ GadgetStates.wzStateOf S a b c = WZ.ab_c))
    ∧ ((ofEdges S).Reachable b c ↔ (GadgetStates.wzStateOf S a b c = WZ.abc
        ∨ GadgetStates.wzStateOf S a b c = WZ.a_bc))
    ∧ ((ofEdges S).Reachable a c ↔ (GadgetStates.wzStateOf S a b c = WZ.abc
        ∨ GadgetStates.wzStateOf S a b c = WZ.ac_b)) := by
  by_cases hab : (ofEdges S).Reachable a b
  · by_cases hbc : (ofEdges S).Reachable b c
    · have hac : (ofEdges S).Reachable a c := hab.trans hbc
      refine ⟨?_, ?_, ?_⟩ <;> simp +decide [GadgetStates.wzStateOf, hab, hbc, hac]
    · have hac : ¬ (ofEdges S).Reachable a c := fun h => hbc (hab.symm.trans h)
      refine ⟨?_, ?_, ?_⟩ <;> simp +decide [GadgetStates.wzStateOf, hab, hbc, hac]
  · by_cases hbc : (ofEdges S).Reachable b c
    · have hac : ¬ (ofEdges S).Reachable a c := fun h => hab (h.trans hbc.symm)
      refine ⟨?_, ?_, ?_⟩ <;> simp +decide [GadgetStates.wzStateOf, hab, hbc, hac]
    · by_cases hac : (ofEdges S).Reachable a c
      · refine ⟨?_, ?_, ?_⟩ <;> simp +decide [GadgetStates.wzStateOf, hab, hbc, hac]
      · refine ⟨?_, ?_, ?_⟩ <;> simp +decide [GadgetStates.wzStateOf, hab, hbc, hac]

/-- **Steps 1-3.**  The bunkbed reachability indicator of a tuple of configurations depends only
on the induced state tuples. -/
lemma reach_iff_wz (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222)))
    (h0 : ∀ i, S₀ i ⊆ cop i) (h1 : ∀ i, S₁ i ⊆ cop i) (x y : Fin 10) (l : Fin 2) :
    (bbGraph subT (Finset.univ.biUnion S₀) (Finset.univ.biUnion S₁)).Reachable
        (iota x, 0) (iota y, l)
      ↔ (wzGraph hollomTriple hollomT (mk2 (stOf S₀) (stOf S₁))).Reachable (x, 0) (y, l) := by
  refine bbreduce S₀ S₁ h0 h1 (mk2 (stOf S₀) (stOf S₁)) (fun i m => ?_) x y l
  have hst : mk2 (stOf S₀) (stOf S₁) (i, m)
      = GadgetStates.wzStateOf (if m = 0 then S₀ i else S₁ i)
          (emb i 0) (emb i 1) (emb i 1204) := by
    rcases fin2_cases m with rfl | rfl <;> simp [mk2, stOf]
  rw [hst]
  exact reach_pairs _ _ _ _

end SimA
namespace SimA

open Bunkbed Bunkbed.Hyper Bunkbed.Sub Bunkbed.Sub3 SimpleGraph Finset

/-! ### Step 4: the fibre of the state map is a product of per-copy fibres -/

/-- The fibre of `stOf` over `φ` is cut out coordinatewise, so it is again a `piFinset`. -/
lemma fibre_eq (φ : Fin 6 → WZ) :
    (Fintype.piFinset (fun i => (cop i).powerset)).filter (fun S => stOf S = φ)
      = Fintype.piFinset (fun i => (cop i).powerset.filter
          (fun T => GadgetStates.wzStateOf T (emb i 0) (emb i 1) (emb i 1204) = φ i)) := by
  ext S
  simp only [Finset.mem_filter, Fintype.mem_piFinset, funext_iff, stOf, forall_and]

/-! ### Step 5: on a fibre the weight sum factorises into the five gadget probabilities -/

lemma weight_sum_fibre (φ : Fin 6 → WZ) :
    (∑ S ∈ (Fintype.piFinset (fun i => (cop i).powerset)).filter (fun S => stOf S = φ),
        ∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S i))
      = ∏ i, Pgad (φ i) := by
  rw [fibre_eq, ← Finset.prod_univ_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Finset.sum_filter]
  exact copy_prob i (φ i)

/-- **Steps 4-5.**  A weighted sum over tuples of configurations whose coefficient depends only on
the induced state tuple collapses to a sum over state tuples, with the gadget's five partition
probabilities as weights. -/
lemma key (F : (Fin 6 → WZ) → ℚ) :
    (∑ S ∈ Fintype.piFinset (fun i => (cop i).powerset),
        F (stOf S) * ∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S i))
      = ∑ φ : Fin 6 → WZ, F φ * ∏ i, Pgad (φ i) := by
  have h1 : ∀ S : Fin 6 → Finset (Sym2 (Fin 7222)),
      (∑ φ : Fin 6 → WZ, if stOf S = φ then
          F φ * ∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S i) else 0)
        = F (stOf S) * ∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S i) := by
    intro S
    rw [Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl (fun S _ => (h1 S).symm), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun φ _ => ?_)
  calc (∑ S ∈ Fintype.piFinset (fun i => (cop i).powerset), if stOf S = φ then
          F φ * ∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S i) else 0)
      = ∑ S ∈ (Fintype.piFinset (fun i => (cop i).powerset)).filter (fun S => stOf S = φ),
          F φ * ∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S i) :=
        (Finset.sum_filter _ _).symm
    _ = F φ * ∑ S ∈ (Fintype.piFinset (fun i => (cop i).powerset)).filter
            (fun S => stOf S = φ), ∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S i) :=
        (Finset.mul_sum _ _ _).symm
    _ = F φ * ∏ i, Pgad (φ i) := by rw [weight_sum_fibre]

end SimA
namespace SimA

open Bunkbed Bunkbed.Hyper Bunkbed.Sub Bunkbed.Sub3 SimpleGraph Finset

lemma cop_disjoint : ∀ i j : Fin 6, i ≠ j → Disjoint (cop i) (cop j) := copies_disjoint

/-- Rewriting an indicator along an equivalence of its condition.  Used with `exact`, so that
the two `Decidable` instances are fixed by unification with the goal rather than resynthesised. -/
lemma ind_mul_eq {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) (u v : ℚ) :
    (if p then (1 : ℚ) else 0) * u * v = (if q then (1 : ℚ) else 0) * u * v := by
  by_cases hq : q
  · rw [if_pos (h.mpr hq), if_pos hq]
  · rw [if_neg (fun hp => hq (h.mp hp)), if_neg hq]

/-- The Wierman-Ziff reachability indicator of a pair of level configurations. -/
noncomputable def wzInd (x y : Fin 10) (l : Fin 2) (φ₀ φ₁ : Fin 6 → WZ) : ℚ :=
  if (wzGraph hollomTriple hollomT (mk2 φ₀ φ₁)).Reachable (x, 0) (y, l) then 1 else 0

lemma wzInd_def (x y : Fin 10) (l : Fin 2) (φ₀ φ₁ : Fin 6 → WZ) :
    wzInd x y l φ₀ φ₁ = if (wzGraph hollomTriple hollomT (mk2 φ₀ φ₁)).Reachable (x, 0) (y, l)
      then (1 : ℚ) else 0 := rfl

/-! ### Step 6: assembling the two levels -/

/-- The currying bijection between pairs of level configurations and configurations of the
bunkbed hypergraph. -/
private def pairEq2 : ((Fin 6 → WZ) × (Fin 6 → WZ)) ≃ (Fin 6 × Fin 2 → WZ) where
  toFun φ := mk2 φ.1 φ.2
  invFun ψ := (fun i => ψ (i, 0), fun i => ψ (i, 1))
  left_inv φ := Prod.ext (by funext i; simp [mk2]) (by funext i; simp +decide [mk2])
  right_inv ψ := by
    funext p
    obtain ⟨i, j⟩ := p
    fin_cases j <;> simp [mk2]

private lemma pairEq2_apply (φ₀ φ₁ : Fin 6 → WZ) : pairEq2 (φ₀, φ₁) = mk2 φ₀ φ₁ := rfl

/-- **Step 6.**  `wzProb` as a double sum over the lower- and the upper-level configuration. -/
lemma wz_pair (x y : Fin 10) (l : Fin 2) :
    wzProb hollomTriple hollomT Pgad (x, 0) (y, l)
      = ∑ φ₀ : Fin 6 → WZ, ∑ φ₁ : Fin 6 → WZ,
          wzInd x y l φ₀ φ₁ * ((∏ i, Pgad (φ₀ i)) * ∏ i, Pgad (φ₁ i)) := by
  rw [wzProb, ← Equiv.sum_comp pairEq2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun φ₀ _ => Finset.sum_congr rfl (fun φ₁ _ => ?_))
  rw [pairEq2_apply, wzInd_def]
  congr 1
  rw [Fintype.prod_prod_type]
  have hfac : ∀ i : Fin 6, (∏ j : Fin 2, Pgad (mk2 φ₀ φ₁ (i, j)))
      = Pgad (φ₀ i) * Pgad (φ₁ i) := by
    intro i
    rw [Fin.prod_univ_two]
    simp +decide [mk2]
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_mul_distrib]

/-! ### The double sum over configurations equals the double sum over state tuples -/

lemma main_sum (x y : Fin 10) (l : Fin 2) :
    (∑ S₀ ∈ Fintype.piFinset (fun i => (cop i).powerset),
      ∑ S₁ ∈ Fintype.piFinset (fun i => (cop i).powerset),
        (if (bbGraph subT (Finset.univ.biUnion (fun i => S₀ i))
              (Finset.univ.biUnion (fun i => S₁ i))).Reachable (iota x, 0) (iota y, l)
            then (1 : ℚ) else 0)
          * (∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S₀ i))
          * (∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S₁ i)))
      = ∑ φ₀ : Fin 6 → WZ, ∑ φ₁ : Fin 6 → WZ,
          wzInd x y l φ₀ φ₁ * ((∏ i, Pgad (φ₀ i)) * ∏ i, Pgad (φ₁ i)) := by
  calc (∑ S₀ ∈ Fintype.piFinset (fun i => (cop i).powerset),
          ∑ S₁ ∈ Fintype.piFinset (fun i => (cop i).powerset),
            (if (bbGraph subT (Finset.univ.biUnion (fun i => S₀ i))
                  (Finset.univ.biUnion (fun i => S₁ i))).Reachable (iota x, 0) (iota y, l)
                then (1 : ℚ) else 0)
              * (∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S₀ i))
              * (∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S₁ i)))
      = ∑ S₀ ∈ Fintype.piFinset (fun i => (cop i).powerset),
          ∑ S₁ ∈ Fintype.piFinset (fun i => (cop i).powerset),
            wzInd x y l (stOf S₀) (stOf S₁)
              * (∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S₀ i))
              * (∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S₁ i)) := by
        refine Finset.sum_congr rfl ?_
        intro S₀ h₀
        refine Finset.sum_congr rfl ?_
        intro S₁ h₁
        simp only [Fintype.mem_piFinset, Finset.mem_powerset] at h₀ h₁
        rw [wzInd_def]
        exact ind_mul_eq (reach_iff_wz S₀ S₁ h₀ h₁ x y l) _ _
    _ = ∑ S₀ ∈ Fintype.piFinset (fun i => (cop i).powerset), ∑ φ₁ : Fin 6 → WZ,
            wzInd x y l (stOf S₀) φ₁
              * (∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S₀ i))
              * ∏ i, Pgad (φ₁ i) :=
        Finset.sum_congr rfl (fun S₀ _ => key (fun φ₁ => wzInd x y l (stOf S₀) φ₁
          * ∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S₀ i)))
    _ = ∑ φ₁ : Fin 6 → WZ, ∑ S₀ ∈ Fintype.piFinset (fun i => (cop i).powerset),
            wzInd x y l (stOf S₀) φ₁
              * (∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S₀ i))
              * ∏ i, Pgad (φ₁ i) := Finset.sum_comm
    _ = ∑ φ₁ : Fin 6 → WZ, ∑ S₀ ∈ Fintype.piFinset (fun i => (cop i).powerset),
            (wzInd x y l (stOf S₀) φ₁ * ∏ i, Pgad (φ₁ i))
              * ∏ i, weight (cop i) (fun _ => (1 / 2 : ℚ)) (S₀ i) :=
        Finset.sum_congr rfl (fun φ₁ _ => Finset.sum_congr rfl (fun S₀ _ => by ring))
    _ = ∑ φ₁ : Fin 6 → WZ, ∑ φ₀ : Fin 6 → WZ,
            (wzInd x y l φ₀ φ₁ * ∏ i, Pgad (φ₁ i)) * ∏ i, Pgad (φ₀ i) :=
        Finset.sum_congr rfl (fun φ₁ _ =>
          key (fun φ₀ => wzInd x y l φ₀ φ₁ * ∏ i, Pgad (φ₁ i)))
    _ = ∑ φ₀ : Fin 6 → WZ, ∑ φ₁ : Fin 6 → WZ,
            (wzInd x y l φ₀ φ₁ * ∏ i, Pgad (φ₁ i)) * ∏ i, Pgad (φ₀ i) := Finset.sum_comm
    _ = ∑ φ₀ : Fin 6 → WZ, ∑ φ₁ : Fin 6 → WZ,
            wzInd x y l φ₀ φ₁ * ((∏ i, Pgad (φ₀ i)) * ∏ i, Pgad (φ₁ i)) :=
        Finset.sum_congr rfl (fun φ₀ _ => Finset.sum_congr rfl (fun φ₁ _ => by ring))

end SimA

/-! ## The simulation identity -/

/-- **Bunkbed percolation at `1/2` on the substituted graph is the Wierman-Ziff model on
Hollom's hypergraph.** -/
theorem solution (x y : Fin 10) (l : Fin 2) :
    bbProb Bunkbed.Sub.subEdges (fun _ => (1 / 2 : ℚ)) Bunkbed.Sub.subT
        (Bunkbed.Sub.iota x, 0) (Bunkbed.Sub.iota y, l)
      = wzProb hollomTriple hollomT Pgad (x, 0) (y, l) := by
  have h1 : bbProb Bunkbed.Sub.subEdges (fun _ => (1 / 2 : ℚ)) Bunkbed.Sub.subT
        (Bunkbed.Sub.iota x, 0) (Bunkbed.Sub.iota y, l)
      = ∑ S₀ ∈ Fintype.piFinset (fun i => (SimA.cop i).powerset),
          ∑ S₁ ∈ Fintype.piFinset (fun i => (SimA.cop i).powerset),
            (if (bbGraph Bunkbed.Sub.subT (Finset.univ.biUnion (fun i => S₀ i))
                  (Finset.univ.biUnion (fun i => S₁ i))).Reachable
                (Bunkbed.Sub.iota x, 0) (Bunkbed.Sub.iota y, l) then (1 : ℚ) else 0)
              * (∏ i, weight (SimA.cop i) (fun _ => (1 / 2 : ℚ)) (S₀ i))
              * (∏ i, weight (SimA.cop i) (fun _ => (1 / 2 : ℚ)) (S₁ i)) := by
    rw [SimA.subEdges_eq]
    exact bbfactor SimA.cop SimA.cop_disjoint _ _ _ _
  rw [h1, SimA.main_sum x y l, SimA.wz_pair x y l]

#print axioms SimA.copies_disjoint
#print axioms SimA.reach_iff_wz
#print axioms SimA.key
#print axioms SimA.main_sum
#print axioms SimA.wz_pair
#print axioms solution
