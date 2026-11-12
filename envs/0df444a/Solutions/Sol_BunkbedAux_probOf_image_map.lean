-- Prove2me | solution 1 for BunkbedAux.probOf_image_map
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T04:59:01.546415+00:00
-- url     : https://prove2.me/submissions/1e1da576-dd84-4cfc-b837-0b35e9e206e8

import Definitions.Def_BunkbedSubstituted

/-!
# Percolation is invariant under an injective relabelling of the vertices

In the substituted graph of Theorem 1.2 each gadget copy is the *image*
`(gadgetE 1204).image (Sym2.map (emb i))` of the gadget, not the gadget itself.  To identify the
partition probabilities of a copy with those of `G₁₂₀₄` one needs to know that percolation
commutes with an injective relabelling of the vertices.  This file supplies that.

The two reusable pieces are

* `BunkbedRelabel.reach_image_map` — **reachability transports along an injective relabelling**:
  for injective `f`, `u` and `v` are connected in `ofEdges S` iff `f u` and `f v` are connected
  in `ofEdges (S.image (Sym2.map f))`;
* `solution` — **relabelling invariance of `probOf`** for a *constant* weight: if the event `ev`
  on subconfigurations of `E` corresponds to the event `ev'` on their images, then
  `probOf E (fun _ => c) ev = probOf (E.image (Sym2.map f)) (fun _ => c) ev'`.

They are then combined into `BunkbedRelabel.copy_partProb`: the five partition probabilities of
the triple `(emb i 0, emb i 1, emb i 1204)` inside the copy glued in at hyperedge `i` are exactly
the five partition probabilities of `G₁₂₀₄` at its attachment triple `(0, 1, Fin.last 1204)`.

`GadgetStates.wzStateOf`, `GadgetStates.PartEvent`, `GadgetStates.partProb` and
`GadgetStates.prob_state_eq` are copied verbatim from `Solutions/Sub_states.lean`, which is not
importable as a library; nothing else is copied from it.  The injectivity of `emb i` is copied
from `Solutions/Sub2_count.lean` (same reason) into the namespace `BunkbedRelabel`.
-/

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
theorem solution {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
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

#print axioms solution
#print axioms BunkbedRelabel.reach_image_map
#print axioms BunkbedRelabel.probOf_image_map
#print axioms BunkbedRelabel.copy_partProb
#print axioms BunkbedRelabel.copy_Pabc
#print axioms BunkbedRelabel.copy_Pa_b_c
#print axioms BunkbedRelabel.emb_inj
#print axioms BunkbedRelabel.wzStateOf_image
