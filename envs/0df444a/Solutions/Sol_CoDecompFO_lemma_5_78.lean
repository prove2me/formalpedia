-- Prove2me | solution 1 for CoDecompFO.lemma_5_78
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T22:07:30.409331+00:00
-- url     : https://prove2.me/submissions/84077648-ab23-4133-a5ff-96a525bfd812

import Mathlib
import Definitions.Def_CoDecompFO_HTh
import Definitions.Def_CoDecompFO_Lim

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- The strategy form of the game semantics, through any map `π`. -/
theorem strat_aux {σ : Sig} (G P : Type) [σ.lang.Structure G] (π : G → P) (k : ℕ)
    (ψ : σ.lang.BoundedFormula Empty k) :
    ∀ (m : ℕ) (l : List G),
      AltSat (G := G) ψ m l ↔
        ∃ S : Strat G m, Strat.Total m S ∧ AllHyp ψ m (push π m (ind σ k m S l)) := by
  intro m
  induction m with
  | zero =>
    intro l
    constructor
    · intro h
      refine ⟨(), trivial, ?_⟩
      intro N hN
      have hN' : N = atomsOf σ k l := hN
      rw [hN']
      exact h
    · rintro ⟨S, -, hA⟩
      exact hA (atomsOf σ k l) (Set.mem_singleton _)
  | succ m ih =>
    intro l
    constructor
    · intro h
      have h' : ∀ x : G, ∃ y : G, AltSat ψ m (l ++ [x, y]) := h
      choose y hy using h'
      have h2 : ∀ x, ∃ S : Strat G m, Strat.Total m S ∧
          AllHyp ψ m (push π m (ind σ k m S (l ++ [x, y x]))) := fun x => (ih _).1 (hy x)
      choose Sx hT hA using h2
      let S0 : G → Set (G × Strat G m) := fun x => {(y x, Sx x)}
      refine ⟨S0, ?_, ?_⟩
      · show ∀ x : G, (S0 x).Nonempty ∧ ∀ c ∈ S0 x, Strat.Total m c.2
        intro x
        refine ⟨⟨_, Set.mem_singleton _⟩, ?_⟩
        intro c hc
        have hc' : c = (y x, Sx x) := hc
        subst hc'
        exact hT x
      · show ∀ x', ∀ p ∈ push π (m + 1) (ind σ k (m + 1) S0 l) x', ∀ c ∈ p, AllHyp ψ m c.2
        intro x' p hp c hc
        obtain ⟨x, p0, -, hp0, rfl⟩ := hp
        have hp0' : p0 = (fun c : G × Strat G m => (c.1, ind σ k m c.2 (l ++ [x, c.1]))) '' S0 x :=
          hp0
        subst hp0'
        obtain ⟨c0, ⟨s, hs, rfl⟩, rfl⟩ := hc
        have hs' : s = (y x, Sx x) := hs
        subst hs'
        exact hA x
    · rintro ⟨S, hT, hA⟩
      have hT' : ∀ x : G, (S x).Nonempty ∧ ∀ c ∈ S x, Strat.Total m c.2 := hT
      have hA' : ∀ x', ∀ p ∈ push π (m + 1) (ind σ k (m + 1) S l) x', ∀ c ∈ p, AllHyp ψ m c.2 := hA
      show ∀ x : G, ∃ y : G, AltSat ψ m (l ++ [x, y])
      intro x
      obtain ⟨⟨c, hc⟩, hT2⟩ := hT' x
      refine ⟨c.1, (ih _).2 ⟨c.2, hT2 c hc, ?_⟩⟩
      exact hA' (π x) _ ⟨x, _, rfl, Set.mem_singleton _, rfl⟩
        (π c.1, push π m (ind σ k m c.2 (l ++ [x, c.1])))
        ⟨(c.1, ind σ k m c.2 (l ++ [x, c.1])), ⟨c, hc, rfl⟩, rfl⟩

/-- Heads are invariant under a map that preserves and reflects the relations. -/
theorem atomsOf_map {σ : Sig} {G G' : Type} [σ.lang.Structure G] [σ.lang.Structure G'] (f : G → G')
    (hf : ∀ (i : Fin σ.r) (args : Fin (σ.ar i) → G), σ.holds i (f ∘ args) ↔ σ.holds i args)
    (k : ℕ) (l : List G) : atomsOf σ k (l.map f) = atomsOf σ k l := by
  ext A
  simp only [atomsOf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨args, h1, h2⟩
    have h3 : ∀ j, ∃ a, l[(A.2 j).val]? = some a ∧ f a = args j := by
      intro j
      have h4 := h1 j
      rw [List.getElem?_map] at h4
      exact Option.map_eq_some_iff.1 h4
    choose a ha1 ha2 using h3
    refine ⟨a, ha1, ?_⟩
    have h5 : args = f ∘ a := by
      funext j
      exact (ha2 j).symm
    rw [h5] at h2
    exact (hf _ _).1 h2
  · rintro ⟨args, h1, h2⟩
    refine ⟨f ∘ args, ?_, (hf _ _).2 h2⟩
    intro j
    rw [List.getElem?_map, h1 j]
    rfl

/-- The alternating sentence is invariant under a surjection that preserves and reflects the
relations. -/
theorem altSat_map {σ : Sig} {G G' : Type} [σ.lang.Structure G] [σ.lang.Structure G'] (f : G → G')
    (hf : ∀ (i : Fin σ.r) (args : Fin (σ.ar i) → G), σ.holds i (f ∘ args) ↔ σ.holds i args)
    (hs : Function.Surjective f) (k : ℕ) (ψ : σ.lang.BoundedFormula Empty k) :
    ∀ (m : ℕ) (l : List G), AltSat (G := G') ψ m (l.map f) ↔ AltSat (G := G) ψ m l := by
  intro m
  induction m with
  | zero =>
    intro l
    show Holds ψ (atomsOf σ k (l.map f)) ↔ Holds ψ (atomsOf σ k l)
    rw [atomsOf_map f hf]
  | succ m ih =>
    intro l
    show (∀ x : G', ∃ y : G', AltSat ψ m (l.map f ++ [x, y])) ↔
      (∀ x : G, ∃ y : G, AltSat ψ m (l ++ [x, y]))
    constructor
    · intro h x
      obtain ⟨y', hy'⟩ := h (f x)
      obtain ⟨y, rfl⟩ := hs y'
      refine ⟨y, (ih (l ++ [x, y])).1 ?_⟩
      have h6 : (l ++ [x, y]).map f = l.map f ++ [f x, f y] := by simp
      rw [h6]
      exact hy'
    · intro h x'
      obtain ⟨x, rfl⟩ := hs x'
      obtain ⟨y, hy⟩ := h x
      refine ⟨f y, ?_⟩
      have h7 := (ih (l ++ [x, y])).2 hy
      have h6 : (l ++ [x, y]).map f = l.map f ++ [f x, f y] := by simp
      rw [h6] at h7
      exact h7

theorem mem_subtree_root {σ : Sig} (T : CoDecomp σ) (r s : Fin T.b) : s ∈ T.subtree r r := by
  simp [CoDecomp.subtree]

/-- The restriction of a matching family to the subtree at the root, which is the whole tree. -/
def toPartial {σ : Sig} (T : CoDecomp σ) (r : Fin T.b) (x : T.Lim) : T.PartialLim r r :=
  ⟨fun s => x.val s.1, fun e _ _ => x.compat e⟩

theorem toPartial_surj {σ : Sig} (T : CoDecomp σ) (r : Fin T.b) :
    Function.Surjective (toPartial T r) := by
  intro y
  exact ⟨⟨fun t => y.val ⟨t, mem_subtree_root T r t⟩,
    fun e => y.compat e (mem_subtree_root T r _) (mem_subtree_root T r _)⟩, rfl⟩

theorem toPartial_holds {σ : Sig} (T : CoDecomp σ) (r : Fin T.b) (i : Fin σ.r)
    (args : Fin (σ.ar i) → T.Lim) :
    σ.holds i (toPartial T r ∘ args) ↔ σ.holds i args := by
  show (∀ s : T.subtree r r, σ.holds i (fun j => ((toPartial T r ∘ args) j).val s)) ↔
    (∀ t, σ.holds i (fun j => (args j).val t))
  constructor
  · intro h t
    exact h ⟨t, mem_subtree_root T r t⟩
  · intro h s
    exact h s.1

end CoDecompFO

theorem solution {σ : CoDecompFO.Sig} (T : CoDecompFO.CoDecomp σ) (r : Fin T.b) (ℓ : ℕ)
    (ψ : σ.lang.BoundedFormula Empty (2 * ℓ)) (hψ : CoDecompFO.IsMatrix ψ) :
    CoDecompFO.AltSat (G := T.Lim) ψ ℓ [] ↔
      ∃ S : CoDecompFO.Strat (T.PartialLim r r) ℓ, CoDecompFO.Strat.Total ℓ S ∧
        CoDecompFO.AllHyp ψ ℓ (CoDecompFO.push (T.partialProj r r) ℓ
          (CoDecompFO.ind σ (2 * ℓ) ℓ S [])) := by
  rw [← CoDecompFO.strat_aux (T.PartialLim r r) _ (T.partialProj r r) (2 * ℓ) ψ ℓ []]
  exact (CoDecompFO.altSat_map (CoDecompFO.toPartial T r) (CoDecompFO.toPartial_holds T r)
    (CoDecompFO.toPartial_surj T r) (2 * ℓ) ψ ℓ []).symm
