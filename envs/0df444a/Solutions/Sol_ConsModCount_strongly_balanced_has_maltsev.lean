-- Prove2me | solution 1 for ConsModCount.strongly_balanced_has_maltsev
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-09T16:14:21.026605+00:00
-- url     : https://prove2.me/submissions/7be9c120-dc6b-4972-bc7e-d969ff3fa2ca

import Definitions.Def_ConsModCount_Balance
import Definitions.Def_ConsModCount_Polymorphism

set_option autoImplicit false

namespace ConsModCount
namespace SBM

/-- **Polymorphism images are pp-definable.** For any family of columns `col j ∈ D^n`, the set of
tuples `(f (col j))_j` with `f` an `n`-ary polymorphism of `H` is pp-definable over `H`. The pp
formula quantifies the graph of `f` (one variable per point of `D^n`), asserts that `f` is a
polymorphism, and exposes its values at the columns. -/
theorem pp_image {D : Type} [Fintype D] [DecidableEq D] (H : Template D) {k n : ℕ}
    (col : Fin k → Fin n → D) :
    PPDefinable H {a : Fin k → D | ∃ f : (Fin n → D) → D, IsPolymorphism H f ∧
      ∀ j, a j = f (col j)} := by
  classical
  set N := Fintype.card (Fin n → D) with hN
  let e : (Fin n → D) ≃ Fin N := Fintype.equivFin _
  let atomsOf : Fin H.s → List (Σ i : Fin H.s, Fin (H.arity i) → Fin (k + N)) := fun i =>
    ((Finset.univ.filter (fun M : Fin n → Fin (H.arity i) → D => ∀ l, M l ∈ H.rel i)).toList).map
      (fun M => ⟨i, fun j => Fin.natAdd k (e (fun l => M l j))⟩)
  let φ : PPFormula H k :=
    { m := N
      atoms := (List.finRange H.s).flatMap atomsOf
      eqs := (List.finRange k).map (fun j => (Fin.castAdd N j, Fin.natAdd k (e (col j)))) }
  refine ⟨φ, fun a => ?_⟩
  rw [Set.mem_setOf_eq]
  symm
  constructor
  · rintro ⟨b, hat, heq⟩
    refine ⟨fun x => b (e x), ?_, ?_⟩
    · intro i M hM
      have hc : (⟨i, fun j => Fin.natAdd k (e (fun l => M l j))⟩ :
          Σ i : Fin H.s, Fin (H.arity i) → Fin (k + N)) ∈ φ.atoms := by
        simp only [φ, List.mem_flatMap, List.mem_finRange, true_and]
        exact ⟨i, List.mem_map.2 ⟨M, by simpa using hM, rfl⟩⟩
      have := hat _ hc
      simpa [Function.comp_def, Fin.append_right] using this
    · intro j
      have hc : (Fin.castAdd N j, Fin.natAdd k (e (col j))) ∈ φ.eqs := by
        simp [φ]
      have := heq _ hc
      have h1 : Fin.append a b (Fin.castAdd N j) = a j := Fin.append_left a b j
      rw [h1] at this
      simpa [Fin.append_right] using this
  · rintro ⟨f, hf, ha⟩
    refine ⟨fun q => f (e.symm q), ?_, ?_⟩
    · intro c hc
      simp only [φ, List.mem_flatMap, List.mem_finRange, true_and, atomsOf, List.mem_map,
        Finset.mem_toList, Finset.mem_filter, Finset.mem_univ] at hc
      obtain ⟨i, M, hM, rfl⟩ := hc
      have := hf i M hM
      simpa [Function.comp_def, Fin.append_right] using this
    · intro q hq
      simp only [φ, List.mem_map, List.mem_finRange, true_and] at hq
      obtain ⟨j, rfl⟩ := hq
      have h1 : Fin.append a (fun q => f (e.symm q)) (Fin.castAdd N j) = a j :=
        Fin.append_left a _ j
      simp only
      rw [h1, Fin.append_right, Equiv.symm_apply_apply, ha j]

/-- Block-rank-one matrices have rectangular support in the three-point sense. -/
theorem rect_of_blockRankOne {α β : Type} (M : α → β → ℕ) (hM : BlockRankOne M)
    (p p' : α) (q q' : β) (h1 : 0 < M p q) (h2 : 0 < M p q') (h3 : 0 < M p' q) :
    0 < M p' q' := by
  obtain ⟨s, A, B, -, -, hA, hB, hsupp, -⟩ := hM
  obtain ⟨i, hpi, hqi⟩ := (hsupp p q).1 h1
  obtain ⟨i', hpi', hqi'⟩ := (hsupp p q').1 h2
  obtain ⟨i'', hpi'', hqi''⟩ := (hsupp p' q).1 h3
  have e1 : i = i' := by
    by_contra hne
    exact Set.disjoint_left.1 (hA hne) hpi hpi'
  have e2 : i = i'' := by
    by_contra hne
    exact Set.disjoint_left.1 (hB hne) hqi hqi''
  subst e1; subst e2
  exact (hsupp p' q').2 ⟨i, hpi'', hqi'⟩

/-- The grouping `Fin (m + m) ≃ Fin m ⊕ Fin m ⊕ Fin 0`. -/
def grp (m : ℕ) : Fin (m + m) ≃ Fin m ⊕ Fin m ⊕ Fin 0 :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sumEmpty (Fin m) (Fin 0)).symm)

theorem groupTuple_castAdd {D : Type} (m : ℕ) (a b : Fin m → D) (c : Fin 0 → D) (i : Fin m) :
    groupTuple (grp m) a b c (Fin.castAdd m i) = a i := by
  simp [groupTuple, grp]

theorem groupTuple_natAdd {D : Type} (m : ℕ) (a b : Fin m → D) (c : Fin 0 → D) (i : Fin m) :
    groupTuple (grp m) a b c (Fin.natAdd m i) = b i := by
  unfold groupTuple grp
  rw [Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem fin3_eta {D : Type} (t : Fin 3 → D) : ![t 0, t 1, t 2] = t := by
  funext i; fin_cases i <;> rfl

theorem sbm_main {D : Type} [Fintype D] [DecidableEq D] [Nonempty D] (H : Template D)
    (hSB : StronglyBalanced H) : HasMaltsev H := by
  classical
  set m := Fintype.card (D × D) with hm
  have hm1 : 1 ≤ m := Fintype.card_pos
  let pr : Fin m ≃ D × D := (Fintype.equivFin (D × D)).symm
  let xv : Fin m → D := fun i => (pr i).1
  let yv : Fin m → D := fun i => (pr i).2
  let colX : Fin m → Fin 3 → D := fun i => ![xv i, yv i, yv i]
  let colY : Fin m → Fin 3 → D := fun i => ![yv i, yv i, xv i]
  let col : Fin (m + m) → Fin 3 → D := Fin.append colX colY
  let R : Set (Fin (m + m) → D) := {a | ∃ f : (Fin 3 → D) → D, IsPolymorphism H f ∧
      ∀ j, a j = f (col j)}
  have hR : PPDefinable H R := pp_image H col
  have cX : ∀ i, col (Fin.castAdd m i) = colX i := fun i => Fin.append_left colX colY i
  have cY : ∀ i, col (Fin.natAdd m i) = colY i := fun i => Fin.append_right colX colY i
  have hB := hSB (m + m) R hR m m 0 (grp m) hm1 hm1
  -- membership of a grouped tuple
  have hmem : ∀ (a b : Fin m → D) (c : Fin 0 → D), groupTuple (grp m) a b c ∈ R ↔
      ∃ f : (Fin 3 → D) → D, IsPolymorphism H f ∧ (∀ i, a i = f (colX i)) ∧
        ∀ i, b i = f (colY i) := by
    intro a b c
    constructor
    · rintro ⟨f, hf, hj⟩
      refine ⟨f, hf, fun i => ?_, fun i => ?_⟩
      · have := hj (Fin.castAdd m i)
        rw [groupTuple_castAdd, cX] at this
        exact this
      · have := hj (Fin.natAdd m i)
        rw [groupTuple_natAdd, cY] at this
        exact this
    · rintro ⟨f, hf, ha, hb⟩
      refine ⟨f, hf, fun j => ?_⟩
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [groupTuple_castAdd, ha i, cX]
      · rw [groupTuple_natAdd, hb i, cY]
  have hpos : ∀ a b : Fin m → D, 0 < witnessMatrix R (grp m) a b ↔
      ∃ f : (Fin 3 → D) → D, IsPolymorphism H f ∧ (∀ i, a i = f (colX i)) ∧
        ∀ i, b i = f (colY i) := by
    intro a b
    rw [witnessMatrix, Nat.card_pos_iff]
    constructor
    · rintro ⟨⟨c, hc⟩, -⟩
      exact (hmem a b c).1 hc
    · intro h
      exact ⟨⟨Fin.elim0, (hmem a b Fin.elim0).2 h⟩, inferInstance⟩
  have proj : ∀ k : Fin 3, IsPolymorphism H (fun t : Fin 3 → D => t k) := by
    intro k i t ht
    exact ht k
  have h1 : 0 < witnessMatrix R (grp m) yv yv :=
    (hpos _ _).2 ⟨_, proj 1, fun i => by simp [colX], fun i => by simp [colY]⟩
  have h2 : 0 < witnessMatrix R (grp m) yv xv :=
    (hpos _ _).2 ⟨_, proj 2, fun i => by simp [colX], fun i => by simp [colY]⟩
  have h3 : 0 < witnessMatrix R (grp m) xv yv :=
    (hpos _ _).2 ⟨_, proj 0, fun i => by simp [colX], fun i => by simp [colY]⟩
  have h4 := rect_of_blockRankOne _ hB yv xv yv xv h1 h2 h3
  obtain ⟨f, hf, hX, hY⟩ := (hpos _ _).1 h4
  refine ⟨fun x y z => f ![x, y, z], ?_, ?_⟩
  · intro x y
    have hxy : pr (pr.symm (x, y)) = (x, y) := pr.apply_symm_apply _
    have ex : xv (pr.symm (x, y)) = x := by simp [xv, hxy]
    have ey : yv (pr.symm (x, y)) = y := by simp [yv, hxy]
    have a1 := hX (pr.symm (x, y))
    have a2 := hY (pr.symm (x, y))
    simp only [colX, colY, ex, ey] at a1 a2
    exact ⟨a1.symm, a2.symm⟩
  · intro i t ht
    have := hf i t ht
    have e : ∀ j, ![t 0 j, t 1 j, t 2 j] = fun l => t l j := fun j => fin3_eta (fun l => t l j)
    show (fun j => f ![t 0 j, t 1 j, t 2 j]) ∈ H.rel i
    simp only [e]
    exact this

end SBM
end ConsModCount

open ConsModCount in
theorem solution {D : Type} [Fintype D] [DecidableEq D] [Nonempty D] (H : Template D)
    (hSB : StronglyBalanced H) :
    HasMaltsev H :=
  ConsModCount.SBM.sbm_main H hSB
