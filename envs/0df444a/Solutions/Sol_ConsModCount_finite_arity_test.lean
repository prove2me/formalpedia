-- Prove2me | solution 1 for ConsModCount.finite_arity_test
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-09T16:05:12.828922+00:00
-- url     : https://prove2.me/submissions/963991b1-1de3-4e35-887c-4073c0cb0002

import Definitions.Def_ConsModCount_Balance
import Definitions.Def_ConsModCount_Polymorphism

set_option autoImplicit false

namespace ConsModCount
namespace FAT

/-- Coordinatewise application commutes with `Fin.append`. -/
theorem append_map {D : Type} {k m n : ℕ} (f : (Fin n → D) → D) (a : Fin n → Fin k → D)
    (b : Fin n → Fin m → D) :
    Fin.append (fun j => f (fun l => a l j)) (fun q => f (fun l => b l q)) =
      fun x => f (fun l => Fin.append (a l) (b l) x) := by
  funext x
  refine Fin.addCases (fun j => ?_) (fun q => ?_) x <;> simp [Fin.append_left, Fin.append_right]

/-- Polymorphisms of every arity preserve every pp-definable relation. -/
theorem preserves_of_pp {D : Type} (H : Template D) {k n : ℕ} (R : Set (Fin k → D))
    (hR : PPDefinable H R) (f : (Fin n → D) → D) (hf : IsPolymorphism H f) :
    Preserves f R := by
  obtain ⟨φ, hφ⟩ := hR
  intro t ht
  have hb : ∀ l, φ.Holds (t l) := fun l => (hφ _).1 (ht l)
  choose b hb using hb
  rw [hφ]
  refine ⟨fun q => f (fun l => b l q), ?_, ?_⟩
  · intro c hc
    rw [append_map]
    exact hf c.1 (fun l => Fin.append (t l) (b l) ∘ c.2) (fun l => (hb l).1 c hc)
  · intro e he
    rw [append_map]
    exact congrArg f (funext fun l => (hb l).2 e he)

/-- **Galois lemma, finite-arity form.** If `R = range r` with `r : Fin n → D^k` and every
`n`-ary polymorphism of `H` preserves `R`, then `R` is pp-definable over `H`. The pp formula
quantifies one variable per point of `D^n` (the graph of an `n`-ary operation), asserts that
this operation is a polymorphism, and exposes its values at the columns of `r`. -/
theorem pp_of_preserved {D : Type} [Fintype D] [DecidableEq D] (H : Template D) {k n : ℕ}
    (R : Set (Fin k → D)) (r : Fin n → Fin k → D) (hr : Set.range r = R)
    (hpres : ∀ f : (Fin n → D) → D, IsPolymorphism H f → Preserves f R) :
    PPDefinable H R := by
  classical
  set N := Fintype.card (Fin n → D) with hN
  let e : (Fin n → D) ≃ Fin N := Fintype.equivFin _
  let col : Fin k → (Fin n → D) := fun j l => r l j
  let atomsOf : Fin H.s → List (Σ i : Fin H.s, Fin (H.arity i) → Fin (k + N)) := fun i =>
    ((Finset.univ.filter (fun M : Fin n → Fin (H.arity i) → D => ∀ l, M l ∈ H.rel i)).toList).map
      (fun M => ⟨i, fun j => Fin.natAdd k (e (fun l => M l j))⟩)
  let φ : PPFormula H k :=
    { m := N
      atoms := (List.finRange H.s).flatMap atomsOf
      eqs := (List.finRange k).map (fun j => (Fin.castAdd N j, Fin.natAdd k (e (col j)))) }
  refine ⟨φ, fun a => ?_⟩
  -- `φ` holds at `a` iff `a` is the column-image of some `n`-ary polymorphism.
  have key : φ.Holds a ↔ ∃ f : (Fin n → D) → D, IsPolymorphism H f ∧ ∀ j, a j = f (col j) := by
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
  rw [key]
  constructor
  · intro haR
    rw [← hr] at haR
    obtain ⟨l0, rfl⟩ := haR
    refine ⟨fun x => x l0, fun i t ht => ht l0, fun j => rfl⟩
  · rintro ⟨f, hf, ha⟩
    have hmem : ∀ l, r l ∈ R := fun l => hr ▸ ⟨l, rfl⟩
    have := hpres f hf r hmem
    have hae : a = fun j => f (fun l => r l j) := funext ha
    rw [hae]
    exact this

/-- The model of `Q_C` on `Fin 3` with `d ↦ 0`. -/
def Q3 : Finset (Fin 4 → Fin 3) :=
  Finset.univ.filter (fun w => Even (Finset.univ.filter (fun j => w j = 0)).card)

theorem Q3_card : Q3.card = 41 := by decide

/-- `Q_C` has an enumeration by `Fin 41` (it has exactly `16 + 24 + 1 = 41` tuples). -/
theorem exists_enum {D : Type} [DecidableEq D] (C : Finset D) (d : D) (hC : C.card = 3)
    (hd : d ∈ C) : ∃ r : Fin 41 → Fin 4 → D, Set.range r = Q C d := by
  have h2 : (C.erase d).card = 2 := by rw [Finset.card_erase_of_mem hd, hC]
  obtain ⟨x, y, hxy, hE⟩ := Finset.card_eq_two.1 h2
  have hx : x ∈ C.erase d := by rw [hE]; simp
  have hy : y ∈ C.erase d := by rw [hE]; simp
  have hxd : x ≠ d := (Finset.mem_erase.1 hx).1
  have hyd : y ≠ d := (Finset.mem_erase.1 hy).1
  have hxC : x ∈ C := (Finset.mem_erase.1 hx).2
  have hyC : y ∈ C := (Finset.mem_erase.1 hy).2
  let g : Fin 3 → D := ![d, x, y]
  have hgC : ∀ j, g j ∈ C := by
    intro j; fin_cases j <;> simp [g, hd, hxC, hyC]
  have hg0 : ∀ j, g j = d ↔ j = 0 := by
    intro j; fin_cases j <;> simp [g, hxd, hyd]
  have hgsurj : ∀ z ∈ C, ∃ j, g j = z := by
    intro z hz
    by_cases hzd : z = d
    · exact ⟨0, by simp [g, hzd]⟩
    · have : z ∈ C.erase d := Finset.mem_erase.2 ⟨hzd, hz⟩
      rw [hE] at this
      rcases Finset.mem_insert.1 this with h | h
      · exact ⟨1, by simp [g, h]⟩
      · exact ⟨2, by simp [g, (Finset.mem_singleton.1 h)]⟩
  have hcount : ∀ w : Fin 4 → Fin 3,
      (Finset.univ.filter (fun j => g (w j) = d)) = Finset.univ.filter (fun j => w j = 0) := by
    intro w; exact Finset.filter_congr (fun j _ => hg0 (w j))
  let E := (Q3.equivFinOfCardEq Q3_card).symm
  refine ⟨fun i => g ∘ (E i).1, ?_⟩
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    have hw := (E i).2
    simp only [Q3, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine ⟨fun j => hgC _, ?_⟩
    simp only [Function.comp_def]
    rw [hcount]
    convert hw using 2
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  · rintro ⟨hzC, hev⟩
    choose w hw using fun j => hgsurj (z j) (hzC j)
    have hwz : g ∘ w = z := funext hw
    have hwQ : w ∈ Q3 := by
      simp only [Q3, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hcount w]
      simpa [hw] using hev
    refine ⟨Q3.equivFinOfCardEq Q3_card ⟨w, hwQ⟩, ?_⟩
    simp [E, hwz]

theorem fat_main {D : Type} [Fintype D] [DecidableEq D] [Nonempty D] (H : Template D)
    (_hH : Conservative H) (C : Finset D) (d : D) (hC : C.card = 3) (hd : d ∈ C) :
    PPDefinable H (Q C d) ↔
      ∀ f : (Fin 41 → D) → D, IsPolymorphism H f → Preserves f (Q C d) := by
  constructor
  · intro h f hf
    exact preserves_of_pp H _ h f hf
  · intro h
    obtain ⟨r, hr⟩ := exists_enum C d hC hd
    exact pp_of_preserved H _ r hr h

end FAT
end ConsModCount

open ConsModCount in
theorem solution {D : Type} [Fintype D] [DecidableEq D] [Nonempty D] (H : Template D)
    (hH : Conservative H) (C : Finset D) (d : D) (hC : C.card = 3) (hd : d ∈ C) :
    PPDefinable H (Q C d) ↔
      ∀ f : (Fin 41 → D) → D, IsPolymorphism H f → Preserves f (Q C d) :=
  ConsModCount.FAT.fat_main H hH C d hC hd
