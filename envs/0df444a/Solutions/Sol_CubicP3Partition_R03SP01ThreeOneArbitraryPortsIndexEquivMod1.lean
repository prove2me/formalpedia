-- Prove2me | solution 1 for CubicP3Partition.R03SP01ThreeOneArbitraryPortsIndexEquivMod1
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:21:46.957152+00:00
-- url     : https://prove2.me/submissions/d5bc1891-1221-4bf7-8b7a-4a50dd1543dc

import Mathlib

namespace CubicP3Partition

set_option maxRecDepth 100000


end CubicP3Partition

open CubicP3Partition
theorem solution
    (b d : Nat) (hd : 1 ≤ d) (hdn : d < 1 + 3 * b) (hr : d % 3 = 1) :
    ∃ e : Fin (d - 1) ⊕ (Fin ((1 + 3 * b) - d - 3) ⊕ Fin 4) ≃
      Fin (1 + 3 * b),
      (∀ i : Fin (d - 1), e (Sum.inl i) =
        ⟨1 + i.val, by omega⟩) ∧
      (∀ j : Fin ((1 + 3 * b) - d - 3), e (Sum.inr (Sum.inl j)) =
        ⟨d + 2 + j.val, by omega⟩) ∧
      e (Sum.inr (Sum.inr 0)) = ⟨0, by omega⟩ ∧
      e (Sum.inr (Sum.inr 1)) = ⟨d, by omega⟩ ∧
      e (Sum.inr (Sum.inr 2)) = ⟨d + 1, by omega⟩ ∧
      e (Sum.inr (Sum.inr 3)) = ⟨(1 + 3 * b) - 1, by omega⟩ := by
  have hmod : d % 3 < 3 := Nat.mod_lt _ (by omega)
  have hd1 : 1 ≤ d := hd
  have hto : d - 1 + ((1 + 3 * b) - d - 3) + 4 = 1 + 3 * b := by
    omega
  have hnpos : 0 < 1 + 3 * b := by omega
  have hd1lt : d + 1 < 1 + 3 * b := by omega
  let f : Fin (d - 1) ⊕ (Fin ((1 + 3 * b) - d - 3) ⊕ Fin 4) →
      Fin (1 + 3 * b) := fun z => match z with
    | Sum.inl i => ⟨1 + i.val, by have hi := i.isLt; omega⟩
    | Sum.inr (Sum.inl j) => ⟨d + 2 + j.val, by have hj := j.isLt; omega⟩
    | Sum.inr (Sum.inr q) =>
      if q = 0 then ⟨0, hnpos⟩
      else if q = 1 then ⟨d, hdn⟩
      else if q = 2 then ⟨d + 1, hd1lt⟩
      else ⟨(1 + 3 * b) - 1, by omega⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hval := congrArg Fin.val hxy
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        apply congrArg Sum.inl
        apply Fin.ext
        dsimp [f] at hval
        omega
      | inr y =>
        cases y with
        | inl j =>
          exfalso
          dsimp [f] at hval
          omega
        | inr q =>
          fin_cases q <;> dsimp [f] at hval <;> omega
    | inr x =>
      cases x with
      | inl i =>
        cases y with
        | inl j =>
          exfalso
          dsimp [f] at hval
          omega
        | inr y =>
          cases y with
          | inl j =>
            apply congrArg (fun z => Sum.inr (Sum.inl z))
            apply Fin.ext
            dsimp [f] at hval
            omega
          | inr q =>
            fin_cases q <;> dsimp [f] at hval <;> omega
      | inr q =>
        cases y with
        | inl i =>
          fin_cases q <;> dsimp [f] at hval <;> omega
        | inr y =>
          cases y with
          | inl i =>
            fin_cases q <;> dsimp [f] at hval <;> omega
          | inr r =>
            apply congrArg (fun z => Sum.inr (Sum.inr z))
            apply Fin.ext
            fin_cases q <;> fin_cases r <;> dsimp [f] at hval <;> omega
  have hf_surj : Function.Surjective f := by
    intro x
    by_cases hx0 : x.val = 0
    · refine ⟨Sum.inr (Sum.inr 0), ?_⟩
      apply Fin.ext
      dsimp [f]
      simp [hx0]
    · by_cases hxd : x.val = d
      · refine ⟨Sum.inr (Sum.inr 1), ?_⟩
        apply Fin.ext
        dsimp [f]
        simp [hx0, hxd]
      · by_cases hdp1 : x.val = d + 1
        · refine ⟨Sum.inr (Sum.inr 2), ?_⟩
          apply Fin.ext
          dsimp [f]
          simp [hx0, hxd, hdp1]
        · by_cases hxn1 : x.val = (1 + 3 * b) - 1
          · refine ⟨Sum.inr (Sum.inr 3), ?_⟩
            apply Fin.ext
            dsimp [f]
            simp [hx0, hxd, hdp1, hxn1]
          · by_cases hlow : 1 ≤ x.val ∧ x.val ≤ d - 1
            · refine ⟨Sum.inl ⟨x.val - 1, by omega⟩, ?_⟩
              apply Fin.ext
              dsimp [f]
              omega
            · have hhigh : d + 2 ≤ x.val := by omega
              refine ⟨Sum.inr (Sum.inl ⟨x.val - (d + 2), by omega⟩), ?_⟩
              apply Fin.ext
              dsimp [f]
              omega
  let e : Fin (d - 1) ⊕ (Fin ((1 + 3 * b) - d - 3) ⊕ Fin 4) ≃
      Fin (1 + 3 * b) := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rfl
  · intro j
    rfl
  · rfl
  · rfl
  · rfl
  · rfl

