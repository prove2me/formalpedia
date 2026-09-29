-- Prove2me | solution 1 for CubicP3Partition.R03SP01ThreeOneArbitraryPortsIndexEquivMod0
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:21:45.582286+00:00
-- url     : https://prove2.me/submissions/c855b534-136a-4109-bbee-b723b53d642a

import Mathlib

namespace CubicP3Partition

set_option maxRecDepth 100000


end CubicP3Partition

open CubicP3Partition
theorem solution
    (b d : Nat) (hd : 1 ≤ d) (hdn : d < 1 + 3 * b) (hr : d % 3 = 0) :
    ∃ e : Fin (d - 3) ⊕ (Fin ((1 + 3 * b) - d - 1) ⊕ Fin 4) ≃
      Fin (1 + 3 * b),
      (∀ i : Fin (d - 3), e (Sum.inl i) =
        ⟨2 + i.val, by omega⟩) ∧
      (∀ j : Fin ((1 + 3 * b) - d - 1), e (Sum.inr (Sum.inl j)) =
        ⟨d + 1 + j.val, by omega⟩) ∧
      e (Sum.inr (Sum.inr 0)) = ⟨0, by omega⟩ ∧
      e (Sum.inr (Sum.inr 1)) = ⟨1, by omega⟩ ∧
      e (Sum.inr (Sum.inr 2)) = ⟨d - 1, by omega⟩ ∧
      e (Sum.inr (Sum.inr 3)) = ⟨d, by omega⟩ := by
  have hmod : d % 3 < 3 := Nat.mod_lt _ (by omega)
  have hd3 : 3 ≤ d := by omega
  have hto : d - 3 + ((1 + 3 * b) - d - 1) + 4 = 1 + 3 * b := by
    omega
  have hnpos : 0 < 1 + 3 * b := by omega
  have hdm1lt : d - 1 < 1 + 3 * b := by omega
  let f : Fin (d - 3) ⊕ (Fin ((1 + 3 * b) - d - 1) ⊕ Fin 4) →
      Fin (1 + 3 * b) := fun z => match z with
    | Sum.inl i => ⟨2 + i.val, by have hi := i.isLt; omega⟩
    | Sum.inr (Sum.inl j) => ⟨d + 1 + j.val, by have hj := j.isLt; omega⟩
    | Sum.inr (Sum.inr q) =>
      if q = 0 then ⟨0, hnpos⟩
      else if q = 1 then ⟨1, by omega⟩
      else if q = 2 then ⟨d - 1, hdm1lt⟩
      else ⟨d, hdn⟩
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
    · by_cases hx1 : x.val = 1
      · refine ⟨Sum.inr (Sum.inr 1), ?_⟩
        apply Fin.ext
        dsimp [f]
        simp [hx0, hx1]
      · by_cases hxm1 : x.val = d - 1
        · refine ⟨Sum.inr (Sum.inr 2), ?_⟩
          apply Fin.ext
          dsimp [f]
          simp [hx0, hx1, hxm1]
        · by_cases hxd : x.val = d
          · refine ⟨Sum.inr (Sum.inr 3), ?_⟩
            apply Fin.ext
            dsimp [f]
            simp [hx0, hx1, hxm1, hxd]
          · by_cases hlow : 2 ≤ x.val ∧ x.val ≤ d - 2
            · refine ⟨Sum.inl ⟨x.val - 2, by omega⟩, ?_⟩
              apply Fin.ext
              dsimp [f]
              omega
            · have hhigh : d + 1 ≤ x.val := by omega
              refine ⟨Sum.inr (Sum.inl ⟨x.val - (d + 1), by omega⟩), ?_⟩
              apply Fin.ext
              dsimp [f]
              omega
  let e : Fin (d - 3) ⊕ (Fin ((1 + 3 * b) - d - 1) ⊕ Fin 4) ≃
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

