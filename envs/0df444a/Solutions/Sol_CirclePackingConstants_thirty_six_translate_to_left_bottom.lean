-- Prove2me | solution 1 for CirclePackingConstants.thirty_six_translate_to_left_bottom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T09:35:20.702276+00:00
-- url     : https://prove2.me/submissions/b11cabce-ef1e-4cb9-b0be-3f6db882f157

import Definitions.Def_CirclePackingConstants

namespace CirclePackingConstants

def InUnitSquare36 (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

theorem translateToLeftBottomProof :
    ∀ p : Fin 36 → Point,
      (∀ i, InUnitSquare36 (p i)) →
      ∃ q : Fin 36 → Point,
        (∀ i, InUnitSquare36 (q i)) ∧
        (∀ i j, sqDist (q i) (q j) = sqDist (p i) (p j)) ∧
        (∃ i, (q i).1 = 0) ∧
        (∃ j, (q j).2 = 0) := by
  intro p hp
  classical
  let xs : Finset ℝ := Finset.univ.image (fun i : Fin 36 => (p i).1)
  let ys : Finset ℝ := Finset.univ.image (fun i : Fin 36 => (p i).2)
  have hxs : xs.Nonempty := by
    refine ⟨(p (0 : Fin 36)).1, ?_⟩
    simp [xs]
  have hys : ys.Nonempty := by
    refine ⟨(p (0 : Fin 36)).2, ?_⟩
    simp [ys]
  let xmin : ℝ := xs.min' hxs
  let ymin : ℝ := ys.min' hys
  have hxmin_mem : xmin ∈ xs := by
    simpa [xmin] using Finset.min'_mem xs hxs
  have hymin_mem : ymin ∈ ys := by
    simpa [ymin] using Finset.min'_mem ys hys
  have hxmin_nonneg : 0 ≤ xmin := by
    rcases Finset.mem_image.mp hxmin_mem with ⟨i, -, hi⟩
    have hi0 : 0 ≤ (p i).1 := (hp i).1
    simpa [hi] using hi0
  have hymin_nonneg : 0 ≤ ymin := by
    rcases Finset.mem_image.mp hymin_mem with ⟨i, -, hi⟩
    have hi0 : 0 ≤ (p i).2 := (hp i).2.2.1
    simpa [hi] using hi0
  have hxmin_le (i : Fin 36) : xmin ≤ (p i).1 := by
    have h := Finset.min'_le xs (p i).1 (by simp [xs])
    simpa [xmin] using h
  have hymin_le (i : Fin 36) : ymin ≤ (p i).2 := by
    have h := Finset.min'_le ys (p i).2 (by simp [ys])
    simpa [ymin] using h
  let q : Fin 36 → Point := fun i =>
    ((p i).1 - xmin, (p i).2 - ymin)
  have hq : ∀ i, InUnitSquare36 (q i) := by
    intro i
    rcases hp i with ⟨hx0, hx1, hy0, hy1⟩
    have hxl := hxmin_le i
    have hyl := hymin_le i
    dsimp [q, InUnitSquare36]
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    · linarith
  have hdist : ∀ i j, sqDist (q i) (q j) = sqDist (p i) (p j) := by
    intro i j
    dsimp [q, sqDist]
    ring
  have hleft : ∃ i, (q i).1 = 0 := by
    rcases Finset.mem_image.mp hxmin_mem with ⟨i, -, hi⟩
    refine ⟨i, ?_⟩
    have hi' : (p i).1 = xmin := by
      simpa using hi
    dsimp [q]
    linarith
  have hbottom : ∃ i, (q i).2 = 0 := by
    rcases Finset.mem_image.mp hymin_mem with ⟨i, -, hi⟩
    refine ⟨i, ?_⟩
    have hi' : (p i).2 = ymin := by
      simpa using hi
    dsimp [q]
    linarith
  exact ⟨q, hq, hdist, hleft, hbottom⟩

end CirclePackingConstants

theorem solution :
    ∀ p : Fin 36 → CirclePackingConstants.Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) →
      ∃ q : Fin 36 → CirclePackingConstants.Point,
        (∀ i, 0 ≤ (q i).1 ∧ (q i).1 ≤ 1 ∧ 0 ≤ (q i).2 ∧ (q i).2 ≤ 1) ∧
        (∀ i j, CirclePackingConstants.sqDist (q i) (q j) =
          CirclePackingConstants.sqDist (p i) (p j)) ∧
        (∃ i, (q i).1 = 0) ∧
        (∃ j, (q j).2 = 0) := by
  intro p hp
  simpa [CirclePackingConstants.InUnitSquare36] using
    CirclePackingConstants.translateToLeftBottomProof p hp
