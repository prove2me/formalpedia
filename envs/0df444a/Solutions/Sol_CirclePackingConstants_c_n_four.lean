-- Prove2me | solution 1 for CirclePackingConstants.c_n_four
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T16:25:17.916483+00:00
-- url     : https://prove2.me/submissions/92fb4701-a6c7-4acf-9700-9618c2b205a3

import Definitions.Def_CirclePackingConstants
import Theorems.Thm_CirclePackingConstants_r_n_eq_of_sharp_unit_square_separation

noncomputable section

namespace CirclePackingConstants

private def quadrant (p : Point) : Bool × Bool :=
  (decide (p.1 ≤ 1 / 2), decide (p.2 ≤ 1 / 2))

private lemma square_le_oriented {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ 1)
    (hxy : x ≤ y) : (x - y) ^ 2 ≤ y - x := by
  have h₀ : 0 ≤ y - x := by linarith
  have h₁ : 0 ≤ 1 - (y - x) := by linarith
  nlinarith only [mul_nonneg h₀ h₁]

/-- The squared edge lengths of a cyclic list consisting of two lower-half
values followed by two upper-half values sum to at most two. -/
private lemma cycle_squares_le_two {u₀ u₁ u₂ u₃ : ℝ}
    (h₀₀ : 0 ≤ u₀) (h₀₁ : u₀ ≤ 1)
    (h₁₀ : 0 ≤ u₁) (h₁₁ : u₁ ≤ 1)
    (h₂₀ : 0 ≤ u₂) (h₂₁ : u₂ ≤ 1)
    (h₃₀ : 0 ≤ u₃) (h₃₁ : u₃ ≤ 1)
    (h₁₂ : u₁ ≤ u₂) (h₀₃ : u₀ ≤ u₃) :
    (u₀ - u₁) ^ 2 + (u₁ - u₂) ^ 2 +
      (u₂ - u₃) ^ 2 + (u₃ - u₀) ^ 2 ≤ 2 := by
  rcases le_total u₀ u₁ with h₀₁' | h₁₀'
  · rcases le_total u₂ u₃ with h₂₃ | h₃₂
    · have e₀₁ := square_le_oriented h₀₀ h₁₁ h₀₁'
      have e₁₂ := square_le_oriented h₁₀ h₂₁ h₁₂
      have e₂₃ := square_le_oriented h₂₀ h₃₁ h₂₃
      have e₃₀ := square_le_oriented h₀₀ h₃₁ h₀₃
      nlinarith
    · have e₀₁ := square_le_oriented h₀₀ h₁₁ h₀₁'
      have e₁₂ := square_le_oriented h₁₀ h₂₁ h₁₂
      have e₂₃ := square_le_oriented h₃₀ h₂₁ h₃₂
      have e₃₀ := square_le_oriented h₀₀ h₃₁ h₀₃
      nlinarith
  · rcases le_total u₂ u₃ with h₂₃ | h₃₂
    · have e₀₁ := square_le_oriented h₁₀ h₀₁ h₁₀'
      have e₁₂ := square_le_oriented h₁₀ h₂₁ h₁₂
      have e₂₃ := square_le_oriented h₂₀ h₃₁ h₂₃
      have e₃₀ := square_le_oriented h₀₀ h₃₁ h₀₃
      nlinarith
    · have e₀₁ := square_le_oriented h₁₀ h₀₁ h₁₀'
      have e₁₂ := square_le_oriented h₁₀ h₂₁ h₁₂
      have e₂₃ := square_le_oriented h₃₀ h₂₁ h₃₂
      have e₃₀ := square_le_oriented h₀₀ h₃₁ h₀₃
      nlinarith

private lemma same_quadrant_sqDist_le_one {p q : Point}
    (hp : 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1)
    (hq : 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1)
    (hcell : quadrant p = quadrant q) : sqDist p q ≤ 1 := by
  have hxcell : decide (p.1 ≤ 1 / 2) = decide (q.1 ≤ 1 / 2) := by
    exact congrArg Prod.fst hcell
  have hycell : decide (p.2 ≤ 1 / 2) = decide (q.2 ≤ 1 / 2) := by
    exact congrArg Prod.snd hcell
  have hxiff : (p.1 ≤ 1 / 2 ↔ q.1 ≤ 1 / 2) := by
    exact decide_eq_decide.mp hxcell
  have hyiff : (p.2 ≤ 1 / 2 ↔ q.2 ≤ 1 / 2) := by
    exact decide_eq_decide.mp hycell
  have hx : (p.1 - q.1) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    rcases hp with ⟨hp0, hp1, _, _⟩
    rcases hq with ⟨hq0, hq1, _, _⟩
    by_cases hpl : p.1 ≤ 1 / 2
    · have hql := hxiff.mp hpl
      have h₀ : 0 ≤ 1 / 2 - (p.1 - q.1) := by linarith
      have h₁ : 0 ≤ 1 / 2 + (p.1 - q.1) := by linarith
      nlinarith only [mul_nonneg h₀ h₁]
    · have hql : ¬q.1 ≤ 1 / 2 := by
        intro hql
        exact hpl (hxiff.mpr hql)
      have h₀ : 0 ≤ 1 / 2 - (p.1 - q.1) := by linarith
      have h₁ : 0 ≤ 1 / 2 + (p.1 - q.1) := by linarith
      nlinarith only [mul_nonneg h₀ h₁]
  have hy : (p.2 - q.2) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    rcases hp with ⟨_, _, hp0, hp1⟩
    rcases hq with ⟨_, _, hq0, hq1⟩
    by_cases hpl : p.2 ≤ 1 / 2
    · have hql := hyiff.mp hpl
      have h₀ : 0 ≤ 1 / 2 - (p.2 - q.2) := by linarith
      have h₁ : 0 ≤ 1 / 2 + (p.2 - q.2) := by linarith
      nlinarith only [mul_nonneg h₀ h₁]
    · have hql : ¬q.2 ≤ 1 / 2 := by
        intro hql
        exact hpl (hyiff.mpr hql)
      have h₀ : 0 ≤ 1 / 2 - (p.2 - q.2) := by linarith
      have h₁ : 0 ≤ 1 / 2 + (p.2 - q.2) := by linarith
      nlinarith only [mul_nonneg h₀ h₁]
  unfold sqDist
  nlinarith

private lemma four_points_have_close_pair (p : Fin 4 → Point)
    (hp : ∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) :
    ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ 1 := by
  by_contra hclose
  push_neg at hclose
  have hfar : ∀ i j, i ≠ j → 1 < sqDist (p i) (p j) := by
    intro i j hij
    exact hclose i j hij
  have hinj : Function.Injective (fun i : Fin 4 ↦ quadrant (p i)) := by
    intro i j hcell
    by_contra hij
    exact (not_le_of_gt (hfar i j hij))
      (same_quadrant_sqDist_le_one (hp i) (hp j) hcell)
  have hbij : Function.Bijective (fun i : Fin 4 ↦ quadrant (p i)) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by decide⟩
  obtain ⟨a, ha⟩ := hbij.2 (true, true)
  obtain ⟨b, hb⟩ := hbij.2 (false, true)
  obtain ⟨c, hc⟩ := hbij.2 (true, false)
  obtain ⟨d, hd⟩ := hbij.2 (false, false)
  have ha' : (p a).1 ≤ 1 / 2 ∧ (p a).2 ≤ 1 / 2 := by
    simpa [quadrant] using ha
  have hb' : ¬(p b).1 ≤ 1 / 2 ∧ (p b).2 ≤ 1 / 2 := by
    simpa [quadrant] using hb
  have hc' : (p c).1 ≤ 1 / 2 ∧ ¬(p c).2 ≤ 1 / 2 := by
    simpa [quadrant] using hc
  have hd' : ¬(p d).1 ≤ 1 / 2 ∧ ¬(p d).2 ≤ 1 / 2 := by
    simpa [quadrant] using hd
  have hac : a ≠ c := by
    intro e
    subst c
    have h := ha.symm.trans hc
    simpa using congrArg Prod.snd h
  have hcd : c ≠ d := by
    intro e
    subst d
    have h := hc.symm.trans hd
    simpa using congrArg Prod.fst h
  have hdb : d ≠ b := by
    intro e
    subst b
    have h := hd.symm.trans hb
    simpa using congrArg Prod.snd h
  have hba : b ≠ a := by
    intro e
    subst a
    have h := hb.symm.trans ha
    simpa using congrArg Prod.fst h
  rcases hp a with ⟨hax0, hax1, hay0, hay1⟩
  rcases hp b with ⟨hbx0, hbx1, hby0, hby1⟩
  rcases hp c with ⟨hcx0, hcx1, hcy0, hcy1⟩
  rcases hp d with ⟨hdx0, hdx1, hdy0, hdy1⟩
  have hx := cycle_squares_le_two
    hax0 hax1 hcx0 hcx1 hdx0 hdx1 hbx0 hbx1
    (by linarith [hc'.1, hd'.1]) (by linarith [ha'.1, hb'.1])
  have hy := cycle_squares_le_two
    hay0 hay1 hby0 hby1 hdy0 hdy1 hcy0 hcy1
    (by linarith [hb'.2, hd'.2]) (by linarith [ha'.2, hc'.2])
  have eac := hfar a c hac
  have ecd := hfar c d hcd
  have edb := hfar d b hdb
  have eba := hfar b a hba
  unfold sqDist at eac ecd edb eba
  nlinarith

theorem cFourProof : c_n 4 = Real.pi / 4 := by
  have hlower : ∃ p : Fin 4 → Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) ∧
      ∀ i j, i ≠ j → (1 : ℝ) ^ 2 ≤ sqDist (p i) (p j) := by
    refine ⟨![(0, 0), (1, 0), (0, 1), (1, 1)], ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [sqDist] <;> norm_num
  have hr : r_n 4 = (1 : ℝ) / (2 * (1 + 1)) :=
    r_n_eq_of_sharp_unit_square_separation (by norm_num) hlower
      (by simpa using four_points_have_close_pair)
  norm_num at hr
  unfold c_n
  rw [hr]
  ring

end CirclePackingConstants

theorem solution : CirclePackingConstants.c_n 4 = Real.pi / 4 :=
  CirclePackingConstants.cFourProof
