-- Prove2me | solution 1 for BealeConvexMin.QuadSimplex.cost_decreases
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:56:15.205855+00:00
-- url     : https://prove2.me/submissions/c83522d6-f50b-426b-b622-6cb4651764f9

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau
import Definitions.Def_BealeConvexMin_QuadSimplex_BealeStep

namespace BealeConvexMin.QuadSimplex

theorem aux_cd_pivotC00 {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (P : Fin (N + 1))
    (hP : P ≠ 0) (d : Fin (N + 1) → ℝ) :
    pivotC c P d 0 0 = c 0 0 + c 0 P * (-d 0 / d P) +
      (c P 0 + c P P * (-d 0 / d P)) * (-d 0 / d P) := by
  have h0 : (0 : Fin (N + 1)) ≠ P := fun h => hP h.symm
  simp only [pivotC, pivotCPrime, pivotE, Matrix.of_apply, if_neg h0]

theorem aux_cd_real (c a b t : ℝ) (ha : a < 0) (ht : 0 < t) (hbt : b * t ≤ -a) :
    c + a * t + (a + b * t) * t < c := by
  have h := mul_neg_of_neg_of_pos (by linarith : 2 * a + b * t < 0) ht
  nlinarith [h]

theorem aux_cd_orient_facts {n N : ℕ} (T : Tableau n N) (p : Fin N) (hsymm : T.c.IsSymm)
    (hlab : LabelsConsistent T) (hpos : BasicPositive T) (hadm : AdmissibleChoice T p) :
    (orient T p).c 0 0 = T.c 0 0 ∧
    (orient T p).c 0 p.succ = (orient T p).c p.succ 0 ∧
    (orient T p).c p.succ 0 < 0 ∧
    ∀ q, (orient T p).row q p.succ < 0 → 0 < (orient T p).row q 0 := by
  have hs : ∀ i j, T.c i j = T.c j i := fun i j => (hsymm.apply j i)
  have hne : (0 : Fin (N + 1)) ≠ p.succ := (Fin.succ_ne_zero p).symm
  unfold orient
  split_ifs with hc
  · have hfree : T.lab p = none := by
      rcases hadm.1 with ⟨h, _⟩ | ⟨_, h⟩
      · exact h
      · exact absurd h (not_lt.mpr hc.le)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [negateSlot, hne]
    · simp [negateSlot, hne, hs 0 p.succ]
    · simp [negateSlot, hne]; linarith
    · intro q hq
      simp only [negateSlot, if_neg hne] at hq ⊢
      apply hpos
      intro k hk
      have hrowq := congrFun (hlab.2 k q hk) p.succ
      have hkp : k ≠ p := by
        rintro rfl
        rw [hfree] at hk
        cases hk
      rw [hrowq, Pi.single_apply, if_neg (fun h => hkp (Fin.succ_injective _ h).symm)] at hq
      simp at hq
  · refine ⟨rfl, hs 0 p.succ, ?_, ?_⟩
    · rcases hadm.1 with ⟨_, h⟩ | ⟨_, h⟩
      · push Not at hc; exact lt_of_le_of_ne hc h
      · exact h
    · intro q hq
      apply hpos
      intro k hk
      have hrowq := congrFun (hlab.2 k q hk) p.succ
      rw [hrowq, Pi.single_apply] at hq
      split_ifs at hq <;> linarith

end BealeConvexMin.QuadSimplex

open BealeConvexMin.QuadSimplex

theorem solution {n N : ℕ} (T T' : Tableau n N) (hsymm : T.c.IsSymm)
    (hlab : LabelsConsistent T) (hpos : BasicPositive T) (hstep : BealeStep T T') :
    T'.c 0 0 < T.c 0 0 := by
  obtain ⟨p, hadm, hcase⟩ := hstep
  obtain ⟨h00, hsym, ha, hrow⟩ := aux_cd_orient_facts T p hsymm hlab hpos hadm
  have hP : p.succ ≠ 0 := Fin.succ_ne_zero p
  rcases hcase with ⟨q, ⟨hqneg, _⟩, hb, rfl⟩ | ⟨hb, _, rfl⟩
  · show pivotC (orient T p).c p.succ ((orient T p).row q) 0 0 < T.c 0 0
    rw [aux_cd_pivotC00 _ _ hP, hsym, h00]
    have hd0 := hrow q hqneg
    have htpos : 0 < -(orient T p).row q 0 / (orient T p).row q p.succ := by
      rw [neg_div, ← div_neg]; exact div_pos hd0 (neg_pos.mpr hqneg)
    have hratio : ratio (orient T p) p q =
        -(orient T p).row q 0 / (orient T p).row q p.succ := by
      simp only [ratio]; rw [div_neg, neg_div]
    rw [hratio] at hb
    generalize -(orient T p).row q 0 / (orient T p).row q p.succ = t at htpos hb ⊢
    apply aux_cd_real _ _ _ _ ha htpos
    rcases hb with hb | hb
    · nlinarith
    · by_cases hbpos : 0 < (orient T p).c p.succ p.succ
      · rw [le_div_iff₀ hbpos] at hb; linarith
      · push Not at hbpos; nlinarith
  · show pivotC (orient T p).c p.succ ((orient T p).c p.succ) 0 0 < T.c 0 0
    rw [aux_cd_pivotC00 _ _ hP, hsym, h00]
    have hbt : (orient T p).c p.succ p.succ *
        (-(orient T p).c p.succ 0 / (orient T p).c p.succ p.succ) = -(orient T p).c p.succ 0 := by
      field_simp
    have htpos : 0 < -(orient T p).c p.succ 0 / (orient T p).c p.succ p.succ :=
      div_pos (neg_pos.mpr ha) hb
    exact aux_cd_real _ _ _ _ ha htpos hbt.le
