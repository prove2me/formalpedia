-- Prove2me | solution 1 for GenCountSampleLLL.lemma_6_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:46:43.918198+00:00
-- url     : https://prove2.me/submissions/6ead8290-4fa3-42c3-9105-13c5c2028c2b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GenCountSampleLLL_lemma_2_1
import Theorems.Thm_GenCountSampleLLL_insertion_auxiliary_stochastic
import Theorems.Thm_GenCountSampleLLL_insertion_auxiliary_weighted_balance
import Definitions.Def_GenCountSampleLLL_insertionChain
import Definitions.Def_mm_basic
noncomputable section
open scoped Classical BigOperators ENNReal
open GenCountSampleLLL

private theorem nuA_pos (I : Inst) (σ : I.Assign) : 0 < I.nuA σ := by
  unfold Inst.nuA
  apply Finset.prod_pos
  intro v hv
  exact ENNReal.toReal_pos (I.ν_pos v (σ v)) ((I.ν v).apply_ne_top (σ v))

private theorem nuU_pos (I : Inst) (U : Finset (Fin I.n)) (σ : I.Assign) : 0 < I.nuU U σ := by
  unfold Inst.nuU
  apply Finset.prod_pos
  intro v hv
  exact ENNReal.toReal_pos (I.ν_pos v (σ v)) ((I.ν v).apply_ne_top (σ v))

private theorem wt_pos (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ls : List I.Label) (b : I.Base) : 0 < I.wt D a ls b := by
  induction ls generalizing D a with
  | nil => cases b <;> simp [Inst.wt, nuA_pos, nuU_pos]
  | cons l ls ih =>
    obtain ⟨T,z,i⟩ := l
    simp only [Inst.wt]
    exact mul_pos (nuU_pos I _ _) (ih _ _)

private theorem wtil_pos (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (β : ℝ) (hβ : 0 < β) (X : I.S D a) : 0 < I.wtil β D a X := by
  unfold Inst.wtil Inst.w
  split_ifs
  · exact div_pos (wt_pos I _ _ _ _) hβ
  · exact wt_pos I _ _ _ _

private theorem piDist_isDist_of_good (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (β : ℝ) (hβ : 0 < β)
    (hgood : (I.Good (D.erase a)).Nonempty) : MarkovMixing.IsDist (I.piDist β D a) := by
  have hD : 0 < D.card := Finset.card_pos.mpr ⟨a,ha⟩
  obtain ⟨σ, hσ⟩ := hgood
  have hstate : (⟨[], Inst.Base.inp σ⟩ : I.St) ∈ I.states D.card D a := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
    rw [hk, Inst.states]
    simp [hσ]
  let X : I.S D a := ⟨⟨[], Inst.Base.inp σ⟩, hstate⟩
  have hM : 0 < I.Mtot β D a := by
    unfold Inst.Mtot
    apply Finset.sum_pos'
    · intro Y hY
      exact le_of_lt (wtil_pos I D a β hβ Y)
    · exact ⟨X, Finset.mem_univ _, wtil_pos I D a β hβ X⟩
  constructor
  · intro Y
    exact le_of_lt (div_pos (wtil_pos I D a β hβ Y) hM)
  · unfold Inst.piDist
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hM)

private theorem lemma_6_4_of_unnormalized_balance (I : Inst)
    (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D) (β : ℝ) (hβ : 0 < β)
    (hgood : (I.Good (D.erase a)).Nonempty)
    (hK : MarkovMixing.IsStochastic (I.Kker β D a))
    (hbalance : ∀ X Y : I.S D a,
      I.wtil β D a X * I.Kker β D a X Y = I.wtil β D a Y * I.Kker β D a Y X) :
    MarkovMixing.IsStationary (I.Kker β D a) (I.piDist β D a) ∧
      MarkovMixing.DetailedBalance (I.Kker β D a) (I.piDist β D a) := by
  have hdb : MarkovMixing.DetailedBalance (I.Kker β D a) (I.piDist β D a) := by
    intro X Y
    unfold Inst.piDist
    calc
      _ = (I.wtil β D a X * I.Kker β D a X Y) / I.Mtot β D a := by ring
      _ = (I.wtil β D a Y * I.Kker β D a Y X) / I.Mtot β D a := by rw [hbalance X Y]
      _ = _ := by ring
  refine ⟨⟨piDist_isDist_of_good I D a ha β hβ hgood, ?_⟩, hdb⟩
  funext Y
  change (∑ X : I.S D a, I.piDist β D a X * I.Kker β D a X Y) = I.piDist β D a Y
  calc
    _ = ∑ X : I.S D a, I.piDist β D a Y * I.Kker β D a Y X := by
      apply Finset.sum_congr rfl
      intro X hX
      exact hdb X Y
    _ = I.piDist β D a Y * ∑ X : I.S D a, I.Kker β D a Y X := by rw [Finset.mul_sum]
    _ = _ := by rw [hK.2 Y, mul_one]


private theorem Kker_offdiag_scaling (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (β : ℝ) (X Y : I.S D a) (hne : X ≠ Y) :
    I.Kker β D a X Y = (if I.isOut X.1 then β else 1) * I.Pker D a X Y := by
  have hv : Y.1 ≠ X.1 := by
    intro h
    exact hne (Subtype.ext h.symm)
  rcases X with ⟨⟨ls,b⟩, hX⟩
  cases ls with
  | nil =>
    cases b with
    | inp σ => simp [Inst.Kker, Inst.isOut]
    | out σ =>
      have hout : I.isOut (⟨[], Inst.Base.out σ⟩ : I.St) := ⟨σ, rfl⟩
      simp only [Inst.Kker, Inst.Pker, Inst.stepRule, Inst.baseRule, Inst.dirac, hout, if_true]
      simp only [hne, if_false, mul_zero, zero_add]
      have hv' : Y.1 ≠ ⟨[], Inst.Base.out σ⟩ := hv
      simp only [hv', if_false, add_zero]
      split_ifs <;> ring
    | tree T σ => simp [Inst.Kker, Inst.isOut]
    | lay T z i σ => simp [Inst.Kker, Inst.isOut]
  | cons x xs => simp [Inst.Kker, Inst.isOut]

private theorem Kker_balance_of_Pker_balance (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (β : ℝ) (hβ : 0 < β)
    (hP : ∀ X Y : I.S D a, I.w D a X * I.Pker D a X Y = I.w D a Y * I.Pker D a Y X) :
    ∀ X Y : I.S D a,
      I.wtil β D a X * I.Kker β D a X Y = I.wtil β D a Y * I.Kker β D a Y X := by
  intro X Y
  by_cases heq : X = Y
  · subst Y; rfl
  · rw [Kker_offdiag_scaling I D a β X Y heq,
      Kker_offdiag_scaling I D a β Y X (Ne.symm heq)]
    unfold Inst.wtil
    by_cases hx : I.isOut X.1 <;> by_cases hy : I.isOut Y.1 <;>
      simp only [hx, hy, if_true, if_false, one_mul] <;>
      field_simp <;> nlinarith [hP X Y, hβ]

private theorem Kker_row_mixture (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (β : ℝ) (X Y : I.S D a) :
    I.Kker β D a X Y =
      if I.isOut X.1 then β * I.Pker D a X Y + (if X = Y then 1 - β else 0)
      else I.Pker D a X Y := by
  by_cases hXY : X = Y
  · subst Y
    rcases X with ⟨⟨ls,b⟩, hX⟩
    cases ls with
    | nil =>
      cases b with
      | inp σ => simp [Inst.Kker, Inst.isOut]
      | out σ =>
        have hout : I.isOut (⟨[], Inst.Base.out σ⟩ : I.St) := ⟨σ,rfl⟩
        simp only [Inst.Kker, Inst.Pker, Inst.stepRule, Inst.baseRule, Inst.dirac, hout, if_true]
        simp
        ring
      | tree T σ => simp [Inst.Kker, Inst.isOut]
      | lay T z i σ => simp [Inst.Kker, Inst.isOut]
    | cons l ls => simp [Inst.Kker, Inst.isOut]
  · rw [Kker_offdiag_scaling I D a β X Y hXY]
    by_cases hout : I.isOut X.1 <;> simp [hout, hXY]

private theorem Kker_stochastic_of_Pker_stochastic (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (β : ℝ) (hβ : 0 ≤ β ∧ β ≤ 1)
    (hP : MarkovMixing.IsStochastic (I.Pker D a)) :
    MarkovMixing.IsStochastic (I.Kker β D a) := by
  constructor
  · intro X Y
    rw [Kker_row_mixture]
    by_cases hout : I.isOut X.1
    · simp only [hout, if_true]
      apply add_nonneg (mul_nonneg hβ.1 (hP.1 X Y))
      split_ifs <;> linarith
    · simpa [hout] using hP.1 X Y
  · intro X
    simp_rw [Kker_row_mixture]
    by_cases hout : I.isOut X.1
    · simp only [hout, if_true]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hP.2 X]
      simp
    · simpa [hout] using hP.2 X


private theorem lemma_6_4_of_auxiliary_reversible (I : Inst)
    (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D) (β : ℝ) (hβ : 0 < β ∧ β < 1)
    (hgood : (I.Good (D.erase a)).Nonempty)
    (hP : MarkovMixing.IsStochastic (I.Pker D a))
    (hbalance : ∀ X Y : I.S D a,
      I.w D a X * I.Pker D a X Y = I.w D a Y * I.Pker D a Y X) :
    MarkovMixing.IsStationary (I.Kker β D a) (I.piDist β D a) ∧
      MarkovMixing.DetailedBalance (I.Kker β D a) (I.piDist β D a) := by
  apply lemma_6_4_of_unnormalized_balance I D a ha β hβ.1 hgood
  · exact Kker_stochastic_of_Pker_stochastic I D a β ⟨le_of_lt hβ.1, le_of_lt hβ.2⟩ hP
  · exact Kker_balance_of_Pker_balance I D a β hβ.1 hbalance


theorem solution (I : Inst) (x : Fin I.m → ℝ) (hx : ∀ b, 0 < x b ∧ x b < 1)
    (hLLL : I.LLLCond (1 / 100) x) (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D)
    (β : ℝ) (hβ : 0 < β ∧ β < 1) :
    MarkovMixing.IsStationary (I.Kker β D a) (I.piDist β D a) ∧
      MarkovMixing.DetailedBalance (I.Kker β D a) (I.piDist β D a) := by
  have hZ : 0 < I.Z (D.erase a) := (lemma_2_1 I x hx hLLL).1 _
  have hgood : (I.Good (D.erase a)).Nonempty := by
    by_contra h
    have hempty : I.Good (D.erase a) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [Inst.Z, hempty] at hZ
  exact lemma_6_4_of_auxiliary_reversible I D a ha β hβ hgood
    (insertion_auxiliary_stochastic I x hx hLLL D a ha)
    (insertion_auxiliary_weighted_balance I x hx hLLL D a ha)
