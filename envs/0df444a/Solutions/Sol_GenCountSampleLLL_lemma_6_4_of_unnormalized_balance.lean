-- Prove2me | solution 1 for GenCountSampleLLL.lemma_6_4_of_unnormalized_balance
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:43:09.597631+00:00
-- url     : https://prove2.me/submissions/345ab70e-41e4-4953-b7e6-29b79d6f0e47

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

theorem solution (I : Inst)
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

