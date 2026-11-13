-- Prove2me | solution 1 for GenCountSampleLLL.insertion_input_return_edge_balance
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:50:39.722012+00:00
-- url     : https://prove2.me/submissions/48bf79c3-986f-4bc3-b450-c0b514517e49

import Definitions.Def_GenCountSampleLLL_insertionChain
import Theorems.Thm_GenCountSampleLLL_lemma_6_4_return_balance
noncomputable section
open scoped Classical BigOperators
open GenCountSampleLLL

private theorem iRule_reset_layer (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (σ : I.Assign) (T : Finset (Fin I.m)) (z : I.Assign) :
    I.iRule D a σ Rule.reset ⟨[], Inst.Base.lay T z (I.ell D a T) σ⟩ =
      I.expL D a (fun L => if (T,z) ∈ L then 1 / (L.card : ℝ) else 0) := by
  unfold Inst.iRule Inst.expL
  apply Finset.sum_congr rfl
  intro ω hω
  congr 1
  let L := I.Llist D a ω
  change (if L = ∅ then I.dirac ⟨[], Inst.Base.inp σ⟩ ⟨[], Inst.Base.lay T z (I.ell D a T) σ⟩
    else ∑ e ∈ L, I.dirac ⟨[], Inst.Base.lay e.1 e.2 (I.ell D a e.1) σ⟩
      ⟨[], Inst.Base.lay T z (I.ell D a T) σ⟩ / (L.card : ℝ)) =
        if (T,z) ∈ L then 1 / (L.card : ℝ) else 0
  by_cases hL : L = ∅
  · simp [hL, Inst.dirac]
  · simp only [hL, if_false]
    by_cases he : (T,z) ∈ L
    · rw [Finset.sum_eq_single (T,z)]
      · simp [he, Inst.dirac]
      · intro e heL hne
        have hneq : (⟨[], Inst.Base.lay T z (I.ell D a T) σ⟩ : I.St) ≠
            ⟨[], Inst.Base.lay e.1 e.2 (I.ell D a e.1) σ⟩ := by
          intro h
          have hb := congrArg Inst.St.base h
          cases e with
          | mk U y =>
            simp only [Inst.Base.lay.injEq] at hb
            apply hne
            exact Prod.ext hb.1.symm hb.2.1.symm
        simp [Inst.dirac, hneq]
      · exact fun h => (h he).elim
    · have hs : ∀ e ∈ L, e ≠ (T,z) := fun e heL heq => he (heq ▸ heL)
      have hzero : ∑ e ∈ L, I.dirac ⟨[], Inst.Base.lay e.1 e.2 (I.ell D a e.1) σ⟩
          ⟨[], Inst.Base.lay T z (I.ell D a T) σ⟩ / (L.card : ℝ) = 0 := by
        apply Finset.sum_eq_zero
        intro e heL
        have hneq : (⟨[], Inst.Base.lay T z (I.ell D a T) σ⟩ : I.St) ≠
            ⟨[], Inst.Base.lay e.1 e.2 (I.ell D a e.1) σ⟩ := by
          intro h
          have hb := congrArg Inst.St.base h
          cases e with
          | mk U y =>
            simp only [Inst.Base.lay.injEq] at hb
            apply hs (U,y) heL
            exact Prod.ext hb.1.symm hb.2.1.symm
        simp [Inst.dirac, hneq]
      simp [he, hzero]

theorem solution (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (σ : I.Assign) (T : Finset (Fin I.m)) (z : I.Assign) (X Y : I.S D a)
    (hX : X.1 = ⟨[], Inst.Base.inp σ⟩)
    (hY : Y.1 = ⟨[], Inst.Base.lay T z (I.ell D a T) σ⟩)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) :
    I.w D a X * I.Pker D a X Y = I.w D a Y * I.Pker D a Y X := by
  have hret := lemma_6_4_return_balance I D a T z hT hz
  have hXY : X ≠ Y := by
    intro h
    have hv := congrArg Subtype.val h
    rw [hX, hY] at hv
    cases hv
  have hxy : I.Pker D a X Y = (1 / 6 : ℝ) *
      I.expL D a (fun L => if (T,z) ∈ L then 1 / (L.card : ℝ) else 0) := by
    simp only [Inst.Pker, hXY, if_false, mul_zero, zero_add, hX, hY,
      Inst.stepRule, Inst.baseRule]
    rw [iRule_reset_layer]
    by_cases hb : I.bad a σ <;> simp [Inst.iRule, Inst.dirac, hb]
  have hyx : I.Pker D a Y X = (1 / 6 : ℝ) * I.retProb D a (T,z) := by
    simp only [Inst.Pker, Ne.symm hXY, if_false, mul_zero, zero_add, hX, hY,
      Inst.stepRule, Inst.baseRule]
    by_cases he : 0 < I.ell D a T <;> simp [Inst.dirac, he]
  rw [hxy, hyx, hret]
  simp [Inst.w, Inst.wt, hX, hY]
  ring

