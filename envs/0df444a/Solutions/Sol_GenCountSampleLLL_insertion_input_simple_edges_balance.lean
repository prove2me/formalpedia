-- Prove2me | solution 1 for GenCountSampleLLL.insertion_input_simple_edges_balance
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:59:49.47756+00:00
-- url     : https://prove2.me/submissions/f76983a3-9c60-4c9a-8192-ba8d8094ed2e

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators
open GenCountSampleLLL

private theorem input_output_edge_balance (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (σ : I.Assign) (X Y : I.S D a)
    (hX : X.1 = ⟨[], Inst.Base.inp σ⟩)
    (hY : Y.1 = ⟨[], Inst.Base.out σ⟩) (hgood : ¬ I.bad a σ) :
    I.w D a X * I.Pker D a X Y = I.w D a Y * I.Pker D a Y X := by
  have hXY : X ≠ Y := by
    intro h
    have hv := congrArg Subtype.val h
    rw [hX, hY] at hv
    cases hv
  have hxy : I.Pker D a X Y = (1 / 6 : ℝ) := by
    simp only [Inst.Pker, hXY, if_false, mul_zero, zero_add, hX, hY,
      Inst.stepRule, Inst.baseRule]
    simp [Inst.iRule, Inst.dirac, hgood, Inst.expL]
  have hyx : I.Pker D a Y X = (1 / 6 : ℝ) := by
    simp [Inst.Pker, Ne.symm hXY, hX, hY, Inst.stepRule, Inst.baseRule, Inst.dirac]
  rw [hxy, hyx]
  simp [Inst.w, Inst.wt, hX, hY]

private theorem input_singleton_tree_edge_balance (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (σ : I.Assign) (X Y : I.S D a)
    (hX : X.1 = ⟨[], Inst.Base.inp σ⟩)
    (hY : Y.1 = ⟨[], Inst.Base.tree {a} σ⟩)
    (hbad : I.bad a σ) (hQ : I.Qv D σ = {a}) :
    I.w D a X * I.Pker D a X Y = I.w D a Y * I.Pker D a Y X := by
  have hXY : X ≠ Y := by
    intro h
    have hv := congrArg Subtype.val h
    rw [hX, hY] at hv
    cases hv
  have hxy : I.Pker D a X Y = (1 / 6 : ℝ) := by
    simp only [Inst.Pker, hXY, if_false, mul_zero, zero_add, hX, hY,
      Inst.stepRule, Inst.baseRule]
    simp [Inst.iRule, Inst.dirac, hbad, Inst.expL]
  have hyx : I.Pker D a Y X = (1 / 6 : ℝ) := by
    simp only [Inst.Pker, Ne.symm hXY, if_false, mul_zero, zero_add, hX, hY,
      Inst.stepRule, Inst.baseRule, hQ, if_true]
    simp [Inst.dirac]
  rw [hxy, hyx]
  simp [Inst.w, Inst.wt, hX, hY]

private theorem input_Q_singleton (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (σ : I.Assign) (hgood : σ ∈ I.Good (D.erase a)) (hbad : I.bad a σ) :
    I.Qv D σ = {a} := by
  have hs : ∀ b ∈ D.erase a, ¬ I.bad b σ := (Finset.mem_filter.mp hgood).2
  ext b
  simp only [Inst.Qv, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hb, hbadb⟩
    by_contra hne
    exact hs b (Finset.mem_erase.mpr ⟨hne, hb⟩) hbadb
  · intro he
    subst b
    exact ⟨ha,hbad⟩

theorem solution (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (σ : I.Assign) (hgood : σ ∈ I.Good (D.erase a))
    (X : I.S D a) (hX : X.1 = ⟨[], Inst.Base.inp σ⟩) :
    (¬ I.bad a σ → ∀ Y : I.S D a, Y.1 = ⟨[], Inst.Base.out σ⟩ →
      I.w D a X * I.Pker D a X Y = I.w D a Y * I.Pker D a Y X) ∧
    (I.bad a σ → ∀ Y : I.S D a, Y.1 = ⟨[], Inst.Base.tree {a} σ⟩ →
      I.w D a X * I.Pker D a X Y = I.w D a Y * I.Pker D a Y X) := by
  constructor
  · intro hbad Y hY
    exact input_output_edge_balance I D a σ X Y hX hY hbad
  · intro hbad Y hY
    exact input_singleton_tree_edge_balance I D a σ X Y hX hY hbad
      (input_Q_singleton I D a ha σ hgood hbad)
