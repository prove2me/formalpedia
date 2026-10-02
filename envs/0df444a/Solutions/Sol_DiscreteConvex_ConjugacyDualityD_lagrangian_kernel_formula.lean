-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityD.lagrangian_kernel_formula
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:41:04.50034+00:00
-- url     : https://prove2.me/submissions/01a9fc2c-bf8c-4a80-bcf7-e88d94980cca

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IndicatorWT
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ConvexConjE
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_KR

set_option autoImplicit false

universe u

open Classical in
open DiscreteConvex.ConjugacyDualityD in
theorem lkf4d_elemL {V : Type u} [Fintype V] [DecidableEq V]
    (c : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (x y u : V → ℤ) (a : ℝ) (hca : c x = (a : WithTop ℝ)) :
    ToEReal (Fr c (fun _ => (0 : WithTop ℝ)) B x u) + ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal) =
      if (fun v => x v + u v) ∈ B then ((a + ∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal) else ⊤ := by
  unfold Fr F0 IndicatorWT
  rw [hca]
  split_ifs with h
  · simp only [add_zero]
    show ((a : EReal)) + _ = _
    rw [EReal.coe_add]
  · show ((⊤ : EReal)) + _ = _
    exact EReal.top_add_coe _

open Classical in
open DiscreteConvex.ConjugacyDualityD in
theorem lkf4d_elemT {V : Type u} [Fintype V] [DecidableEq V]
    (B : Set (V → ℤ)) (y z : V → ℤ) :
    ((∑ i, ((fun v => -y v) i : ℝ) * (z i : ℝ) : ℝ) : EReal) - ToEReal (IndicatorWT B z) =
      if z ∈ B then ((∑ i, ((fun v => -y v) i : ℝ) * (z i : ℝ) : ℝ) : EReal) else ⊥ := by
  unfold IndicatorWT
  split_ifs with h
  · show _ - ((0 : ℝ) : EReal) = _
    rw [← EReal.coe_sub, sub_zero]
  · show _ - (⊤ : EReal) = _
    exact EReal.sub_top _

open Classical in
open DiscreteConvex.ConjugacyDualityD in
theorem solution {V : Type u} [Fintype V] [DecidableEq V] (c : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (x y : V → ℤ)
    (hx : x ∈ DomZ c) :
    KR c (fun _ => (0 : WithTop ℝ)) B x y =
      ToEReal (c x) - ((∑ i, (x i : ℝ) * (y i : ℝ) : ℝ) : EReal) -
        ConvexConjE (fun z => ToEReal (IndicatorWT B z)) (fun v => -y v) := by
  have hx' : c x ≠ ⊤ := hx
  obtain ⟨a, hca⟩ := WithTop.ne_top_iff_exists.mp hx'
  rw [← hca]
  set C : ℝ := a - ∑ i, (x i : ℝ) * (y i : ℝ) with hC
  have hR1 : ToEReal ((a : WithTop ℝ)) - ((∑ i, (x i : ℝ) * (y i : ℝ) : ℝ) : EReal) = (C : EReal) := by
    show (a : EReal) - _ = _
    rw [← EReal.coe_sub]
  rw [hR1]
  -- key identity: for z ∈ B, the L-element at u = z - x equals C - T-element
  have hkey : ∀ z : V → ℤ, (C : EReal) - ((∑ i, ((fun v => -y v) i : ℝ) * (z i : ℝ) : ℝ) : EReal) =
      ((a + ∑ i, ((z i - x i : ℤ) : ℝ) * (y i : ℝ) : ℝ) : EReal) := by
    intro z
    rw [← EReal.coe_sub]
    congr 1
    have hs : ∀ w : V → ℤ, ∑ i, ((y i : ℤ) : ℝ) * (w i : ℝ) = ∑ i, (w i : ℝ) * (y i : ℝ) :=
      fun w => Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    simp only [hC, Int.cast_sub, Int.cast_neg, sub_mul, neg_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    rw [hs z]
    ring
  unfold KR ConvexConjE
  apply le_antisymm
  · -- LHS ≤ RHS
    set L := sInf {t : EReal | ∃ u : V → ℤ,
      t = ToEReal (Fr c (fun _ => (0 : WithTop ℝ)) B x u) + ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal)} with hL
    have hLz : ∀ z ∈ B, L ≤ ((a + ∑ i, ((z i - x i : ℤ) : ℝ) * (y i : ℝ) : ℝ) : EReal) := by
      intro z hz
      apply sInf_le
      refine ⟨fun v => z v - x v, ?_⟩
      rw [lkf4d_elemL c B x y _ a hca.symm]
      have : (fun v => x v + (z v - x v)) = z := by funext v; ring
      rw [if_pos (by rw [this]; exact hz)]
    by_cases h1 : L = ⊥
    · rw [h1]; exact bot_le
    by_cases h2 : L = ⊤
    · -- B must be empty
      have hB : ∀ z, z ∉ B := by
        intro z hz
        have := hLz z hz
        rw [h2] at this
        exact absurd this (not_le.mpr (EReal.coe_lt_top _))
      have hS : sSup {t : EReal | ∃ z : V → ℤ, t = ((∑ i, ((fun v => -y v) i : ℝ) * (z i : ℝ) : ℝ) : EReal)
          - (fun z => ToEReal (IndicatorWT B z)) z} = ⊥ := by
        rw [sSup_eq_bot]
        rintro t ⟨z, rfl⟩
        rw [lkf4d_elemT B y z, if_neg (hB z)]
      rw [hS, EReal.sub_bot (EReal.coe_ne_bot C)]
      exact le_top
    · set l : ℝ := L.toReal
      have hl : (l : EReal) = L := EReal.coe_toReal h2 h1
      rw [← hl]
      have hS : sSup {t : EReal | ∃ z : V → ℤ, t = ((∑ i, ((fun v => -y v) i : ℝ) * (z i : ℝ) : ℝ) : EReal)
          - (fun z => ToEReal (IndicatorWT B z)) z} ≤ ((C - l : ℝ) : EReal) := by
        apply sSup_le
        rintro t ⟨z, rfl⟩
        show _ - ToEReal (IndicatorWT B z) ≤ _
        rw [lkf4d_elemT B y z]
        split_ifs with hz
        · have h3 := hLz z hz
          rw [← hl, ← hkey z] at h3
          rw [EReal.coe_sub]
          have h4 := EReal.sub_le_sub (le_refl (C : EReal)) h3
          -- h4 : C - (C - T) ≤ C - l
          have e : (C : EReal) - ((C : EReal) - ((∑ i, ((fun v => -y v) i : ℝ) * (z i : ℝ) : ℝ) : EReal)) =
              ((∑ i, ((fun v => -y v) i : ℝ) * (z i : ℝ) : ℝ) : EReal) := by
            rw [← EReal.coe_sub, ← EReal.coe_sub]; congr 1; ring
          rw [e] at h4
          exact h4
        · exact bot_le
      have h5 := EReal.sub_le_sub (le_refl (C : EReal)) hS
      have e : (C : EReal) - ((C - l : ℝ) : EReal) = (l : EReal) := by
        rw [← EReal.coe_sub]; congr 1; ring
      rw [e] at h5
      exact h5
  · -- RHS ≤ LHS
    apply le_sInf
    rintro t ⟨u, rfl⟩
    rw [lkf4d_elemL c B x y u a hca.symm]
    split_ifs with hu
    · set z : V → ℤ := fun v => x v + u v
      have hT : ((∑ i, ((fun v => -y v) i : ℝ) * (z i : ℝ) : ℝ) : EReal) ≤
          sSup {t : EReal | ∃ z : V → ℤ, t = ((∑ i, ((fun v => -y v) i : ℝ) * (z i : ℝ) : ℝ) : EReal)
            - (fun z => ToEReal (IndicatorWT B z)) z} := by
        apply le_sSup
        refine ⟨z, ?_⟩
        show _ = _ - ToEReal (IndicatorWT B z)
        rw [lkf4d_elemT B y z, if_pos hu]
      have h5 := EReal.sub_le_sub (le_refl (C : EReal)) hT
      rw [hkey z] at h5
      have e : (∑ i, ((z i - x i : ℤ) : ℝ) * (y i : ℝ)) = ∑ i, (u i : ℝ) * (y i : ℝ) := by
        apply Finset.sum_congr rfl; intro i _; simp [z]
      rw [e] at h5
      exact h5
    · exact le_top
