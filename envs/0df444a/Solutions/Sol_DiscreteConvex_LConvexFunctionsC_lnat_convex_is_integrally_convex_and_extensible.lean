-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsC.lnat_convex_is_integrally_convex_and_extensible
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:26:25.591926+00:00
-- url     : https://prove2.me/submissions/3b111388-b0f0-43bb-be9e-7f8998a6e0bf

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_ConvexExtensible
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IsIntegrallyConvexFunction
import Theorems.Thm_DiscreteConvex_ConjugacyDualityC_lnat2_convex_is_integrally_convex

open Classical
open scoped Pointwise
open DiscreteConvex.LConvexFunctionsC

variable {V : Type*} [Fintype V] [DecidableEq V]

private noncomputable def zeroInd : (V → ℤ) → WithTop ℝ :=
  fun p => if p = 0 then 0 else ⊤

private lemma zeroInd_lnatC : DiscreteConvex.ConjugacyDualityC.LNaturalConvex (zeroInd (V := V)) := by
  constructor
  · intro x y
    unfold DiscreteConvex.ConjugacyDualityC.LiftedFunctionL zeroInd
    by_cases hx : (fun v => x (some v) - x none) = 0
    · by_cases hy : (fun v => y (some v) - y none) = 0
      · have hsup : (fun v => (x ⊔ y) (some v) - (x ⊔ y) none) = 0 := by
          ext v
          have hxv : x (some v) = x none := sub_eq_zero.mp (congr_fun hx v)
          have hyv : y (some v) = y none := sub_eq_zero.mp (congr_fun hy v)
          simp [Pi.sup_apply, hxv, hyv]
        have hinf : (fun v => (x ⊓ y) (some v) - (x ⊓ y) none) = 0 := by
          ext v
          have hxv : x (some v) = x none := sub_eq_zero.mp (congr_fun hx v)
          have hyv : y (some v) = y none := sub_eq_zero.mp (congr_fun hy v)
          simp [Pi.inf_apply, hxv, hyv]
        simp only [hx, hy, hsup, hinf, ite_true, add_zero, le_rfl]
      · simp [hy]
    · simp [hx]
  · refine ⟨0, fun x => ?_⟩
    unfold DiscreteConvex.ConjugacyDualityC.LiftedFunctionL zeroInd
    have h1 : (fun v => (x + 1) (some v) - (x + 1) none) = (fun v => x (some v) - x none) := by
      ext v; simp [Pi.add_apply]
    rw [h1]
    simp

private lemma lnat_imp_ic (g : (V → ℤ) → WithTop ℝ) (hg : LNaturalConvex g) :
    IsIntegrallyConvexFunction g := by
  have hgC : DiscreteConvex.ConjugacyDualityC.LNaturalConvex g := hg
  have hIC : DiscreteConvex.ConjugacyDualityC.IsIntegrallyConvexFunction g := by
    apply DiscreteConvex.ConjugacyDualityC.lnat2_convex_is_integrally_convex.1
    refine ⟨g, zeroInd, hgC, zeroInd_lnatC, ?_, ?_⟩
    · intro p
      have hle : DiscreteConvex.ConjugacyDualityC.ToEReal (g p) ≤
          DiscreteConvex.ConjugacyDualityC.InfConvE g zeroInd p := by
        apply le_sInf
        rintro L ⟨p1, p2, rfl, rfl⟩
        by_cases hp2 : p2 = 0
        · subst hp2
          have h0 : DiscreteConvex.ConjugacyDualityC.ToEReal (zeroInd (0 : V → ℤ)) = 0 := by
            dsimp [DiscreteConvex.ConjugacyDualityC.ToEReal, zeroInd]
            rw [if_pos rfl]
            rfl
          rw [add_zero, h0, add_zero]
        · have htop : DiscreteConvex.ConjugacyDualityC.ToEReal (zeroInd p2) = ⊤ := by
            dsimp [DiscreteConvex.ConjugacyDualityC.ToEReal, zeroInd]
            rw [if_neg hp2]
            rfl
          rw [htop]
          cases gp1 : g p1 with
          | top =>
            change DiscreteConvex.ConjugacyDualityC.ToEReal (g (p1 + p2)) ≤ (⊤ : EReal) + ⊤
            rw [EReal.top_add_top]
            exact le_top
          | coe a =>
            change DiscreteConvex.ConjugacyDualityC.ToEReal (g (p1 + p2)) ≤ (a : EReal) + ⊤
            rw [EReal.coe_add_top]
            exact le_top
      intro hbot
      rw [hbot] at hle
      have hne : DiscreteConvex.ConjugacyDualityC.ToEReal (g p) ≠ ⊥ := WithBot.coe_ne_bot
      exact hne (le_bot_iff.mp hle)
    · ext p
      unfold DiscreteConvex.ConjugacyDualityC.InfConv
      symm
      apply IsLeast.csInf_eq
      constructor
      · refine ⟨p, 0, by simp, ?_⟩
        simp [zeroInd]
      · rintro L ⟨p1, p2, rfl, rfl⟩
        by_cases hp2 : p2 = 0
        · subst hp2
          simp [zeroInd]
        · simp [zeroInd, hp2]
  exact hIC

theorem solution (g : (V → ℤ) → WithTop ℝ)
    (hg : LNaturalConvex g) :
    IsIntegrallyConvexFunction g ∧ ConvexExtensible g := by
  have hIC : IsIntegrallyConvexFunction g := lnat_imp_ic g hg
  refine ⟨hIC, fun p => ?_⟩
  let x : V → ℝ := fun v => (p v : ℝ)
  have hIC_x := hIC x
  let S₀ := Finset.filter (fun y => y ∈ DomZ g) (IntegralNeighborhoodFinset x)
  change ConvexClosureVal g x = ConvexClosureValOn g S₀ x at hIC_x
  rw [hIC_x]
  have hN : IntegralNeighborhoodFinset x = {p} := by
    ext y
    simp only [IntegralNeighborhoodFinset,
      Fintype.mem_piFinset, Finset.mem_Icc, x, Int.floor_intCast, Int.ceil_intCast,
      Finset.mem_singleton, funext_iff]
    constructor
    · intro h v; have := h v; omega
    · intro h v; have := h v; omega
  by_cases hp : g p = ⊤
  · have hS₀ : S₀ = ∅ := by
      dsimp [S₀]
      rw [hN, Finset.filter_singleton, if_neg]
      simp [DomZ, hp]
    rw [hS₀]
    unfold ConvexClosureValOn
    have hemp : {L : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
        (∀ y ∈ (∅ : Finset (V → ℤ)), 0 ≤ lam y) ∧
        (∑ y ∈ (∅ : Finset (V → ℤ)), lam y = 1) ∧
        (∀ y ∈ (∅ : Finset (V → ℤ)), y ∈ DomZ g) ∧
        (∀ v, ∑ y ∈ (∅ : Finset (V → ℤ)), lam y * (y v : ℝ) = x v) ∧
        L = ((∑ y ∈ (∅ : Finset (V → ℤ)), lam y * (g y).untopD 0 : ℝ) : WithTop ℝ)} = ∅ := by
      ext L
      simp
    rw [hemp, hp]
    change (if (∅ : Set (WithTop ℝ)) ⊆ {⊤} ∨ ¬BddBelow ∅ then ⊤ else _) = ⊤
    exact if_pos (Or.inl (Set.empty_subset _))
  · have hS₀ : S₀ = {p} := by
      dsimp [S₀]
      rw [hN, Finset.filter_singleton, if_pos]
      exact hp
    rw [hS₀]
    unfold ConvexClosureValOn
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hp
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨fun _ => 1, ?_, ?_, ?_, ?_, ?_⟩
      · intro y _; norm_num
      · simp
      · intro y hy; rw [Finset.mem_singleton.mp hy]; exact hp
      · intro v; simp [x]
      · simp [← hr]
    · rintro L ⟨lam, _, h1, _, _, rfl⟩
      rw [Finset.sum_singleton] at h1
      simp [h1, ← hr]
