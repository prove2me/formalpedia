-- Prove2me | solution 1 for DiscreteConvex.AlgorithmsC.extreme_base_bounded_by_eta
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T07:25:42.679987+00:00
-- url     : https://prove2.me/submissions/5a07430d-72e9-4196-94ea-cd5c97246def

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_Submodular
import Definitions.Def_DiscreteConvex_AlgorithmsC_RhoTilde
import Definitions.Def_DiscreteConvex_AlgorithmsC_ReachSet
import Definitions.Def_DiscreteConvex_AlgorithmsC_Eta

set_option autoImplicit false

open Classical in
open scoped Pointwise in
open DiscreteConvex.AlgorithmsC in
theorem gammaSet_inter_2438012f {V : Type*} [Fintype V] [DecidableEq V]
    {U : Type*} [DecidableEq U] (Gamma : U → Finset V)
    (hGammaDisj : ∀ u v : U, u ≠ v → Disjoint (Gamma u) (Gamma v)) (A B : Finset U) :
    GammaSet Gamma A ∩ GammaSet Gamma B = GammaSet Gamma (A ∩ B) := by
  ext v
  simp only [GammaSet, Finset.mem_inter, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨a, ha, hva⟩, ⟨b, hb, hvb⟩⟩
    have hab : a = b := by
      by_contra h
      exact Finset.disjoint_left.mp (hGammaDisj a b h) hva hvb
    subst hab
    exact ⟨a, ⟨ha, hb⟩, hva⟩
  · rintro ⟨a, ⟨ha, hb⟩, hva⟩
    exact ⟨⟨a, ha, hva⟩, ⟨a, hb, hva⟩⟩

open Classical in
open scoped Pointwise in
open DiscreteConvex.AlgorithmsC in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    (rho : Finset V → ℤ) (hrho : Submodular rho) (Gamma : U → Finset V) (Z : Finset V)
    (hGammaDisj : ∀ u v : U, u ≠ v → Disjoint (Gamma u) (Gamma v))
    (F : U → U → Prop) (u : U) (yu : ℤ) (Y : Finset U) (hY : ReachSet F u ⊆ Y)
    (hyu : yu = RhoTilde rho Gamma Z Y - RhoTilde rho Gamma Z (Y.erase u)) :
    (yu : ℝ) ≤ (Eta rho Gamma Z F : ℝ) := by
  set R := ReachSet F u with hRdef
  have hu : u ∈ R := by
    rw [hRdef, ReachSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩
  have hEta : RhoTilde rho Gamma Z R - RhoTilde rho Gamma Z (R.erase u) ≤ Eta rho Gamma Z F := by
    unfold Eta
    exact Finset.le_sup' (fun w => RhoTilde rho Gamma Z (ReachSet F w)
      - RhoTilde rho Gamma Z ((ReachSet F w).erase w)) (Finset.mem_univ u)
  have hsub := hrho.2 (GammaSet Gamma (Y.erase u) ∪ Z) (GammaSet Gamma R ∪ Z)
  have hYeq : Y.erase u ∪ R = Y := by
    ext w
    simp only [Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (⟨_, hw⟩ | hw)
      · exact hw
      · exact hY hw
    · intro hw
      by_cases h : w = u
      · subst h; exact Or.inr hu
      · exact Or.inl ⟨h, hw⟩
  have hIeq : Y.erase u ∩ R = R.erase u := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, hY h3⟩, h3⟩
  have hU : (GammaSet Gamma (Y.erase u) ∪ Z) ∪ (GammaSet Gamma R ∪ Z) = GammaSet Gamma Y ∪ Z := by
    have : GammaSet Gamma Y = GammaSet Gamma (Y.erase u) ∪ GammaSet Gamma R := by
      conv_lhs => rw [← hYeq]
      ext x
      simp only [GammaSet, Finset.mem_biUnion, Finset.mem_union]
      constructor
      · rintro ⟨a, ha | ha, hx⟩
        · exact Or.inl ⟨a, ha, hx⟩
        · exact Or.inr ⟨a, ha, hx⟩
      · rintro (⟨a, ha, hx⟩ | ⟨a, ha, hx⟩)
        · exact ⟨a, Or.inl ha, hx⟩
        · exact ⟨a, Or.inr ha, hx⟩
    rw [this]
    ext w
    simp only [Finset.mem_union]
    tauto
  have hI : (GammaSet Gamma (Y.erase u) ∪ Z) ∩ (GammaSet Gamma R ∪ Z)
      = GammaSet Gamma (R.erase u) ∪ Z := by
    rw [← hIeq, ← gammaSet_inter_2438012f Gamma hGammaDisj]
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  rw [hU, hI] at hsub
  have hint : yu ≤ Eta rho Gamma Z F := by
    rw [hyu]
    simp only [RhoTilde] at hEta ⊢
    linarith
  exact_mod_cast hint
