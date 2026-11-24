-- Prove2me | solution 1 for BondySimonovits.exists_mixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:04:19.294919+00:00
-- url     : https://prove2.me/submissions/6fa452f6-acf7-4a57-9505-ae7629425e61

module
public import Definitions.Def_BondySimonovitsLib_BSLayers
public import Definitions.Def_BondySimonovitsLib_BSCycle

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V) [DecidableRel K.Adj]
namespace BondySimonovits
theorem _root_.solution (lev : V → ℕ) (i D : ℕ) (Y : Finset V)
    (hYlev : ∀ v ∈ Y, lev v = i ∨ lev v = i + 1)
    (hYadj : ∀ u ∈ Y, ∀ v ∈ Y, K.Adj u v → lev u ≠ lev v)
    (hmin : ∀ Y' ⊆ Y, Y'.Nonempty → (∀ u ∈ Y', D ≤ (Y'.filter (K.Adj u)).card) → Y' = Y)
    (hdeg : ∀ u ∈ Y, D ≤ (Y.filter (K.Adj u)).card)
    (χ : V → Prop) (s0 s1 : V) (hs0 : s0 ∈ Y ∧ lev s0 = i) (hs1 : s1 ∈ Y ∧ lev s1 = i)
    (hχ0 : χ s0) (hχ1 : ¬ χ s1) :
    ∃ w ∈ Y, ∃ a b, (a ∈ Y ∧ lev a = i) ∧ (b ∈ Y ∧ lev b = i) ∧ K.Adj w a ∧ K.Adj w b ∧
      χ a ∧ ¬ χ b := by
  classical
  by_contra hno
  have nomix : ∀ w ∈ Y, ∀ a b, (a ∈ Y ∧ lev a = i) → (b ∈ Y ∧ lev b = i) → K.Adj w a →
      K.Adj w b → χ a → χ b := by
    intro w hw a b ha hb hwa hwb hχa
    by_contra hχb
    exact hno ⟨w, hw, a, b, ha, hb, hwa, hwb, hχa, hχb⟩
  set Y' := Y.filter (fun v => ∃ u, (u ∈ Y ∧ lev u = i) ∧ χ u ∧ (u = v ∨ K.Adj v u)) with hY'
  have hsub : Y' ⊆ Y := Finset.filter_subset _ _
  have hne : Y'.Nonempty := ⟨s0, Finset.mem_filter.2 ⟨hs0.1, s0, hs0, hχ0, Or.inl rfl⟩⟩
  have hdeg' : ∀ u ∈ Y', D ≤ (Y'.filter (K.Adj u)).card := by
    intro v hv
    refine (hdeg v (hsub hv)).trans (Finset.card_le_card ?_)
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    refine ⟨Finset.mem_filter.2 ⟨hz.1, ?_⟩, hz.2⟩
    obtain ⟨hvY, u, hu, hχu, huv⟩ := Finset.mem_filter.1 hv
    rcases huv with rfl | hvu
    · exact ⟨u, hu, hχu, Or.inr hz.2.symm⟩
    · have hvl : lev v = i + 1 := by
        have := hYadj v hvY u hu.1 hvu
        rcases hYlev v hvY with h | h <;> omega
      have hzl : lev z = i := by
        have := hYadj v hvY z hz.1 hz.2
        rcases hYlev z hz.1 with h | h <;> omega
      exact ⟨z, ⟨hz.1, hzl⟩, nomix v hvY u z hu ⟨hz.1, hzl⟩ hvu hz.2 hχu, Or.inl rfl⟩
  have heq := hmin Y' hsub hne hdeg'
  have hs1' : s1 ∈ Y' := heq ▸ hs1.1
  obtain ⟨-, u, hu, hχu, hu1⟩ := Finset.mem_filter.1 hs1'
  rcases hu1 with rfl | h
  · exact hχ1 hχu
  · exact hYadj s1 hs1.1 u hu.1 h (by rw [hs1.2, hu.2])
end BondySimonovits
