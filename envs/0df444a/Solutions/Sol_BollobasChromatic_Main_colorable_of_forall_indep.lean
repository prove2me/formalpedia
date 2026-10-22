-- Prove2me | solution 1 for BollobasChromatic.Main.colorable_of_forall_indep
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:49:23.145005+00:00
-- url     : https://prove2.me/submissions/df857fc2-94e3-4b8a-9559-2a1de180d403

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting

set_option autoImplicit false
open Filter Topology Asymptotics
open BollobasChromatic.Main

theorem solution (n : ℕ) (G : SimpleGraph (Fin n)) (s n1 : ℕ) (hs : 1 ≤ s)
    (hind : ∀ S : Finset (Fin n), S.card = n1 → ∃ T ⊆ S, G.IsNIndepSet s T) :
    G.Colorable (n / s + n1) := by
  classical
  have key : ∀ k : ℕ, ∀ R : Finset (Fin n), R.card = k →
      ∃ f : Fin n → ℕ, (∀ x ∈ R, ∀ y ∈ R, G.Adj x y → f x ≠ f y) ∧
        ∀ x ∈ R, f x < R.card / s + n1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro R hR
      by_cases hsmall : R.card < n1
      · refine ⟨fun x => if h : x ∈ R then (R.equivFin ⟨x, h⟩ : ℕ) else 0, ?_, ?_⟩
        · intro x hx y hy hxy heq
          simp only [dif_pos hx, dif_pos hy] at heq
          have := R.equivFin.injective (Fin.ext heq)
          have hxy' : x = y := congrArg Subtype.val this
          exact G.loopless.irrefl _ (hxy' ▸ hxy)
        · intro x hx
          simp only [dif_pos hx]
          have := (R.equivFin ⟨x, hx⟩).isLt
          have h0 : 0 ≤ R.card / s := Nat.zero_le _
          omega
      · have hsmall' : n1 ≤ R.card := not_lt.mp hsmall
        obtain ⟨S, hSR, hSc⟩ := Finset.exists_subset_card_eq hsmall'
        obtain ⟨T, hTS, hT⟩ := hind S hSc
        have hTR : T ⊆ R := hTS.trans hSR
        have hTc : T.card = s := hT.card_eq
        have hsR : s ≤ R.card := by rw [← hTc]; exact Finset.card_le_card hTR
        have hR'c : (R \ T).card = R.card - s := by
          rw [Finset.card_sdiff_of_subset hTR, hTc]
        obtain ⟨f', hf'1, hf'2⟩ := ih (R.card - s) (by omega) (R \ T) hR'c
        have hdiv : R.card / s = (R.card - s) / s + 1 := by
          have : R.card = (R.card - s) + s := by omega
          conv_lhs => rw [this]
          exact Nat.add_div_right _ (by omega)
        refine ⟨fun x => if x ∈ T then (R.card - s) / s + n1 else f' x, ?_, ?_⟩
        · intro x hx y hy hxy
          by_cases hxT : x ∈ T <;> by_cases hyT : y ∈ T
          · exfalso
            have := hT.isIndepSet hxT hyT (G.ne_of_adj hxy)
            exact this hxy
          · have hy' : y ∈ R \ T := Finset.mem_sdiff.mpr ⟨hy, hyT⟩
            have := hf'2 y hy'
            rw [hR'c] at this
            simp only [hxT, hyT, if_true, if_false]
            omega
          · have hx' : x ∈ R \ T := Finset.mem_sdiff.mpr ⟨hx, hxT⟩
            have := hf'2 x hx'
            rw [hR'c] at this
            simp only [hxT, hyT, if_true, if_false]
            omega
          · have hx' : x ∈ R \ T := Finset.mem_sdiff.mpr ⟨hx, hxT⟩
            have hy' : y ∈ R \ T := Finset.mem_sdiff.mpr ⟨hy, hyT⟩
            simp only [hxT, hyT, if_false]
            exact hf'1 x hx' y hy' hxy
        · intro x hx
          by_cases hxT : x ∈ T
          · simp only [hxT, if_true]
            omega
          · have hx' : x ∈ R \ T := Finset.mem_sdiff.mpr ⟨hx, hxT⟩
            have := hf'2 x hx'
            rw [hR'c] at this
            simp only [hxT, if_false]
            omega
  obtain ⟨f, hf1, hf2⟩ := key n Finset.univ (by simp)
  rw [Finset.card_univ, Fintype.card_fin] at hf2
  rw [SimpleGraph.colorable_iff_exists_bdd_nat_coloring]
  exact ⟨SimpleGraph.Coloring.mk f (fun {x y} h => hf1 x (Finset.mem_univ _) y (Finset.mem_univ _) h),
    fun x => hf2 x (Finset.mem_univ _)⟩

