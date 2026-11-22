-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.prefix_of_matched
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:32:14.057253+00:00
-- url     : https://prove2.me/submissions/c868595b-2953-4fd4-b9ad-3ce8dea9dc7a

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Theorems.Thm_DeciSigma1_Holes_Fresh_StrictlySeparated_ne_right
public import Theorems.Thm_DeciSigma1_Holes_Fresh_retained_of_mem_sites
public import Theorems.Thm_DeciSigma1_Holes_Fresh_retained_length
public import Theorems.Thm_DeciSigma1_Holes_Fresh_greatestPreimage_site
public import Theorems.Thm_DeciSigma1_Holes_Fresh_take_drop_deleteSites
public import Theorems.Thm_DeciSigma1_Holes_Fresh_greatestPreimage_add_eq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_drop_eq_take_append_site
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_sitePositions
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_length
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks
attribute [local simp] DeciSigma1.Holes.Fresh.length_upperSeq
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} {δ : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (hδ : 0 < δ) {F x y : List α} {cx cy : Finset ℕ}
    (hsx : StrictlySeparated δ cx) (hsy : StrictlySeparated δ cy)
    (hx : ∀ c ∈ cx, c + δ < x.length ∧ (x.drop c).take δ = F)
    (hy : ∀ c ∈ cy, c + δ < y.length ∧ (y.drop c).take δ = F) :
    ∀ L a b, (deletePositions y (sitePositions δ cy)).length = b + L →
      (deletePositions y (sitePositions δ cy)).drop b <+:
        (deletePositions x (sitePositions δ cx)).drop a →
      (∀ d, 0 < d → d < L → (IsJunction δ cx (a + d) ↔ IsJunction δ cy (b + d))) →
      y.drop (greatestPreimage (sitePositions δ cy) b) <+:
          x.drop (greatestPreimage (sitePositions δ cx) a) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro a b hL hpre hm
  obtain ⟨r, hr⟩ := hpre
  have hlenb : ((deletePositions y (sitePositions δ cy)).drop b).length = L := by simp; omega
  by_cases hex : ∃ d, 0 < d ∧ d < L ∧ IsJunction δ cy (b + d)
  · classical
    have hd0 := (Nat.find_spec hex).1
    have hdL := (Nat.find_spec hex).2.1
    have hdJ := (Nat.find_spec hex).2.2
    set d₁ := Nat.find hex with hd₁
    have hmin : ∀ d, 0 < d → d < d₁ → ¬ IsJunction δ cy (b + d) :=
      fun d h1 h2 h3 => Nat.find_min hex h2 ⟨h1, by omega, h3⟩
    have hfy : ∀ J, IsJunction δ cy J → ¬ (b < J ∧ J < b + d₁) := by
      rintro J hJ ⟨h1, h2⟩
      exact hmin (J - b) (by omega) (by omega) (by rwa [Nat.add_sub_cancel' h1.le])
    have hfx : ∀ J, IsJunction δ cx J → ¬ (a < J ∧ J < a + d₁) := by
      rintro J hJ ⟨h1, h2⟩
      have := (hm (J - a) (by omega) (by omega)).mp (by rwa [Nat.add_sub_cancel' h1.le])
      exact hmin (J - a) (by omega) (by omega) this
    obtain ⟨cT, hcT, hcTe⟩ := hdJ
    obtain ⟨cH, hcH, hcHe⟩ := (hm d₁ hd0 hdL).mpr ⟨cT, hcT, hcTe⟩
    have ky := greatestPreimage_add_eq hd0 hfy (retained_of_mem_sites hsy hcT)
      (fun c hc => hsy.ne_right hδ hcT hc) hcTe
    have kx := greatestPreimage_add_eq hd0 hfx (retained_of_mem_sites hsx hcH)
      (fun c hc => hsx.ne_right hδ hcH hc) hcHe
    have jy := greatestPreimage_site hsy hcT
    have jx := greatestPreimage_site hsx hcH
    rw [hcTe] at jy
    rw [hcHe] at jx
    have hP : ((deletePositions y (sitePositions δ cy)).drop b).take d₁ =
        ((deletePositions x (sitePositions δ cx)).drop a).take d₁ := by
      rw [← hr, List.take_append_of_le_length (by omega)]
    have eqy : y.drop (greatestPreimage (sitePositions δ cy) b) =
        ((deletePositions y (sitePositions δ cy)).drop b).take d₁ ++
          (F ++ y.drop (greatestPreimage (sitePositions δ cy) (b + d₁))) := by
      rw [take_drop_deleteSites y hfy, jy]
      exact drop_eq_take_append_site ky (hy cT hcT).2
    have eqx : x.drop (greatestPreimage (sitePositions δ cx) a) =
        ((deletePositions x (sitePositions δ cx)).drop a).take d₁ ++
          (F ++ x.drop (greatestPreimage (sitePositions δ cx) (a + d₁))) := by
      rw [take_drop_deleteSites x hfx, jx]
      exact drop_eq_take_append_site kx (hx cH hcH).2
    have hpre' : (deletePositions y (sitePositions δ cy)).drop (b + d₁) <+:
        (deletePositions x (sitePositions δ cx)).drop (a + d₁) := by
      rw [← List.drop_drop, ← List.drop_drop, ← hr, List.drop_append_of_le_length (by omega)]
      exact List.prefix_append _ _
    have ih' := ih (L - d₁) (by omega) (a + d₁) (b + d₁) (by omega) hpre' (fun d h1 h2 => by
      have := hm (d₁ + d) (by omega) (by omega)
      rwa [← Nat.add_assoc, ← Nat.add_assoc] at this)
    rw [eqy, eqx, hP]
    exact (List.prefix_append_right_inj _).mpr ((List.prefix_append_right_inj _).mpr ih')
  · have hfy : ∀ J, IsJunction δ cy J → ¬ (b < J ∧ J < b + L) := by
      rintro J hJ ⟨h1, h2⟩
      exact hex ⟨J - b, by omega, by omega, by rwa [Nat.add_sub_cancel' h1.le]⟩
    have hfx : ∀ J, IsJunction δ cx J → ¬ (a < J ∧ J < a + L) := by
      rintro J hJ ⟨h1, h2⟩
      have := (hm (J - a) (by omega) (by omega)).mp (by rwa [Nat.add_sub_cancel' h1.le])
      exact hex ⟨J - a, by omega, by omega, this⟩
    have hyl : y.length ∉ (sitePositions δ cy) := fun h => by
      obtain ⟨c, hc, h1, h2⟩ := mem_sitePositions.mp h
      have := (hy c hc).1; omega
    have hyy : y.drop (greatestPreimage (sitePositions δ cy) b) =
        (deletePositions y (sitePositions δ cy)).drop b := by
      rcases Nat.eq_zero_or_pos L with hL0 | hLpos
      · have hb : b = (deletePositions y (sitePositions δ cy)).length := by omega
        rw [hb, greatestPreimage_length y hyl, List.drop_length, List.drop_length]
      · have ky := greatestPreimage_add_eq hLpos hfy
          (retained_length fun c hc => (hy c hc).1.le)
          (fun c hc he => by have := (hy c hc).1; omega)
          (by rw [← hL, length_deletePositions])
        have h1 := take_drop_deleteSites y hfy
        rw [List.take_of_length_le (by omega),
          List.take_of_length_le (by simp; omega)] at h1
        exact h1.symm
    have : (deletePositions y (sitePositions δ cy)).drop b =
        ((deletePositions x (sitePositions δ cx)).drop a).take L := by
      rw [← hr, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    rw [hyy, this, take_drop_deleteSites x hfx]
    exact List.take_prefix _ _
end DeciSigma1.Holes.Fresh
