-- Prove2me | solution 1 for Erdos1219.no_good_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:46:29.915794+00:00
-- url     : https://prove2.me/submissions/19ae3254-b448-45c4-a571-482653955191

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Theorems.Thm_Erdos1219_not_good_unfold
import Theorems.Thm_Erdos1219_exists_large_fibre

set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {W : Type u} [LinearOrder W] [WellFoundedLT W]
namespace Erdos1219
theorem _root_.solution {f : W → W → Bool} (hf : ∀ x y, f x y = f y x) {c : Bool}
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hW : #W = Order.succ (2 ^ μ)) (hord : ord #W = typeLT W)
    (hno : ∀ α, ¬ IsGood f c μ α) : ∃ H : Set W, #H = #W ∧ Homog f c H := by
  have h2μ : ℵ₀ ≤ 2 ^ μ := hμ.trans (cantor μ).le
  have hreg : Cardinal.IsRegular #W := by rw [hW]; exact isRegular_succ h2μ
  have hℵW : ℵ₀ ≤ #W := hreg.aleph0_le
  have hchoice : ∀ α : W, ∃ (Z : Set W) (δ : W), α ∈ bigCof μ →
      (Z ⊆ nbr f c α ∧ Homog f (!c) Z ∧ #Z ≤ μ ∧ δ < α ∧ Z ⊆ Iio δ ∧
        nbr f c α ∩ common f c Z ⊆ Iio δ) := by
    intro α
    by_cases hα : α ∈ bigCof μ
    · obtain ⟨Z, δ, hZδ⟩ := not_good_unfold hα (hno α)
      exact ⟨Z, δ, fun _ => hZδ⟩
    · exact ⟨∅, α, fun h => absurd h hα⟩
  choose Z δ hZδ using hchoice
  obtain ⟨δ₀, hδ₀⟩ := exists_large_fibre hμ hW hord δ fun α hα => (hZδ α hα).2.2.2.1
  -- Claim B: pigeonhole on the map `α ↦ Z α`
  have hTcard : #{t : Set W // t ⊆ Iio δ₀ ∧ #t ≤ μ} < (#W).ord.cof := by
    rw [hreg.cof_ord]
    refine (mk_bounded_subset_le (Iio δ₀) μ).trans_lt ?_
    have hIio : #(Iio δ₀) ≤ 2 ^ μ := by
      rw [← Order.lt_succ_iff, ← hW]
      exact mk_Iio_lt δ₀ hord
    calc max #(Iio δ₀) ℵ₀ ^ μ ≤ (2 ^ μ) ^ μ := power_le_power_right (max_le hIio h2μ)
      _ = 2 ^ μ := by rw [← power_mul, mul_eq_self hμ]
      _ < #W := by rw [hW]; exact Order.lt_succ _
  let φ : {α | α ∈ bigCof μ ∧ δ α = δ₀} → {t : Set W // t ⊆ Iio δ₀ ∧ #t ≤ μ} := fun α =>
    ⟨Z α, by
      have h := hZδ α.1 α.2.1
      refine ⟨h.2.2.2.2.1.trans ?_, h.2.2.1⟩
      rw [α.2.2]⟩
  obtain ⟨Z₀, t, htF, htcard, hφ⟩ := infinite_pigeonhole_set φ #W hδ₀ hℵW hTcard
  have htZ : ∀ x ∈ t, Z x = Z₀.1 := fun x hx => congrArg Subtype.val (hφ hx)
  have htW : #t = #W := le_antisymm (mk_set_le t) htcard
  -- Claim C: remove the points `≤ δ₀`
  refine ⟨t \ Iic δ₀, ?_, ?_⟩
  · have h1 : t.Infinite := infinite_coe_iff.1 (infinite_iff.2 (hℵW.trans htcard))
    have h2 : #(Iic δ₀) < #t := by rw [htW]; exact mk_Iic_lt δ₀ hord hℵW
    have hsdiff : #(t \ Iic δ₀ : Set W) = #t := by
      refine le_antisymm (mk_le_mk_of_subset Set.diff_subset) ?_
      by_contra hlt
      have hlt' : #(t \ Iic δ₀ : Set W) < #t := lt_of_not_ge hlt
      have hcov : t ⊆ (t \ Iic δ₀) ∪ Iic δ₀ := fun x hx =>
        if h : x ∈ Iic δ₀ then Or.inr h else Or.inl ⟨hx, h⟩
      have hle : #t ≤ #(t \ Iic δ₀ : Set W) + #(Iic δ₀) :=
        (mk_le_mk_of_subset hcov).trans (mk_union_le _ _)
      exact not_lt_of_ge hle (add_lt_of_lt (hℵW.trans htcard) hlt' h2)
    rw [hsdiff, htW]
  · have hbool : ∀ b d : Bool, ¬ b = d → b = !d := by decide
    have key : ∀ a ∈ t \ Iic δ₀, ∀ a' ∈ t \ Iic δ₀, a < a' → f a a' = c := by
      intro a ha a' ha' hlt
      have haF := htF ha.1
      have ha'F := htF ha'.1
      have hZa := hZδ a haF.1
      have hZa' := hZδ a' ha'F.1
      have haD : a ∈ common f c (Z a') := by
        intro z hz
        rw [htZ a' ha'.1, ← htZ a ha.1] at hz
        exact (hZa.1 hz).2
      by_contra hne
      have hmem : a ∈ nbr f c a' ∩ common f c (Z a') := ⟨⟨hlt, hbool _ _ hne⟩, haD⟩
      have hlt' := hZa'.2.2.2.2.2 hmem
      rw [ha'F.2] at hlt'
      exact ha.2 (le_of_lt hlt')
    intro a ha a' ha' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key a ha a' ha' h
    · rw [hf]; exact key a' ha' a ha h
end Erdos1219
