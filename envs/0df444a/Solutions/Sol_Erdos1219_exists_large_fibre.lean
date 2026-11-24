-- Prove2me | solution 1 for Erdos1219.exists_large_fibre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:45:55.164778+00:00
-- url     : https://prove2.me/submissions/95daf515-884a-4207-988e-30b4150bb207

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Theorems.Thm_Erdos1219_exists_forall_lt_of_mk_lt
import Theorems.Thm_Erdos1219_exists_gt_of_regular
import Theorems.Thm_Erdos1219_exists_seq

set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {W : Type u} [LinearOrder W] [WellFoundedLT W]
namespace Erdos1219
theorem _root_.solution {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hW : #W = Order.succ (2 ^ μ)) (hord : ord #W = typeLT W)
    (δ : W → W) (hδ : ∀ α ∈ bigCof μ, δ α < α) :
    ∃ δ₀, #W ≤ #{α | α ∈ bigCof μ ∧ δ α = δ₀} := by
  have h2μ : ℵ₀ ≤ 2 ^ μ := hμ.trans (cantor μ).le
  have hreg : Cardinal.IsRegular #W := by rw [hW]; exact isRegular_succ h2μ
  have hℵW : ℵ₀ ≤ #W := hreg.aleph0_le
  by_contra hcon
  push Not at hcon
  -- strict bounds for the (small) fibres
  choose g hg using fun δ₀ => exists_forall_lt_of_mk_lt hreg hord (hcon δ₀)
  -- the closure step `h`
  have hstep : ∀ x : W, #(insert x (g '' Iic x) : Set W) < #W := by
    intro x
    calc #(insert x (g '' Iic x) : Set W) ≤ #(g '' Iic x) + 1 := mk_insert_le
      _ ≤ #(Iic x) + 1 := add_le_add mk_image_le le_rfl
      _ < #W := add_lt_of_lt hℵW (mk_Iic_lt x hord hℵW) (one_lt_aleph0.trans_le hℵW)
  choose h hh using fun x => exists_forall_lt_of_mk_lt hreg hord (hstep x)
  have hxh : ∀ x, x < h x := fun x => hh x x (mem_insert x _)
  have hgh : ∀ x δ', δ' ≤ x → g δ' < h x := fun x δ' hδ' =>
    hh x (g δ') (mem_insert_of_mem x (mem_image_of_mem g hδ'))
  -- the index well-order `I` of cardinality `μ⁺`
  have hI : #((Order.succ μ).ord.ToType) = Order.succ μ := mk_ord_toType _
  have hordI : ord #((Order.succ μ).ord.ToType) = typeLT ((Order.succ μ).ord.ToType) := by
    rw [hI, type_toType]
  have hregI : Cardinal.IsRegular #((Order.succ μ).ord.ToType) := by
    rw [hI]; exact isRegular_succ hμ
  have hμI : μ < #((Order.succ μ).ord.ToType) := by rw [hI]; exact Order.lt_succ μ
  have hIW : #((Order.succ μ).ord.ToType) < #W := by
    rw [hI, hW]
    exact (Order.succ_le_of_lt (cantor μ)).trans_lt (Order.lt_succ _)
  obtain ⟨β, hβ⟩ := exists_seq (I := (Order.succ μ).ord.ToType) (κ := #W)
    (fun s hs => exists_forall_lt_of_mk_lt hreg hord hs)
    (fun ξ => (mk_Iio_lt ξ hordI).trans hIW) h
  have hβmono : ∀ ξ η : (Order.succ μ).ord.ToType, η < ξ → β η < β ξ :=
    fun ξ η hη => (hxh _).trans (hβ ξ η hη)
  -- the least strict upper bound `α₀` of the range of `β`
  have hT : {x : W | ∀ ξ, β ξ < x}.Nonempty := by
    obtain ⟨x, hx⟩ := exists_forall_lt_of_mk_lt hreg hord (s := range β)
      (mk_range_le.trans_lt hIW)
    exact ⟨x, fun ξ => hx _ (mem_range_self ξ)⟩
  obtain ⟨α₀, hα₀T, hbelow⟩ : ∃ α₀ : W, (∀ ξ, β ξ < α₀) ∧ ∀ y, y < α₀ → ∃ ξ, y ≤ β ξ := by
    refine ⟨(wellFounded_lt (α := W)).min _ hT, (wellFounded_lt (α := W)).min_mem _ hT, ?_⟩
    intro y hy
    by_contra hcon'
    push Not at hcon'
    exact (wellFounded_lt (α := W)).not_lt_min {x : W | ∀ ξ, β ξ < x} (x := y) hcon' hy
  -- `α₀` has big cofinality
  have hα₀S : α₀ ∈ bigCof μ := by
    intro Z hZ hZμ
    choose ξ hξ using fun z : Z => hbelow z (hZ z.2)
    obtain ⟨ξ', hξ'⟩ := exists_forall_lt_of_mk_lt hregI hordI (s := range ξ)
      (mk_range_le.trans_lt (hZμ.trans_lt hμI))
    refine ⟨β ξ', hα₀T ξ', fun z hz => ?_⟩
    exact (hξ ⟨z, hz⟩).trans_lt (hβmono _ _ (hξ' _ (mem_range_self _)))
  -- but `α₀` lies in the fibre of `δ α₀`, which is bounded below `α₀`
  have h1 : α₀ < g (δ α₀) := hg (δ α₀) α₀ ⟨hα₀S, rfl⟩
  obtain ⟨ξ, hξ⟩ := hbelow _ (hδ α₀ hα₀S)
  obtain ⟨ξ', hξξ'⟩ := exists_gt_of_regular hregI hordI ξ
  have h2 : g (δ α₀) < β ξ' := (hgh _ _ hξ).trans (hβ ξ' ξ hξξ')
  exact lt_irrefl α₀ (h1.trans (h2.trans (hα₀T ξ')))
end Erdos1219
