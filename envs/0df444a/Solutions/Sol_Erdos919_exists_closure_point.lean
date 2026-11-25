-- Prove2me | solution 1 for Erdos919.exists_closure_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:37:20.727243+00:00
-- url     : https://prove2.me/submissions/4ef17f7d-de9d-491d-b884-d3a5452a36ae

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_mk_Iio_W
public import Theorems.Thm_Erdos919_mk_ulift_nat_le_aleph1
public import Theorems.Thm_Erdos919_exists_gt_of_small

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution (β : W.{u} → W.{u}) (a : W.{u}) :
    ∃ δ, a < δ ∧ ∀ ζ < δ, β ζ ≤ δ := by
  have hstep : ∀ x : W.{u}, ∃ y, x < y ∧ ∀ ζ < x, β ζ < y := by
    intro x
    obtain ⟨u, hu⟩ := exists_gt_of_small (J := Option (Iio x))
      (fun o => o.elim x (fun z => β z.1)) (by
        rw [mk_option]
        exact (add_le_add (mk_Iio_W x) le_rfl).trans (add_one_eq (aleph0_le_aleph 1)).le)
    exact ⟨u, hu none, fun ζ hζ => hu (some ⟨ζ, hζ⟩)⟩
  choose g hg1 hg2 using hstep
  let s : ℕ → W.{u} := fun n => g^[n] a
  obtain ⟨u, hu⟩ := exists_gt_of_small (fun n : ULift.{u} ℕ => s n.down) mk_ulift_nat_le_aleph1
  let U : Set W.{u} := {u | ∀ n, s n < u}
  have hUne : U.Nonempty := ⟨u, fun n => hu ⟨n⟩⟩
  have hsucc : ∀ n, s (n + 1) = g (s n) := fun n => Function.iterate_succ_apply' g n a
  refine ⟨WellFounded.min wellFounded_lt U hUne, (WellFounded.min_mem _ U hUne) 0, ?_⟩
  intro ζ hζ
  have hζU : ζ ∉ U := fun hmem => WellFounded.not_lt_min wellFounded_lt U hmem hζ
  simp only [U, mem_ofPred_eq, not_forall, not_lt] at hζU
  obtain ⟨n, hn⟩ := hζU
  have h1 : ζ < s (n + 1) := by rw [hsucc]; exact lt_of_le_of_lt hn (hg1 _)
  have h2 : β ζ < s (n + 1 + 1) := by rw [hsucc]; exact hg2 _ ζ h1
  exact (h2.trans ((WellFounded.min_mem _ U hUne) (n + 1 + 1))).le
end Erdos919
