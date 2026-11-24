-- Prove2me | solution 1 for Bl.SecondBlockLemmaD.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:56.047932+00:00
-- url     : https://prove2.me/submissions/db3e760c-b5ee-4954-8acc-35d8b8cd32e0

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Bl Bl.SecondBlockLemmaD
namespace Bl.SecondBlockLemmaD
theorem _root_.solution {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B] [DecidableEq B]
    (π : A →+ B) (hπ : Function.Surjective π) (G : B → ℂ) :
    (Fintype.card A : ℂ)⁻¹ * ∑ a, G (π a) = (Fintype.card B : ℂ)⁻¹ * ∑ b, G b := by
  have hfib : ∀ b : B, (univ.filter fun a => π a = b).card = (univ.filter fun a => π a = 0).card :=
    fun b => AddMonoidHom.card_fiber_eq_of_mem_range π (hπ b) (hπ 0)
  set c := (univ.filter fun a => π a = 0).card with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact Finset.card_ne_zero.2 ⟨0, Finset.mem_filter.2 ⟨Finset.mem_univ _, map_zero π⟩⟩
  have hsum : ∑ a, G (π a) = ∑ b, (c : ℂ) * G b := by
    rw [← Finset.sum_fiberwise Finset.univ π (fun a => G (π a))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.1 ha).2]), Finset.sum_const,
      hfib b, nsmul_eq_mul]
  have hcard : Fintype.card A = Fintype.card B * c := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := π) (t := univ)
      (fun _ _ => Finset.mem_univ _)]
    rw [Finset.sum_congr rfl (fun b _ => hfib b), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hB : (Fintype.card B : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
  rw [hsum, ← Finset.mul_sum, hcard]
  push_cast
  field_simp
end Bl.SecondBlockLemmaD
