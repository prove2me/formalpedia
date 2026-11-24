-- Prove2me | solution 1 for Bl.SecondBlockLemmaF.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:29.623937+00:00
-- url     : https://prove2.me/submissions/285bc72d-c81d-42c6-96ae-2d8ce58f9048

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasE_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.SecondBlockLemmaF
namespace Bl.SecondBlockLemmaF
theorem _root_.solution :
  ∀ {M : Type u_1} [inst : AddCommMonoid.{u_1} M] (r : Nat) (S : Fin (HAdd.hAdd.{0, 0, 0} r 1) → Finset.{0} Nat)
  (F : (Fin (HAdd.hAdd.{0, 0, 0} r 1) → Nat) → M),
  Eq.{u_1 + 1} (Finset.sum.{0, u_1} (Fintype.piFinset.{0, 0} S) fun (μ : Fin (HAdd.hAdd.{0, 0, 0} r 1) → Nat) ↦ F μ)
    (Finset.sum.{0, u_1} (S 0) fun (a : Nat) ↦
      Finset.sum.{0, u_1} (Fintype.piFinset.{0, 0} fun (t : Fin r) ↦ S t.succ) fun (μ' : Fin r → Nat) ↦
        F (Fin.cons.{1} a μ')) := by
  intro M _ r S F
  rw [← Finset.sum_product' (f := fun a μ' => F (Fin.cons a μ'))]
  refine Finset.sum_nbij' (fun μ => (μ 0, Fin.tail μ)) (fun p => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    simp only [Fintype.mem_piFinset, Finset.mem_product] at hμ ⊢
    exact ⟨hμ 0, fun t => hμ t.succ⟩
  · intro p hp
    simp only [Fintype.mem_piFinset, Finset.mem_product] at hp ⊢
    intro i
    refine Fin.cases ?_ (fun t => ?_) i
    · simpa only [Fin.cons_zero] using hp.1
    · simpa only [Fin.cons_succ] using hp.2 t
  · intro μ _
    exact Fin.cons_self_tail μ
  · intro p _
    simp only [Fin.cons_zero, Fin.tail_cons]
  · intro μ _
    simp only [Fin.cons_self_tail]
end Bl.SecondBlockLemmaF
