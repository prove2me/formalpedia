-- Prove2me | solution 1 for DetDLP.w3_driver_trace_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T00:43:56.886963+00:00
-- url     : https://prove2.me/submissions/fe0b3071-e9f5-482e-a683-b780b87e904f

import Definitions.Def_DetDLP_W3_Driver
import Theorems.Thm_DetDLP_w3_stage2_abstract_coset_recovery

set_option autoImplicit false
open DetDLP

theorem solution {V : Type} [AddCommGroup V] [Fintype V] [DecidableEq V] {M m : ℕ} [NeZero M]
    (hm : 2 ≤ m) (hM : 2 ≤ M) (hcard : Nat.card V = M) (P Q : V) (hg : addOrderOf P = M)
    (ref B : IndexedFactorBase V m) (hB : Function.Surjective B.tupleVal) (accepts : ℕ → Prop) :
    w3_traceOutput ref B M P Q accepts ↔ ∃ u, u < M ∧ u • P = Q ∧ accepts u := by
  classical
  have ht : AddSubgroup.zmultiples P = ⊤ := (AddSubgroup.zmultiples P).eq_top_of_card_eq
    ((Nat.card_zmultiples P).trans (hg.trans hcard.symm))
  have all (g : V) : g ∈ AddSubgroup.zmultiples P := by rw [ht]; trivial
  let e := (zmodAddEquivOfGenerator all hcard).symm
  have hP : e P = 1 := zmodAddEquivOfGenerator_symm_apply_generator all hcard
  constructor
  · rintro ⟨_,U,y,hU,hy,hacc⟩
    have h := (w3_stage2_abstract_coset_recovery M hM P Q e hP hm B hB U hU).2 y hy
    exact ⟨_,h.2.1,h.2.2,hacc⟩
  · rintro ⟨u,hu,he,hacc⟩
    choose U hU using fun j => hB (B.elem P Q j)
    obtain ⟨hex,hok⟩ := w3_stage2_abstract_coset_recovery M hM P Q e hP hm B hB U hU
    obtain ⟨y,hy⟩ := hex
    obtain ⟨hj,_,_⟩ := hok y hy
    have htar : B.elem P Q B.targetCoord = Q := by simp [IndexedFactorBase.elem, IndexedFactorBase.targetCoord]
    have heq : y B.targetCoord = (u : ZMod M) := by rw [hj,htar,←he,map_nsmul,hP,nsmul_eq_mul,mul_one]
    refine ⟨fun g _ => hB g,U,y,hU,hy,?_⟩
    rwa [heq,ZMod.val_natCast_of_lt hu]
