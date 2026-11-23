-- Prove2me | solution 1 for FRI_query_prob_eq_card_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:34:20.461598+00:00
-- url     : https://prove2.me/submissions/4098c62c-e526-4136-8254-970ac4715c7c

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
open scoped Classical
theorem _root_.solution [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) (T : FRITranscript P)
    (h_nonempty : Nonempty { x // x ∈ P.D_0 }) :
    FRI_query_prob P f_0 bound T =
    (Finset.univ.filter (fun s ↦
      let T' := { T with s := s }
      FRI_State P f_0 bound T' (P.num_foldings + 1))).card /
        (Fintype.card (Fin P.q_rep → { x // x ∈ P.D_0 }) : ENNReal) := by
  simp only [FRI_query_prob, nonempty_subtype, PMF.toMeasure_apply_fintype, Fintype.card_pi,
    Fintype.card_coe, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow]
  split_ifs with h
  · simp_all only [nonempty_subtype, Set.indicator, Set.mem_setOf_eq,
      PMF.uniformOfFintype_apply, Fintype.card_pi, Fintype.card_coe, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Nat.cast_pow]
    rw [Finset.sum_ite]
    simp_all
    rfl
  · simp_all only [nonempty_subtype]
