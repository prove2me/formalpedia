-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.disjointness_of_supports_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:34.514522+00:00
-- url     : https://prove2.me/submissions/77c28ea3-c8d9-4578-8844-d2d716487e28

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.SeparatedPolydiscsDisjoint := by
  intro ι _ ro D D' hro hne hprod
  rw [Set.disjoint_left]
  intro x hx hx'
  have hlt : ∀ v, ‖D v - D' v‖ < ro := fun v => by
    have h1 := hx v
    have h2 := hx' v
    calc ‖D v - D' v‖ = ‖(x v - D' v) - (x v - D v)‖ := by ring_nf
      _ ≤ ‖x v - D' v‖ + ‖x v - D v‖ := norm_sub_le _ _
      _ < ro := by linarith
  have hne' : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hne (Subsingleton.elim _ _)
  by_cases h0 : ∃ v, ‖D v - D' v‖ = 0
  · obtain ⟨v, hv⟩ := h0
    have h1 : ∏ v, ‖D v - D' v‖ = 0 := Finset.prod_eq_zero (Finset.mem_univ v) hv
    have h2 := pow_pos hro (Fintype.card ι)
    linarith
  · simp only [not_exists] at h0
    have h1 : ∏ v, ‖D v - D' v‖ < ∏ _v : ι, ro :=
      Finset.prod_lt_prod_of_nonempty (fun i _ => lt_of_le_of_ne (norm_nonneg _) (Ne.symm (h0 i)))
        (fun i _ => hlt i) Finset.univ_nonempty
    simp only [Finset.prod_const, Finset.card_univ] at h1
    linarith
end Formalism.HermitianLatticeCounting.P
