-- Prove2me | solution 1 for Erdos919.erdos919_aleph1_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:42:22.833062+00:00
-- url     : https://prove2.me/submissions/5857b667-0a7e-4985-8b22-f132c37675aa

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_tensorTop_lower
public import Theorems.Thm_Erdos919_tensorTop_colorableOn
public import Theorems.Thm_Erdos919_smallCard_comap
public import Theorems.Thm_Erdos919_mk_W
public import Theorems.Thm_Erdos919_aleph1_lt_aleph2
public import Theorems.Thm_Erdos919_mk_ulift_nat_le_aleph1
public import Theorems.Thm_Erdos919_equiv_lex
public import Theorems.Thm_Erdos919_bigGraph_smallType
public import Theorems.Thm_Erdos919_smallCard_of_smallType
public import Theorems.Thm_Erdos919_bigGraph_lower
public import Theorems.Thm_Erdos919_mk_T1
public import Theorems.Thm_Erdos919_T1_not_inj

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution :
    (∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ ChiAleph1 G) ↔
      ∃ H : SimpleGraph W.{u}, SmallCardCC H ∧ IsEmpty (H.Coloring ℕ) := by
  constructor
  · rintro ⟨G, hG, -, hχ⟩
    obtain ⟨e⟩ := equiv_lex.{u}
    exact ⟨G.comap e, smallCard_comap e (smallCard_of_smallType hG),
      ⟨fun c => hχ.false (coloringOfComap e c)⟩⟩
  · rintro ⟨H, hH, hχ⟩
    let K := tensorTop H T1.{u}
    have hK : SmallCardCC K := by
      intro X hX
      exact tensorTop_colorableOn H X (hH _ (mk_image_le.trans hX))
    have hWT : Nonempty (W.{u} ≃ W.{u} × T1.{u}) := by
      apply Cardinal.eq.1
      rw [mk_prod, Cardinal.lift_id, Cardinal.lift_id, mk_W, mk_T1,
        mul_eq_left (aleph0_le_aleph 2) aleph1_lt_aleph2.le (aleph_pos 1).ne']
    obtain ⟨e⟩ := hWT
    let H' := K.comap e
    refine ⟨bigGraph H', bigGraph_smallType H' (smallCard_comap e hK), ?_, ?_⟩
    · exact ⟨T1, mk_T1.le, ⟨bigGraphColoring (coloringComap e (tensorTopColoringT H T1))⟩⟩
    · refine ⟨fun c => ?_⟩
      obtain ⟨d⟩ := bigGraph_lower mk_ulift_nat_le_aleph1 (coloringULift c)
      obtain ⟨d'⟩ := tensorTop_lower H T1_not_inj (coloringOfComap e d)
      exact hχ.false (coloringDown d')
end Erdos919
