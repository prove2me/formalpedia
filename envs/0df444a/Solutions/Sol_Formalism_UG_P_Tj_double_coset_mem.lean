-- Prove2me | solution 1 for Formalism.UG.P.Tj_double_coset_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:23:16.384999+00:00
-- url     : https://prove2.me/submissions/fe74c725-896f-4f90-9a3a-af21182dde9e

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Theorems.Thm_Formalism_UG_P_ind_biInv
import Theorems.Thm_Formalism_UG_P_mem_hecke_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.TjMem := by
  unfold Formalism.UG.TjMem
  intro L _ O ϖ k _ n j hϖ
  rw [mem_hecke_iff]
  constructor
  · unfold Tj
    apply ind_biInv
    rintro a' b' x ⟨a, ha, b, hb, e⟩
    rw [Set.mem_setOf_eq]
    exact ⟨↑a' * a, (GLint (Fin n) O).mul_mem a'.2 ha, b * ↑b', (GLint (Fin n) O).mul_mem hb b'.2,
      by simp only [Units.val_mul, e, mul_assoc]⟩
  · by_cases hne : ∃ g0, Tj k n O ϖ j g0 ≠ 0
    · obtain ⟨g0, hg0⟩ := hne
      unfold Tj at hg0
      obtain ⟨a0, ha0, b0, hb0, e0⟩ := Set.mem_of_indicator_ne_zero hg0
      refine ⟨{g0}, fun x hx => ⟨g0, Finset.mem_singleton_self _, ?_⟩⟩
      unfold Tj at hx
      obtain ⟨a, ha, b, hb, e⟩ := Set.mem_of_indicator_ne_zero hx
      refine ⟨⟨a * a0⁻¹, (GLint (Fin n) O).mul_mem ha ((GLint (Fin n) O).inv_mem ha0)⟩,
        ⟨b0⁻¹ * b, (GLint (Fin n) O).mul_mem ((GLint (Fin n) O).inv_mem hb0) hb⟩, ?_⟩
      apply Units.ext
      simp only [Subgroup.coe_mk, Units.val_mul, e, e0]
      simp only [mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left]
    · push_neg at hne
      exact ⟨∅, fun x hx => absurd (hne x) hx⟩
end Formalism.UG.P
