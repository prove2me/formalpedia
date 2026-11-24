-- Prove2me | solution 1 for Formalism.UG.P.mul_eq_out_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:39:50.166855+00:00
-- url     : https://prove2.me/submissions/735ba93e-e671-41b3-95ca-90905b2d0281

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FiniteCosetsInDoset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G]
namespace Formalism.UG.P
theorem _root_.solution (K : Subgroup G) (s : G) (k : K) :
    ∃ k' : K, (k : G) * s =
      (((QuotientGroup.mk k : K ⧸ conjInter K s).out : K) : G) * s * k' := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (conjInter K s) k
  have hmem : ((h⁻¹ : conjInter K s) : K) ∈ conjInter K s := (h⁻¹).2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hmem
  obtain ⟨m, hmK, hm⟩ := hmem
  refine ⟨⟨m, hmK⟩, ?_⟩
  rw [hh]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, InvMemClass.coe_inv] at hm
  have hm' : s * m = ((h : K) : G)⁻¹ * s := by
    rw [← hm]; group
  simp only [Subgroup.coe_mul]
  rw [mul_assoc _ s, hm']
  group
end Formalism.UG.P
