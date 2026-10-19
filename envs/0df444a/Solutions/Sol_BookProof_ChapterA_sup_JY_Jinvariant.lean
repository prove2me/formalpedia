-- Prove2me | solution 1 for BookProof.ChapterA.sup_JY_Jinvariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:26:04.057979+00:00
-- url     : https://prove2.me/submissions/39fdf87d-5820-457b-8a4f-278234a7d4b2

-- Generated from ChapterA1e.lean — solution of BookProof.ChapterA.sup_JY_Jinvariant
import Mathlib
import Definitions.Def_ChapterA1e
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (Y : Submodule ℝ V) :
    ∀ x ∈ Y ⊔ JY Y, Jmap x ∈ Y ⊔ JY Y := by

  intro x hx;    rw [ Submodule.mem_sup ] at hx;    obtain ⟨ a, ha, b, hb, rfl ⟩ := hx;
  simp_all only [Jmap_apply, smul_add, Submodule.mem_sup] ;
  refine ⟨ Complex.I • b, ?_, Complex.I • a, ?_, ?_ ⟩ <;>
    simp_all only [JY, Submodule.mem_map, LinearIsometry.coe_toLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, Jmap_apply, ne_eq, Complex.I_ne_zero,
      not_false_eq_true, smul_right_inj, exists_eq_right];
  · obtain ⟨ y, hy, rfl ⟩ := hb; simp [ ← smul_assoc, hy ] ;
  · exact add_comm _ _
