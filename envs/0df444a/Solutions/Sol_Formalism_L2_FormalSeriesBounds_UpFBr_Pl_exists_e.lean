-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.exists_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:58:31.343137+00:00
-- url     : https://prove2.me/submissions/b38cd84b-5bad-4758-bb60-abf319dea574

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPlP
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_completeA
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_lift_idem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_natCast_mul_tmul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_natCast_tmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Polynomial
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution [Module.Free ℤ OE] [Module.Finite ℤ OE] (ε : OE) (hε1 : ∃ y, ε * ε - ε = (l : OE) * y) :
    ∃ e z : ℤ_[l] ⊗[ℤ] OE, e * e = e ∧ e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z := by
  have := completeA (l := l) (OE := OE)
  obtain ⟨y, hy⟩ := hε1
  have h : ((1 : ℤ_[l]) ⊗ₜ[ℤ] ε) * ((1 : ℤ_[l]) ⊗ₜ[ℤ] ε) - (1 : ℤ_[l]) ⊗ₜ[ℤ] ε ∈
      Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)} := by
    rw [Ideal.mem_span_singleton']
    refine ⟨(1 : ℤ_[l]) ⊗ₜ[ℤ] y, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_sub, hy, mul_comm, natCast_mul_tmul,
      mul_one, natCast_tmul]
  obtain ⟨e, he, he'⟩ := lift_idem _ _ h
  rw [Ideal.mem_span_singleton'] at he'
  obtain ⟨z, hz⟩ := he'
  exact ⟨e, z, he, by rw [← hz, mul_comm]⟩
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
