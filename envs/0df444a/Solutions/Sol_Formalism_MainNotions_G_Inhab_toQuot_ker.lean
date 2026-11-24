-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.toQuot_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:40:18.537363+00:00
-- url     : https://prove2.me/submissions/4e6c5acf-f072-4131-a58c-1ec220000d6a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLPb
import Theorems.Thm_Formalism_MainNotions_G_Inhab_gen_mem
import Theorems.Thm_Formalism_MainNotions_G_Inhab_p_smul_gen
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_gen
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (h : HidaSetting p n' W Qq O Kf ι σ j w) (a : ℤ) :
    LinearMap.ker (toQuot W (Qq := Qq) p a) = Ideal.span {(p : W)} := by
  have := h.frac_alt
  ext c
  rw [LinearMap.mem_ker, Ideal.mem_span_singleton]
  show Submodule.mkQ _ (c • (⟨gen Qq p a, gen_mem a⟩ : ↥(line W (Qq := Qq) p a))) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  show c • gen Qq p a ∈ line W p (a + 1) ↔ _
  constructor
  · intro hc
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hc
    have hd' : d • gen Qq p (a + 1) = c • gen Qq p a := hd
    rw [← p_smul_gen (W := W) h a, smul_smul] at hd'
    have h0 := congrFun hd' 0
    simp only [gen, Pi.smul_apply, Algebra.smul_def] at h0
    have h1 := mul_right_cancel₀ (zpow_ne_zero a (p_ne h)) h0
    have h2 : d * (p : W) = c := IsFractionRing.injective W Qq h1
    exact ⟨d, by rw [← h2, mul_comm]⟩
  · rintro ⟨d, rfl⟩
    rw [mul_comm, mul_smul, p_smul_gen h]
    exact Submodule.smul_mem _ _ (gen_mem _)
end Formalism.MainNotions.G.Inhab
