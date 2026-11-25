-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieQL.inf_ker_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:52:53.040313+00:00
-- url     : https://prove2.me/submissions/574475d9-0cc7-454e-86d1-47128667ce14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_QuotLocalOfQuotientLength
import Theorems.Thm_Formalism_L2_Pj_QAt_TieQL_c_eq_sum
import Theorems.Thm_Formalism_L2_Pj_QAt_TieQL_cK_coordK
import Theorems.Thm_Formalism_L2_Pj_QAt_TieQL_det_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open Formalism.L2.Pj.QAt.TieQL
open Module
variable {O Q : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [AddCommGroup Q] [Module O Q] {ρ : ℕ}
namespace Formalism.L2.Pj.QAt.TieQL
theorem _root_.solution (b : Basis (Fin ρ) O Q) (c : Fin ρ → (Q →ₗ[O] O)) (th : Fin ρ → Q)
    (hdet : (Matrix.of fun i j => c i (th j)).det ≠ 0) :
    LinearMap.range (coordK b) ⊓ (LinearMap.ker (cK b c)).restrictScalars O = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf, LinearMap.mem_range] at hv
  obtain ⟨⟨q, rfl⟩, hv⟩ := hv
  rw [Submodule.restrictScalars_mem, LinearMap.mem_ker] at hv
  have hA : (matA b c).det ≠ 0 := by
    intro h0
    apply hdet
    rw [det_mul_eq b c th, Matrix.det_mul, h0, zero_mul]
  have hc : ∀ i, c i q = 0 := by
    intro i
    have h1 : cK b c (coordK b q) i = 0 := by rw [hv]; rfl
    rw [cK_coordK] at h1
    exact IsFractionRing.injective O (FractionRing O) (by rw [h1, map_zero])
  have hvec : (matA b c).mulVec (fun k => b.repr q k) = 0 := by
    funext i
    rw [Pi.zero_apply, ← hc i, c_eq_sum b c i q]
    rfl
  have hr := Matrix.eq_zero_of_mulVec_eq_zero hA hvec
  have hq : q = 0 := by
    apply b.repr.injective
    ext k
    simpa using congrFun hr k
  rw [hq, map_zero]
end Formalism.L2.Pj.QAt.TieQL
