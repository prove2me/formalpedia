-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.oneFn_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:39:43.286351+00:00
-- url     : https://prove2.me/submissions/cf2d92ed-97db-4a7d-b20a-91c9fcfd1b14

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
import Theorems.Thm_Formalism_MainNotions_G_Inhab_isLatTup_smul_iff
import Theorems.Thm_P2M_Formalism_MainNotions_G_Inhab_natAct_one__272d2e55828d
import Theorems.Thm_Formalism_MainNotions_G_Inhab_oneFn_pos
import Theorems.Thm_Formalism_MainNotions_G_Inhab_oneFn_neg
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
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (C : Level P)
variable (h0 : ∀ v, P.lam0 v = fun _ _ => 0)
include h0
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (hχ : C.χ = 1) (Hv : P.Tup → Submodule O P.Xsp) (hH : ∀ L, (1 : P.Xsp) ∈ Hv L) :
    oneFn P ∈ C.funMod Hv := by
  unfold Level.funMod
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.proj_apply]
    intro L hL
    rw [oneFn_pos P hL]
    exact hH L
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]
    intro L hL
    exact oneFn_neg P hL
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, hχ, MonoidHom.one_apply, Units.val_one, one_smul]
    intro γ L
    by_cases hL : P.IsLatTup L
    · rw [oneFn_pos P ((isLatTup_smul_iff P C γ L).mpr hL), oneFn_pos P hL]
      simp [Level.actX, natAct_one' P h0]
    · rw [oneFn_neg P (mt (isLatTup_smul_iff P C γ L).mp hL), oneFn_neg P hL]
      simp
end Formalism.MainNotions.G.Inhab
