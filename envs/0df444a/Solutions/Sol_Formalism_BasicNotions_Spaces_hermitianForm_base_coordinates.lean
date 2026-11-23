-- Prove2me | solution 1 for Formalism.BasicNotions.Spaces.hermitianForm_base_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:24.465408+00:00
-- url     : https://prove2.me/submissions/c20ab4d0-e68b-41c5-ac7a-2d50c6302b5d

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_DataKernels
import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace Formalism.BasicNotions
open NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct
section Defs
variable {F E : Type} [Field F] [CommRing E] [Algebra F E]
end Defs
section Iw
variable (F : Type) [Field F] [NumberField F] (k : ℕ)
end Iw
namespace Spaces
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (sp : Spaces R F E)
private theorem hT_eq_hform_gram_reindex_frame (S : HSpace E) {n : ℕ} (h : S.rank = n) (x y : S.V) :
    S.hT x y = hform (starRingEnd E) (S.gram.reindex (finCongr h) (finCongr h))
      ((S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)) x)
      ((S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)) y) := by
  subst h
  simp [hform, HSpace.gram]
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end Spaces
attribute [instance] ColLevel.fM_acg ColLevel.fM_mod
namespace ColLevel
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
end ColLevel
end Formalism.BasicNotions
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions
open NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct
open Formalism.BasicNotions.Spaces
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (sp : Spaces R F E)
namespace Formalism.BasicNotions.Spaces
theorem _root_.solution (x y : (sp.X 0).V) :
    (sp.X 0).hT x y = hform (sp.cm.sig : E →+* E) sp.gram0 (sp.crd0 x) (sp.crd0 y) := by
  exact hT_eq_hform_gram_reindex_frame (sp.X 0) sp.rank0 x y
end Formalism.BasicNotions.Spaces
