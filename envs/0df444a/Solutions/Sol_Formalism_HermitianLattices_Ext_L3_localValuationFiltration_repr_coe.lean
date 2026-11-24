-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.localValuationFiltration.repr_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:18.004868+00:00
-- url     : https://prove2.me/submissions/cd6ed09e-5267-4d3e-b9a5-43f44bedd002

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.localValuationFiltration
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans traceDeterminantCongruences reductionMapsOfForms
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.localValuationFiltration
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (b : Basis κ K V) (y : spanO b) (j : κ) :
    b.repr (y : V) j = algebraMap (𝓞 K) K (crd b y j) := by
  have hy : (y : V) = ∑ i, algebraMap (𝓞 K) K (crd b y i) • b i := by
    conv_lhs => rw [← (bO b).sum_equivFun y]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Submodule.coe_smul, algebraMap_smul]
    congr 1
    simp only [bO, Basis.span_apply]
  rw [hy, map_sum]
  simp only [map_smul, Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
end Formalism.HermitianLattices.Ext.L3.localValuationFiltration
