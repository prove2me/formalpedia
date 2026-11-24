-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.integral_gW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:32.349295+00:00
-- url     : https://prove2.me/submissions/ebfbff5e-10d8-4224-8e13-706758d3ed47

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoTsumDivPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemIdealLatticeIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_sBox_eq
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
open NumberField Module Filter Topology MeasureTheory Pointwise
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution [IsTotallyReal F] {m : ℕ} (hm : 1 ≤ m) :
    ∫ x in sBox F, gW F m x = ((m : ℝ)⁻¹) ^ Fintype.card {w : InfinitePlace F // w.IsReal} := by
  have hE : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)⟩
  have h1 : (volume : Measure ({w : InfinitePlace F // w.IsComplex} → ℂ)).real Set.univ = 1 := by
    rw [volume_pi, Measure.pi_of_empty]
    simp
  rw [sBox_eq, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  unfold gW
  rw [integral_fun_fst (f := fun y : {w : InfinitePlace F // w.IsReal} → ℝ => ∏ w, y w ^ (m - 1)),
    h1, one_smul, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun _ (y : ℝ) => y ^ (m - 1)), Finset.prod_const,
    Finset.card_univ]
  congr 1
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_pow, Nat.cast_sub hm]
  simp
end Formalism.HermitianLattices.Ext.L3.BoxSum
