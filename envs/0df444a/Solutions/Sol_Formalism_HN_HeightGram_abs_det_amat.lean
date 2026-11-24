-- Prove2me | solution 1 for Formalism.HN.HeightGram.abs_det_amat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:16.618873+00:00
-- url     : https://prove2.me/submissions/bdabd9ff-f69e-4b68-9ff5-f21d5f61b614

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.HeightGram
variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
attribute [local instance] isEmpty_real
open scoped Classical
open MeasureTheory ZSpan
namespace Formalism.HN.HeightGram
theorem _root_.solution (eS : Free.ChooseBasisIndex ℤ (𝓞 K) ≃ InfinitePlace K × Fin 2) :
    |(amat (lamK K) eS).det| = (2⁻¹) ^ InfinitePlace.nrComplexPlaces K * √|(discr K : ℝ)| := by
  classical
  let e' : mixedEmbedding.index K ≃ Free.ChooseBasisIndex ℤ (𝓞 K) := (idxE K).trans eS.symm
  let A' := (mixedEmbedding.stdBasis K).toMatrix ((mixedEmbedding.latticeBasis K).reindex e'.symm)
  have hvol : volume (fundamentalDomain (mixedEmbedding.latticeBasis K)) = (‖A'.det‖₊ : ENNReal) := by
    rw [← fundamentalDomain_reindex _ e'.symm, ← norm_toNNReal, measure_fundamentalDomain
      ((mixedEmbedding.latticeBasis K).reindex e'.symm) volume (mixedEmbedding.stdBasis K),
      mixedEmbedding.volume_fundamentalDomain_stdBasis, mul_one]
    rfl
  have hA : amat (lamK K) eS = A'.submatrix (idxE K).symm (idxE K).symm := by
    ext ⟨v, r⟩ q
    have hq : e' ((idxE K).symm q) = eS.symm q := by simp [e']
    simp only [amat, of_apply, submatrix_apply, A', Basis.toMatrix_apply, Basis.reindex_apply,
      Equiv.symm_symm, hq, mixedEmbedding.latticeBasis_apply]
    fin_cases r
    · simp [idxE, lamK, mixedEmbedding.mixedEmbedding_apply_isComplex]
    · simp [idxE, lamK, mixedEmbedding.mixedEmbedding_apply_isComplex]
  have h1 := mixedEmbedding.volume_fundamentalDomain_latticeBasis K
  rw [hvol] at h1
  have h2 := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal, ENNReal.coe_toReal, Real.coe_sqrt, coe_nnnorm, coe_nnnorm,
    Int.norm_eq_abs, Real.norm_eq_abs] at h2
  rw [hA, det_submatrix_equiv_self]
  convert h2 using 3
end Formalism.HN.HeightGram
