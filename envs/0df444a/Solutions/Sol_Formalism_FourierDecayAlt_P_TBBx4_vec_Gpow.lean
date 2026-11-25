-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx4.vec_Gpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:36.633064+00:00
-- url     : https://prove2.me/submissions/cdb5928f-2e37-4758-a607-904f6a9cd4f2

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularityAtPlaceOfSubadditive
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx4_orbJ_smul_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Gf_of_Zhat
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Gf_sgs
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_ae_inSS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx4
open MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal ComplexConjugate
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
namespace Formalism.FourierDecayAlt.P.TBBx4
theorem _root_.solution (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p₀ : ℕ) {γ : C.LPt}
    (_hγ : D.IsLocPt γ (P.r + 1)) (hG : 0 < Gp p γ) :
    p.V (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • F g) γ =
      ((Gp p γ ^ p₀ : ℝ) : ℂ) • p.V F γ := by
  have hc : ((Gp p γ ^ p₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hG p₀).ne'
  unfold KB.Pl.V D.vecV
  split_ifs with h1 h2
  · apply orbJ_smul_ae _ _ _ _ _ _ hc
    filter_upwards [TBBx2.ae_inSS p.T.base] with q hq
    have hGq : Gf P.k P.r p.T.base.z p.T.base.z' (B.sgs q h2.choose) = Gp p γ := by
      rw [TBBx2.Gf_sgs _ q hq, TBBx2.Gf_of_Zhat _ _ _ _ h2.choose_spec.2.1]
      rfl
    unfold D.orbIntegrand B.rho
    simp only [hGq, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    rw [smul_comm]
  · simp
  · simp
end Formalism.FourierDecayAlt.P.TBBx4
