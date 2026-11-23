-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.square_near_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:12.55557+00:00
-- url     : https://prove2.me/submissions/3c95160c-eb6b-4246-8d09-2cae5686fadd

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_J_nhds
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_root_exists
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open A6x9
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.SquareNear := by
  intro K _ _ _ R ψ hd hn
  obtain ⟨π, hπ, hπ'⟩ := hd.unif
  obtain ⟨u2, hu2⟩ := hn 2 (by norm_num)
  obtain ⟨k, hk⟩ := hπ' ((u2⁻¹ : Kˣ) : K)
  have hs : ((2 : ℕ) : K) * ((u2⁻¹ : Kˣ) : K) = 1 := by rw [← hu2]; simp
  refine ⟨(fun x => ((u2⁻¹ : Kˣ) : K) * x) ⁻¹' (mulR R ((π : K) ^ (k + 1)) : Set K), ?_, ?_⟩
  · apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
    simpa using J_nhds π hd (k + 1)
  · intro a ha
    obtain ⟨l, -, hl⟩ := root_exists π hd hn hπ hπ' hs hk ha
    have e : (1 + l) ^ 2 = (a : K) := by
      rw [hl]; linear_combination ((a : K) - 1) * hs
    have hu : IsUnit (1 + l) := by
      have : IsUnit ((1 + l) ^ 2) := by rw [e]; exact a.isUnit
      exact (isUnit_pow_iff (by norm_num)).1 this
    obtain ⟨b, hb⟩ := hu
    refine ⟨b, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, hb, e]
end Formalism.FourierDecayAlt.P
