-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.cor_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:50:37.288298+00:00
-- url     : https://prove2.me/submissions/e329d116-b2b0-401c-a54c-3ffaef3938d5

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_SwappedHighestWeightNeZero
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_cor_line
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_cor_emb_hw
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_cor_eval_hw
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_cor_eval_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW
variable {p : ℕ} [Fact p.Prime] {r n : ℕ}
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution (hk : RowGlDiv) (hI : SwpInt) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (μ : Fin r → ℤ)
    (h : MvPolynomial (Fin n × Fin r) ℚ_[p]) (hh : (GR p r ν).IsHW μ h) (hW : h ∈ swappedDualWeyl p r n ν)
    (hM : h ∈ IntPol p (Fin n × Fin r)) : h ∈ cor_L p hn ν := by
  obtain ⟨c, rfl⟩ := cor_line hk hn ν hν μ h hW hh
  rw [swappedHighestWeight, ← map_smul] at hM
  obtain ⟨f0, hf0⟩ := (hI p r n _).mp hM
  have hc : algebraMap ℤ_[p] ℚ_[p] (eval (idPoint ℤ_[p] r n) f0) = c := by
    rw [← cor_eval_map, hf0, smul_eq_C_mul, map_mul, eval_C, cor_eval_hw, mul_one]
  refine ⟨eval (idPoint ℤ_[p] r n) f0 • hw ℤ_[p] hn ν,
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩), ?_⟩
  rw [map_smul, cor_emb_hw, ← hc, algebraMap_smul]
end Formalism.InvariantFactorPaths.INST
