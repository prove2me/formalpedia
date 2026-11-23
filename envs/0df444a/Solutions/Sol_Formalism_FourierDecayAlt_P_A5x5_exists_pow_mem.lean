-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.exists_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:32.138982+00:00
-- url     : https://prove2.me/submissions/a985714d-918e-4df7-8661-0e673e9b129f

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution {R : Subring K} {ϖ : K} (hϖ : ϖ ∈ R) (h : ∀ x : K, ∃ m : ℕ, ϖ ^ m * x ∈ R)
    {α : Type} [Fintype α] (f : α → K) : ∃ m : ℕ, ∀ a, ϖ ^ m * f a ∈ R := by
  choose g hg using fun a => h (f a)
  refine ⟨∑ a, g a, fun a => ?_⟩
  have hle : g a ≤ ∑ b, g b := Finset.single_le_sum (fun b _ => Nat.zero_le (g b)) (Finset.mem_univ a)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, pow_add, mul_comm (ϖ ^ g a) (ϖ ^ k), mul_assoc]
  exact R.mul_mem (R.pow_mem hϖ k) (hg a)
end Formalism.FourierDecayAlt.P.A5x5
