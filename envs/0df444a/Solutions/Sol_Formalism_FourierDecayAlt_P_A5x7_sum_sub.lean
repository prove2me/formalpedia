-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x7.sum_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:36.529253+00:00
-- url     : https://prove2.me/submissions/3eb4bfc0-1a0f-477e-9ccc-0d7921fa53c5

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x7
theorem _root_.solution {k n : ℕ} (e : Fin k → Fin n) (he : Function.Injective e) (f : Fin n → K)
    (hf : ∀ b, b ∉ Set.range e → f b = 0) : ∑ b, f b = ∑ i, f (e i) := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := e) (f := f) (fun x _ y _ h => he h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro b _ hb
  apply hf
  rintro ⟨i, rfl⟩
  exact hb (Finset.mem_image_of_mem e (Finset.mem_univ i))
end Formalism.FourierDecayAlt.P.A5x7
