-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovolBound_trace_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:32:13.329736+00:00
-- url     : https://prove2.me/submissions/e61c5794-f1d4-449e-810d-2f45b7e58ccc

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (r : 𝓞 K) :
    ∃ z : ℤ, Algebra.trace ℚ K (algebraMap (𝓞 K) K r) = z := by
  have hi : IsIntegral ℤ (Algebra.trace ℚ K (algebraMap (𝓞 K) K r)) :=
    Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe r)
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  exact ⟨z, by rw [← hz]; simp⟩
end Formalism.HermitianLatticesTheory
