-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_hcompl_le_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:22.133463+00:00
-- url     : https://prove2.me/submissions/f70acc7d-ab0f-458e-921c-7f2f14745097

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
open NumberField
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) :
    hcompl (K := K) w.asIdeal ≤ (conjPl w).asIdeal.primeCompl := by
  unfold hcompl
  rw [Submonoid.closure_le]
  rintro s ⟨_, hs2⟩
  show s ∉ (conjPl w).asIdeal
  intro hmem
  change s ∈ w.asIdeal.map (cO K) at hmem
  rw [Ideal.mem_map_of_equiv] at hmem
  obtain ⟨x, hx, rfl⟩ := hmem
  refine hs2 x ?_ hx
  show (x : K) = star ((cO K x : 𝓞 K) : K)
  simp [cO]
end Formalism.DivisionValues
