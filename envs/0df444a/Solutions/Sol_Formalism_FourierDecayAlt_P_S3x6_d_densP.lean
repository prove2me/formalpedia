-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.d_densP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:09.217075+00:00
-- url     : https://prove2.me/submissions/61fec25d-31ca-4716-a25f-0915a446733d

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
open Matrix Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution (η : ℤ) (q b : ℕ) :
    densP η q 1 b = ∏ i ∈ Finset.range b, (1 - (η : ℝ) ^ (i + 1) * ((q : ℝ) ^ (i + 1))⁻¹) := by
  unfold densP
  have h1 : Finset.Icc (1 : ℤ) b = (Finset.range b).image (fun i : ℕ => ((i : ℤ) + 1)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(x - 1).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [h1, Finset.prod_image (by intro x _ y _ hxy; simpa using hxy)]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 : ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h2, zpow_natCast, _root_.zpow_neg, zpow_natCast]
end Formalism.FourierDecayAlt.P.S3x6
