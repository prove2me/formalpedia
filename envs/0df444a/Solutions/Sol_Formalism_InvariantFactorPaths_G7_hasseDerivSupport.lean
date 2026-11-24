-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.hasseDerivSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:01:31.534276+00:00
-- url     : https://prove2.me/submissions/3955f1e1-fe93-4433-962d-2dc798307489

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_CC
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_gen
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_pow_single
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_prod
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : HasseDegree := by
  intro K ι κ _ _ b β Q n hn
  classical
  change n ∈ (MvPolynomial.coeff β (shiftPoly b Q)).support at hn
  rw [shiftPoly_eq_sum, MvPolynomial.coeff_sum, MvPolynomial.mem_support_iff,
    MvPolynomial.coeff_sum] at hn
  obtain ⟨n0, hn0, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hs : ∑ x ∈ n0.support, Finsupp.single x (n0 x) = n0 := Finsupp.sum_single n0
  have h := biLe_mul (biLe_CC (ι := ι) (κ := κ) (MvPolynomial.coeff n0 Q))
    (biLe_prod n0.support (fun x => Finsupp.single x (n0 x)) _
      (fun x _ => biLe_pow_single (biLe_gen b x) (n0 x)))
  simp only [zero_add, hs] at h
  obtain ⟨h1, h2⟩ := h β n (MvPolynomial.mem_support_iff.mpr hne)
  refine ⟨n0, hn0, h1, ?_⟩
  rwa [Finsupp.degree_eq_sum β] at h2
end Formalism.InvariantFactorPaths.G7
