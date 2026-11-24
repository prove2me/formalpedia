-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.hecke_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:25.190102+00:00
-- url     : https://prove2.me/submissions/b56eab2e-a349-4c27-832f-561ac96de1df

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric
import Theorems.Thm_Formalism_FT_SymmetricSeries_esymm_hsymm_rel


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
open CSym
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : HEConvolution := by
  intro K σ _ _ _ x n hn
  have h := Formalism.FT.SymmetricSeries.esymm_hsymm_rel (σ := σ) (R := K) n hn
  have h2 := congrArg (MvPolynomial.eval x) h
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_zero] at h2
  rw [← Finset.sum_range_reflect]
  have hterm : ∀ j ∈ range (n + 1), (-1 : K) ^ (n + 1 - 1 - j) * hF x (n + 1 - 1 - j) * eF x (n - (n + 1 - 1 - j)) =
      (-1) ^ n * ((-1) ^ j * MvPolynomial.eval x (MvPolynomial.esymm σ K j) *
        MvPolynomial.eval x (MvPolynomial.hsymm σ K (n - j))) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [show n + 1 - 1 - j = n - j by omega, show n - (n - j) = j by omega]
    have e : (-1 : K) ^ n = (-1) ^ (n - j) * (-1) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    have e2 : (-1 : K) ^ (n - j) = (-1) ^ n * (-1) ^ j := by
      rw [e, mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]
    unfold hF eF
    rw [e2]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, h2, mul_zero]
end Formalism.InvariantFactorPaths.G7
