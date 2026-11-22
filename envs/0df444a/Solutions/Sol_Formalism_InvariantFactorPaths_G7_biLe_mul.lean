-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biLe_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:12.125504+00:00
-- url     : https://prove2.me/submissions/13c64d27-b099-4ea1-b711-378b5848d414

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree

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
variable {K ι κ : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {n0 n0' : ι →₀ ℕ} {W W' : MvPolynomial κ (MvPolynomial ι K)} (h : BiLe n0 W)
    (h' : BiLe n0' W') : BiLe (n0 + n0') (W * W') := by
  classical
  intro β n hn
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul, MvPolynomial.coeff_sum] at hn
  obtain ⟨q, hq, hq0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  rw [MvPolynomial.coeff_mul] at hq0
  obtain ⟨r, hr, hr0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq0
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq hr
  have hA : r.1 ∈ (MvPolynomial.coeff q.1 W).support :=
    MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hr0)
  have hB : r.2 ∈ (MvPolynomial.coeff q.2 W').support :=
    MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hr0)
  obtain ⟨hA1, hA2⟩ := h q.1 r.1 hA
  obtain ⟨hB1, hB2⟩ := h' q.2 r.2 hB
  refine ⟨?_, ?_⟩
  · rw [← hr]
    exact add_le_add hA1 hB1
  · rw [← hr, ← hq]
    simp only [map_add]
    omega
end Formalism.InvariantFactorPaths.G7
