-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_hW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:47.378588+00:00
-- url     : https://prove2.me/submissions/57aaba56-a81b-493e-9f19-ad800d331ae6

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_E_eq
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_Eul_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_mem_dualWeyl_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {r n : ℕ}
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {μ : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) ℂ} (hf : f ∈ dualWeyl ℂ r n μ)
    (s : Fin n) : ∑ b : Fin r, X (b, s) * pderiv (b, s) f = C ((μ s : ℕ) : ℂ) * f := by
  have hwh := (mem_dualWeyl_iff.1 hf).1
  rw [xn_E_eq, ← xn_Eul_eq]
  have hmono : ∀ (d : Fin r × Fin n →₀ ℕ) (c : ℂ), ndEul ℂ r n s (monomial d c) =
      C (((Finsupp.weight (colW r n) d) s : ℕ) : ℂ) * monomial d c := by
    intro d c
    induction d using Finsupp.induction
    next =>
      rw [← MvPolynomial.C_apply, MvPolynomial.derivation_C]
      simp
    next v k d hv hk ih =>
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [MvPolynomial.monomial_single_add, Derivation.leibniz, ih, Derivation.leibniz_pow]
      simp only [ndEul, MvPolynomial.mkDerivation_X, map_add, Pi.add_apply, Nat.add_sub_cancel]
      first
      | rw [Finsupp.weight_single_index]
      | rw [Finsupp.weight_single]
      simp only [colW, smul_eq_mul, nsmul_eq_mul, Pi.smul_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
        map_add, map_mul, map_natCast, map_one]
      ring
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hmono, hwh (MvPolynomial.mem_support_iff.1 hd)]
end Formalism.BranchingDeterminantCap
