-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.pderiv_keep_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:16.502553+00:00
-- url     : https://prove2.me/submissions/aa7e8f9f-f1b0-4c16-9db4-b9f9d44e25bd

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_ne_of_lt
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c : Fin r)
    (Mt : WithTop ℤ) :
    ∀ x ∈ restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | ((wt LL (K + 1) 0 m : ℤ) : WithTop ℤ) ≤ Mt},
      pderiv (Fin.last K, c) x ∈
        restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | ((wt LL (K + 1) 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.mem_restrictSupport_iff]
  refine (Finset.coe_subset.2 MvPolynomial.support_monomial_subset).trans ?_
  rw [Finset.coe_singleton, Set.singleton_subset_iff]
  have hmx := hx hm
  simp only [Set.mem_setOf_eq] at hmx ⊢
  refine le_trans ?_ hmx
  have hle : wt LL (K + 1) 0 (m - Finsupp.single (Fin.last K, c) 1) ≤ wt LL (K + 1) 0 m := by
    rw [wt_succ LL hv, wt_succ LL hv,
      wt_congr LL K 0 (m - Finsupp.single (Fin.last K, c) 1) m ?_]
    · have h3 : (m - Finsupp.single (Fin.last K, c) 1 : Fin (K + 1) × Fin r →₀ ℕ) (Fin.last K, 0) ≤
          m (Fin.last K, 0) := by
        rw [Finsupp.tsub_apply]
        exact Nat.sub_le _ _
      omega
    · intro i hi
      have hne : ((Fin.last K, c) : Fin (K + 1) × Fin r) ≠ (i, 0) :=
        fun h => last_ne_of_lt i hi (congrArg Prod.fst h)
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hne, Nat.sub_zero]
  exact_mod_cast hle
end Formalism.InvariantFactorPaths.L4
