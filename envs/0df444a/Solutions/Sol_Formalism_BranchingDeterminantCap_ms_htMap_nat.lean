-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.ms_htMap_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:40.821244+00:00
-- url     : https://prove2.me/submissions/89fad088-10aa-4672-9fb4-74672ae93ece

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Theorems.Thm_Formalism_BranchingDeterminantCap_ms_opNorm_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution [Nonempty ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (n : ℕ) :
    htMap b X b X ((n : K) • (LinearMap.id : V →ₗ[K] V)) = 2 * Real.log n := by
  unfold Formalism.HN.htMap
  simp_rw [ms_opNorm_nat b X hX n]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.log_pow]
  have hc : (0 : ℝ) < (Fintype.card (InfinitePlace K) : ℝ) := by exact_mod_cast Fintype.card_pos
  simp only [Formalism.HN.nPl]
  field_simp
  push_cast
  ring
end Formalism.BranchingDeterminantCap
