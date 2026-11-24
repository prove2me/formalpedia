-- Prove2me | solution 1 for Formalism.SA.P.trace_pow_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:46:29.083388+00:00
-- url     : https://prove2.me/submissions/db2cc01d-e03d-47fe-b0d7-ed9f6faeb8e2

import Definitions.Def_Formalism_LatticeRigidity_StatementD
import Mathlib
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Theorems.Thm_Formalism_SA_P_trace_pow_restrict_maxGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open Matrix Polynomial
open scoped ComplexOrder
variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
namespace Formalism.SA.P
theorem _root_.solution (f : Module.End K V) (j : ℕ) :
    LinearMap.trace K V (f ^ j) = ∑ μ ∈ (finite_eig f).toFinset,
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ j := by
  classical
  have htop : ⨆ μ ∈ (finite_eig f).toFinset, f.maxGenEigenspace μ = ⊤ := by
    refine eq_top_iff.mpr ?_
    first
    | rw [← Module.End.iSup_maxGenEigenspace_eq_top f]
    | rw [← Module.End.iSup_maxGenEigenspace_eq_top (f := f)]
    refine iSup_le fun μ => ?_
    by_cases hμ : f.maxGenEigenspace μ = ⊥
    · rw [hμ]; exact bot_le
    · exact le_iSup₂_of_le (f := fun μ (_ : μ ∈ (finite_eig f).toFinset) => f.maxGenEigenspace μ)
        μ (by simpa using hμ) le_rfl
  have hind : iSupIndep (fun μ : (finite_eig f).toFinset => f.maxGenEigenspace (μ : K)) := by
    first
    | exact (Module.End.independent_maxGenEigenspace f).comp Subtype.val_injective
    | exact (Module.End.iSupIndep_maxGenEigenspace f).comp Subtype.val_injective
  have hmap : ∀ μ : K, Set.MapsTo (f ^ j) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    fun μ => Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ
  have key := LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup _ hind hmap ⊤ htop.symm
  have htr := LinearMap.trace_restrict_eq_of_forall_mem (⊤ : Submodule K V) (f ^ j)
    (fun x => (Submodule.mem_top : (f ^ j) x ∈ (⊤ : Submodule K V)))
  exact htr.symm.trans (key.trans (Finset.sum_congr rfl fun μ _ => trace_pow_restrict_maxGen f μ j))
end Formalism.SA.P
