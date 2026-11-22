-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ops_keep_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:15.438899+00:00
-- url     : https://prove2.me/submissions/8ede6335-6ae2-4175-9c1e-7a2ec0a0a31a

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {k σ : Type} [Field k]
namespace Formalism.CountingSumsFrames
theorem _root_.solution (S : Set σ) (Q : Set (σ →₀ ℕ))
    (hQ : ∀ m m' : σ →₀ ℕ, (∀ v, v ∉ S → m v = m' v) → m ∈ Q → m' ∈ Q)
    {T : Module.End k (MvPolynomial σ k)} (hT : T ∈ FockB.Ops S) :
    ∀ x ∈ restrictSupport k Q, T x ∈ restrictSupport k Q := by
  unfold FockB.Ops at hT
  induction hT using Algebra.adjoin_induction
  · rename_i T' hT'
    simp only [FockB.atoms, Set.mem_setOf_eq] at hT'
    obtain ⟨u, hu, rfl | rfl⟩ := hT'
    · intro z hz
      rw [MvPolynomial.mem_restrictSupport_iff] at hz
      show X u * z ∈ restrictSupport k Q
      rw [MvPolynomial.as_sum z, Finset.mul_sum]
      refine Submodule.sum_mem _ fun m hm => ?_
      rw [X, monomial_mul, one_mul, MvPolynomial.mem_restrictSupport_iff]
      refine (Finset.coe_subset.mpr support_monomial_subset).trans ?_
      rw [Finset.coe_singleton, Set.singleton_subset_iff]
      refine hQ m _ (fun w hw => ?_) (hz hm)
      have : u ≠ w := fun h => hw (h ▸ hu)
      simp [Finsupp.single_apply, this]
    · intro z hz
      rw [MvPolynomial.mem_restrictSupport_iff] at hz
      show pderiv u z ∈ restrictSupport k Q
      rw [MvPolynomial.as_sum z, map_sum]
      refine Submodule.sum_mem _ fun m hm => ?_
      rw [pderiv_monomial, MvPolynomial.mem_restrictSupport_iff]
      refine (Finset.coe_subset.mpr support_monomial_subset).trans ?_
      rw [Finset.coe_singleton, Set.singleton_subset_iff]
      refine hQ m _ (fun w hw => ?_) (hz hm)
      have : u ≠ w := fun h => hw (h ▸ hu)
      simp [Finsupp.single_apply, this]
  · rename_i c
    intro z hz
    rw [Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ _ hz
  · rename_i ihx ihy
    intro z hz
    rw [LinearMap.add_apply]
    exact Submodule.add_mem _ (ihx z hz) (ihy z hz)
  · rename_i ihx ihy
    intro z hz
    exact ihx _ (ihy z hz)
end Formalism.CountingSumsFrames
