-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.slice_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:21:11.962785+00:00
-- url     : https://prove2.me/submissions/c7bfe13c-e650-4122-98f7-2d0b5cbeb19f

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bSlice_add
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bSlice_zero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_injective_apply_prodMk_of_injective
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bSlice_mapDomain_same
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bSlice_mapDomain_ne

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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
variable {R : Type u} [CommRing R] {T σ ρ : Type}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (e : T × σ → ρ) (he : Function.Injective e) (Q : T → MvPolynomial σ R)
    (s : Finset T) :
    ∀ κ ∈ (∏ t ∈ s, rename (fun y => e (t, y)) (Q t)).support,
      (∀ t ∈ s, bSlice e he t κ ∈ (Q t).support) ∧ ∀ t, t ∉ s → bSlice e he t κ = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro κ hm
    simp only [Finset.prod_empty] at hm
    have hz : κ = 0 := by
      by_contra hne
      rw [MvPolynomial.mem_support_iff] at hm
      apply hm
      rw [MvPolynomial.coeff_one, if_neg (Ne.symm hne)]
    subst hz
    exact ⟨fun t ht => absurd ht (Finset.notMem_empty t), fun t _ => bSlice_zero e he t⟩
  | insert c s hc ih =>
    intro κ hm
    rw [Finset.prod_insert hc] at hm
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
    rw [support_rename_of_injective (injective_apply_prodMk_of_injective e he c), Finset.mem_image] at hm1
    obtain ⟨u, hu, rfl⟩ := hm1
    obtain ⟨ih1, ih2⟩ := ih m2 hm2
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · rw [bSlice_add]
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · rw [bSlice_mapDomain_same, ih2 t hc, add_zero]
        exact hu
      · have hne : t ≠ c := fun h => hc (h ▸ ht')
        rw [bSlice_mapDomain_ne e he hne, zero_add]
        exact ih1 t ht'
    · rw [Finset.mem_insert, not_or] at ht
      rw [bSlice_add, bSlice_mapDomain_ne e he ht.1, ih2 t ht.2, add_zero]
end Formalism.DworkPowerSeriesWeights
