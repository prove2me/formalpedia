-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.li_of_lead
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:21.642677+00:00
-- url     : https://prove2.me/submissions/045f2f86-de9b-4e65-913b-0007d6707110

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord

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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
theorem _root_.solution {k V V' ι O : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup V']
    [Module k V'] [LinearOrder O] (v : ι → V) (Γ : ι → O) (π : O → V →ₗ[k] V')
    (h0 : ∀ i γ, Γ i < γ → π γ (v i) = 0)
    (hli : ∀ γ, LinearIndependent k (fun i : {i // Γ i = γ} => π γ (v i.1))) :
    LinearIndependent k v := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  by_contra hgi
  have hne : (s.filter fun j => g j ≠ 0).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  obtain ⟨j, hj, hjmax⟩ := (s.filter fun j => g j ≠ 0).exists_max_image Γ hne
  have hsum : ∑ k ∈ s, g k • π (Γ j) (v k) = 0 := by
    have := congrArg (π (Γ j)) hg
    simpa only [map_sum, map_smul, map_zero] using this
  have hsum2 : ∑ k ∈ s.filter (fun k => Γ k = Γ j), g k • π (Γ j) (v k) = 0 := by
    rw [Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun k hk => ?_) hsum
    split_ifs with hk'
    · rfl
    · by_cases hgk : g k = 0
      · simp [hgk]
      · have hle : Γ k ≤ Γ j := hjmax k (Finset.mem_filter.mpr ⟨hk, hgk⟩)
        rw [h0 k (Γ j) (lt_of_le_of_ne hle hk'), smul_zero]
  have hsumT : ∑ x ∈ s.subtype (fun k => Γ k = Γ j), g x.1 • π (Γ j) (v x.1) = 0 := by
    rw [Finset.sum_subtype_eq_sum_filter (f := fun k => g k • π (Γ j) (v k))]
    exact hsum2
  have hj0 := (linearIndependent_iff'.mp (hli (Γ j))) (s.subtype (fun k => Γ k = Γ j)) (fun x => g x.1) hsumT
    ⟨j, rfl⟩ (Finset.mem_subtype.mpr (Finset.mem_filter.mp hj).1)
  exact (Finset.mem_filter.mp hj).2 hj0
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
