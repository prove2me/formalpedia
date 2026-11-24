-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lattice_average_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:18.62702+00:00
-- url     : https://prove2.me/submissions/692fdbf1-5f98-494d-bfd7-7d19dba99d48

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_bad_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_isUnit_orbZ_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_top_intTT_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_card_and_eq_add_card
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_finite_coker
import Theorems.Thm_Formalism_FourierDecayAlt_P_integral_points_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x9
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.AvgClaim := by
  intro K _ _ _ R ψ hD h h' s t t' k hh hk hks
  classical
  have hF := (integral_points_finite K R ψ hD (addBlock h s t)).prod
    (integral_points_finite K R ψ hD (addBlock h' s t'))
  have hQ : ∀ q, q ∈ hF.toFinset ↔ IsInt R (orbZ (addBlock h s t) (rep R q.1)) ∧
      IsInt R (orbZ (addBlock h' s t') (rep R q.2)) := by
    intro q
    rw [Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hfin : ∀ (m : ℕ) (Z : Matrix (Fin m) (Fin m) K), IsInt R Z → IsUnit Z.det →
      Finite (coker R Z) := fun m Z hZ hd => A5x3.finite_coker hD Z hZ hd
  have hbad := bad_zero R ψ hD.selfDual hD.unitary hfin h h' s t t' k hh hk hks hF.toFinset hQ
  rw [top_intTT_eq R ψ (k + 1) _ _ hF.toFinset hQ, top_intTT_eq R ψ k _ _ hF.toFinset hQ]
  refine Eq.trans ?_ (add_zero _)
  rw [← hbad, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [← add_mul]
  congr 1
  have hq' := (hQ q).1 hq
  have f1 := hfin _ _ hq'.1 (isUnit_orbZ_det _ _)
  have f2 := hfin _ _ hq'.2 (isUnit_orbZ_det _ _)
  have f3 : Finite (coker R (orbZ (addBlock h s t) (rep R q.1)) ≃ₗ[R]
      coker R (orbZ (addBlock h' s t') (rep R q.2))) :=
    Finite.of_injective (fun φ => (φ : coker R (orbZ (addBlock h s t) (rep R q.1)) →
      coker R (orbZ (addBlock h' s t') (rep R q.2)))) DFunLike.coe_injective
  have hs := card_and_eq_add_card
    (fun φ : coker R (orbZ (addBlock h s t) (rep R q.1)) ≃ₗ[R]
      coker R (orbZ (addBlock h' s t') (rep R q.2)) =>
      φ ∈ isoZZ R (orbZ (addBlock h s t) (rep R q.1)) (orbZ (addBlock h' s t') (rep R q.2)))
    (fun φ => InTT R (k + 1) (orbZ (addBlock h s t) (rep R q.1))
      (orbZ (addBlock h' s t') (rep R q.2)) φ)
    (fun φ => InTT R k (orbZ (addBlock h s t) (rep R q.1))
      (orbZ (addBlock h' s t') (rep R q.2)) φ)
    (fun φ hφ j hj hjn => hφ j (by omega) hjn)
  rw [hs, Nat.cast_add]
  rfl
end Formalism.FourierDecayAlt.P
