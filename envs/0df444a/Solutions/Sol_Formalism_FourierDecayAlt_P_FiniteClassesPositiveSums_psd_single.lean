-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums.psd_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:41.560384+00:00
-- url     : https://prove2.me/submissions/dc7db55b-42a1-47bd-a73e-14f3dfb79390

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteClassesPositiveSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_psd_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_psd_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_periodic_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteClassesPositiveSums_finsum_classes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
variable {K : Type} [CommRing K] (R : Subring K)
variable {R} {F : Finset (Point K)} {Lc : Set K} {S : Finset (K ⧸ R.toAddSubgroup)}
namespace Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
theorem _root_.solution (hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ Lc → y ∈ S)
    {M : Point K → Point K → ℂ} {Θ : K → Point K → Point K → ℂ}
    (h1 : ∀ x, ∀ r ∈ R, Θ (x + r) = Θ x) (h2 : ∀ x, IsPSD F (Θ x))
    (h3 : ∀ x, x ∉ Lc → ∀ h ∈ F, ∀ h' ∈ F, Θ x h h' = 0)
    (h5 : IsPSD F (fun h h' => M h h' - ∑ᶠ y : K ⧸ R.toAddSubgroup, Θ (Quotient.out y) h h'))
    (x : K) : IsPSD F (fun h h' => M h h' - Θ x h h') := by
  classical
  have key := psd_add h5 (psd_sum (S.erase ((x : K) : K ⧸ R.toAddSubgroup))
    (fun y => Θ (Quotient.out y)) (fun y _ => h2 _))
  refine psd_congr key ?_
  intro h hh h' hh'
  have e1 := finsum_classes hS h3 hh hh'
  have e2 : Θ (Quotient.out ((x : K) : K ⧸ R.toAddSubgroup)) = Θ x := periodic_out R Θ h1 x
  simp only [e1]
  by_cases hx : ((x : K) : K ⧸ R.toAddSubgroup) ∈ S
  · rw [← add_sum_erase S (fun y => Θ (Quotient.out y) h h') hx, e2]
    ring
  · rw [erase_eq_of_notMem hx]
    have : Θ x h h' = 0 := by
      rw [← e2]
      exact h3 _ (fun hc => hx (hS _ hc)) h hh h' hh'
    rw [this]; ring
end Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums
