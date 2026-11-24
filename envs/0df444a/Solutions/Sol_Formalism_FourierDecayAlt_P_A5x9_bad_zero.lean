-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.bad_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:21.198802+00:00
-- url     : https://prove2.me/submissions/f5a24a85-65ca-4872-95ff-8b060bfcd327

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_fibre_zero
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
noncomputable section
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (ψ : AddChar K ℂ) (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hun : ∀ x : K, conj (ψ x) = ψ (-x))
    (hfin : ∀ (m : ℕ) (Z : Matrix (Fin m) (Fin m) K), IsInt R Z → IsUnit Z.det →
      Finite (coker R Z))
    (h h' : Point K) (s : ℕ) (t t' : Kˣ) (k : ℕ) (hh : h.1.sum = h'.1.sum) (hk : h.1.sum ≤ k)
    (hks : k + 2 ≤ h.1.sum + s)
    (Q : Finset (Cos R (addBlock h s t) × Cos R (addBlock h' s t')))
    (hQ : ∀ q, q ∈ Q ↔ IsInt R (orbZ (addBlock h s t) (rep R q.1)) ∧
      IsInt R (orbZ (addBlock h' s t') (rep R q.2))) :
    ∑ q ∈ Q, (badN R k (addBlock h s t) (addBlock h' s t') q : ℂ) *
        (phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))) = 0 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (t := Q.image (fun q => (kap R k (addBlock h s t) q.1, kap R k (addBlock h' s t') q.2)))
    (g := fun q => (kap R k (addBlock h s t) q.1, kap R k (addBlock h' s t') q.2))
    (fun q hq => Finset.mem_image_of_mem _ hq)]
  apply Finset.sum_eq_zero
  rintro ⟨y, y'⟩ _
  have key := fibre_zero R ψ hsd hun hfin h h' s t t' k hh hk hks Q hQ y y'
  rw [← key]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext q
  simp only [Finset.mem_filter, Prod.mk.injEq]
end Formalism.FourierDecayAlt.P.A5x9
