-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BranchingSystems.fin_cap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:59:28.005689+00:00
-- url     : https://prove2.me/submissions/38efeaf8-c833-4591-8c9f-da6184f8c145

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_Qr_mem_CapSp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BranchingSystems
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.FourierDecayAlt.P.BranchingSystems
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (β : ℂ) (M : Fin n → ℤ) (i : Fin n) :
    {t : ℤ | CapSp E (shf β (Function.update M i t)) ≠ ⊥}.Finite := by
  obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (Finset.univ.image fun j : Fin n => -(shf β M j))
  have hc : (∏ j ∈ Finset.univ.erase i, (w + shf β M j)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j _ h0
    apply hw
    rw [Finset.mem_image]
    exact ⟨j, Finset.mem_univ _, by linear_combination -h0⟩
  have hf : ∀ t : ℤ, cpol (shf β (Function.update M i t)) w =
      (w + β + (t : ℂ)) * ∏ j ∈ Finset.univ.erase i, (w + shf β M j) := by
    intro t
    unfold cpol
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp [shf]; ring
    · apply Finset.prod_congr rfl
      intro j hj
      have hne : j ≠ i := Finset.ne_of_mem_erase hj
      simp [shf, Function.update_of_ne hne]
  refine Set.Finite.subset (Set.Finite.preimage
    (f := fun t : ℤ => cpol (shf β (Function.update M i t)) w) ?_
    (Module.End.finite_hasEigenvalue (qdet E w))) ?_
  · intro a _ b _ e
    simp only [hf] at e
    have e1 := mul_right_cancel₀ hc e
    have e2 : (a : ℂ) = b := by linear_combination e1
    exact_mod_cast e2
  · intro t ht
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ht
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (mem_CapSp.mp hv w), hv0⟩
end Formalism.FourierDecayAlt.P.BranchingSystems
