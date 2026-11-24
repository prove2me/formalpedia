-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.sum_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:49:46.084939+00:00
-- url     : https://prove2.me/submissions/dfc6f06c-0363-417a-9c3f-8c8b1aa2d797

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
theorem _root_.solution {t n : ℕ} {M : Type*} [AddCommMonoid M] (e : Fin t ≃ Fin n) (F : (Fin t → Fin n) → M)
    (hF : ∀ c, ¬ Function.Injective c → F c = 0) :
    ∑ c, F c = ∑ τ : Equiv.Perm (Fin t), F (e ∘ τ) := by
  classical
  rw [← Finset.sum_filter_of_ne (p := Function.Injective) (fun c _ hc => by
    by_contra h
    exact hc (hF c h))]
  symm
  refine Finset.sum_bij' (fun τ _ => e ∘ τ)
    (fun (c : Fin t → Fin n) (hc : c ∈ Finset.univ.filter (fun c : Fin t → Fin n => Function.Injective c)) =>
      Equiv.ofBijective (e.symm ∘ c)
        ((Finite.injective_iff_bijective).mp (e.symm.injective.comp (Finset.mem_filter.mp hc).2)))
    ?_ ?_ ?_ ?_ ?_
  · intro τ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact e.injective.comp τ.injective
  · intro c _
    exact Finset.mem_univ _
  · intro τ _
    ext j
    simp
  · intro c _
    funext j
    simp
  · intro τ _
    rfl
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
