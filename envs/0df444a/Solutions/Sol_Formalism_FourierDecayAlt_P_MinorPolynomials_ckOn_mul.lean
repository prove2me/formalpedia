-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:47:51.799408+00:00
-- url     : https://prove2.me/submissions/ff8f1e09-9b77-42b9-a88b-4f3f9d6f2e35

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_Bd_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution {UU : Set (Mat k r)} {A B : Mat k r → C6.EndH Wp Wq} (hA : CkOn ⊤ UU A) (hB : CkOn ⊤ UU B) :
    CkOn ⊤ UU (fun g => A g * B g) := by
  intro g₀ hg₀
  obtain ⟨U, f, hU, hgU, hf, hfe⟩ := hA g₀ hg₀
  obtain ⟨V, f', hV, hgV, hf', hfe'⟩ := hB g₀ hg₀
  refine ⟨U ∩ V, fun g => f g * f' g, hU.inter hV, ⟨hgU, hgV⟩, ?_, ?_⟩
  · exact (hf.mono inter_subset_left).mul (hf'.mono inter_subset_right)
  · intro g hg hgG
    simp only [hfe g hg.1 hgG, hfe' g hg.2 hgG]
end Formalism.FourierDecayAlt.P.MinorPolynomials
