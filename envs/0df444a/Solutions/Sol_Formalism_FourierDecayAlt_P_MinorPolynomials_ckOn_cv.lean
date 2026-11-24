-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_cv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:44:34.251992+00:00
-- url     : https://prove2.me/submissions/3275a625-2d17-42ae-bedf-6b1555317d1d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_cda_cvs
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_ckOn_epart
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_domL_gpos
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_isOpen_big_cell_set
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_mem_domL
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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) {L : Finset (Fin (r + 2))} {e : CT k r nf × List (Mat k r)}
    (he : Good L e) : CkOn ⊤ (C6.domL D L) (cv D fib e.1) := by
  intro g₀ hg₀
  have hgpos : g₀ ∈ GPos D := domL_gpos hg₀
  obtain ⟨U, f, hU, hgU, hf, hfe⟩ := ckOn_epart D fib hfib e.1.es he.2.1 g₀ hgpos
  have hcvs : ContDiffOn ℝ ∞ (cvs D e.1) (V0 D L) :=
    (isOpen_big_cell_set D L).contDiffOn_iff.2 (fun x hx => cda_cvs D he hx)
  refine ⟨U ∩ V0 D L, fun g => cvs D e.1 g • f g, hU.inter (isOpen_big_cell_set D L), ⟨hgU, ((mem_domL D L g₀).1 hg₀).2⟩, ?_, ?_⟩
  · exact (hcvs.mono inter_subset_right).smul (hf.mono inter_subset_left)
  · intro g hg hgG
    simp only [cv, hfe g hg.1 hgG]
end Formalism.FourierDecayAlt.P.MinorPolynomials
