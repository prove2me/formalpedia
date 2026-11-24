-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.nz_of_domL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:32:43.33437+00:00
-- url     : https://prove2.me/submissions/055d59d2-da8f-44e0-a1c3-e01a1d66ca31

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet

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
theorem _root_.solution {D : RealPlaceData k r Wp Wq} {L : Finset (Fin (r + 2))} {g : Mat k r} (hg : g ∈ C6.domL D L)
    {nf : ℕ} {e : CT k r nf × List (Mat k r)} (he : Good L e) :
    (∀ l, (e.1.a l ≠ 0 ∨ e.1.b l ≠ 0) → Dmin k r D.z D.z' g l ≠ 0) ∧
      (e.1.c ≠ 0 → ((Gf k r D.z D.z' g : ℝ) : ℂ) ≠ 0) := by
  have hlast : Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0 := by
    intro h0
    have hG : 0 < Gf k r D.z D.z' g := hg.2.1
    simp only [Gf, h0, Complex.normSq_zero, zero_sub] at hG
    have := mul_nonneg (mul_pos D.T_pos D.T'_pos).le (Complex.normSq_nonneg (Dmin k r D.z D.z' g ⟨r, by omega⟩))
    linarith
  obtain ⟨hab, -, -⟩ := he
  refine ⟨fun l hl => ?_, fun _ => ?_⟩
  · rcases hab l hl with hl | rfl
    · exact hg.2.2 l hl
    · exact hlast
  · exact_mod_cast hg.2.1.ne'
end Formalism.FourierDecayAlt.P.MinorPolynomials
