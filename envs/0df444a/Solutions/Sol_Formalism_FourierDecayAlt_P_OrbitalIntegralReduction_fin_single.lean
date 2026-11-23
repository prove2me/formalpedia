-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.fin_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:47.743617+00:00
-- url     : https://prove2.me/submissions/b02b6e2f-0a43-43af-a1fd-0a5c0b52dace

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_antidiagonal_block_mul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_st_lowW_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_integral_points_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (hD : LocalDatum K R ψ) (n : ℕ) (π : Kˣ) :
    {q : upUniG K n ⧸ intSub R (upUniG K n) |
      IsInt R ((π : K) • sec_m (Quotient.out q))}.Finite := by
  have key := integral_points_finite K R ψ hD (addBlock h0 n π)
  have hinj : Function.Injective (fun q₂ : upUniG K n ⧸ intSub R (upUniG K n) =>
      ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n π))) := by
    intro a b h
    exact (Prod.ext_iff.1 h).2
  refine (key.preimage (Set.injOn_of_injective hinj)).subset ?_
  intro q₂ hq
  have hrep : rep R ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n π)) = (1, Quotient.out q₂) :=
    Prod.ext (st_lowW_single n π _) rfl
  show IsInt R (orbZ (addBlock h0 n π) (rep R ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n π))))
  rw [hrep]
  show IsInt R ((1 : Matrix (Fin n) (Fin n) K) * antidiagonalBlock n π * sec_m (Quotient.out q₂))
  rw [Matrix.one_mul, antidiagonal_block_mul_left]
  intro a b
  exact hq (Fin.rev a) b
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
