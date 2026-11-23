-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.dot_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:22.309318+00:00
-- url     : https://prove2.me/submissions/4fb38aa3-6fa5-49fd-a297-614a5d232e58

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_mem_PL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x6
open Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {m : ℕ} (ψ : AddChar K ℂ)
namespace Formalism.FourierDecayAlt.P.A6x6
theorem _root_.solution {L : AddSubgroup K} {x u : Fin m → K} (hx : x ∈ PL L m)
    (hu : u ∈ PL (perp ψ L) m) : ψ (x ⬝ᵥ u) = 1 := by
  unfold dotProduct
  refine Finset.sum_induction _ (fun a => ψ a = 1)
    (fun a b ha hb => by rw [AddChar.map_add_eq_mul, ha, hb, one_mul])
    (AddChar.map_zero_eq_one ψ) fun i _ => ?_
  rw [mul_comm]
  exact mem_PL.1 hu i _ (mem_PL.1 hx i)
end Formalism.FourierDecayAlt.P.A6x6
