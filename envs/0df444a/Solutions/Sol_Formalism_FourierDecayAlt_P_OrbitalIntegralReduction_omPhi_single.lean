-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.omPhi_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:49.196993+00:00
-- url     : https://prove2.me/submissions/522807f0-171d-4ed6-9540-f5729d1282d6

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_antidiagonal_block_mul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_st_lowW_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_st_sLow_one

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
theorem _root_.solution (n : ℕ) (z : Kˣ) (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ) :
    omPhi R ψ (addBlock h0 n z) Φ = ∑ᶠ q : upUniG K n ⧸ intSub R (upUniG K n),
      Φ n (((z : K) • sec_m (Quotient.out q)).submatrix Fin.rev id) *
        ψ (sUp (sec_m (Quotient.out q))) := by
  unfold omPhi
  symm
  refine finsum_eq_of_bijective
    (fun q₂ => ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n z))) ⟨?_, ?_⟩ ?_
  · intro a b h
    exact (Prod.ext_iff.1 h).2
  · rintro ⟨q₁, q₂⟩
    refine ⟨q₂, ?_⟩
    refine Prod.ext ?_ rfl
    show Quotient.mk _ 1 = q₁
    rw [← Quotient.out_eq q₁, st_lowW_single n z (Quotient.out q₁)]
  · intro q₂
    have hrep : rep R ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n z)) = (1, Quotient.out q₂) :=
      Prod.ext (st_lowW_single n z _) rfl
    show _ = Φ (addBlock h0 n z).1.sum (orbZ (addBlock h0 n z)
        (rep R ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n z)))) *
      phase ψ (rep R ((Quotient.mk _ 1, q₂) : Cos R (addBlock h0 n z)))
    rw [hrep]
    show _ = Φ n ((1 : Matrix (Fin n) (Fin n) K) * antidiagonalBlock n z * sec_m (Quotient.out q₂)) *
      ψ (sLow (1 : Matrix (Fin n) (Fin n) K) + sUp (sec_m (Quotient.out q₂)))
    rw [Matrix.one_mul, antidiagonal_block_mul_left, st_sLow_one, zero_add]
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
