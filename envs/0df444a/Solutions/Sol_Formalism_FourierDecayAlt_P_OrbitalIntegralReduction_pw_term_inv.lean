-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.pw_term_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:33.954574+00:00
-- url     : https://prove2.me/submissions/4ce081e6-efc3-4d9d-ad5e-d7a01c47548d

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_psi_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_lastE_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_lastE_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_ro_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_ro_low
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_ro_int

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
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (hD : LocalDatum K R ψ) {m : ℕ} (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (t c : K) (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (s : K)
    (ξ r : Fin m → K) (hr : ∀ i, r i ∈ R) :
    Φ (m + 1) ((Hm t c (ξ + r) u).submatrix Fin.rev id) * ψ (lastE (ξ + r) + s) =
      Φ (m + 1) ((Hm t c ξ u).submatrix Fin.rev id) * ψ (lastE ξ + s) := by
  have e1 : (Hm t c (ξ + r) u).submatrix Fin.rev id =
      (pw_ro r).submatrix Fin.rev Fin.rev * (Hm t c ξ u).submatrix Fin.rev id * 1 := by
    rw [pw_ro_mul, Matrix.mul_one]
    exact (Matrix.submatrix_mul_equiv (pw_ro r) (Hm t c ξ u) Fin.rev Fin.revPerm id).symm
  have hone : IsInt R (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    intro i j
    by_cases h : i = j
    · rw [h, Matrix.one_apply_eq]; exact R.one_mem
    · rw [Matrix.one_apply_ne h]; exact R.zero_mem
  rw [e1, hΦ.1 _ _ _ (pw_ro_low r) (pw_ro_int R r hr) (isUpUni_one K) hone, pw_lastE_add,
    show lastE ξ + lastE r + s = (lastE ξ + s) + lastE r by ring, AddChar.map_add_eq_mul,
    psi_R hD (pw_lastE_mem R r hr), mul_one]
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
