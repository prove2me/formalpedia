-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.GG_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:06.760936+00:00
-- url     : https://prove2.me/submissions/2b2d361a-7be1-4336-a293-7343675b3277

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_orbital_integral_change_estimate

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
theorem _root_.solution (hD : LocalDatum K R ψ) (hC : Cst R ϖ L₀ Λ₀ Q a b) (m : ℕ) :
    ∃ b₁ : ℕ, ∀ Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ, PhiHyp R (m + 1) L₀ Λ₀ Q Φ →
    ∀ D' : Kˣ, ((D' : K) ∈ Q ∨ -(D' : K) ∈ Q) → ∀ μ ∈ R,
    ∀ (x l : Fin m → K) (y l' : Pr (m + 1) → K),
      (∀ k, ∃ r ∈ R, l k = μ * (ϖ : K) ^ b₁ * r) → (∀ p, ∃ r ∈ R, l' p = μ * (ϖ : K) ^ b₁ * r) →
      GG R ψ Φ (D' : K) (x + l) (y + l') = GG R ψ Φ (D' : K) x y ∧
      (GG R ψ Φ (D' : K) x y ≠ 0 → ∃ r ∈ R, g0 (D' : K) (x + l) - g0 (D' : K) x = μ * r) := by
  refine ⟨b + 3 * ((m + 1) * a) + 2 * a + 1, fun Φ hΦ D' hD' μ hμ x l y l' hl hl' => ?_⟩
  by_cases hG : GG R ψ Φ (D' : K) x y = 0
  · refine ⟨?_, fun h => absurd hG h⟩
    by_contra hne
    have hG' : GG R ψ Φ (D' : K) (x + l) (y + l') ≠ 0 := by rwa [hG] at hne
    have key := (orbital_integral_change_estimate hD hC m Φ hΦ D' hD' μ hμ (x + l) (-l) (y + l') (-l')
      (fun k => by
        obtain ⟨r, hr, e⟩ := hl k
        exact ⟨-r, R.neg_mem hr, by show -(l k) = _; rw [e]; ring⟩)
      (fun p => by
        obtain ⟨r, hr, e⟩ := hl' p
        exact ⟨-r, R.neg_mem hr, by show -(l' p) = _; rw [e]; ring⟩) hG').1
    rw [add_neg_cancel_right, add_neg_cancel_right] at key
    exact hne key.symm
  · obtain ⟨h1, h2⟩ := orbital_integral_change_estimate hD hC m Φ hΦ D' hD' μ hμ x l y l' hl hl' hG
    exact ⟨h1, fun _ => h2⟩
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
