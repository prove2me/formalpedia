-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.pw_Phi_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:54.747075+00:00
-- url     : https://prove2.me/submissions/4b366f71-27a6-41cc-9737-d12abd3c1bb1

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_det_HH_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_det_ZZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_prod_xt
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (hC : Cst R ϖ L₀ Λ₀ Q a b) {m : ℕ} (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (t D' ρ : K) (hD' : D' ∈ Q ∨ -D' ∈ Q) (x : Fin m → K)
    (y : Pr (m + 1) → K) (hx : ∀ k, IsUnit (x k)) (ht : Sm R ϖ b t) (hρ : Sm R ϖ b (ρ - x0 D' x)) :
    Φ (m + 1) (ZZ t (Fin.cons ρ x : Fin (m + 1) → K) y) = Φ (m + 1) (ZZ 0 (xt D' x) y) := by
  have hdet : (ZZ 0 (xt D' x) y).det ∈ Q ∨ -(ZZ 0 (xt D' x) y).det ∈ Q := by
    rcases det_ZZ 0 (xt D' x) y with e | e <;> rw [e, det_HH_zero, pw_prod_xt D' x hx]
    · exact hD'
    · rw [neg_neg]; exact hD'.symm
  have hY : ∀ i j, (ZZ t (Fin.cons ρ x : Fin (m + 1) → K) y - ZZ 0 (xt D' x) y) i j ∈ Λ₀ := by
    intro i j
    simp only [Matrix.sub_apply, ZZ, Matrix.submatrix_apply, id, HH]
    generalize Fin.rev i = i1
    by_cases h1 : i1 = j
    · subst h1
      rw [if_pos rfl, if_pos rfl]
      refine Fin.cases ?_ (fun k => ?_) i1
      · simpa [xt] using hC.abelian₂ _ hρ
      · simp [xt]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : i1 < j
      · rw [dif_pos h2, dif_pos h2, sub_self]; exact Λ₀.zero_mem
      · rw [dif_neg h2, dif_neg h2]
        by_cases h3 : j.val + 1 = i1.val
        · rw [if_pos h3, if_pos h3, sub_zero]; exact hC.abelian₂ _ ht
        · rw [if_neg h3, if_neg h3, sub_self]; exact Λ₀.zero_mem
  have := hΦ.2.2 _ _ hdet hY
  rwa [add_sub_cancel] at this
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
