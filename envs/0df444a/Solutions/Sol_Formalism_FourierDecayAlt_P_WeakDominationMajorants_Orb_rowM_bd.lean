-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.rowM_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:39:28.44991+00:00
-- url     : https://prove2.me/submissions/fa67c16c-f7e0-4914-bd96-131b05e61eba

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_LU_norm_mul_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_one_le_X
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_orbit_constant_five_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_orbit_constant_eight_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_cPg_nn
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_pow_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_Linv_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_Pmx_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_Pmg_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_rowM_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix
open Matrix
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakDominationMajorants Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
variable {k r : ℕ}
variable {Γ δ : ℝ} {g n n' : Mat k r}
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
theorem _root_.solution (hΓ : 1 ≤ Γ) (hδ : 0 < δ) (hg : g ∈ GV k r) (hgΓ : gN g ≤ Γ) (hld : ∀ b, δ ≤ ‖ld (Zm g) b‖)
    (hdet : δ ≤ ‖(Zm g).det‖) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r)
    (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) (a : Fin r) :
    ‖n j (esI k r a)‖ ≤ c10 r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r + 1) := by
  set X := gN (n⁻¹ * g * n')
  have hX : 1 ≤ X := one_le_X hg hn hn'
  rw [rowM_eq hδ hdet hn hn' j hj1 hj2 a]
  have h1 := norm_mul_entry (Pm g) (Lm n)⁻¹ _ _ (cPg_nn hΓ hδ) (Pmg_bd hΓ hδ hgΓ hdet)
    (Linv_bd hΓ hδ hg hgΓ hld hdet hn hn') j a
  have h2 := Pmx_bd hδ hg hdet hn hn' j a
  have p1 : X ^ (2 * r) ≤ X ^ (2 * r + 1) := pow_mono hX (by omega)
  have p2 : X ^ (r + 1) ≤ X ^ (2 * r + 1) := pow_mono hX (by omega)
  have := orbit_constant_five_nonneg (r := r) hΓ hδ; have := cPg_nn (r := r) hΓ hδ; have := orbit_constant_eight_nonneg (r := r) hΓ hδ
  calc ‖(Pm g * (Lm n)⁻¹) j a - Pm (n⁻¹ * g * n') j a‖
      ≤ ‖(Pm g * (Lm n)⁻¹) j a‖ + ‖Pm (n⁻¹ * g * n') j a‖ := norm_sub_le _ _
    _ ≤ (r : ℝ) * (cPg r Γ δ * (c5 r Γ δ * X ^ (2 * r))) + c8 r δ * X ^ (r + 1) := by
        simpa using add_le_add h1 h2
    _ ≤ (r : ℝ) * (cPg r Γ δ * (c5 r Γ δ * X ^ (2 * r + 1))) + c8 r δ * X ^ (2 * r + 1) := by gcongr
    _ = c10 r Γ δ * X ^ (2 * r + 1) := by unfold c10; ring
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
