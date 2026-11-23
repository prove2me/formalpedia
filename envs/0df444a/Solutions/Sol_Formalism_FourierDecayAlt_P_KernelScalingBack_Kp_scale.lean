-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.Kp_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:43.349687+00:00
-- url     : https://prove2.me/submissions/64c1dc10-d544-4ece-8f9c-5ff9ca851258

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_isInt_mul_DG
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_orbZ_fm
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_fm_bij
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_iso_mul_DG
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_phase_fm
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_card_isoZZ_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_isoZZ_refl
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_Kp_eq_section
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_inv_toCos_rep
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K) (S : List ℕ) (T c : ℕ → Kˣ)
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1)
    (hc : ∀ b, ((c b : Kˣ) : K) ∈ R ∧ (((c b)⁻¹ : Kˣ) : K) ∈ R)
    (hA : ∀ p : lowW K S T × upUniG K S.sum, IsInt R (orbZ ((S, T) : Point K) p) →
      ∀ j b : Fin S.sum, j.val + 1 = S.sum →
        ((((dg S c j)⁻¹ : Kˣ) : K) - 1) * (orbZ ((S, T) : Point K) p)⁻¹ j b ∈ R)
    (hB : ∀ p : lowW K S T × upUniG K S.sum, IsInt R (orbZ ((S, T) : Point K) p) →
      ∀ (j : Fin S.sum) (hj : j.val + 1 < S.sum),
      ((((dg S c j)⁻¹ : Kˣ) : K) * ((dg S c ⟨j.val + 1, hj⟩ : Kˣ) : K) - 1) *
        (((p.2⁻¹ : upUniG K S.sum) : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) j
          ⟨j.val + 1, hj⟩ ∈ R)
    (w' : Point K) :
    Kp R ψ ((S, T * c) : Point K) w' = Kp R ψ ((S, T) : Point K) w' := by
  have hd : ∀ b, ((dg S c b : Kˣ) : K) ∈ R ∧ (((dg S c b)⁻¹ : Kˣ) : K) ∈ R := fun b => hc _
  rw [A5x8.Kp_eq_section R ψ hψ ((S, T * c) : Point K) w' (Cos R ((S, T) : Point K)) (Cos R w')
    (fun q => fm S T c (rep R q)) (fun q => rep R q) (fm_bij R S T c hc)
    (by simp only [A5x8.inv_toCos_rep]; exact Function.bijective_id)]
  unfold Kp
  refine finsum_congr fun q => ?_
  show A5x8.Gterm R ψ ((S, T * c) : Point K) w' (fm S T c (rep R q.1)) (rep R q.2) =
    A5x8.Gterm R ψ ((S, T) : Point K) w' (rep R q.1) (rep R q.2)
  generalize rep R q.1 = p
  generalize rep R q.2 = p'
  unfold A5x8.Gterm
  by_cases hZ : IsInt R (orbZ ((S, T) : Point K) p)
  · rw [phase_fm R S T c ψ hψ p (hB p hZ), orbZ_fm,
      ← A5x4.card_isoZZ_congr R (iso_mul_DG R (dg S c) hd _ (hA p hZ)) (A5x4.isoZZ_refl R _)]
    have hi := (isInt_mul_DG R (dg S c) hd (orbZ ((S, T) : Point K) p)).2 hZ
    by_cases h' : IsInt R (orbZ w' p')
    · rw [if_pos ⟨hi, h'⟩, if_pos ⟨hZ, h'⟩]
    · rw [if_neg (fun h => h' h.2), if_neg (fun h => h' h.2)]
  · have hZ' : ¬ IsInt R (orbZ ((S, T * c) : Point K) (fm S T c p)) := by
      intro h1
      rw [orbZ_fm] at h1
      exact hZ ((isInt_mul_DG R (dg S c) hd _).1 h1)
    rw [if_neg (fun h => hZ' h.1), if_neg (fun h => hZ h.1)]
    simp
end Formalism.FourierDecayAlt.P.KernelScalingBack
