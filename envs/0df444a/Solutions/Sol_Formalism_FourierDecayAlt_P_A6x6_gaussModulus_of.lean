-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.gaussModulus_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:52.0277+00:00
-- url     : https://prove2.me/submissions/56cff4ad-bdf3-494b-8adf-0208153d9491

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_gi_PL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_lat_PL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_mem_perp_of_dot
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_PL_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_b_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_normSq_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_gi_of_ge
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_rpow_of_sq
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_good_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_LL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_relIndex_ne_zero
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x5_modK_mul__b5e25af6776b
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x6
open Formalism.FourierDecayAlt.P.A5x5
namespace Formalism.FourierDecayAlt.P.A6x6
theorem _root_.solution (hPL : PerpLat) : GaussModulus := by
  intro K _ _ _ R ψ hd hn m M hM hdet L Λ hL hΛ hAdm hInv
  obtain ⟨hP, hPP, hvol⟩ := hPL K R ψ hd hn L hL
  have h2 : IsUnit (2 : K) := by simpa using hn 2 (by norm_num)
  have lΛ : Lat (PL Λ m) := lat_PL hΛ
  have lL : Lat (PL L m) := lat_PL hL
  have lP : Lat (PL (perp ψ L) m) := lat_PL hP
  have lR : Lat (LL R (Fin m)) := lat_LL hd.isOpen hd.isCompact
  have hdi : IsUnit (M⁻¹).det := Matrix.isUnit_nonsing_inv_det M hdet
  have lN : Lat ((PL (perp ψ L) m).map (mv M⁻¹)) := lat_map hdi lP
  have hfin := relIndex_ne_zero lΛ.op lL.cp
  have hS := normSq_sum h2 hM hInv hd.unitary hdet hAdm hPP hfin
  have hle := PL_le hInv
  have hleN : PL Λ m ≤ (PL (perp ψ L) m).map (mv M⁻¹) := by
    intro l hl
    refine ⟨M *ᵥ l, mem_perp_of_dot ψ fun x hx => b_one h2 hM hInv hx hl, ?_⟩
    simp [mulVec_mulVec, nonsing_inv_mul _ hdet]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hS
  have hS' : ‖∑ᶠ y : Fin m → K ⧸ Λ, gaussF ψ L M (sec Λ y)‖ ^ 2 =
      gi (PL L m) (PL Λ m) * gi ((PL (perp ψ L) m).map (mv M⁻¹)) (PL Λ m) := by
    rw [gi_of_ge hle, gi_of_ge hleN]; exact_mod_cast hS
  have hv : volL R Λ ^ m = gi (PL Λ m) (LL R (Fin m)) := (gi_PL Λ R.toAddSubgroup).symm
  have hv0 : 0 ≤ volL R Λ := by unfold volL; positivity
  have e1 : gi (PL L m) (PL Λ m) * volL R Λ ^ m = volL R L ^ m := by
    rw [hv, gi_trans lL lΛ lR]; exact gi_PL L R.toAddSubgroup
  have e2 : gi ((PL (perp ψ L) m).map (mv M⁻¹)) (PL Λ m) * volL R Λ ^ m =
      volL R (perp ψ L) ^ m * modK R (M⁻¹).det := by
    rw [hv, gi_trans lN lΛ lR, ← gi_trans lN (lat_map hdi lR) lR, gi_map (mv_injective hdi)]
    congr 1
    · exact gi_PL (perp ψ L) R.toAddSubgroup
    · exact good_fin hd m M⁻¹ hdi
  have e3 : modK R (M⁻¹).det * modK R M.det = 1 := by
    rw [← modK_mul' hd hdi hdet, ← det_mul, nonsing_inv_mul _ hdet, det_one, modK_one]
  have hpos : 0 < modK R M.det := by
    have := modK_pos hd.isOpen hd.isCompact hdet.unit
    simpa using this
  apply rpow_of_sq hpos (norm_nonneg _)
  show ‖(volL R Λ : ℂ) ^ m * ∑ᶠ y : Fin m → K ⧸ Λ, gaussF ψ L M (sec Λ y)‖ ^ 2 * _ = 1
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hv0, mul_pow, hS']
  calc (volL R Λ ^ m) ^ 2 * (gi (PL L m) (PL Λ m) *
        gi ((PL (perp ψ L) m).map (mv M⁻¹)) (PL Λ m)) * modK R M.det
      = (gi (PL L m) (PL Λ m) * volL R Λ ^ m) *
        (gi ((PL (perp ψ L) m).map (mv M⁻¹)) (PL Λ m) * volL R Λ ^ m) * modK R M.det := by ring
    _ = (volL R L * volL R (perp ψ L)) ^ m * (modK R (M⁻¹).det * modK R M.det) := by
        rw [e1, e2]; ring
    _ = 1 := by rw [hvol, e3]; simp
end Formalism.FourierDecayAlt.P.A6x6
