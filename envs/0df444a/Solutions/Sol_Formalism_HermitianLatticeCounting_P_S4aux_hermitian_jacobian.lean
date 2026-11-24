-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.hermitian_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:02.350532+00:00
-- url     : https://prove2.me/submissions/8ced8cfc-289a-4936-84be-d235f792d6fa

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hj_exists_omega
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hj_basis
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hj_caseA
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hj_caseB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : HermJac := by
  intro F E _ _ _ _ hs h2 hfix m A
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [h2]; norm_num)
  obtain ⟨ω, hω⟩ := hj_exists_omega (F := F) (E := E) h2
  obtain ⟨β, h0, h1⟩ := hj_basis h2 ω hω
  have hstδ : star (ω - star ω) = -(ω - star ω) := by rw [star_sub, star_star]; ring
  obtain ⟨e2, he2⟩ := hfix ((ω - star ω) * (ω - star ω)) (by rw [star_mul', hstδ]; ring)
  by_cases hz : e2 = 0
  ·
    have hε : (ω - star ω) * (ω - star ω) = 0 := by rw [← he2, hz, map_zero]
    have hne : ω - star ω ≠ 0 := by
      intro h
      obtain ⟨c, hc⟩ := hfix ω (sub_eq_zero.1 h).symm
      exact hω c hc
    obtain ⟨t, ht⟩ := hfix (ω + star ω) (by rw [star_add, star_star, add_comm])
    have htwo : (2 : F) ≠ 0 := by
      intro h2F
      have h2E : (2 : E) = 0 := by
        have := congrArg (algebraMap F E) h2F
        rw [map_ofNat, map_zero] at this
        exact this
      have e1 : ω - star ω = algebraMap F E t := by
        rw [ht]; linear_combination (-(star ω)) * h2E
      rw [e1, ← map_mul] at hε
      have : t * t = 0 := (map_eq_zero_iff _ (algebraMap F E).injective).1 hε
      have ht0 : t = 0 := mul_self_eq_zero.1 this
      rw [ht0, map_zero] at e1
      exact hne e1
    have hεF : ∀ c : F, algebraMap F E c ≠ ω - star ω := by
      intro c hc
      have e1 : star (ω - star ω) = ω - star ω := by rw [← hc, hs]
      rw [hstδ] at e1
      have e3 : algebraMap F E 2 * (ω - star ω) = 0 := by
        rw [map_ofNat]; linear_combination -e1
      have e4 : algebraMap F E 2⁻¹ * algebraMap F E 2 = 1 := by
        rw [← map_mul, inv_mul_cancel₀ htwo, map_one]
      apply hne
      linear_combination (algebraMap F E 2⁻¹) * e3 - (ω - star ω) * e4
    obtain ⟨β', h0', h1'⟩ := hj_basis h2 (ω - star ω) hεF
    exact hj_caseB hs (ω - star ω) β' h0' h1' hε hstδ htwo m A
  · have hδ : IsUnit (ω - star ω) := by
      refine IsUnit.of_mul_eq_one ((ω - star ω) * algebraMap F E e2⁻¹) ?_
      rw [← mul_assoc, ← he2, ← map_mul, mul_inv_cancel₀ hz, map_one]
    exact hj_caseA hs h2 hfix ω β h0 h1 hδ m A
end Formalism.HermitianLatticeCounting.P.S4aux
