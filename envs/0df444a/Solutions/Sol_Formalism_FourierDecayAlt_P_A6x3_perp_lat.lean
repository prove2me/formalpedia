-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.perp_lat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:51.343068+00:00
-- url     : https://prove2.me/submissions/35f9d0b8-69a7-4f43-9a34-a3c27b07fda5

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_lat_mulLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_volL_mulLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_mulLat_inv_mulLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_perp_mulLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_nat_mul_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_perp_small
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_relIndex_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x3
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x3
theorem _root_.solution (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    {L : AddSubgroup K} (hL : Lat L) :
    Lat (perp ψ L) ∧ perp ψ (perp ψ L) = L ∧ volL R L * volL R (perp ψ L) = 1 := by
  have hR := lat_R hd.isOpen hd.isCompact
  have hne : R.toAddSubgroup.relIndex L ≠ 0 := relIndex_ne_zero hR.op hL.cp
  obtain ⟨c, hc⟩ := hn _ hne
  have hcL : mulLat (c : K) L ≤ R.toAddSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    rw [AddMonoidHom.coe_mulLeft, hc]
    exact nat_mul_mem hx
  have hL' := lat_mulLat c hL
  obtain ⟨h1, h2, h3⟩ := perp_small hd hn hL' hcL
  have e1 : perp ψ L = mulLat (c : K) (perp ψ (mulLat (c : K) L)) := by
    have := perp_mulLat (ψ := ψ) c⁻¹ (mulLat (c : K) L)
    rwa [mulLat_inv_mulLat, inv_inv] at this
  refine ⟨e1 ▸ lat_mulLat c h1, ?_, ?_⟩
  · rw [e1, perp_mulLat, h2, mulLat_inv_mulLat]
  · rw [e1, volL_mulLat hR c h1]
    rw [volL_mulLat hR c hL] at h3
    rw [← h3]
    ring
end Formalism.FourierDecayAlt.P.A6x3
