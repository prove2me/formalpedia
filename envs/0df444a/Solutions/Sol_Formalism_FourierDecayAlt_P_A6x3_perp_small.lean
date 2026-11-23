-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.perp_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:59.706+00:00
-- url     : https://prove2.me/submissions/2b45b514-e59c-4d1f-97e4-e02ef8874c52

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_volL_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_lat_mulLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_perp_anti
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_perp_mulLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_relIndex_perp
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_perp_perp
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_perp_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_nat_mul_mem
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
    {L : AddSubgroup K} (hL : Lat L) (hLR : L ≤ R.toAddSubgroup) :
    Lat (perp ψ L) ∧ perp ψ (perp ψ L) = L ∧ volL R L * volL R (perp ψ L) = 1 := by
  have hR := lat_R hd.isOpen hd.isCompact
  have hA := perp_R hd
  have hne : L.relIndex R.toAddSubgroup ≠ 0 := relIndex_ne_zero hL.op hR.cp
  obtain ⟨b, hb⟩ := hn _ hne
  have hbL : mulLat (b : K) R.toAddSubgroup ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    rw [AddMonoidHom.coe_mulLeft, hb]
    exact nat_mul_mem hx
  have hfin : (mulLat (b : K) R.toAddSubgroup).relIndex R.toAddSubgroup ≠ 0 :=
    relIndex_ne_zero (lat_mulLat b hR).op hR.cp
  have hRP : R.toAddSubgroup ≤ perp ψ L := by
    conv_lhs => rw [← hA]
    exact perp_anti hLR
  have hop : IsOpen ((perp ψ L : AddSubgroup K) : Set K) := AddSubgroup.isOpen_mono hRP hR.op
  refine ⟨⟨hop, ?_⟩, perp_perp hA b hfin hbL hLR, ?_⟩
  · have hle : perp ψ L ≤ mulLat ((b⁻¹ : Kˣ) : K) R.toAddSubgroup := by
      have := perp_anti (ψ := ψ) hbL
      rwa [perp_mulLat, hA] at this
    exact (lat_mulLat b⁻¹ hR).cp.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ hop) hle
  · rw [volL_eq, volL_eq, gi, gi, relIndex_perp hA b hfin hbL hLR,
      AddSubgroup.relIndex_eq_one.2 hLR, AddSubgroup.relIndex_eq_one.2 hRP]
    have : (L.relIndex R.toAddSubgroup : ℝ) ≠ 0 := by exact_mod_cast hne
    field_simp
end Formalism.FourierDecayAlt.P.A6x3
