-- Prove2me | solution 1 for Formalism.ELL.CubeTwoAlt.div_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:06.129498+00:00
-- url     : https://prove2.me/submissions/b2bec086-9819-4183-8192-bc0fc065426b

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_X_one_dvd_of_subst_X_zero_eq_zero
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_vec_mem
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_subst_mem_T_of_mem
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_hasSubst2
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_subst_XX
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_X_mem_T
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_mem_T
import Theorems.Thm_Formalism_G_LogP_subst_XX


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.CubeTwoAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
namespace Formalism.ELL.CubeTwoAlt
theorem _root_.solution {W : WeierstrassCurve K} (H : MvPowerSeries (Fin 2) K) (hT : H ∈ T W)
    (h : H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] = 0) :
    ∃ Q ∈ T W, H = (MvPowerSeries.X 1 - MvPowerSeries.X 0) * Q := by
  have c0 : cc (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : cc (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hτ : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1 + MvPowerSeries.X 0] := FormalGroupPointsHom.hasSubst2 c0 (by simp)
  have hτ' : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1 - MvPowerSeries.X 0] := FormalGroupPointsHom.hasSubst2 c0 (by simp)
  have hε : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] :=
    FormalGroupPointsHom.hasSubst2 c0 (by simp)
  obtain ⟨H', hH'⟩ : ∃ H', H' = H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1 + MvPowerSeries.X 0] := ⟨_, rfl⟩
  have e1 : H'.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] = 0 := by
    rw [hH', MvPowerSeries.subst_comp_subst_apply hτ hε]
    have : (fun i => MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0]
        (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1 + MvPowerSeries.X 0] i))
        = ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] := by
      funext i; fin_cases i
      · simp [MvPowerSeries.subst_X hε]
      · simp [MvPowerSeries.subst_add hε, MvPowerSeries.subst_X hε]
    rw [this]; exact h
  obtain ⟨Q', hQ'⟩ := X_one_dvd_of_subst_X_zero_eq_zero H' e1
  have hback : H'.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1 - MvPowerSeries.X 0] = H := by
    rw [hH', MvPowerSeries.subst_comp_subst_apply hτ hτ']
    have : (fun i => MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        MvPowerSeries.X 1 - MvPowerSeries.X 0]
        (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1 + MvPowerSeries.X 0] i))
        = ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] := by
      funext i; fin_cases i
      · simp [MvPowerSeries.subst_X hτ']
      · simp [MvPowerSeries.subst_add hτ', MvPowerSeries.subst_X hτ']
    rw [this]; exact FormalGroupPointsHom.subst_XX H
  refine ⟨Q'.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1 - MvPowerSeries.X 0], ?_, ?_⟩
  · have hH'T : H' ∈ T W := by
      rw [hH']
      exact subst_mem_T_of_mem hT (vec_mem (X_mem_T 0) ((T W).add_mem (X_mem_T 1) (X_mem_T 0)))
        (FormalGroupQuadraticJets.hv c0 (by simp))
    have hQ'T : Q' ∈ T W := by
      rw [mem_T]; intro e
      have := congrArg (MvPowerSeries.coeff (e + Finsupp.single 1 1)) hQ'
      rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, if_pos le_add_self,
        add_tsub_cancel_right, one_mul] at this
      rw [← this]; exact mem_T.mp hH'T _
    exact subst_mem_T_of_mem hQ'T (vec_mem (X_mem_T 0) ((T W).sub_mem (X_mem_T 1) (X_mem_T 0)))
      (FormalGroupQuadraticJets.hv c0 (by simp))
  · conv_lhs => rw [← hback]
    rw [hQ', MvPowerSeries.subst_mul hτ', MvPowerSeries.subst_X hτ']
    simp
end Formalism.ELL.CubeTwoAlt
