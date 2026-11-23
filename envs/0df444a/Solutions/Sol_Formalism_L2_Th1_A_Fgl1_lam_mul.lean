-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.lam_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:54.079975+00:00
-- url     : https://prove2.me/submissions/baa87701-167a-43ea-bafe-5a450d7983fa

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_coeff_lam
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_coeff_Wi
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_coeff_Wi
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_coeff_lam
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_eq_single_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Fgl1
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
open Formalism.ELL.WeierstrassChordSeries (eq_single_iff)
namespace Formalism.L2.Th1.A.Fgl1
theorem _root_.solution : (MvPowerSeries.X 1 - MvPowerSeries.X 0) * lam W = Wi W 1 - Wi W 0 := by
  ext e
  have he := eq_single_iff e
  rw [sub_mul, map_sub, map_sub,
    show (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = MvPowerSeries.monomial (Finsupp.single 1 1) 1 from rfl,
    show (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) = MvPowerSeries.monomial (Finsupp.single 0 1) 1 from rfl,
    MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, coeff_Wi, coeff_Wi, coeff_lam, coeff_lam]
  simp only [he.1, he.2, Finsupp.single_le_iff, Finsupp.tsub_apply, Finsupp.single_apply, one_mul]
  by_cases h0 : e 0 = 0 <;> by_cases h1 : e 1 = 0 <;> simp [h0, h1]
  · rw [if_pos (by omega), Nat.sub_add_cancel (by omega)]
  · rw [if_pos (by omega), Nat.sub_add_cancel (by omega)]
  · rw [if_pos (by omega), if_pos (by omega), show e 0 + (e 1 - 1) + 1 = e 0 - 1 + e 1 + 1 by omega, sub_self]
end Formalism.L2.Th1.A.Fgl1
