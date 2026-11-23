-- Prove2me | solution 1 for Formalism.ELL.CubeTwoAlt.coeff_subst_X0_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:08.112112+00:00
-- url     : https://prove2.me/submissions/5b61e627-0cee-4085-bceb-09180b267722

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_hasSubst2
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
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.CubeTwoAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
namespace Formalism.ELL.CubeTwoAlt
theorem _root_.solution (H : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) (he : e 1 = 0) :
    MvPowerSeries.coeff e (H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0]) =
      MvPowerSeries.coeff e H := by
  classical
  have hs : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] :=
    FormalGroupPointsHom.hasSubst2 (by simp) (by simp)
  have hprod : ∀ d : Fin 2 →₀ ℕ,
      (d.prod fun s n => (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] s) ^ n)
        = MvPowerSeries.X 0 ^ d 0 * 0 ^ d 1 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp
  rw [MvPowerSeries.coeff_subst hs, finsum_eq_single _ e]
  · rw [hprod, he, pow_zero, mul_one, MvPowerSeries.coeff_X_pow]
    have : e = Finsupp.single 0 (e 0) := ((eq_single_iff e).2).mpr he
    rw [if_pos this, smul_eq_mul, mul_one]
  · intro d hd
    rw [hprod]
    rcases Nat.eq_zero_or_pos (d 1) with h1 | h1
    · rw [h1, pow_zero, mul_one, MvPowerSeries.coeff_X_pow, if_neg, smul_zero]
      intro h
      apply hd
      have hd' : d = Finsupp.single 0 (d 0) := ((eq_single_iff d).2).mpr h1
      rw [hd']
      exact h.symm
    · rw [zero_pow h1.ne', mul_zero, map_zero, smul_zero]
end Formalism.ELL.CubeTwoAlt
