-- Prove2me | solution 1 for Formalism.L2.Th1.C.isogenyU_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:49:41.057593+00:00
-- url     : https://prove2.me/submissions/aa47334b-d533-49cd-b87d-770039eac6a2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideB
import Theorems.Thm_Formalism_L2_Th1_C_USideB_hs_of
import Theorems.Thm_Formalism_L2_Th1_C_USideB_cc_subst
import Theorems.Thm_Formalism_L2_Th1_C_USideB_cc_mulBy
import Theorems.Thm_Formalism_L2_Th1_C_USideB_subst_rescale
import Theorems.Thm_Formalism_L2_Th1_C_USideB_l_ne_zero
import Theorems.Thm_Formalism_L2_Th1_C_USideB_subst_wpShift
import Theorems.Thm_Formalism_L2_Th1_C_USideB_mvExp_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open USideB
namespace Formalism.L2.Th1.C
theorem _root_.solution (hE : MvExpLaws) (hS : MvExpSubst) : IsogenyU := by
  intro K _ _ e s2 l linv ph A c0 ι _ xP al h hph hX hI
  set m := mulBy l linv al with hmdef
  have hl : PowerSeries.HasSubst l := hs_of h.1
  have hmc : PowerSeries.constantCoeff m = 0 := cc_mulBy h al
  have hms : PowerSeries.HasSubst m := hs_of hmc
  have hneg : ∀ f : PowerSeries K, PowerSeries.subst m (-f) = -PowerSeries.subst m f := by
    intro f
    rw [← PowerSeries.coe_substAlgHom hms, map_neg]

  have k1 : PowerSeries.subst l (PowerSeries.rescale al (sgStar e s2)) =
      m * mvExp (-(PowerSeries.subst m ph)) := by
    rw [subst_rescale h al, ← hph.2, PowerSeries.subst_mul hms, PowerSeries.subst_X hms,
      hS K Unit (-ph) m (by simp [hph.1]) hmc, hneg]
  have key := congrArg (PowerSeries.substAlgHom hl) hI
  simp only [map_mul, map_pow, map_prod, PowerSeries.coe_substAlgHom] at key
  rw [k1, PowerSeries.subst_X hl, PowerSeries.subst_C, ← hph.2] at key
  have hC : (MvPowerSeries.C al : PowerSeries K) = PowerSeries.C al := rfl
  rw [hC] at key

  have hprod : PowerSeries.X ^ (2 * Fintype.card ι) *
      ∏ P, PowerSeries.subst l (wpShift e (xP P + c0)) =
      (∏ P, (A - PowerSeries.C (xP P) * PowerSeries.X ^ 2)) * l ^ (2 * Fintype.card ι) := by
    calc PowerSeries.X ^ (2 * Fintype.card ι) * ∏ P, PowerSeries.subst l (wpShift e (xP P + c0))
        = (∏ _P : ι, (PowerSeries.X : PowerSeries K) ^ 2) *
            ∏ P, PowerSeries.subst l (wpShift e (xP P + c0)) := by
          rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
      _ = ∏ P, (PowerSeries.X ^ 2 * PowerSeries.subst l (wpShift e (xP P + c0))) :=
          Finset.prod_mul_distrib.symm
      _ = ∏ P, ((A - PowerSeries.C (xP P) * PowerSeries.X ^ 2) * l ^ 2) :=
          Finset.prod_congr rfl fun P _ => subst_wpShift h.1 hX (xP P)
      _ = (∏ P, (A - PowerSeries.C (xP P) * PowerSeries.X ^ 2)) * ∏ _P : ι, l ^ 2 :=
          Finset.prod_mul_distrib
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have p1 : (mvExp (-(PowerSeries.subst m ph)) : PowerSeries K) ^ 2 =
      mvExp (-((2 : K) • PowerSeries.subst m ph)) := by
    rw [mvExp_pow hE (by rw [map_neg, cc_subst hmc hph.1, neg_zero]) 2]
    congr 1
    rw [smul_neg]
    norm_num
  have p2 : (mvExp (-ph) : PowerSeries K) ^ (2 * (Fintype.card ι + 1)) =
      mvExp (-((2 * ((Fintype.card ι : K) + 1)) • ph)) := by
    rw [mvExp_pow hE (by rw [map_neg, hph.1, neg_zero]) _]
    congr 1
    rw [smul_neg]
    push_cast
    rfl
  apply mul_right_cancel₀ (pow_ne_zero (2 * Fintype.card ι) (l_ne_zero h))
  rw [← p1, ← p2, map_pow]
  linear_combination PowerSeries.X ^ (2 * Fintype.card ι) * key +
    PowerSeries.C al ^ 2 * PowerSeries.X ^ (2 * (Fintype.card ι + 1)) *
      (mvExp (-ph) : PowerSeries K) ^ (2 * (Fintype.card ι + 1)) * hprod
end Formalism.L2.Th1.C
