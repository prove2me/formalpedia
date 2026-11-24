-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantGroupCounts.card_ker_eq_card_hermD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:05:22.832841+00:00
-- url     : https://prove2.me/submissions/8c6fa7eb-69ab-4535-bc90-6e6c56d9d590

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_OneAddFormEqIff
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_card_entD
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_card_hermD_sq
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_card_ker_mulDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.HermitianLattices.Ext.L3
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantGroupCounts
variable {A : Type*} [CommRing A] [StarRing A]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {d : m → A}
namespace Formalism.L2.SG.Pf.discriminantGroupCounts
theorem _root_.solution [Finite A] (hd : ∀ i, star (d i) = d i) {θ e : A}
    (he : (θ - star θ) * e = 1)
    (hsq : ∀ i j, Nat.card {a : A // d i * a * d j = 0} =
      Nat.card {a : A // a * d i = 0} * Nat.card {a : A // a * d j = 0}) :
    Nat.card (AddMonoidHom.mulRight (diagonal d)).ker = Nat.card (hermD d) := by
  have h1 := card_hermD_sq (d := d) hd he
  rw [card_entD] at h1
  have h2 := card_ker_mulDiag (A := A) d
  have h3 : Nat.card (AddMonoidHom.mulRight (diagonal d)).ker ^ 2 = Nat.card (hermD d) ^ 2 := by
    rw [h1, h2]
    simp only [hsq, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow]
    ring
  exact Nat.pow_left_injective (by norm_num) h3
end Formalism.L2.SG.Pf.discriminantGroupCounts
