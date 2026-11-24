-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantGroupCounts.card_hermD_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:42:30.760804+00:00
-- url     : https://prove2.me/submissions/77d50f5f-421d-405f-a450-4bb8ec04d2b0

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_OneAddFormEqIff
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_range_trD

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
    (he : (θ - star θ) * e = 1) : Nat.card (hermD d) ^ 2 = Nat.card (entD d) := by
  classical
  have hrange := range_trD (d := d) hd he
  have hu : star (θ - star θ) = -(θ - star θ) := by rw [star_sub, star_star, neg_sub]
  have hse : star e = -e := by
    have h1 : star e * star (θ - star θ) = 1 := by rw [← star_mul, he, star_one]
    rw [hu] at h1
    calc star e = star e * ((θ - star θ) * e) := by rw [he, mul_one]
      _ = (star e * (θ - star θ)) * e := by ring
      _ = -e := by
        rw [show star e * (θ - star θ) = -1 by linear_combination -h1]
        ring
  have hk : Nat.card (trD d).ker = Nat.card (hermD d) := by
    symm
    refine Nat.card_congr
      { toFun := fun S => ⟨⟨(θ - star θ) • S.1, ?_⟩, ?_⟩
        invFun := fun Y => ⟨e • Y.1.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · obtain ⟨_, hS0⟩ : S.1ᴴ = S.1 ∧ ∀ i j, d i * S.1 i j * d j = 0 := S.2
      show ∀ i j, d i * ((θ - star θ) • S.1) i j * d j = 0
      intro i j
      rw [Matrix.smul_apply, smul_eq_mul]
      calc d i * ((θ - star θ) * S.1 i j) * d j = (θ - star θ) * (d i * S.1 i j * d j) := by ring
        _ = 0 := by rw [hS0 i j, mul_zero]
    · obtain ⟨hS, _⟩ : S.1ᴴ = S.1 ∧ ∀ i j, d i * S.1 i j * d j = 0 := S.2
      show (θ - star θ) • S.1 + ((θ - star θ) • S.1)ᴴ = 0
      ext i j
      have hSij : star (S.1 j i) = S.1 i j := by rw [← Matrix.conjTranspose_apply, hS]
      simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
        star_mul, hSij, hu, Matrix.zero_apply]
      ring
    · have hY0 : Y.1.1 + Y.1.1ᴴ = 0 := Y.2
      have hY : ∀ i j, d i * Y.1.1 i j * d j = 0 := Y.1.2
      show (e • Y.1.1)ᴴ = e • Y.1.1 ∧ ∀ i j, d i * (e • Y.1.1) i j * d j = 0
      refine ⟨?_, fun i j => ?_⟩
      · ext i j
        have h0 := congrFun (congrFun hY0 i) j
        simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.zero_apply] at h0
        simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul, hse]
        linear_combination (-e) * h0
      · rw [Matrix.smul_apply, smul_eq_mul]
        calc d i * (e * Y.1.1 i j) * d j = e * (d i * Y.1.1 i j * d j) := by ring
          _ = 0 := by rw [hY i j, mul_zero]
    · intro S
      apply Subtype.ext
      show e • (θ - star θ) • S.1 = S.1
      rw [smul_smul, mul_comm, he, one_smul]
    · intro Y
      apply Subtype.ext
      apply Subtype.ext
      show (θ - star θ) • e • Y.1.1 = Y.1.1
      rw [smul_smul, he, one_smul]
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (trD d).ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (trD d)).toEquiv, hrange, hk, sq]
end Formalism.L2.SG.Pf.discriminantGroupCounts
