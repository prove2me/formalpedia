-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantGroupCounts.range_trD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:28:34.056812+00:00
-- url     : https://prove2.me/submissions/4d5dd591-03c9-44ba-875e-4cb6db812c6c

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_OneAddFormEqIff
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_star_entry

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
theorem _root_.solution (hd : ∀ i, star (d i) = d i) {θ e : A} (he : (θ - star θ) * e = 1) :
    (trD d).range = hermD d := by
  have hu : star (θ - star θ) = -(θ - star θ) := by rw [star_sub, star_star, neg_sub]
  have hse : star e = -e := by
    have h1 : star e * star (θ - star θ) = 1 := by rw [← star_mul, he, star_one]
    rw [hu] at h1
    calc star e = star e * ((θ - star θ) * e) := by rw [he, mul_one]
      _ = (star e * (θ - star θ)) * e := by ring
      _ = -e := by
        rw [show star e * (θ - star θ) = -1 by linear_combination -h1]
        ring
  ext S
  rw [AddMonoidHom.mem_range]
  constructor
  · rintro ⟨Y, rfl⟩
    have hY : ∀ i j, d i * Y.1 i j * d j = 0 := Y.2
    show (Y.1 + Y.1ᴴ)ᴴ = Y.1 + Y.1ᴴ ∧ ∀ i j, d i * (Y.1 + Y.1ᴴ) i j * d j = 0
    refine ⟨?_, fun i j => ?_⟩
    · rw [conjTranspose_add, conjTranspose_conjTranspose, add_comm]
    · rw [Matrix.add_apply, Matrix.conjTranspose_apply, mul_add, add_mul, hY i j,
        star_entry hd (hY j i), add_zero]
  · intro hS'
    obtain ⟨hS, hS0⟩ : Sᴴ = S ∧ ∀ i j, d i * S i j * d j = 0 := hS'
    refine ⟨⟨(θ * e) • S, ?_⟩, ?_⟩
    · show ∀ i j, d i * ((θ * e) • S) i j * d j = 0
      intro i j
      rw [Matrix.smul_apply, smul_eq_mul]
      calc d i * (θ * e * S i j) * d j = θ * e * (d i * S i j * d j) := by ring
        _ = 0 := by rw [hS0 i j, mul_zero]
    · show (θ * e) • S + ((θ * e) • S)ᴴ = S
      ext i j
      have hSij : star (S j i) = S i j := by rw [← Matrix.conjTranspose_apply, hS]
      simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
        star_mul, hSij, hse]
      linear_combination (S i j) * he
end Formalism.L2.SG.Pf.discriminantGroupCounts
