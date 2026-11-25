-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LocalizedFibreSets.phiCount_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:43:18.650308+00:00
-- url     : https://prove2.me/submissions/a3913634-e888-403b-9a09-10ec6f5d8a4e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CardPhiSucc
import Theorems.Thm_Formalism_L2_SG_Pf_LocalizedFibreSets_card_phi_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_mk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LocalizedFibreSets
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}
namespace Formalism.L2.SG.Pf.LocalizedFibreSets
theorem _root_.solution (h1 : PhiModP) : PhiCount := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro T _ hT0
    have hb : (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ 1)) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker, pow_one]
    have hT' : T = 0 := by
      ext i j
      have := hT0 i j
      rw [hb, Ideal.mem_bot] at this
      exact this
    subst hT'
    rw [mul_one]
    exact h1 K F hK 𝔭 h𝔭 m a ha
  | succ k hk ih =>
    intro T hT hT0
    have hs : Function.Semiconj (piQ K 𝔭 k) star star := by
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      unfold piQ
      rw [star_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, star_mk]
    rw [card_phi_succ hK h𝔭 a hk T hT hT0]
    push_cast
    rw [ih (T.map (piQ K 𝔭 k)) ?_ ?_]
    · ring
    · rw [← Matrix.conjTranspose_map _ hs, hT]
    · intro i j
      obtain ⟨x, hx, hxT⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hT0 i j)
      rw [Matrix.map_apply, ← hxT]
      unfold piQ
      rw [Ideal.Quotient.factor_mk]
      exact Ideal.mem_map_of_mem _ hx
end Formalism.L2.SG.Pf.LocalizedFibreSets
