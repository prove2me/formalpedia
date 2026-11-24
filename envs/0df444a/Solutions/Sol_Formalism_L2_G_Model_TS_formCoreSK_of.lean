-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.formCoreSK_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:17:53.61299+00:00
-- url     : https://prove2.me/submissions/231bd199-1d43-4acf-aaf0-832d61a57c08

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FormSK
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FormSK
import Theorems.Thm_Formalism_L2_G_Model_TS_charZero_of_irreducible_natCast
import Theorems.Thm_Formalism_L2_G_Model_TS_nuOf_antitone
import Theorems.Thm_Formalism_L2_G_Model_TS_nuOf_le_ellWt
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.InvariantFactorPaths.INST
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (h : FormCoreG) : FormCoreSK := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS m lam hl
  have : Fact p.Prime := ⟨hS.prime⟩
  have : IsFractionRing O Kf := hS.frac_O
  have : IsFractionRing W Qq := hS.frac_alt
  have : CharZero W := charZero_of_irreducible_natCast hS.prime hS.p_unif
  have hinj : Function.Injective (ι.comp (algebraMap W Qq)) :=
    ι.injective.comp (IsFractionRing.injective W Qq)
  have : CharZero Kf := charZero_of_injective_ringHom hinj
  have hj : Function.Injective j := by
    intro x y hxy
    apply hinj
    simp only [RingHom.comp_apply, hS.ι_comp, hxy]
  have hp : ¬ IsUnit ((p : ℕ) : O) := by
    intro hu
    have := hS.finite.to_isIntegral.isLocalHom hj
    have hu' : IsUnit (j (p : W)) := by rwa [map_natCast]
    exact hS.p_unif.not_isUnit (isUnit_of_map_unit j _ hu')
  obtain ⟨B, ha, hb, hc, hd, he⟩ := h p O Kf hp (m + 1) (m + 1) le_rfl (nuOf lam) (nuOf_antitone hl)
  refine ⟨B, ha, hb, hc, ?_⟩
  intro Q hQ P hP
  unfold expN
  split_ifs with h0
  · rw [pow_zero, one_smul]
    refine he (fun t => ?_) Q hQ P hP
    have := nuOf_le_ellWt hl t
    omega
  · exact hd (ellWt lam) (Or.inl (nuOf_le_ellWt hl)) Q hQ P hP
end Formalism.L2.G.Model.TS
