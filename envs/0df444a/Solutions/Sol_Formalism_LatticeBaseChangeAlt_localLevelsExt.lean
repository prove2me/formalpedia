-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.localLevelsExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:56:10.437606+00:00
-- url     : https://prove2.me/submissions/578bcf4f-1141-4e9e-8950-a83703641884

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_LocalStepLevelsExt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LevelsChain
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepExtOf
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LevelsChainOfAddOneLe
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_levelsChain_of_add_one_le
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_levelsChain
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_localStepExt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LatticeBaseChangeAlt
open Module
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : LocalStepLevelsExt := by
  intro ι _ ep f ν v νs c' T R I hep hT hc hv hν O K K₁ V W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ϖ hϖ M Θ N₁ Z Zm N' e be n th c AA AA' N₁' ρ a a' hM hΘ h1 h2 h3 h4 h5 h6 ha ha' h7 h8 h9 h10
    h11 h12 h13 h14 h15 h16 h17 hcase hA hN V'
  have h := localStepExt O K K₁ V W ϖ hϖ M Θ N₁ Z Zm N' e be n th c AA AA' N₁' ρ a a' hM hΘ h1 h2 h3
    h4 h5 h6 ha ha' h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
    (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hA) (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hN) h17 V'
  have hAn := ENat.toNat_le_of_le_natCast hA
  have hNn := ENat.toNat_le_of_le_natCast hN
  have hlev : ∑ z, ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - ((e : ℤ) : ℝ))⌉ : ℤ) : ℝ) * f z ≤
        T * c' * ∑ z, ((ep z : ℝ) * f z) * v z := by
    rcases hcase with h0 | h0
    · exact levelsChain ι ep f ν v νs c' T (e : ℤ) hep hT hc hv hν (Or.inl (by exact_mod_cast h0))
    · exact levelsChain_of_add_one_le ι ep f ν v νs c' T (e : ℤ) hep hT hc hv hν (by exact_mod_cast h0)
  simp only [Int.cast_natCast] at hlev
  have hsumcast : (((∑ z, (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat * f z : ℕ)) : ℝ) =
      ∑ z, ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉ : ℤ) : ℝ) * f z := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Nat.cast_mul]
    congr 1
    have h0 : (0 : ℤ) ≤ max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉ := le_max_left _ _
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  have hRnn : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have key : ((Module.length O (↥AA' ⧸ AA.comap AA'.subtype)).toNat : ℝ) ≤
      (R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) := by
    calc ((Module.length O (↥AA' ⧸ AA.comap AA'.subtype)).toNat : ℝ)
        ≤ ((R * ∑ z, (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat * f z : ℕ) : ℝ) := by
          exact_mod_cast hAn
      _ ≤ _ := by
          rw [Nat.cast_mul, hsumcast]
          exact mul_le_mul_of_nonneg_left hlev hRnn
  have key2 : ((Module.length O (↥AA ⧸ N₁'.comap AA.subtype)).toNat : ℝ) ≤ (R : ℝ) * (I : ℝ) := by
    exact_mod_cast hNn
  have hd : (0 : ℝ) ≤ (finrank K K₁ : ℝ) := Nat.cast_nonneg _
  have hR : (finrank K K₁ : ℝ) *
        (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
      (finrank K K₁ : ℝ) * ((e : ℝ) * (finrank K V' : ℝ) +
          ((Module.length O (↥AA' ⧸ AA.comap AA'.subtype)).toNat : ℝ) +
          ((Module.length O (↥AA ⧸ N₁'.comap AA.subtype)).toNat : ℝ) +
          ((Module.length O (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ)) +
        (((IsDiscreteValuationRing.addVal O a).toNat : ℝ) -
          ((IsDiscreteValuationRing.addVal O a').toNat : ℝ) +
          (finrank K K₁ : ℝ) * (n : ℝ) * (be : ℝ)) := by
    exact_mod_cast h
  have hmul := mul_le_mul_of_nonneg_left (add_le_add key key2) hd
  nlinarith [hR, hmul]
end Formalism.LatticeBaseChangeAlt
