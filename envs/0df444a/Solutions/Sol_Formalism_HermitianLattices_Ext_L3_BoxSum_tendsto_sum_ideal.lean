-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.tendsto_sum_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:42.159274+00:00
-- url     : https://prove2.me/submissions/40bd2a84-ff02-4d02-aab2-81debcbc05de

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoTsumDivPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemIdealLatticeIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_measurableSet_sBox
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_convex_sBox
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_isBounded_sBox
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_continuous_gW
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_integral_gW
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_tsum_eq
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_card_real
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LatSum_tendsto_tsum_div_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_isTotallyReal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_discrTower
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vInv_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Filter Topology MeasureTheory Pointwise
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {m : ℕ} (hm : 1 ≤ m)
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ I},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1))
      atTop (𝓝 ((m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm I : ℝ))) := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  obtain ⟨-, hfr, hdisc⟩ := discrTower K F hK hF
  have key := LatSum.tendsto_tsum_div_pow (mixedEmbedding.idealLattice F (fracU hI)) volume
    isBounded_sBox measurableSet_sBox (convex_sBox.addHaar_frontier volume) (continuous_gW m)
  rw [integral_gW hm, card_real hK hF, mixedEmbedding.covolume_idealLattice,
    mixedEmbedding.finrank, hfr, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one] at key
  have hsq : Tendsto (fun j : ℕ => j ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have key2 := key.comp hsq
  have hlim : ((m : ℝ)⁻¹) ^ Formalism.HermitianLatticesTheory.fDeg K /
      (((FractionalIdeal.absNorm ((fracU hI : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : ℚ) : ℝ) * Real.sqrt |(discr F : ℝ)|) =
      (m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm I : ℝ) := by
    have h1 : FractionalIdeal.absNorm ((fracU hI : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = (Ideal.absNorm I : ℚ) :=
      FractionalIdeal.coeIdeal_absNorm I
    have h2 : |(discr F : ℝ)| = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K := by
      rw [hdisc, abs_of_nonneg (pow_nonneg (mul_nonneg zero_le_two (vInv_pos K).le) _)]
    rw [h1, h2, zpow_neg, zpow_natCast, inv_pow, div_div, Rat.cast_natCast, mul_comm]
  rw [hlim] at key2
  refine Tendsto.congr' ?_ key2
  filter_upwards [eventually_gt_atTop 0] with j hj
  have hj' : (0 : ℝ) < (j : ℝ) ^ 2 := by positivity
  have hcast : ((j ^ 2 : ℕ) : ℝ) = (j : ℝ) ^ 2 := by push_cast; rfl
  have h3 := tsum_eq hK hF m hI (N := ((j ^ 2 : ℕ) : ℝ)) (by rw [hcast]; exact hj')
  rw [Function.comp_apply, h3, hcast, zpow_neg, zpow_natCast, inv_pow, div_eq_mul_inv, mul_assoc, ← mul_inv, ← pow_add, mul_comm]
  congr 3
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring
end Formalism.HermitianLattices.Ext.L3.BoxSum
