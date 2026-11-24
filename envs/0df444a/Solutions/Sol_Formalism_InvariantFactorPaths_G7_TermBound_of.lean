-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TermBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:47:39.535316+00:00
-- url     : https://prove2.me/submissions/0c350cee-d5e3-4ba4-b578-5f6c8f8b63c7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_degree_jn
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_support_topLow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_jetPair_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_agree_refl
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_agree_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_agree_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_closure_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_sum_piece
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_term_bound
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_LT_ExpP_term_bound


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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (h1 : JetPairingHasseIdentity) (h2 : HasseDerivIntegralHomogeneous) : TermBound := by
  intro K Tp Lw Φ κ _ _ _ _ _ _ _ _ p D dQ h g Z Y aA dA aB dB b e Q hp hpn _ hg haA haB hb hZ hY
    hZlow hdec hQ hQh hD
  classical
  obtain ⟨U, hU, hgU⟩ := hg
  have hag : ETerm.Agree D h (∑ j, ETerm.piece p Z Y aA dA aB dB b j) := by
    rw [ETerm.sum_piece]
    exact hdec
  have hsupp : ∀ m ∈ (topMonoP e * lowPoly Q).support, m.degree = D := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 (ETerm.support_topLow e Q hm)
    have hnd : n.degree = dQ := by
      have := hQh (MvPolynomial.mem_support_iff.1 hn)
      rw [← this, Finsupp.degree_eq_weight_one]
      rfl
    rw [ETerm.degree_jn, hnd, hD]
  have key : jetPair (topMonoP e * lowPoly Q) g =
      ∑ i ∈ range (D + 1), ∑ k ∈ Finset.piAntidiag (univ : Finset (Φ ⊕ κ ⊕ Fin 2)) i,
        ((p : K) ^ i)⁻¹ * (((Nat.multinomial univ k : ℕ) : K) *
          jetPair (topMonoP e * lowPoly Q)
            ((∏ j, ETerm.piece p Z Y aA dA aB dB b j ^ k j) * U i)) := by
    have h0 : jetPair (topMonoP e * lowPoly Q) g = jetPair (topMonoP e * lowPoly Q)
        (∑ i ∈ range (D + 1), MvPowerSeries.C (((p : K) ^ i)⁻¹) *
          ((∑ j, ETerm.piece p Z Y aA dA aB dB b j) ^ i * U i)) := by
      refine ETerm.jetPair_congr _ _ _ fun m hm => ?_
      rw [hgU m, hsupp m hm, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MvPowerSeries.coeff_C_mul,
        ETerm.agree_mul (ETerm.agree_pow hag i) (ETerm.agree_refl D (U i)) m (hsupp m hm).le]
    rw [h0, Formalism.DworkPowerSeriesWeights.jetPair_sum_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Formalism.DworkPowerSeriesWeights.jetPair_C_mul_right, Finset.sum_pow_eq_sum_piAntidiag, Finset.sum_mul,
      Formalism.DworkPowerSeriesWeights.jetPair_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc : ((Nat.multinomial univ k : ℕ) : MvPowerSeries (Tp ⊕ Lw) K) =
        MvPowerSeries.C ((Nat.multinomial univ k : ℕ) : K) := (map_natCast _ _).symm
    rw [mul_assoc, hc, Formalism.DworkPowerSeriesWeights.jetPair_C_mul_right]
  rw [key]
  have hmain := ETerm.closure_sum (ETerm.valid p aA dA aB dB b e Q) (ETerm.bnd K p e)
    (range (D + 1)) (fun i => ∑ k ∈ Finset.piAntidiag (univ : Finset (Φ ⊕ κ ⊕ Fin 2)) i,
        ((p : K) ^ i)⁻¹ * (((Nat.multinomial univ k : ℕ) : K) *
          jetPair (topMonoP e * lowPoly Q)
            ((∏ j, ETerm.piece p Z Y aA dA aB dB b j ^ k j) * U i)))
    (fun i _ => ETerm.closure_sum _ _ _ _ fun k hk =>
      ETerm.term_bound h1 h2 p Z Y aA dA aB dB b e Q hp hpn haA haB hb hZ hY hZlow hQ i k
        (Finset.mem_piAntidiag.1 hk).1 (U i) (hU i))
  rcases hmain with h0 | ⟨⟨α, β, i2, n⟩, hv, hbd⟩
  · exact Or.inl h0
  · exact Or.inr ⟨α, β, i2, n, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2, hbd⟩
end Formalism.InvariantFactorPaths.G7
