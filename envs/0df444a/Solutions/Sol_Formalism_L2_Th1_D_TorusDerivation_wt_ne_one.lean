-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.wt_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:35:33.765864+00:00
-- url     : https://prove2.me/submissions/6e6084d9-b6f7-4693-977e-36c69971800a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_exists_of_sum_eq_one
import Theorems.Thm_Formalism_HermitianLattices_IntegralLatticeDensity_no_form_of_bidegree_one_one


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (torus lw degE degO NoLowBidegree)
open Formalism.InvariantFactorPaths.G7 (lgF at1 DivAB)
open TorusDerivation
open Formalism.L2.Th1.D.TorusDerivation
variable {K : Type} [Field K] {d : ℕ} [NeZero d]
namespace Formalism.L2.Th1.D.TorusDerivation
theorem _root_.solution {l : ℕ} (hl : 2 ≤ l) {ζ : K} (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
    {n : ZMod d →₀ ℕ} (hE : degE n = 1) (hO : degO n = 1) : wt l ζ n ≠ 1 := by
  classical
  have hd : d ≠ 0 := NeZero.ne d
  have hN : l ^ d - 1 ≠ 0 := by
    have := Nat.one_lt_pow hd (show 1 < l by omega)
    omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN
  obtain ⟨s, hs1, hs⟩ := exists_of_sum_eq_one _ hE
  obtain ⟨t, ht1, ht⟩ := exists_of_sum_eq_one _ hO
  have hse : s.val % 2 = 0 := by
    by_contra hc
    rw [if_neg hc] at hs1
    omega
  have hto : ¬ t.val % 2 = 0 := by
    intro hc
    rw [if_pos hc] at ht1
    omega
  rw [if_pos hse] at hs1
  rw [if_neg hto] at ht1
  have hst : s ≠ t := fun h => hto (h ▸ hse)
  have hw : wt l ζ n = ζ ^ (lw l s + lw l t) := by
    unfold wt
    rw [Finset.prod_eq_mul s t hst, hs1, ht1, pow_one, pow_one, zpow_add₀ hζ0]
    · rintro c - ⟨hcs, hct⟩
      have hc0 : n c = 0 := by
        by_cases hc : c.val % 2 = 0
        · have := hs c hcs
          rwa [if_pos hc] at this
        · have := ht c hct
          rwa [if_neg hc] at this
      rw [hc0, pow_zero]
    · intro h
      exact absurd (Finset.mem_univ s) h
    · intro h
      exact absurd (Finset.mem_univ t) h
  intro h1
  rw [hw, hζ.zpow_eq_one_iff_dvd] at h1
  have e : lw l s + lw l t = (l : ℤ) ^ s.val - (l : ℤ) ^ t.val := by
    unfold lw
    rw [if_pos hse, if_neg hto]
    ring
  rw [e] at h1
  have := Formalism.HermitianLattices.IntegralLatticeDensity.no_form_of_bidegree_one_one l d s.val t.val hl (ZMod.val_lt s) (ZMod.val_lt t) h1
  rw [this] at hse
  exact hto hse
end Formalism.L2.Th1.D.TorusDerivation
