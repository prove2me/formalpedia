-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.sum_log_norm_over_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:52:53.488784+00:00
-- url     : https://prove2.me/submissions/6456ec33-9d12-4407-b470-98f8f3950f8f

import Definitions.Def_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainLatticeSizesModelEventually
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_prBelow_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain2
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (S : Finset (slopeLatticeData.FinPl K)) (p : ℕ) (hp : p.Prime)
    (hS : ∀ w : slopeLatticeData.FinPl K, prBelow w = p → w ∈ S) :
    ∑ w ∈ S.filter (fun w => prBelow w = p), lE w = Real.log (p : ℝ) := by
  classical
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hP
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hPprime : P.IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hPne : P ≠ ⊥ := by simpa [hP] using hpZ.ne_zero
  have hPmax : P.IsMaximal := hPprime.isMaximal hPne
  have : Fintype (P.primesOver (𝓞 K)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 K)
  have hmax : ∀ q : P.primesOver (𝓞 K), q.1.IsMaximal := fun q => by
    have := q.2.1
    have := q.2.2
    exact Ideal.IsMaximal.of_liesOver_isMaximal q.1 P
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hterm : ∀ w : slopeLatticeData.FinPl K, prBelow w = p →
      lE w = Real.log p / (Module.finrank ℚ K : ℝ) * ((w.1.ramificationIdx ℤ * w.1.inertiaDeg ℤ : ℕ) : ℝ) := by
    intro w hw
    have := (prBelow_iff w p).1 hw
    have := w.2
    unfold lE slopeLatticeData.ell ramE
    rw [Ideal.absNorm_eq_pow_inertiaDeg' w.1 hp, Ideal.inertiaDeg'_eq_inertiaDeg]
    push_cast
    rw [Real.log_pow]
    ring
  have hbij : ∑ w ∈ S.filter (fun w => prBelow w = p), lE w
      = ∑ q : P.primesOver (𝓞 K), Real.log p / (Module.finrank ℚ K : ℝ) *
          ((q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ : ℕ) : ℝ) := by
    symm
    refine Finset.sum_bij (fun q _ => (⟨q.1, hmax q⟩ : slopeLatticeData.FinPl K)) ?_ ?_ ?_ ?_
    · intro q _
      have : prBelow (⟨q.1, hmax q⟩ : slopeLatticeData.FinPl K) = p := (prBelow_iff _ p).2 q.2.2
      exact Finset.mem_filter.2 ⟨hS _ this, this⟩
    · intro q _ q' _ h
      exact Subtype.ext (congrArg (fun w : slopeLatticeData.FinPl K => w.1) h)
    · intro w hw
      have hw' := (Finset.mem_filter.1 hw).2
      exact ⟨⟨w.1, w.2.isPrime, (prBelow_iff w p).1 hw'⟩, Finset.mem_univ _, rfl⟩
    · intro q _
      exact (hterm (⟨q.1, hmax q⟩ : slopeLatticeData.FinPl K) ((prBelow_iff _ p).2 q.2.2)).symm
  rw [hbij, ← Finset.mul_sum, ← Nat.cast_sum, hsum, NumberField.RingOfIntegers.rank]
  field_simp
end Formalism.LFunctionChainParameters.LChain2
