-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.decay_assembly_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:44.082253+00:00
-- url     : https://prove2.me/submissions/4d117f05-27c6-49de-beea-661e2c0b197b

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_Final_h1
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_Final_h2
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_cb_weights
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : DecAssembly := by
  intro hDecay hRes hConj hGap N ep lam h Ω T _ μ _ _ κ v X A hlam hgap hκ hX hXb hres hA
  apply hRes Ω T μ v (fun k => ∏ i ∈ Ico 1 N,
    (lead ((κ k).conjTranspose * NormedSpace.exp X * κ k) i).re ^ (-(lam i - lam (i + 1) + 1)))
    _ A (Real.exp_pos _).le hres ?_ hA
  intro k
  obtain ⟨hY, hYb, hYs, hYe⟩ := hConj N ep (κ k) X (hκ k).1 (hκ k).2 hX hXb
  simp only [hYe]
  generalize (κ k).conjTranspose * X * κ k = Y at *
  have hpos : ∀ i, 0 ≤ (lead (NormedSpace.exp Y) i).re := by
    intro i
    by_cases hi : i ≤ N
    · obtain ⟨w, hw0, _, hlead, _⟩ := Formalism.NuclearRankWeightBounds.P.cb_weights N Y hY i hi
      rw [hlead, Complex.ofReal_re]
      exact Finset.sum_nonneg fun J _ => mul_nonneg (hw0 J) (Real.exp_pos _).le
    · simp [lead, hi]
  rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hpos i) _)]
  have hs0 : ∀ i, 0 ≤ (if 1 ≤ i ∧ i < N then lam i - lam (i+1) + 1 else 0) := by
    intro i
    split_ifs with hi
    · have := hlam i hi.1 hi.2; linarith
    · exact le_rfl
  have hD := hDecay N (fun i => if 1 ≤ i ∧ i < N then lam i - lam (i+1) + 1 else 0) ep h Y hs0 hY hYb (by
    intro a b hba hab
    have hba' : b.val < a.val := hba
    have hsum : ∑ i ∈ Ico (b.val+1) (a.val+1), (if 1 ≤ i ∧ i < N then lam i - lam (i+1) + 1 else 0)
        = ∑ i ∈ Ico (b.val+1) (a.val+1), (lam i - lam (i+1) + 1) := by
      apply Finset.sum_congr rfl; intro i hi
      have := Finset.mem_Ico.mp hi
      rw [if_pos ⟨by omega, by have := a.isLt; omega⟩]
    rw [hsum, hGap lam (a.val+1) (b.val+1) (by omega)]
    have h1 := hgap a b hba hab
    have h2 : (b.val:ℝ) < a.val := by exact_mod_cast hba'
    push_cast; linarith)
  have hprod : ∏ i ∈ Ico 1 N, (lead (NormedSpace.exp Y) i).re ^ (-(lam i - lam (i+1) + 1))
      = ∏ i ∈ Ico 1 N, (lead (NormedSpace.exp Y) i).re
        ^ (-(if 1 ≤ i ∧ i < N then lam i - lam (i+1) + 1 else 0)) := by
    apply Finset.prod_congr rfl; intro i hi
    have := Finset.mem_Ico.mp hi
    rw [if_pos ⟨this.1, this.2⟩]
  rw [hprod]
  refine hD.trans (le_of_eq ?_)
  rw [hYs]; unfold decExp; congr 1; ring
end Formalism.HermitianLatticeCounting.P
