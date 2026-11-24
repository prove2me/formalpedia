-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.theorem_c_i
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:16:48.499604+00:00
-- url     : https://prove2.me/submissions/1e3ead97-6cc0-4b77-8b72-bdc9beab5dc6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_inversion_formula

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
open CSym
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : ThmCi := by
  intro K ι _ M _ _ Kk Tm pp ν k t r j Ev Od lam w m hpp hrk hI
  set Q := pp ^ ν with hQdef
  have hQ : Q ≠ 0 := pow_ne_zero _ hpp
  have hinv := inversion_formula K M Kk (fun a i => (Q ^ (-((i : ℤ) * ((NN k t a : ℤ) - i)))) • Tm a i)
    Q t m j hI j le_rfl r
  have hZ : Zop pp ν Ev Od lam w m k t r j (Tm j) =
      (pp ^ (NprimeZ Ev Od lam (w j) r) * Q ^ ((r : ℤ) * ((NN k t j : ℤ) - r))) •
        ∑ l ∈ range (r + 1), ((-1 : K) ^ l * hF (FFam Q t m j) l) •
          ((Q ^ (-(((r - l : ℕ) : ℤ) * ((NN k t j : ℤ) - ((r - l : ℕ) : ℤ))))) • Tm j (r - l)) := by
    unfold Zop
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlr : l ≤ r := by simp only [Finset.mem_range] at hl; omega
    unfold cCoef Ttil
    simp only [smul_smul]
    congr 1
    have h1 : pp ^ (NprimeZ Ev Od lam (w j) r - NprimeZ Ev Od lam (w j) (r - l)) *
        pp ^ (NprimeZ Ev Od lam (w j) (r - l)) = pp ^ (NprimeZ Ev Od lam (w j) r) := by
      rw [← zpow_add₀ hpp]
      ring_nf
    have h2 : Q ^ ((l : ℤ) * ((NN k t j : ℤ) - 2 * r + l)) =
        Q ^ ((r : ℤ) * ((NN k t j : ℤ) - r)) *
          Q ^ (-(((r - l : ℕ) : ℤ) * ((NN k t j : ℤ) - ((r - l : ℕ) : ℤ)))) := by
      rw [← zpow_add₀ hQ]
      congr 1
      push_cast [Nat.cast_sub hlr]
      ring
    rw [h2]
    linear_combination ((-1 : K) ^ l * Q ^ ((r : ℤ) * ((NN k t j : ℤ) - r)) *
      Q ^ (-(((r - l : ℕ) : ℤ) * ((NN k t j : ℤ) - ((r - l : ℕ) : ℤ)))) * hF (FFam Q t m j) l) * h1
  rw [hZ, LinearMap.smul_comp, hinv]
  simp only [LinearMap.comp_smul, smul_smul]
  congr 1
  have hQz : ∀ z : ℤ, Q ^ z = pp ^ ((ν : ℤ) * z) := fun z => by rw [zpow_mul, zpow_natCast]
  rw [hQz, hQz, ← zpow_add₀ hpp, ← zpow_add₀ hpp, ← zpow_add₀ hpp]
  congr 1
  unfold NprimeZ PrZ ArZ NN
  push_cast
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  ring
end Formalism.InvariantFactorPaths.G7
