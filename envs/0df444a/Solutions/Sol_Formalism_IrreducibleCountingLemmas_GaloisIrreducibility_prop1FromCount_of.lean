-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.prop1FromCount_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:21.035541+00:00
-- url     : https://prove2.me/submissions/bfff4b58-e0e9-45fb-8aeb-fe7a13283aa3

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_PropositionOneCentralCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (hDW : DyadicWindow) (hES : ExcludedSimplify) (hP1 : Prop1Core) :
    Prop1FromCount := by
  intro N c X P hN hc hX hmain hP hcard
  set κ := c ^ (-20 : ℤ) with hκdef
  have hc0 : 0 < c := by linarith
  have hκ : 0 < κ := zpow_pos hc0 _
  have hPX : ∀ p ∈ P, 1 ≤ p ∧ (p : ℝ) ≤ X := fun p hp => ⟨(hP p hp).1.one_lt.le, (hP p hp).2⟩
  obtain ⟨j, hj1, hjlt, hjcard⟩ := hDW P X κ hX hκ hPX hcard
  set Y := X / 2 ^ j with hYdef
  set P' := P.filter (fun p : ℕ => Y ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y) with hP'
  have hκX : 0 < κ * X := mul_pos hκ hX
  have hY0 : 0 < Y := by linarith
  have hXY : X * κ ≤ Y := by linarith
  have hQ : (N : ℝ) ^ 4 * c ^ 500 ≤ Y ^ ((1 : ℝ) / 4) :=
    hmain.trans (Real.rpow_le_rpow (mul_pos hX hκ).le hXY (by norm_num))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN21 : (21 : ℝ) ≤ N := by exact_mod_cast hN
  have hc500 : 1 ≤ c ^ 500 := one_le_pow₀ hc
  have hN4 : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ hN1
  have hY14 : 1 ≤ Y ^ ((1 : ℝ) / 4) := le_trans (one_le_mul_of_one_le_of_one_le hN4 hc500) hQ
  have hY1 : 1 ≤ Y := by
    by_contra h
    push_neg at h
    have := Real.rpow_lt_one hY0.le h (by norm_num : (0 : ℝ) < 1 / 4)
    linarith
  have hsplit : Y = Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hY0]
    norm_num
  have hκc : κ * c ^ 500 = c ^ 480 := by
    rw [hκdef, zpow_neg, zpow_ofNat, inv_mul_eq_div, div_eq_iff (pow_pos hc0 20).ne']
    ring
  have hkey : 20 * (N : ℝ) ^ 3 * Y ^ ((3 : ℝ) / 4) < κ * Y := by
    have hY34 : 0 < Y ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hY0 _
    have h1 : 20 * (N : ℝ) ^ 3 < κ * Y ^ ((1 : ℝ) / 4) := by
      have h2 : κ * ((N : ℝ) ^ 4 * c ^ 500) ≤ κ * Y ^ ((1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left hQ hκ.le
      have h3 : κ * ((N : ℝ) ^ 4 * c ^ 500) = (N : ℝ) ^ 4 * c ^ 480 := by
        rw [mul_left_comm, hκc]
      have h4 : (1 : ℝ) ≤ c ^ 480 := one_le_pow₀ hc
      have hNpos : (0 : ℝ) < N := by linarith
      have h5 : 20 * (N : ℝ) ^ 3 < (N : ℝ) ^ 4 := by
        nlinarith [mul_pos (pow_pos hNpos 3) (by linarith : (0 : ℝ) < N - 20)]
      nlinarith [mul_le_mul_of_nonneg_left h4 (pow_pos hNpos 4).le]
    calc 20 * (N : ℝ) ^ 3 * Y ^ ((3 : ℝ) / 4) < κ * Y ^ ((1 : ℝ) / 4) * Y ^ ((3 : ℝ) / 4) :=
          mul_lt_mul_of_pos_right h1 hY34
      _ = κ * (Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4)) := by ring
      _ = κ * Y := by rw [← hsplit]
  have hES' := hES N Y (by omega) hY1
  have hmemP' : ∀ g ∈ P', g.Prime ∧ Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y := by
    intro g hg
    rw [hP', Finset.mem_filter] at hg
    exact ⟨(hP g hg.1).1, hg.2.1, hg.2.2⟩
  have hcardP' : (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) < P'.card := by
    linarith
  obtain ⟨g₁, hg₁, g₂, hg₂, hne, hdisj⟩ := hP1 N Y P' (by omega) hY1 hmemP' hcardP'
  have hg₁' := hmemP' g₁ hg₁
  have hg₂' := hmemP' g₂ hg₂
  rw [hP', Finset.mem_filter] at hg₁ hg₂
  refine ⟨Y, hXY, ?_, by linarith, g₁, hg₁.1, g₂, hg₂.1, hne, ⟨hg₁'.2.1, hg₁'.2.2⟩,
    ⟨hg₂'.2.1, hg₂'.2.2⟩, hdisj⟩
  have h2j : (2 : ℝ) ≤ 2 ^ j := le_self_pow₀ (by norm_num) (by omega)
  calc 2 * Y = 2 * X / 2 ^ j := by rw [hYdef]; ring
    _ ≤ X := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
