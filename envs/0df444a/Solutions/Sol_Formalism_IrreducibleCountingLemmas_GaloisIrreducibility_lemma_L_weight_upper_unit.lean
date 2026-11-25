-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.lemma_L_weight_upper_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:06:55.225958+00:00
-- url     : https://prove2.me/submissions/fce4926d-884d-4409-aae4-6bb211b2d223

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
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8


section
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
private theorem lw_lemma (G : ℝ) (hG : 2 ≤ G) (d : Multiset ℕ) (hd : ∀ x ∈ d, 1 ≤ x)
    (h2 : 2 * (d.sum : ℝ) ≤ G) :
    G ^ d.sum ≤ (1 + 2 * (d.sum : ℝ) / G) * (d.map (fun x => G ^ x - 1)).prod := by
  induction d using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : 1 ≤ a := hd a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, 1 ≤ x := fun x hx => hd x (Multiset.mem_cons_of_mem hx)
    simp only [Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons, Nat.cast_add] at h2 ⊢
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hs0 : (0 : ℝ) ≤ s.sum := Nat.cast_nonneg _
    have ih' := ih hs (by linarith)
    have hG0 : 0 < G := by linarith
    have hGa : G ≤ G ^ a := le_self_pow₀ (by linarith) (by omega)
    have hGa0 : 0 ≤ G ^ a := (pow_pos hG0 a).le
    have hP0 : 0 ≤ (s.map (fun x => G ^ x - 1)).prod := by
      apply Multiset.prod_nonneg
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      have : 1 ≤ G ^ x := one_le_pow₀ (by linarith)
      linarith
    have key : G ^ a * (1 + 2 * (s.sum : ℝ) / G) ≤
        (1 + 2 * ((a : ℝ) + s.sum) / G) * (G ^ a - 1) := by
      rw [← sub_nonneg]
      have e : (1 + 2 * ((a : ℝ) + s.sum) / G) * (G ^ a - 1) - G ^ a * (1 + 2 * (s.sum : ℝ) / G)
          = (2 * a * G ^ a - G - 2 * (a + s.sum)) / G := by
        field_simp
        ring
      rw [e]
      apply div_nonneg _ hG0.le
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1) hGa0]
    calc G ^ (a + s.sum) = G ^ a * G ^ s.sum := pow_add _ _ _
      _ ≤ G ^ a * ((1 + 2 * (s.sum : ℝ) / G) * (s.map (fun x => G ^ x - 1)).prod) :=
          mul_le_mul_of_nonneg_left ih' hGa0
      _ = (G ^ a * (1 + 2 * (s.sum : ℝ) / G)) * (s.map (fun x => G ^ x - 1)).prod := by ring
      _ ≤ ((1 + 2 * ((a : ℝ) + s.sum) / G) * (G ^ a - 1)) * (s.map (fun x => G ^ x - 1)).prod :=
          mul_le_mul_of_nonneg_right key hP0
      _ = _ := by ring
private theorem lw_lemma_2 (G : ℝ) (hG : 2 ≤ G) (d : Multiset ℕ) (hd : ∀ x ∈ d, 1 ≤ x) :
    0 < (d.map (fun x => G ^ x - 1)).prod ∧ (d.map (fun x => G ^ x - 1)).prod ≤ G ^ d.sum := by
  induction d using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : 1 ≤ a := hd a (Multiset.mem_cons_self a s)
    obtain ⟨ih1, ih2⟩ := ih (fun x hx => hd x (Multiset.mem_cons_of_mem hx))
    simp only [Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons]
    have hGa : G ≤ G ^ a := le_self_pow₀ (by linarith) (by omega)
    refine ⟨mul_pos (by linarith) ih1, ?_⟩
    rw [pow_add]
    exact mul_le_mul (by linarith) ih2 ih1.le (pow_pos (by linarith) a).le
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
open scoped ComplexOrder
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial Formalism.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset Polynomial
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
open Finset
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial
section aux
variable {α β : Type} [Fintype α]
end aux
section prod
variable {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
end prod
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : LemmaLWeightU := by
  intro d g hd hg
  have hG : (2 : ℝ) ≤ g := by exact_mod_cast hg
  obtain ⟨hP, hle⟩ := lw_lemma_2 (g : ℝ) hG d hd
  have hpow : (0 : ℝ) < (g : ℝ) ^ d.sum := pow_pos (by linarith) _
  refine ⟨one_div_le_one_div_of_le hP hle, fun h2 => ?_⟩
  have h2' : 2 * (d.sum : ℝ) ≤ g := by exact_mod_cast h2
  have key := lw_lemma (g : ℝ) hG d hd h2'
  rw [div_le_div_iff₀ hP hpow, one_mul]
  exact key
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
