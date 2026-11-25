-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bessel_set_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:06:28.969168+00:00
-- url     : https://prove2.me/submissions/3d23bd4a-f4f4-468a-a221-9a315826ff40

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
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_lt_pairs
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



set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : BesselCard := by
  intro K _ _ s k N hskN
  classical
  set P : Finset (Fin N × Fin N) := Finset.univ.filter (fun x : Fin N × Fin N => x.1 < x.2 ∧
    ¬ ((s ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) < s + k) ∧ (x.2 : ℕ) = s + k)) with hP
  let good : Matrix (Fin N) (Fin N) K → Prop := fun u => (∀ i, u i i = 1) ∧
    (∀ i j, j < i → u i j = 0) ∧
    ∀ i j : Fin N, s ≤ (i : ℕ) → (i : ℕ) < s + k → (j : ℕ) = s + k → u i j = 0
  have hdet : ∀ u, good u → u.det = 1 := by
    intro u hu
    rw [Matrix.det_of_upperTriangular (fun i j hji => hu.2.1 i j hji)]
    simp [hu.1]
  have hzero : ∀ u, good u → ∀ i j, i ≠ j → (i, j) ∉ P → u i j = 0 := by
    intro u hu i j hij hP'
    rcases lt_or_gt_of_ne hij with h | h
    · by_cases hB : (s ≤ (i : ℕ) ∧ (i : ℕ) < s + k) ∧ (j : ℕ) = s + k
      · exact hu.2.2 i j hB.1.1 hB.1.2 hB.2
      · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, h, hB⟩) hP'
    · exact hu.2.1 i j h
  let M : (P → K) → Matrix (Fin N) (Fin N) K := fun f => Matrix.of fun a b =>
    if a = b then 1 else if h : (a, b) ∈ P then f ⟨(a, b), h⟩ else 0
  have hMgood : ∀ f, good (M f) := by
    intro f
    refine ⟨fun a => by simp [M], fun i j hji => ?_, fun i j hi1 hi2 hj => ?_⟩
    · have hne : i ≠ j := (ne_of_gt hji)
      have hnP : (i, j) ∉ P := fun h => absurd (Finset.mem_filter.1 h).2.1 (not_lt.2 hji.le)
      simp [M, hne, hnP]
    · have hne : i ≠ j := by
        intro h
        rw [h] at hi2
        omega
      have hnP : (i, j) ∉ P := fun h => (Finset.mem_filter.1 h).2.2 ⟨⟨hi1, hi2⟩, hj⟩
      simp [M, hne, hnP]
  have hU : ∀ f, IsUnit (M f).det := fun f => by rw [hdet _ (hMgood f)]; exact isUnit_one
  have hmem : ∀ u : GL (Fin N) K, u ∈ besselSet K s k N ↔ good (u : Matrix (Fin N) (Fin N) K) :=
    fun u => Iff.rfl
  let e : (besselSet K s k N) ≃ (P → K) :=
    { toFun := fun u p => ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.nonsingInvUnit (M f) (hU f), by
        rw [hmem]
        exact hMgood f⟩
      left_inv := fun u => by
        have hu1 : good ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := (hmem _).1 u.2
        apply Subtype.ext
        apply Units.ext
        show M (fun p => ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) p.1.1 p.1.2) =
          ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
        ext a b
        simp only [M, Matrix.of_apply]
        by_cases hab : a = b
        · subst hab
          simp [hu1.1]
        · by_cases hΦ : (a, b) ∈ P
          · simp [hab, hΦ]
          · simp [hab, hΦ, hzero _ hu1 a b hab hΦ]
      right_inv := fun f => by
        funext p
        have hne : p.1.1 ≠ p.1.2 := (Finset.mem_filter.1 p.2).2.1.ne
        show M f p.1.1 p.1.2 = f p
        simp [M, hne] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_coe]
  congr 1
  set L := (Finset.univ : Finset (Fin N × Fin N)).filter (fun x => x.1 < x.2) with hL
  have hPL : P = L.filter (fun x => ¬ ((s ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) < s + k) ∧ (x.2 : ℕ) = s + k)) := by
    rw [hP, hL, Finset.filter_filter]
  have hadd := Finset.card_filter_add_card_filter_not (s := L)
    (fun x : Fin N × Fin N => (s ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) < s + k) ∧ (x.2 : ℕ) = s + k)
  beta_reduce at hadd
  have hZ : (L.filter (fun x : Fin N × Fin N =>
      (s ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) < s + k) ∧ (x.2 : ℕ) = s + k)).card = k := by
    have hsk : s + k < N := by omega
    let g : ℕ → Fin N × Fin N := fun i => (⟨min i (N - 1), by omega⟩, ⟨s + k, hsk⟩)
    have himg : L.filter (fun x : Fin N × Fin N =>
        (s ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) < s + k) ∧ (x.2 : ℕ) = s + k) = (Finset.Ico s (s + k)).image g := by
      ext ⟨i, j⟩
      simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_Ico, g, Prod.mk.injEq]
      constructor
      · rintro ⟨-, ⟨h1, h2⟩, h3⟩
        refine ⟨(i : ℕ), ⟨h1, h2⟩, Fin.ext ?_, Fin.ext h3.symm⟩
        show min (i : ℕ) (N - 1) = i
        have := i.2
        omega
      · rintro ⟨a, ⟨h1, h2⟩, rfl, rfl⟩
        refine ⟨?_, ⟨?_, ?_⟩, rfl⟩
        · show min a (N - 1) < s + k
          omega
        · show s ≤ min a (N - 1)
          omega
        · show min a (N - 1) < s + k
          omega
    rw [himg, Finset.card_image_of_injOn, Nat.card_Ico]
    · omega
    · intro a ha b hb hab
      simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
      have := congrArg (fun x : Fin N × Fin N => (x.1 : ℕ)) hab
      simp only [g] at this
      omega
  have hLc : L.card = N * (N - 1) / 2 := by rw [hL]; exact card_lt_pairs N
  rw [hPL]
  generalize N * (N - 1) / 2 = T at hLc ⊢
  omega
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
