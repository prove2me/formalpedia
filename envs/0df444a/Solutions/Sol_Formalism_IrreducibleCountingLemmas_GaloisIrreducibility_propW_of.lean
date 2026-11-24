-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.propW_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:11:54.175231+00:00
-- url     : https://prove2.me/submissions/e0f18638-beed-4945-8a0b-8b115045a57e

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
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_eq_filter
import Theorems.Thm_P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_eq_filter__b757eed49bc8
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_mono
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_nonneg
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_union_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_biUnion_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_compl
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_univ
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_pi
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_one_place
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree
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
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (h1 : SqMassLower) (h3 : LocalEstimateII) (h4 : LocalEstimateIII)
    (h5 : LocalEstimateIV) (h6 : LocalEstimateV) : PropW := by
  classical
  intro K L ι J _ _ _ _ _ _ _ N q₁ d χ P hN hq hq1 hd hne hq2 hd2 hmax h16 hq1d hdd hP0 hP1 hPsq
  have hμ : ∀ x : ι → Fin N → K, 0 ≤ ∏ v, P (x v) :=
    fun x => Finset.prod_nonneg fun v _ => hP0 _
  have hconv : ∀ (p : (Fin N → K) → Prop), wtOf P {c | c ∈ sqSet K N ∧ p c} =
      ∑ c ∈ (sqSet K N).filter p, sqWeight (monicOf c) := by
    intro p
    rw [wtOf_eq_filter']
    exact Finset.sum_congr rfl fun c hc => hPsq c (Finset.mem_filter.1 hc).1
  set q : ℝ := (Fintype.card K : ℝ) with hqdef
  set f : ℝ := (Fintype.card ι : ℝ) with hfdef

  set S1 : Set (Fin N → K) := {c | c ∈ sqSet K N}ᶜ with hS1
  set S3 : Set (Fin N → K) := {c | c ∈ sqSet K N ∧ ∃ l : ℕ, l.Prime ∧
    l ∉ BB (Fintype.card K) N ∧ ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L)} with hS3
  set S4 : Kˣ → Set (Fin N → K) := fun c₀ => {c | c ∈ sqSet K N ∧ ∃ l : ℕ, l.Prime ∧
    l ≠ Fintype.card K ∧ ∃ x ∈ (monicOf c).rootSet L,
      primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))} with hS4
  set S5 : ℕ → Set (Fin N → K) := fun a => {c | c ∈ sqSet K N ∧
    ∃ h : K[X], h ∣ monicOf c ∧ h.natDegree = a} with hS5
  set S6 : Set (Fin N → K) := {c | c ∈ sqSet K N ∧ ¬ ∃ Q : K[X], Irreducible Q ∧ Q ∣ monicOf c ∧
    Q.natDegree.Prime ∧ N < 2 * Q.natDegree ∧ Q.natDegree + 3 ≤ N} with hS6

  have b1 : wtOf P S1 ≤ 2 / q := by
    rw [hS1, wtOf_compl, wtOf_univ, hP1]
    have e : wtOf P {c | c ∈ sqSet K N} = ∑ c ∈ sqSet K N, sqWeight (monicOf c) := by
      have := hconv (fun _ => True)
      simpa using this
    rw [e]
    have := h1 K N (by omega)
    linarith
  have b3 : wtOf P S3 ≤ 23 * Real.log q / Real.sqrt q := by
    refine (hconv _).trans_le ?_
    convert h3 K L N hq
  have b4 : ∀ c₀ : Kˣ, wtOf P (S4 c₀) ≤
      1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / (q - 1) := by
    intro c₀
    refine (hconv _).trans_le ?_
    convert h4 K L N q₁ d c₀ (by omega) hq1 hd hne hq2 hd2 hmax h16 hq1d hdd
  have b5 : ∀ a ∈ Finset.Icc 1 (N / 2), wtOf P (S5 a) ≤ 7 / 8 := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    refine (hconv _).trans_le ?_
    convert h5 K N a (by omega) (by omega)
  have b6 : wtOf P S6 ≤ 1 - 1 / (5 * Real.log N) := by
    refine (hconv _).trans_le ?_
    convert h6 K N hN

  have hcover : {x : ι → Fin N → K | ¬ GoodAt K L N (fun v => monicOf (x v)) χ} ⊆
      (((((⋃ v ∈ (Finset.univ : Finset ι), {x : ι → Fin N → K | x v ∈ S1}) ∪
        (⋃ v ∈ (Finset.univ : Finset ι), {x : ι → Fin N → K | x v ∈ S3})) ∪
        (⋃ w ∈ (Finset.univ : Finset (ι × J)), ({x : ι → Fin N → K | x w.1 ∈ S4 (χ w.1 w.2)} ∪
          {x : ι → Fin N → K | x w.1 ∈ S4 (χ w.1 w.2)⁻¹}))) ∪
        (⋃ a ∈ Finset.Icc 1 (N / 2), {x : ι → Fin N → K | ∀ v, x v ∈ S5 a})) ∪
        {x : ι → Fin N → K | ∀ v, x v ∈ S6}) := by
    intro x hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, Set.mem_setOf_eq,
      Finset.mem_univ, true_implies, forall_true_left] at hcon
    obtain ⟨⟨⟨⟨c1, c3⟩, c4⟩, c5⟩, c6⟩ := hcon
    have hsq : ∀ v, x v ∈ sqSet K N := by
      intro v
      have := c1 v
      simpa [hS1] using this
    have hsq' : ∀ v, Squarefree (monicOf (x v)) ∧ (monicOf (x v)).coeff 0 ≠ 0 := by
      intro v
      have := hsq v
      simpa [sqSet] using this
    apply hx
    refine ⟨fun v => ⟨monicOf_monic _, monicOf_natDegree _, (hsq' v).2⟩, fun v => (hsq' v).1,
      ?_, ?_, ?_, ?_⟩
    · intro l hl hlB v
      by_contra hinj
      exact c3 v ⟨hsq v, l, hl, hlB, hinj⟩
    · intro l hl hlq v j y hy
      refine ⟨fun he => ?_, fun he => ?_⟩
      · exact (c4 (v, j)).1 ⟨hsq v, l, hl, hlq, y, hy, he⟩
      · exact (c4 (v, j)).2 ⟨hsq v, l, hl, hlq, y, hy, he⟩
    · intro a ha1 ha2
      by_contra hall
      push Not at hall
      exact c5 a (Finset.mem_Icc.2 ⟨ha1, by omega⟩) fun v => ⟨hsq v, hall v⟩
    · by_contra hno
      push Not at hno
      apply c6
      intro v
      refine ⟨hsq v, ?_⟩
      rintro ⟨Q, hQ1, hQ2, hQ3, hQ4, hQ5⟩
      exact absurd hQ5 (not_le.2 (hno v Q hQ1 hQ2 hQ3 hQ4))
  rw [← wtOf_eq_filter (fun x : ι → Fin N → K => ∏ v, P (x v))
    (fun x => ¬ GoodAt K L N (fun v => monicOf (x v)) χ)]
  refine (wtOf_mono _ hμ hcover).trans ?_
  refine (wtOf_union_le _ hμ _ _).trans (add_le_add ((wtOf_union_le _ hμ _ _).trans
    (add_le_add ((wtOf_union_le _ hμ _ _).trans (add_le_add ((wtOf_union_le _ hμ _ _).trans
      (add_le_add ?_ ?_)) ?_)) ?_)) ?_)
  · refine (wtOf_biUnion_le _ hμ _ _).trans ?_
    calc ∑ v : ι, wtOf (fun x : ι → Fin N → K => ∏ v, P (x v)) {x | x v ∈ S1}
        = ∑ _v : ι, wtOf P S1 := Finset.sum_congr rfl fun v _ => wtOf_one_place P hP1 S1 v
      _ = f * wtOf P S1 := by simp [hfdef]
      _ ≤ f * (2 / q) := mul_le_mul_of_nonneg_left b1 (Nat.cast_nonneg _)
      _ = 2 * f / q := by ring
  · refine (wtOf_biUnion_le _ hμ _ _).trans ?_
    calc ∑ v : ι, wtOf (fun x : ι → Fin N → K => ∏ v, P (x v)) {x | x v ∈ S3}
        = ∑ _v : ι, wtOf P S3 := Finset.sum_congr rfl fun v _ => wtOf_one_place P hP1 S3 v
      _ = f * wtOf P S3 := by simp [hfdef]
      _ ≤ f * (23 * Real.log q / Real.sqrt q) :=
          mul_le_mul_of_nonneg_left b3 (Nat.cast_nonneg _)
      _ = 23 * f * Real.log q / Real.sqrt q := by ring
  · refine (wtOf_biUnion_le _ hμ _ _).trans ?_
    set B : ℝ := 1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / (q - 1) with hB
    calc ∑ w : ι × J, wtOf (fun x : ι → Fin N → K => ∏ v, P (x v))
          ({x | x w.1 ∈ S4 (χ w.1 w.2)} ∪ {x | x w.1 ∈ S4 (χ w.1 w.2)⁻¹})
        ≤ ∑ _w : ι × J, (B + B) := by
          refine Finset.sum_le_sum fun w _ => (wtOf_union_le _ hμ _ _).trans (add_le_add ?_ ?_)
          · rw [wtOf_one_place P hP1]; exact b4 _
          · rw [wtOf_one_place P hP1]; exact b4 _
      _ = 2 * f * (Fintype.card J : ℝ) * B := by
          simp [hfdef, Fintype.card_prod]; ring
  · refine (wtOf_biUnion_le _ hμ _ _).trans ?_
    calc ∑ a ∈ Finset.Icc 1 (N / 2), wtOf (fun x : ι → Fin N → K => ∏ v, P (x v))
          {x | ∀ v, x v ∈ S5 a}
        ≤ ∑ _a ∈ Finset.Icc 1 (N / 2), (7 / 8 : ℝ) ^ Fintype.card ι := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [wtOf_pi P (fun _ => S5 a), Finset.prod_const, Finset.card_univ]
          exact pow_le_pow_left₀ (wtOf_nonneg P hP0 _) (b5 a ha) _
      _ = ((N / 2 : ℕ) : ℝ) * (7 / 8 : ℝ) ^ Fintype.card ι := by simp
      _ ≤ (N : ℝ) / 2 * (7 / 8 : ℝ) ^ Fintype.card ι := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Nat.cast_div_le
  · rw [wtOf_pi P (fun _ => S6), Finset.prod_const, Finset.card_univ]
    calc wtOf P S6 ^ Fintype.card ι ≤ (Real.exp (-(1 / (5 * Real.log N)))) ^ Fintype.card ι := by
          refine pow_le_pow_left₀ (wtOf_nonneg P hP0 _) (b6.trans ?_) _
          exact Real.one_sub_le_exp_neg _
      _ = Real.exp (-f / (5 * Real.log N)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          rw [hfdef]; ring
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
