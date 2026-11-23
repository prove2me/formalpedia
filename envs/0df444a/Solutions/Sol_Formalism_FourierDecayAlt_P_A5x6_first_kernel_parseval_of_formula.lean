-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.first_kernel_parseval_of_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:45.890927+00:00
-- url     : https://prove2.me/submissions/0e4633b4-e18e-4a36-8ea7-5adcacb52b97

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_pt_det_isUnit
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_first_kernel_inner_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_orbZ_det
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6
namespace Formalism.FourierDecayAlt.P.A5x6
theorem _root_.solution (hF : SingleBlockFormula) (hI : IntFinite) (hCD : CharOrthDual) (hCO : CharOrth)
    (hCC : CokerCard) : SingleBlockParseval := by
  intro K _ _ _ R ψ hL h h' e cr hcr
  classical
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => by
    simpa using (hL.selfDual 1).mpr R.one_mem r hr
  have hκ : Function.Bijective (fun x : K ⧸ R.toAddSubgroup =>
      (Submodule.Quotient.mk ((cr x : Kˣ) : K) : KR R)) := by
    constructor
    · intro x y hxy
      have h1 := (mem_rangeR R _).mp ((Submodule.Quotient.eq _).mp hxy)
      rw [← hcr x, ← hcr y]
      exact QuotientAddGroup.eq_iff_sub_mem.mpr h1
    · intro y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      refine ⟨(a : K ⧸ R.toAddSubgroup), ?_⟩
      apply (Submodule.Quotient.eq _).mpr
      rw [mem_rangeR]
      exact QuotientAddGroup.eq_iff_sub_mem.mp (hcr (a : K ⧸ R.toAddSubgroup))
  let G : (K ⧸ R.toAddSubgroup) → Cos R h × Cos R h' → ℂ := fun x q =>
    (if IsInt R (orbZ h (rep R q.1)) ∧ IsInt R (orbZ h' (rep R q.2)) then
      singleBlockInner R ψ (orbZ h (rep R q.1)) (orbZ h' (rep R q.2)) ((cr x : Kˣ) : K) else 0) *
      phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))
  have hG : ∀ q, (Function.support fun x => G x q).Finite ∧
      ∑ᶠ x, G x q = ((cSize R h * cSize R h' : ℝ) : ℂ) * pairTerm R ψ h h' q := by
    intro q
    by_cases hq : IsInt R (orbZ h (rep R q.1)) ∧ IsInt R (orbZ h' (rep R q.2))
    · have hZ : IsUnit (orbZ h (rep R q.1)).det := by rw [orbZ_det]; exact pt_det_isUnit h
      have hZ' : IsUnit (orbZ h' (rep R q.2)).det := by rw [orbZ_det]; exact pt_det_isUnit h'
      obtain ⟨hC, hcard⟩ := hCC K R ψ hL _ _ hq.1 hZ
      obtain ⟨hC', hcard'⟩ := hCC K R ψ hL _ _ hq.2 hZ'
      obtain ⟨hD, hOD⟩ := hCD K R ψ hL _ _ hq.1 hZ
      have hO := hCO K R ψ hL _ _ hq.1 hZ
      have key := first_kernel_inner_sum R ψ hψ _ _ hZ hZ' hC hC' hD
        (fun x hx => by rw [hOD x, if_pos hx]) (fun x hx => by rw [hOD x, if_neg hx]; simp)
        (fun μ hμ => by rw [hO μ, if_pos hμ]) (fun μ hμ => by rw [hO μ, if_neg hμ]; simp)
        (fun x : K ⧸ R.toAddSubgroup => ((cr x : Kˣ) : K)) hκ
      have hc : (Nat.card (coker R (orbZ h (rep R q.1))) : ℂ) = ((cSize R h : ℝ) : ℂ) := by
        rw [cSize, ← orbZ_det h (rep R q.1), ← hcard]; simp
      have hc' : (Nat.card (coker R (orbZ h' (rep R q.2))) : ℂ) = ((cSize R h' : ℝ) : ℂ) := by
        rw [cSize, ← orbZ_det h' (rep R q.2), ← hcard']; simp
      simp only [G, if_pos hq, mul_assoc]
      constructor
      · refine key.1.subset ?_
        intro x hx
        simp only [Function.mem_support, ne_eq] at hx ⊢
        intro h0; apply hx; rw [h0, zero_mul]
      · rw [← finsum_mul, key.2, hc, hc']
        unfold pairTerm
        rw [if_pos hq]
        push_cast
        ring
    · simp only [G, if_neg hq, pairTerm]
      simp
  have hS := (hI K R ψ hL h).prod (hI K R ψ hL h')
  have hNs : ∀ x, Ns R ψ 1 h h' (cr x) (cr x) = ∑ q ∈ hS.toFinset, G x q := by
    intro x
    rw [hF K R ψ hL h h' (cr x) e]
    apply finsum_eq_sum_of_support_subset
    intro q hq
    simp only [Function.mem_support, ne_eq] at hq
    rw [Set.Finite.coe_toFinset]
    by_contra hcon
    apply hq
    rw [if_neg (fun hI' => hcon ⟨hI'.1, hI'.2⟩)]
    simp
  have hKp : N0 R ψ h h' = ∑ q ∈ hS.toFinset, pairTerm R ψ h h' q := by
    unfold N0 Kp
    apply finsum_eq_sum_of_support_subset
    intro q hq
    simp only [Function.mem_support, ne_eq, pairTerm] at hq
    rw [Set.Finite.coe_toFinset]
    by_contra hcon
    apply hq
    rw [if_neg (fun hI' => hcon ⟨hI'.1, hI'.2⟩)]
    simp
  simp only [hNs]
  constructor
  · refine (Set.Finite.biUnion hS.toFinset.finite_toSet (fun q _ => (hG q).1)).subset ?_
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    by_contra hcon
    apply hx
    apply Finset.sum_eq_zero
    intro q hq
    by_contra h0
    exact hcon (Set.mem_biUnion (Finset.mem_coe.mpr hq) h0)
  · rw [finsum_sum_comm _ _ (fun q _ => (hG q).1), hKp, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => (hG q).2)
end Formalism.FourierDecayAlt.P.A5x6
