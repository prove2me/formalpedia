-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.A2.reductionAfterOfSteps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:43.725261+00:00
-- url     : https://prove2.me/submissions/9a6ad1bf-afab-4671-99e5-5df95b993e1b

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
section gen
variable {α : Type}
variable {E : Type} [AddCommGroup E]
end gen
section ta
variable {E : Type} [Field E] [DecidableEq E]
private theorem isPt_of_mem_pt (Sg : ℕ → ℕ → Finset E) (hNZ : NZSg Sg) :
    ∀ n, ∀ h ∈ PT Sg n, IsPt n h := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h hh
    cases n with
    | zero =>
      simp only [PT, Finset.mem_singleton] at hh
      subst hh
      simp [TA.IsPt, TA.lvl]
    | succ n =>
      simp only [PT, Finset.mem_biUnion, Finset.mem_attach, true_and, Finset.mem_image] at hh
      obtain ⟨a, h0, hh0, t, ht, he⟩ := hh
      subst he
      have hm := Finset.mem_range.mp a.2
      obtain ⟨hl, hb⟩ := ih a.1 hm h0 hh0
      unfold TA.IsPt
      refine ⟨?_, ?_⟩
      · simp [TA.ext, TA.lvl] at hl ⊢
        omega
      · intro b hbm
        simp only [TA.ext, List.mem_append, List.mem_singleton] at hbm
        rcases hbm with hbm | rfl
        · exact hb b hbm
        · refine ⟨?_, hNZ _ _ t ht⟩
          show 1 ≤ n + 1 - a.1
          omega
end ta
section main
variable {E : Type} [Field E] [DecidableEq E]
end main
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism.FourierDecayAlt.P.BudgetLiftBounds Formalism.FourierDecayAlt.TC
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.P.OneLevelCoefficients Finset
open scoped ComplexOrder
variable {E W : Type} [Field E]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B2
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexOrder ComplexConjugate
end Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
namespace Formalism.FourierDecayAlt.P
open RecursionWithDensities
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism.FourierDecayAlt.P.BudgetLiftBounds Formalism.FourierDecayAlt.TC
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
theorem _root_.solution : ReductionAfterOfSteps := by
  intro hOL hEps hA4 hJ C₀ hC₀
  obtain ⟨C', C, hJ'⟩ := hJ C₀ hC₀
  refine ⟨max C' 1, C, ?_⟩
  intro E _ _ H _ _ _ W _ len Kl f Θ D Pat1 Pat3 _ pat1 pat3 c1 c3 ep1 ep3 bd4 Φ tr w0 V jn ρ c
    hKl hf hΘ hr hK hA2 hDA hE hLS hLE hlim hw0 hV hPSD hsum
  have hΘ1 : 1 ≤ Θ := le_trans (le_max_right _ _) hΘ
  have hΘ0 : 0 < Θ := by linarith
  have hep : 0 ≤ (C₀ * Θ ^ (-((Kl : ℝ) - 5 / 2))) ^ f := by
    apply pow_nonneg
    apply mul_nonneg (by linarith)
    first
    | exact Real.rpow_nonneg hΘ0.le _
    | exact Real.rpow_nonneg_of_nonneg hΘ0.le _
  have ha : 0 ≤ (C₀ / Θ) ^ f := pow_nonneg (div_nonneg (by linarith) hΘ0.le) _
  have hG : ∀ Sg : ℕ → ℕ → Finset E, NZSg Sg → (gram (D.K (D.r + 1)) V (PT Sg (D.r + 1))).re ≤
      (1 + C * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * jn := by
    intro Sg hNZ
    obtain ⟨Th, hD⟩ := hDA Sg hNZ
    refine hEps E H W len (D.K (D.r + 1)) (PT Sg (D.r + 1)) Φ V w0 (4 * Kl * (D.r + 1))
      ((1 + C * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i))) jn
      (by omega) (fun eps heps => ?_) hlim (fun p hp => hV p (A1.isPt_of_mem_pt Sg hNZ _ p hp))
    let σ : ℕ → ℝ := fun i => √(lsup D len Kl Sg (Φ eps) i)
    let e' : ℕ → ℝ := fun i => max (D.e i) 0
    have hstep : ∀ i, 1 ≤ i → i ≤ D.r + 1 → σ i ≤
        (1 + (C₀ * Θ ^ (-((Kl : ℝ) - 5 / 2))) ^ f) * √(1 + e' i) * σ (i - 1) +
          ∑ t ∈ Icc 2 i, ((C₀ / Θ) ^ f) ^ (t - 1) * σ (i - t) := by
      intro i hi1 hi
      have he : e' i = D.e i := max_eq_left (hE i hi1 hi).1
      simp only [σ, he]
      exact hOL E H W len Kl D Sg (Φ eps) (tr eps i) Pat1 Pat3 (pat1 i) (pat3 i) (c1 i) (c3 i) (ep1 i)
        (ep3 i) (bd4 i) _ _ i hNZ hi1 hi hep ha hK hA2 ⟨Th, hD⟩ hE
        (hLE eps heps i (Finset.mem_Icc.mpr ⟨hi1, hi⟩)) (hLS i (Finset.mem_Icc.mpr ⟨hi1, hi⟩))
    have hrec := hJ' (Kl : ℝ) Θ f D.r e' σ (by exact_mod_cast hKl) hf (le_trans (le_max_left _ _) hΘ) hr
      (fun i => le_max_right _ _) (fun i => Real.sqrt_nonneg _) hstep
    have hprod : ∏ i ∈ Icc 1 (D.r + 1), (1 + e' i) = ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) :=
      Finset.prod_congr rfl fun i hi => by
        show 1 + max (D.e i) 0 = 1 + D.e i
        rw [max_eq_left (hE i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2).1]
    rw [hprod] at hrec
    have h0 : ∀ w, TA.Slev D Sg (Φ eps) w 0 = ‖Φ eps w []‖ ^ 2 := by
      intro w
      obtain ⟨hK1, -⟩ := hK
      simp only [TA.Slev, TA.gram, PT, Finset.sum_singleton, hK1, one_mul]
      first
      | exact inner_self_eq_norm_sq (𝕜 := ℂ) _
      | simp
    have hl0 : lsup D len Kl Sg (Φ eps) 0 =
        wsup len (4 * Kl * (D.r + 1)) (fun w => ‖Φ eps w []‖ ^ 2) := by
      unfold TA.lsup
      simp only [Nat.sub_zero, h0]
    have hnn : 0 ≤ lsup D len Kl Sg (Φ eps) 0 := by
      rw [hl0]
      unfold TA.wsup
      exact Real.iSup_nonneg fun _ => sq_nonneg _
    have hσ0 : σ 0 ^ 2 = wsup len (4 * Kl * (D.r + 1)) (fun w => ‖Φ eps w []‖ ^ 2) := by
      simp only [σ]
      rw [Real.sq_sqrt hnn, hl0]
    have hg : (gram (D.K (D.r + 1)) (Φ eps w0) (PT Sg (D.r + 1))).re ≤
        lsup D len Kl Sg (Φ eps) (D.r + 1) := by
      unfold TA.lsup TA.wsup
      have hw : len w0 ≤ 4 * Kl * (D.r + 1 - (D.r + 1)) := by omega
      exact le_ciSup (f := fun w : {w // len w ≤ 4 * Kl * (D.r + 1 - (D.r + 1))} =>
        TA.Slev D Sg (Φ eps) w.1 (D.r + 1)) (Set.finite_range _).bddAbove ⟨w0, hw⟩
    have hsq : lsup D len Kl Sg (Φ eps) (D.r + 1) ≤ σ (D.r + 1) ^ 2 := by
      simp only [σ]
      by_cases h : 0 ≤ lsup D len Kl Sg (Φ eps) (D.r + 1)
      · rw [Real.sq_sqrt h]
      · exact le_trans (le_of_lt (not_le.mp h)) (sq_nonneg _)
    calc (gram (D.K (D.r + 1)) (Φ eps w0) (PT Sg (D.r + 1))).re ≤ σ (D.r + 1) ^ 2 := le_trans hg hsq
      _ ≤ (1 + C * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i)) * σ 0 ^ 2 :=
        hrec
      _ = _ := by rw [hσ0]
  exact hA4 E H (D.r + 1) (D.K (D.r + 1)) V ρ c _ hG hPSD hsum
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
