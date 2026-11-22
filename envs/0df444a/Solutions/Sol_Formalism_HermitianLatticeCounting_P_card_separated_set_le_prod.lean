-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.card_separated_set_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:45.975186+00:00
-- url     : https://prove2.me/submissions/abae214e-7cec-403e-9b9c-eaf7915cbaac

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open MeasureTheory Metric
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (S : Finset (ι → F)) (r B : ι → ℝ) (hr : ∀ v, 0 < r v)
    (hB : ∀ v, 0 ≤ B v) (hS : ∀ c ∈ S, ∀ v, ‖c v‖ ≤ B v)
    (hsep : ∀ c ∈ S, ∀ d ∈ S, c ≠ d → ∃ v, 2 * r v ≤ ‖c v - d v‖) :
    (S.card : ℝ) ≤ ∏ v, ((B v + r v) / r v) ^ finrank ℝ F := by
  borelize F
  let μ : Measure F := Measure.addHaar
  let ν : Measure (ι → F) := Measure.pi fun _ => μ
  set n := finrank ℝ F with hn
  let P : (ι → F) → Set (ι → F) := fun c => Set.pi Set.univ fun v => ball (c v) (r v)
  have hPm : ∀ c, MeasurableSet (P c) := fun c => MeasurableSet.univ_pi fun v => measurableSet_ball
  have D : Set.Pairwise (S : Set (ι → F)) (Function.onFun Disjoint P) := by
    rintro c hc d hd hcd
    obtain ⟨v, hv⟩ := hsep c hc d hd hcd
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    have h1 := hx v (Set.mem_univ v)
    have h2 := hx' v (Set.mem_univ v)
    rw [mem_ball, dist_eq_norm] at h1 h2
    have : ‖c v - d v‖ ≤ ‖x v - d v‖ + ‖x v - c v‖ := by
      have e : c v - d v = (x v - d v) - (x v - c v) := by abel
      rw [e]; exact norm_sub_le _ _
    linarith
  have hsub : (⋃ c ∈ S, P c) ⊆ Set.pi Set.univ fun v => ball (0:F) (B v + r v) := by
    refine Set.iUnion₂_subset fun c hc => ?_
    intro x hx v _
    have h1 := hx v (Set.mem_univ v)
    rw [mem_ball, dist_eq_norm] at h1
    rw [mem_ball, dist_zero_right]
    have : ‖x v‖ ≤ ‖x v - c v‖ + ‖c v‖ := by simpa using norm_add_le (x v - c v) (c v)
    linarith [hS c hc v]
  set m := μ (ball 0 1) with hm
  have hvol : ∀ (c : ι → F) (ρ : ι → ℝ), (∀ v, 0 < ρ v) →
      ν (Set.pi Set.univ fun v => ball (c v) (ρ v)) =
        ENNReal.ofReal (∏ v, ρ v ^ n) * m ^ Fintype.card ι := by
    intro c ρ hρ
    simp only [ν, Measure.pi_pi]
    have : ∀ v, μ (ball (c v) (ρ v)) = ENNReal.ofReal (ρ v ^ n) * m := fun v =>
      μ.addHaar_ball_of_pos _ (hρ v)
    simp only [this]
    rw [Finset.prod_mul_distrib, ENNReal.ofReal_prod_of_nonneg (fun v _ => (pow_pos (hρ v) n).le),
      Finset.prod_const, Finset.card_univ]
  have I : (S.card : ENNReal) * ENNReal.ofReal (∏ v, r v ^ n) * m ^ Fintype.card ι ≤
      ENNReal.ofReal (∏ v, (B v + r v) ^ n) * m ^ Fintype.card ι :=
    calc (S.card : ENNReal) * ENNReal.ofReal (∏ v, r v ^ n) * m ^ Fintype.card ι
        = ν (⋃ c ∈ S, P c) := by
          rw [measure_biUnion_finset D fun c _ => hPm c]
          simp only [P, hvol _ r hr, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ ν (Set.pi Set.univ fun v => ball (0:F) (B v + r v)) := measure_mono hsub
      _ = _ := hvol (fun _ => 0) (fun v => B v + r v) (fun v => by linarith [hB v, hr v])
  have hm0 : m ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (measure_ball_pos _ _ zero_lt_one).ne'
  have hmt : m ^ Fintype.card ι ≠ ⊤ := ENNReal.pow_ne_top measure_ball_lt_top.ne
  have J := (ENNReal.mul_le_mul_iff_left hm0 hmt).1 I
  have hA : 0 < ∏ v, r v ^ n := Finset.prod_pos fun v _ => pow_pos (hr v) n
  have K := ENNReal.toReal_le_of_le_ofReal
    (Finset.prod_nonneg fun v _ => pow_nonneg (by linarith [hB v, hr v]) n) J
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hA.le] at K
  simp only [div_pow]
  rw [Finset.prod_div_distrib, le_div_iff₀ hA]
  exact K
end Formalism.HermitianLatticeCounting.P
