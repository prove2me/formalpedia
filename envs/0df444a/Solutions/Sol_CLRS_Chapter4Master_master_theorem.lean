-- Prove2me | solution 1 for CLRS.Chapter4Master.master_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Chutong
-- created : 2026-10-11T06:34:30.428577+00:00
-- url     : https://prove2.me/submissions/a1685a4e-76cb-43d8-8e0d-51d790807c58

import Definitions.Def_CLRS_Chapter4_Master_Basic
import Definitions.Def_CLRS_Chapter4_Master_CaseTwo
import Definitions.Def_CLRS_Chapter4_Master_Rounding
import Definitions.Def_CLRS_Chapter4_Substitution
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Computability.AkraBazzi.AkraBazzi
import Mathlib.Tactic
import Std

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section
namespace CLRS

/-!
# Real-valued recurrence comparison

This file keeps the recurrence hypotheses separate from the analytic estimates
used by the master theorem. In particular, the original toll need not have
Mathlib's stronger `GrowsPolynomially` property. Finite base cases may differ
between comparison recurrences.
-/

open Filter Asymptotics
open scoped Topology

namespace Chapter4Master



namespace Recurrence

variable {T f U g : ℕ → ℝ} {a : ℝ} {r : ℕ → ℕ}

theorem pos (R : Recurrence T f a r) (n : ℕ) : 0 < T n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < R.cutoff
    · exact R.base_pos n hn
    · have hn' := Nat.le_of_not_lt hn
      rw [R.eqn n hn']
      exact add_pos_of_pos_of_nonneg
        (mul_pos R.a_pos (ih (r n) (R.decreases n hn'))) (R.toll_nonneg n)

theorem nonneg (R : Recurrence T f a r) (n : ℕ) : 0 ≤ T n := (R.pos n).le

end Recurrence

/-- Any finite set of initial costs can be bounded by a positive comparison
cost. This is why asymptotic recurrence comparison does not prescribe base
case values or require the two cutoffs to agree. -/
theorem exists_pos_mul_bound (T U : ℕ → ℝ) (hU : ∀ n, 0 < U n) (N : ℕ) :
    ∃ C > 0, ∀ n, n < N → T n ≤ C * U n := by
  let C := 1 + ∑ n ∈ Finset.range N, |T n / U n|
  have hs : 0 ≤ ∑ n ∈ Finset.range N, |T n / U n| :=
    Finset.sum_nonneg fun n _ => abs_nonneg _
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro n hn
  apply (div_le_iff₀ (hU n)).mp
  calc
    T n / U n ≤ |T n / U n| := le_abs_self _
    _ ≤ ∑ j ∈ Finset.range N, |T j / U j| :=
      Finset.single_le_sum (f := fun j => |T j / U j|)
        (fun j _ => abs_nonneg _) (Finset.mem_range.mpr hn)
    _ ≤ C := by dsimp [C]; linarith

namespace Recurrence

variable {T f U g : ℕ → ℝ} {a : ℝ} {r : ℕ → ℕ}

/-- Strong-induction comparison, including a user-supplied common base range. -/
theorem comparison (R : Recurrence T f a r) (S : Recurrence U g a r)
    {N : ℕ} (hRN : R.cutoff ≤ N) (hSN : S.cutoff ≤ N)
    {C : ℝ} (hbase : ∀ n, n < N → T n ≤ C * U n)
    (htoll : ∀ n, N ≤ n → f n ≤ C * g n) : ∀ n, T n ≤ C * U n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < N
    · exact hbase n hn
    · have hn' := Nat.le_of_not_lt hn
      have hr := le_trans hRN hn'
      have hs := le_trans hSN hn'
      rw [R.eqn n hr, S.eqn n hs]
      calc
        a * T (r n) + f n ≤ a * (C * U (r n)) + C * g n :=
          add_le_add (mul_le_mul_of_nonneg_left (ih (r n) (R.decreases n hr)) R.a_pos.le)
            (htoll n hn')
        _ = C * (a * U (r n) + g n) := by ring

/-- An eventual big-O comparison between nonnegative tolls transfers to their
recurrences, even when the finite base cases and thresholds differ. -/
theorem isBigO_of_toll_isBigO (R : Recurrence T f a r) (S : Recurrence U g a r)
    (hfg : f =O[atTop] g) : T =O[atTop] U := by
  obtain ⟨C, hC, hfg⟩ := hfg.exists_pos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hfg.bound
  let M := max N (max R.cutoff S.cutoff)
  obtain ⟨D, hD, hbase⟩ := exists_pos_mul_bound T U S.pos M
  have hRN : R.cutoff ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hSN : S.cutoff ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hall : ∀ n, T n ≤ max C D * U n := R.comparison S hRN hSN
    (fun n hn => (hbase n hn).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (S.nonneg n))) (by
        intro n hn
        have h := hN n (le_trans (le_max_left _ _) hn)
        rw [Real.norm_of_nonneg (R.toll_nonneg n),
          Real.norm_of_nonneg (S.toll_nonneg n)] at h
        exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (S.toll_nonneg n)))
  apply Asymptotics.IsBigO.of_bound (max C D)
  exact Filter.Eventually.of_forall fun n => by
    simpa only [Real.norm_of_nonneg (R.nonneg n), Real.norm_of_nonneg (S.nonneg n)]
      using hall n

theorem isTheta_of_toll_isTheta (R : Recurrence T f a r) (S : Recurrence U g a r)
    (hfg : f =Θ[atTop] g) : T =Θ[atTop] U :=
  ⟨R.isBigO_of_toll_isBigO S hfg.1, S.isBigO_of_toll_isBigO R hfg.2⟩

end Recurrence









end Chapter4Master

end CLRS
end

section
namespace CLRS

/-! Rounded subproblem sizes and the bridge to Mathlib's recurrence theorem. -/
namespace Chapter4Master

open Filter Asymptotics Real
open scoped Topology













theorem akra_exponent {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : ℝ} {r : ℕ → ℕ}
    (R : AkraBazziRecurrence T g (fun _ : Unit => a) (fun _ : Unit => b⁻¹)
      (fun _ : Unit => r)) (hb : 1 < b) :
    AkraBazziRecurrence.p (fun _ : Unit => a) (fun _ : Unit => b⁻¹) =
      Real.logb b a := by
  apply R.injective_sumCoeffsExp
  dsimp only
  rw [R.sumCoeffsExp_p_eq_one]
  simp only [Fintype.sum_unique]
  rw [Real.inv_rpow (by linarith : 0 ≤ b),
    Real.rpow_logb (by linarith : 0 < b) (ne_of_gt hb) (R.a_pos ())]
  simp [ne_of_gt (R.a_pos ())]

end Chapter4Master

end CLRS
end

section
namespace CLRS

/-! # Master theorem: leaf-dominated costs

Polynomially smaller tolls have a summable normalized contribution. The
comparison principle in `Master.Basic` lets this estimate handle an arbitrary
nonnegative toll bounded by such a polynomial, rather than requiring that toll
itself to satisfy a smoothness condition.
-/

open Filter Asymptotics Finset
open scoped Topology

namespace Chapter4Master

/-- A summable normalized toll changes the leaf-count estimate only by a
constant factor. This also handles the zero-toll recurrence. -/
theorem summable_transform_theta (p : ℝ) (g : ℕ → ℝ)
    (hg : ∀ n, 0 ≤ g n)
    (hs : Summable fun n => g n / (n : ℝ) ^ (p + 1)) :
    (fun n : ℕ => (n : ℝ) ^ p *
      (1 + ∑ u ∈ range n, g u / (u : ℝ) ^ (p + 1)))
      =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ p) := by
  have hterm (n : ℕ) : 0 ≤ g n / (n : ℝ) ^ (p + 1) :=
    div_nonneg (hg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hsum (n : ℕ) : 0 ≤ ∑ u ∈ range n, g u / (u : ℝ) ^ (p + 1) :=
    sum_nonneg fun i _ => hterm i
  have hpow (n : ℕ) : 0 ≤ (n : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg n) _
  constructor
  · apply IsBigO.of_bound (1 + ∑' u : ℕ, g u / (u : ℝ) ^ (p + 1))
    apply Filter.Eventually.of_forall
    intro n
    rw [Real.norm_of_nonneg (mul_nonneg (hpow n) (by linarith [hsum n])),
      Real.norm_of_nonneg (hpow n)]
    have hle := hs.sum_le_tsum (range n) (fun i _ => hterm i)
    nlinarith [mul_nonneg (hpow n) (sub_nonneg.mpr hle)]
  · apply IsBigO.of_bound 1
    apply Filter.Eventually.of_forall
    intro n
    rw [Real.norm_of_nonneg (hpow n),
      Real.norm_of_nonneg (mul_nonneg (hpow n) (by linarith [hsum n]))]
    nlinarith [mul_nonneg (hpow n) (hsum n)]

/-- The normalized contribution of a polynomial with exponent below `p` is
summable, including the harmless value assigned at zero by real powers. -/
theorem summable_rpow_quotient {p q : ℝ} (hq : q < p) :
    Summable fun n : ℕ => (n : ℝ) ^ q / (n : ℝ) ^ (p + 1) := by
  have hs : Summable fun n : ℕ => (n : ℝ) ^ (q - (p + 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply hs.congr_cofinite
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℕ)] with n hn
  exact Real.rpow_sub (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) _ _

theorem rpow_transform_theta {p q : ℝ} (hq : q < p) :
    (fun n : ℕ => (n : ℝ) ^ p *
      (1 + ∑ u ∈ range n, (u : ℝ) ^ q / (u : ℝ) ^ (p + 1)))
      =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ p) :=
  summable_transform_theta p (fun n => (n : ℝ) ^ q)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) (summable_rpow_quotient hq)

/-- The analytic estimate applied to Mathlib's verified Akra--Bazzi theorem. -/
theorem akra_rpow_case_one {T : ℕ → ℝ} {a b : Unit → ℝ} {r : Unit → ℕ → ℕ}
    {p q : ℝ} (R : AkraBazziRecurrence T (fun x => x ^ q) a b r)
    (hp : AkraBazziRecurrence.p a b = p) (hq : q < p) :
    T =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ p) := by
  refine R.isTheta_asympBound.trans ?_
  have hbound : AkraBazziRecurrence.asympBound (fun x => x ^ q) a b =
      (fun n : ℕ => (n : ℝ) ^ p *
        (1 + ∑ u ∈ range n, (u : ℝ) ^ q / (u : ℝ) ^ (p + 1))) := by
    funext n
    rw [AkraBazziRecurrence.asympBound_def', hp]
  rw [hbound]
  exact rpow_transform_theta hq

theorem akra_zero_toll {T : ℕ → ℝ} {a b : Unit → ℝ} {r : Unit → ℕ → ℕ}
    {p : ℝ} (R : AkraBazziRecurrence T (fun _ => 0) a b r)
    (hp : AkraBazziRecurrence.p a b = p) :
    T =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ p) := by
  have hbound : AkraBazziRecurrence.asympBound (fun _ => 0) a b =
      (fun n : ℕ => (n : ℝ) ^ p) := by
    funext n
    simp only [AkraBazziRecurrence.asympBound_def', hp, zero_div, sum_const_zero,
      add_zero, mul_one]
  rw [← hbound]
  exact R.isTheta_asympBound

/-- The first master-theorem case for arbitrary rounded sizes: a nonnegative
toll polynomially smaller than the critical exponent leaves the total cost
in the same asymptotic class as the leaves. The original toll has no continuity,
monotonicity, or polynomial-growth hypothesis. -/
theorem case_one {T f : ℕ → ℝ} {a b : ℝ} {r : ℕ → ℕ}
    (R : Recurrence T f a r) (hr : RoundedDivision b r)
    {ε : ℝ} (hε : 0 < ε)
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ) ^ (Real.logb b a - ε))) :
    T =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ Real.logb b a) := by
  let p := Real.logb b a
  let U := solve a r R.cutoff R.decreases (fun n => (n : ℝ) ^ (p - ε))
  have RU : Recurrence U (fun n => (n : ℝ) ^ (p - ε)) a r :=
    solve_recurrence a r R.cutoff R.decreases _ R.cutoff_pos R.a_pos
      (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  let AU := RU.toAkra hr (fun x hx => Real.rpow_nonneg hx _)
    (AkraBazziRecurrence.growsPolynomially_rpow (p - ε))
  have hU : U =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ p) :=
    akra_rpow_case_one AU (akra_exponent AU hr.divisor_gt_one) (by dsimp [p]; linarith)
  let L := solve a r R.cutoff R.decreases (fun _ => 0)
  have RL : Recurrence L (fun _ => 0) a r :=
    solve_recurrence a r R.cutoff R.decreases _ R.cutoff_pos R.a_pos (fun _ => le_rfl)
  let AL := RL.toAkra hr (fun _ _ => le_rfl) AkraBazziRecurrence.growsPolynomially_const
  have hL : L =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ p) :=
    akra_zero_toll AL (akra_exponent AL hr.divisor_gt_one)
  exact ⟨(R.isBigO_of_toll_isBigO RU hf).trans hU.1,
    hL.2.trans (RL.isBigO_of_toll_isBigO R (isBigO_zero f atTop))⟩

end Chapter4Master

end CLRS
end

section
namespace CLRS

/-!
The regularity argument in CLRS, fourth edition, §4.5, case 3.

The recursive child may be any strictly smaller natural size.  A uniform
positive lower bound on the eventual toll absorbs the finitely many base
costs.  In the textbook master theorem this bound follows from the assumed
polynomial dominance.  Regularity alone would not suffice for arbitrary
children and tolls tending to zero.
-/

open Filter Asymptotics

namespace Chapter4Master

/-- Case 3's regularity condition bounds the complete recurrence by its toll.
The finite base costs are absorbed into a constant constructed by the proof;
no bound on the solution `T` is an assumption. -/
theorem regularity_upper {T f : ℕ → ℝ} {a : ℝ} {r : ℕ → ℕ}
    (R : Recurrence T f a r) {N : ℕ} {c δ : ℝ}
    (hc : c < 1) (hδ : 0 < δ)
    (hregular : ∀ n, N ≤ n → a * f (r n) ≤ c * f n)
    (htoll : ∀ n, N ≤ n → δ ≤ f n) :
    ∃ K : ℝ, 0 < K ∧ ∀ n, max R.cutoff N ≤ n → T n ≤ K * f n := by
  classical
  let cutoff := max R.cutoff N
  let M := ∑ i ∈ Finset.range cutoff, T i
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => R.nonneg i
  have hbase : ∀ i, i < cutoff → T i ≤ M := by
    intro i hi
    exact Finset.single_le_sum (fun j _ => R.nonneg j) (Finset.mem_range.mpr hi)
  let K := max (1 / (1 - c)) (a * M / δ + 1)
  have hgap : 0 < 1 - c := sub_pos.mpr hc
  have hKreg : 1 ≤ K * (1 - c) :=
    (div_le_iff₀ hgap).mp (le_max_left _ _)
  have hbaseK : a * M / δ + 1 ≤ K := le_max_right _ _
  have hquot : 0 ≤ a * M / δ := div_nonneg (mul_nonneg R.a_pos.le hM) hδ.le
  have hKone : 1 ≤ K := by linarith
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hKone
  have hKbase : a * M ≤ (K - 1) * δ := by
    apply (div_le_iff₀ hδ).mp
    linarith
  refine ⟨K, hKpos, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hnR : R.cutoff ≤ n := (le_max_left _ _).trans hn
    have hnN : N ≤ n := (le_max_right _ _).trans hn
    have hfn : 0 ≤ f n := R.toll_nonneg n
    rw [R.eqn n hnR]
    by_cases hr : cutoff ≤ r n
    · have hchild := ih (r n) (R.decreases n hnR) hr
      have hscaled := mul_le_mul_of_nonneg_left hchild R.a_pos.le
      have hregularK := mul_le_mul_of_nonneg_left (hregular n hnN) hKpos.le
      have hmargin := mul_le_mul_of_nonneg_right hKreg hfn
      nlinarith
    · have hchild : T (r n) ≤ M := hbase _ (Nat.lt_of_not_ge hr)
      have hscaled := mul_le_mul_of_nonneg_left hchild R.a_pos.le
      have hmargin := mul_le_mul_of_nonneg_left (htoll n hnN) (sub_nonneg.mpr hKone)
      nlinarith

/-- The full asymptotic conclusion of the case-3 regularity argument, with
arbitrary strictly decreasing natural recursive sizes. -/
theorem case_three {T f : ℕ → ℝ} {a : ℝ} {r : ℕ → ℕ}
    (R : Recurrence T f a r) {N : ℕ} {c δ : ℝ}
    (hc : c < 1) (hδ : 0 < δ)
    (hregular : ∀ n, N ≤ n → a * f (r n) ≤ c * f n)
    (htoll : ∀ n, N ≤ n → δ ≤ f n) :
    T =Θ[atTop] f := by
  obtain ⟨K, _, hupper⟩ := regularity_upper R hc hδ hregular htoll
  constructor
  · apply isBigO_iff.mpr
    refine ⟨K, eventually_atTop.2 ⟨max R.cutoff N, ?_⟩⟩
    intro n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg (R.nonneg n),
      abs_of_nonneg (R.toll_nonneg n)] using hupper n hn
  · apply isBigO_iff.mpr
    refine ⟨1, eventually_atTop.2 ⟨R.cutoff, ?_⟩⟩
    intro n hn
    have hchild : 0 ≤ a * T (r n) := mul_nonneg R.a_pos.le (R.nonneg _)
    have hlower : f n ≤ T n := by rw [R.eqn n hn]; linarith
    simpa only [Real.norm_eq_abs, abs_of_nonneg (R.nonneg n),
      abs_of_nonneg (R.toll_nonneg n), one_mul] using hlower

/-- A filter-based form makes the finitely many exceptional sizes implicit. -/
theorem case_three_eventually {T f : ℕ → ℝ} {a : ℝ} {r : ℕ → ℕ}
    (R : Recurrence T f a r) {c δ : ℝ}
    (hc : c < 1) (hδ : 0 < δ)
    (hregular : ∀ᶠ n in atTop, a * f (r n) ≤ c * f n)
    (htoll : ∀ᶠ n in atTop, δ ≤ f n) :
    T =Θ[atTop] f := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hregular.and htoll)
  exact case_three R hc hδ (fun n hn => (hN n hn).1) (fun n hn => (hN n hn).2)

/-- Any nonnegative power lower bound supplies the positive toll bound used
above. In CLRS case 3 the exponent is `log_b a + ε`, with `ε > 0`. -/
theorem case_three_of_polynomial_lower {T f : ℕ → ℝ} {a : ℝ} {r : ℕ → ℕ}
    (R : Recurrence T f a r) {c e : ℝ} (hc : c < 1) (he : 0 ≤ e)
    (hregular : ∀ᶠ n in atTop, a * f (r n) ≤ c * f n)
    (hpoly : (fun n : ℕ => (n : ℝ) ^ e) =O[atTop] f) :
    T =Θ[atTop] f := by
  obtain ⟨C, hC, hbound⟩ := hpoly.exists_pos
  apply case_three_eventually R hc (one_div_pos.mpr hC) hregular
  filter_upwards [hbound.bound, eventually_ge_atTop (1 : ℕ)] with n hbound hn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : 1 ≤ (n : ℝ) ^ e := Real.one_le_rpow hnreal he
  have hpow_nonneg : 0 ≤ (n : ℝ) ^ e := le_trans zero_le_one hpow
  rw [Real.norm_of_nonneg hpow_nonneg, Real.norm_of_nonneg (R.toll_nonneg n)] at hbound
  exact (div_le_iff₀ hC).mpr (by nlinarith)

end Chapter4Master

end CLRS
end

section
namespace CLRS

/-!
# The critical case of the master theorem

The logarithmic exponent is a real number. The summation estimate is proved by
comparing each summand with the increment of an antiderivative, then telescoping.
-/

open Filter Asymptotics Finset Real
open scoped Topology

namespace Chapter4Master

/-- A polynomially growing derivative has comparable values throughout a unit
interval sufficiently far from zero. The mean-value theorem turns this into
bounds on unit increments of its antiderivative. -/
private theorem derivative_increment_bounds {F g : ℝ → ℝ}
    (hg : AkraBazziRecurrence.GrowsPolynomially g)
    (hderiv : ∀ᶠ x in atTop, HasDerivAt F (g x) x) :
    ∃ L > 0, ∃ U > 0, ∀ᶠ n : ℕ in atTop,
      L * g n ≤ F (n + 1) - F n ∧ F (n + 1) - F n ≤ U * g n := by
  obtain ⟨c₁, hc₁, c₂, hc₂, hgp⟩ := hg (1 / 2) (by norm_num)
  refine ⟨c₁ / c₂, div_pos hc₁ hc₂, c₂ / c₁, div_pos hc₂ hc₁, ?_⟩
  have hgp' : ∀ᶠ n : ℕ in atTop, ∀ u ∈ Set.Icc ((1 / 2 : ℝ) * (2 * n)) (2 * n),
      g u ∈ Set.Icc (c₁ * g (2 * n)) (c₂ * g (2 * n)) :=
    ((tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).eventually hgp
  have hderiv' : ∀ᶠ n : ℕ in atTop, ∀ x ≥ (n : ℝ), HasDerivAt F (g x) x :=
    tendsto_natCast_atTop_atTop.eventually (eventually_forall_ge_atTop.mpr hderiv)
  filter_upwards [hgp', hderiv', eventually_ge_atTop 1] with n hn hd hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hcont : ContinuousOn F (Set.Icc (n : ℝ) (n + 1)) := by
    intro x hx
    exact (hd x hx.1).continuousAt.continuousWithinAt
  obtain ⟨x, hx, hval⟩ := exists_hasDerivAt_eq_slope F g (by linarith : (n : ℝ) < n + 1)
    hcont (fun x hx => hd x hx.1.le)
  have hgn := hn n (by constructor <;> linarith)
  have hgx := hn x (by constructor <;> linarith [hx.1, hx.2])
  simp only [add_sub_cancel_left, div_one] at hval
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ hc₂]
    nlinarith [mul_le_mul_of_nonneg_left hgn.2 hc₁.le,
      mul_le_mul_of_nonneg_left hgx.1 hc₂.le]
  · rw [div_mul_eq_mul_div, le_div_iff₀ hc₁]
    nlinarith [mul_le_mul_of_nonneg_left hgx.2 hc₁.le,
      mul_le_mul_of_nonneg_left hgn.1 hc₂.le]

/-- A useful sum-to-antiderivative comparison. The nonnegative summands may be
irregular on any finite initial segment. -/
theorem sum_isTheta_antiderivative {F g : ℝ → ℝ}
    (hg : AkraBazziRecurrence.GrowsPolynomially g)
    (hgn : ∀ n : ℕ, 0 ≤ g n)
    (hderiv : ∀ᶠ x in atTop, HasDerivAt F (g x) x)
    (hF : Tendsto F atTop atTop) :
    (fun n : ℕ => 1 + ∑ i ∈ range n, g i) =Θ[atTop] fun n : ℕ => F n := by
  obtain ⟨L, hL, U, hU, hinc⟩ := derivative_increment_bounds hg hderiv
  obtain ⟨N, hN⟩ := eventually_atTop.1 hinc
  let P := ∑ i ∈ range N, g i
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i _ => hgn i)
  have hsum : ∀ n, N ≤ n →
      L * ((∑ i ∈ range n, g i) - P) ≤ F n - F N ∧
      F n - F N ≤ U * ((∑ i ∈ range n, g i) - P) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp [P]
    | succ n hn ih =>
      have hi := hN n hn
      simp only [sum_range_succ, Nat.cast_add, Nat.cast_one]
      constructor <;> nlinarith [ih.1, ih.2, hi.1, hi.2]
  have hF' : ∀ᶠ n : ℕ in atTop, 1 ≤ F n :=
    (hF.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  constructor
  · rw [isBigO_iff]
    refine ⟨(L + L * P + |F N| + 1) / L, ?_⟩
    filter_upwards [hF', eventually_ge_atTop N] with n hn hnN
    have hs := (hsum n hnN).1
    have hsn : 0 ≤ ∑ i ∈ range n, g i := Finset.sum_nonneg (fun i _ => hgn i)
    rw [Real.norm_of_nonneg (show 0 ≤ 1 + ∑ i ∈ range n, g i by linarith),
      Real.norm_of_nonneg (show 0 ≤ F n by linarith), div_mul_eq_mul_div, le_div_iff₀ hL]
    have hK : 0 ≤ L + L * P + |F N| := by positivity
    have hbound := mul_le_mul_of_nonneg_left hn hK
    have habs := neg_le_abs (F N)
    nlinarith
  · rw [isBigO_iff]
    refine ⟨|F N| + U, ?_⟩
    filter_upwards [hF', eventually_ge_atTop N] with n hn hnN
    have hs := (hsum n hnN).2
    have hsn : 0 ≤ ∑ i ∈ range n, g i := Finset.sum_nonneg (fun i _ => hgn i)
    rw [Real.norm_of_nonneg (show 0 ≤ F n by linarith),
      Real.norm_of_nonneg (show 0 ≤ 1 + ∑ i ∈ range n, g i by linarith)]
    have hbound := mul_nonneg (abs_nonneg (F N)) hsn
    have habs := le_abs_self (F N)
    have hp := mul_nonneg hU.le hP
    nlinarith

/-- The harmonic sum with a real nonnegative logarithmic exponent gains exactly
one power of the logarithm. -/
theorem log_power_sum_isTheta (k : ℝ) (hk : 0 ≤ k) :
    (fun n : ℕ => 1 + ∑ i ∈ range n, (log i) ^ k / i) =Θ[atTop]
      fun n : ℕ => (log n) ^ (k + 1) := by
  have hg : AkraBazziRecurrence.GrowsPolynomially (fun x => (log x) ^ k / x) :=
    (AkraBazziRecurrence.growsPolynomially_log.rpow k
      (by filter_upwards [eventually_ge_atTop 1] with x hx; exact log_nonneg hx)).div
      AkraBazziRecurrence.growsPolynomially_id
  have hgn : ∀ n : ℕ, 0 ≤ (log n) ^ k / n := by
    intro n
    have hn : 0 ≤ log (n : ℝ) := by
      cases n with
      | zero => simp
      | succ n => exact log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    positivity
  have hderiv : ∀ᶠ x in atTop,
      HasDerivAt (fun x => (log x) ^ (k + 1) / (k + 1)) ((log x) ^ k / x) x := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hxpos : 0 < x := by linarith
    have hkpos : 0 < k + 1 := by linarith
    convert (((Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (log_pos hx)))).comp x
      (Real.hasDerivAt_log (ne_of_gt hxpos))).div_const (k + 1)) using 1 <;> try rfl
    simp only [add_sub_cancel_right]
    field_simp [ne_of_gt hkpos, ne_of_gt hxpos]
  have hF : Tendsto (fun x : ℝ => (log x) ^ (k + 1) / (k + 1)) atTop atTop :=
    ((tendsto_rpow_atTop (by linarith : 0 < k + 1)).comp tendsto_log_atTop).atTop_div_const
      (by linarith)
  have h := sum_isTheta_antiderivative hg hgn hderiv hF
  refine h.trans ?_
  simpa only [div_eq_mul_inv, mul_comm] using
    (isTheta_refl (fun n : ℕ => (log n) ^ (k + 1)) atTop).const_mul_left
      (inv_ne_zero (by linarith : k + 1 ≠ 0))



private theorem nat_log_nonneg (n : ℕ) : 0 ≤ log (n : ℝ) := by
  cases n with
  | zero => simp
  | succ n => exact log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

@[simp] theorem logarithmicToll_nat (p k : ℝ) (n : ℕ) :
    logarithmicToll p k n = (n : ℝ) ^ p * (log n) ^ k := by
  simp [logarithmicToll, max_eq_right (nat_log_nonneg n)]

theorem logarithmicToll_nonneg (p k x : ℝ) (hx : 0 ≤ x) :
    0 ≤ logarithmicToll p k x := by
  unfold logarithmicToll
  exact mul_nonneg (rpow_nonneg hx _) (rpow_nonneg (le_max_left _ _) _)

theorem logarithmicToll_growsPolynomially (p k : ℝ) :
    AkraBazziRecurrence.GrowsPolynomially (logarithmicToll p k) := by
  have hlog := AkraBazziRecurrence.growsPolynomially_log.rpow k
    (by filter_upwards [eventually_ge_atTop 1] with x hx; exact log_nonneg hx)
  apply AkraBazziRecurrence.GrowsPolynomially.congr_of_eventuallyEq _
    ((AkraBazziRecurrence.growsPolynomially_rpow p).mul hlog)
  filter_upwards [eventually_ge_atTop 1] with x hx
  simp [logarithmicToll, max_eq_right (log_nonneg hx)]

private theorem logarithmicToll_quotient (p k : ℝ) (hp : 0 ≤ p) (n : ℕ) :
    logarithmicToll p k n / (n : ℝ) ^ (p + 1) = (log n) ^ k / n := by
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (by linarith : p + 1 ≠ 0)]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [logarithmicToll_nat, Real.rpow_add_one (ne_of_gt hnpos)]
    have hpow : (n : ℝ) ^ p ≠ 0 := ne_of_gt (rpow_pos_of_pos hnpos p)
    field_simp [hpow, ne_of_gt hnpos]

/-- The canonical critical-case recurrence, for arbitrary natural input sizes
and any bounded-error rounding of division by `b`. -/
theorem case_two_canonical {T : ℕ → ℝ} {a b k : ℝ} {r : ℕ → ℕ}
    (R : Recurrence T (fun n => logarithmicToll (logb b a) k n) a r)
    (hr : RoundedDivision b r) (ha : 1 ≤ a) (hk : 0 ≤ k) :
    T =Θ[atTop] fun n : ℕ => (n : ℝ) ^ (logb b a) * (log n) ^ (k + 1) := by
  let A := R.toAkra hr (logarithmicToll_nonneg (logb b a) k)
    (logarithmicToll_growsPolynomially (logb b a) k)
  have hp : 0 ≤ logb b a := logb_nonneg hr.divisor_gt_one ha
  have heq : AkraBazziRecurrence.asympBound (logarithmicToll (logb b a) k)
      (fun _ : Unit => a) (fun _ : Unit => b⁻¹) =
      fun n : ℕ => (n : ℝ) ^ (logb b a) *
        (1 + ∑ i ∈ range n, (log i) ^ k / i) := by
    funext n
    rw [AkraBazziRecurrence.asympBound_def', akra_exponent A hr.divisor_gt_one]
    congr 2
    exact Finset.sum_congr rfl (fun i _ => logarithmicToll_quotient _ _ hp i)
  have h := A.isTheta_asympBound
  rw [heq] at h
  exact h.trans ((isTheta_refl (fun n : ℕ => (n : ℝ) ^ (logb b a)) atTop).mul
    (log_power_sum_isTheta k hk))

/-- **Master theorem, case 2 (CLRS fourth edition, §4.5).**
The real logarithmic exponent may be any `k ≥ 0`. No smoothness or monotonicity
is assumed of the original toll: its Θ comparison with the canonical toll
suffices. Floor and ceiling division are instances of `RoundedDivision`. -/
theorem case_two {T f : ℕ → ℝ} {a b k : ℝ} {r : ℕ → ℕ}
    (R : Recurrence T f a r) (hr : RoundedDivision b r) (ha : 1 ≤ a) (hk : 0 ≤ k)
    (hf : f =Θ[atTop] fun n : ℕ => (n : ℝ) ^ (logb b a) * (log n) ^ k) :
    T =Θ[atTop] fun n : ℕ => (n : ℝ) ^ (logb b a) * (log n) ^ (k + 1) := by
  let g : ℕ → ℝ := fun n => logarithmicToll (logb b a) k n
  let U := solve a r R.cutoff R.decreases g
  have S : Recurrence U g a r := solve_recurrence a r R.cutoff R.decreases g
    R.cutoff_pos R.a_pos (fun n => logarithmicToll_nonneg _ _ n (Nat.cast_nonneg n))
  have hfg : f =Θ[atTop] g := by simpa [g] using hf
  exact (R.isTheta_of_toll_isTheta S hfg).trans (case_two_canonical S hr ha hk)

end Chapter4Master

end CLRS
end

section
namespace CLRS

/-!
# CLRS fourth edition, §4.5: the master theorem

For natural sizes, positive finite base costs and a nonnegative toll, all three
cases hold for division rounded down, rounded up, or with any bounded error.
The case-3 regularity inequality is stated at the actual recursive child.
`Real.log` is natural logarithm; changing its base changes only constants.
-/
namespace Chapter4Master

open Filter Asymptotics Real

/-- The textbook case-3 hypotheses discharge the general regularity theorem's
positive toll lower bound. -/
theorem master_case_three {T f : ℕ → ℝ} {a b : ℝ} {r : ℕ → ℕ}
    (R : Recurrence T f a r) (hr : RoundedDivision b r) (ha : 1 ≤ a)
    {ε c : ℝ} (hε : 0 < ε) (hc : c < 1)
    (hf : (fun n : ℕ => (n : ℝ) ^ (logb b a + ε)) =O[atTop] f)
    (hregular : ∀ᶠ n in atTop, a * f (r n) ≤ c * f n) :
    T =Θ[atTop] f := by
  apply case_three_of_polynomial_lower R hc
    (add_nonneg (logb_nonneg hr.divisor_gt_one ha) hε.le) hregular hf



end Chapter4Master

end CLRS
end

namespace CLRS
end CLRS
open CLRS
namespace CLRS.Chapter4Master
end CLRS.Chapter4Master
open CLRS.Chapter4Master
open Filter Asymptotics Real

theorem solution {T f : ℕ → ℝ} {a b : ℝ} {r : ℕ → ℕ}
    (R : Recurrence T f a r) (hr : RoundedDivision b r) (ha : 1 ≤ a) :
    (∀ ε : ℝ, 0 < ε →
      f =O[atTop] (fun n : ℕ => (n : ℝ) ^ (logb b a - ε)) →
      T =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ logb b a)) ∧
    (∀ k : ℝ, 0 ≤ k →
      f =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ logb b a * (log n) ^ k) →
      T =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ logb b a * (log n) ^ (k + 1))) ∧
    (∀ ε c : ℝ, 0 < ε → c < 1 →
      (fun n : ℕ => (n : ℝ) ^ (logb b a + ε)) =O[atTop] f →
      (∀ᶠ n in atTop, a * f (r n) ≤ c * f n) → T =Θ[atTop] f) := by
  exact ⟨fun _ hε hf => case_one R hr hε hf,
    fun _ hk hf => case_two R hr ha hk hf,
    fun _ _ hε hc hf hregular => master_case_three R hr ha hε hc hf hregular⟩
