-- Prove2me | solution 1 for ErschlerZheng.orbitKernel_muBeta_le_and_tail_le_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T12:44:17.199121+00:00
-- url     : https://prove2.me/submissions/c49a23fd-8e48-486f-96fe-1f526ccf3a1d

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels
import Definitions.Def_ErschlerZheng_Construction
import Theorems.Thm_ErschlerZheng_orbitKernel_muBeta_le_and_tail_le
import Theorems.Thm_ErschlerZheng_isProbability_and_hasFiniteEntropy_muBeta_and_mass_ball_compl_le

section
/-!
# Basic facts about sections, `a`, and the generators `b_ω, c_ω, d_ω`

Development helpers for the Grigorchuk part of the Erschler–Zheng mission (not published).
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace GrigBasic

/-! ### Sections -/

/-! ### The root swap -/

/-! ### `a` and the generators -/

/-! ### Words -/

end GrigBasic

end ErschlerZheng
end

section
/-!
# Kernel library for the Markov heat-kernel package

Substochastic kernels on a type `X` (no countability needed): non-negative entries, summable rows
with sums at most one. Their powers `stepProb`, Chapman–Kolmogorov, symmetry of powers, column
sums, and Poisson series facts used by the heat kernel.
-/

open DurrettProbability MarkovChain

namespace MarkovHK

variable {X : Type*}

variable [DecidableEq X]

/-! ## The heat kernel -/

end MarkovHK
end

section
/-!
# Near and far parts of a kernel; `uniformize` of a substochastic kernel (shared by H6 and H8)
-/

open DurrettProbability MarkovChain

namespace MarkovHK

variable {X : Type*}

variable [DecidableEq X]

end MarkovHK
end

section
/-!
# Orbit kernels of `μ_β` and `υ_n` as Markov kernels (helpers for Proposition 7.19, prover 6)

* `G_ω` and the orbit `1^∞·G_ω` are countable.
* For `ν ⩾ 0` summable on a subgroup `K`, the rows of `P_ν` sum to `Σ ν`; `P_ν` is a transition
  kernel when `ν` is a probability, and symmetric when `ν` is.
* `υ_n` restricted to `G_ω` is a sub-probability, so `P_{(υ_n + υ̌_n)/2}` is substochastic.
* `μ_β ⩾ C_β 2^{-nβ} (υ_n + υ̌_n)/2` pointwise, for `n ⩾ 1`, `D ∣ n`.
* `μ_β` is symmetric; `k_n = A⌊log₂ n⌋` is admissible and eventually `⩽ n` (copied from prover 5's
  `P5Goal`, which is still being edited).
-/

open scoped RightActions
open DurrettProbability MarkovChain

namespace ErschlerZheng

namespace P6Dev

open GrigBasic Garrido Filter

set_option linter.unusedSectionVars false

/-! ### Countability -/

lemma gens_finite (ω : ℕ → Fin 3) : (gens ω).Finite := by
  unfold gens
  exact (((Set.finite_singleton _).insert _).insert _).insert _

instance countable_grigorchuk (ω : ℕ → Fin 3) : Countable (grigorchuk ω) := by
  have hT : (gens ω ∪ (gens ω)⁻¹).Countable :=
    ((gens_finite ω).union (gens_finite ω).inv).countable
  have hc : ((grigorchuk ω : Subgroup BinaryTreeAut) : Set BinaryTreeAut).Countable := by
    have h1 : ((grigorchuk ω : Subgroup BinaryTreeAut) : Set BinaryTreeAut) =
        (Submonoid.closure (gens ω ∪ (gens ω)⁻¹) : Set BinaryTreeAut) := by
      unfold grigorchuk
      rw [← Subgroup.closure_toSubmonoid]
      rfl
    rw [h1, Submonoid.closure_eq_image_prod]
    have : Countable (gens ω ∪ (gens ω)⁻¹ : Set BinaryTreeAut) := hT.to_subtype
    have h2 : {l : List BinaryTreeAut | ∀ x ∈ l, x ∈ gens ω ∪ (gens ω)⁻¹} ⊆
        Set.range (fun l : List (gens ω ∪ (gens ω)⁻¹ : Set BinaryTreeAut) =>
          l.map Subtype.val) := by
      intro l hl
      refine ⟨l.attach.map fun x => ⟨x.1, hl x.1 x.2⟩, ?_⟩
      simp [List.map_attach_eq_pmap]
    exact ((Set.countable_range _).mono h2).image _
  exact hc.to_subtype

instance countable_orbitOne (ω : ℕ → Fin 3) : Countable (orbitOne ω) := by
  have : (orbitOne ω).Countable := by
    have h : orbitOne ω ⊆ Set.range (fun g : grigorchuk ω => oneRay <• (g : BinaryTreeAut)) := by
      rintro y ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    exact (Set.countable_range _).mono h
  exact this.to_subtype

/-! ### Orbit kernels -/

section Orbit

variable {H : Type*} [Group H] {X : Type*} [MulAction Hᵐᵒᵖ X] (K : Subgroup H)

lemma orbitKernel_nonneg' {ν : K → ℝ} (hν : ∀ g, 0 ≤ ν g) (o : X) (x y : rightOrbit K o) :
    0 ≤ orbitKernel K ν o x y := by
  classical
  unfold orbitKernel
  exact tsum_nonneg fun g => by split_ifs <;> simp [hν g]

/-- The rows of `P_ν` sum to `Σ ν`. -/
lemma hasSum_orbitKernel_row {ν : K → ℝ} (hν : ∀ g, 0 ≤ ν g) (hs : Summable ν) (o : X)
    (x : rightOrbit K o) : HasSum (fun y => orbitKernel K ν o x y) (∑' g, ν g) := by
  classical
  -- the point `x·g` of the orbit
  let act : K → rightOrbit K o := fun g => ⟨(x : X) <• (g : H), by
    obtain ⟨k, hk, hx⟩ := x.2
    refine ⟨k * g, K.mul_mem hk g.2, ?_⟩
    rw [hx, MulOpposite.op_mul, mul_smul]⟩
  let F : rightOrbit K o × K → ℝ := fun p => if (x : X) <• (p.2 : H) = p.1 then ν p.2 else 0
  have hinj : Function.Injective (fun g : K => (act g, g)) := fun a b h => (Prod.mk.inj h).2
  have hF : HasSum F (∑' g, ν g) := by
    have hcomp : F ∘ (fun g : K => (act g, g)) = ν := by
      funext g; simp [F, act]
    have hsupp : ∀ p ∉ Set.range (fun g : K => (act g, g)), F p = 0 := by
      rintro ⟨y, g⟩ hp
      simp only [F]
      split_ifs with h
      · exact absurd ⟨g, by
          simp only [Prod.mk.injEq, and_true]
          exact Subtype.ext h⟩ hp
      · rfl
    rw [← hinj.hasSum_iff hsupp, hcomp]
    exact hs.hasSum
  refine hF.prod_fiberwise fun y => ?_
  show HasSum (fun g : K => if (x : X) <• (g : H) = y then ν g else 0) (orbitKernel K ν o x y)
  unfold orbitKernel
  refine Summable.hasSum ?_
  refine Summable.of_nonneg_of_le (fun g => by split_ifs <;> simp [hν g]) (fun g => ?_) hs
  split_ifs
  · exact le_rfl
  · exact hν g

end Orbit

/-! ### The measures `υ_n` on `G_ω` -/

/-! ### `μ_β` dominates its `n`-th component -/

/-! ### Symmetry of `μ_β` and the parameters (after prover 5's `P5Goal`) -/

lemma sq_le_two_pow (j : ℕ) (hj : 4 ≤ j) : j ^ 2 ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have h1 : 2 * j + 1 ≤ j ^ 2 := by nlinarith
    calc (j + 1) ^ 2 = j ^ 2 + (2 * j + 1) := by ring
      _ ≤ j ^ 2 + j ^ 2 := by omega
      _ ≤ 2 ^ j + 2 ^ j := by omega
      _ = 2 ^ (j + 1) := by ring

lemma eventually_kLog_le (A : ℕ) : ∀ᶠ n : ℕ in atTop, kLog A n ≤ n := by
  refine (eventually_ge_atTop (2 ^ (2 * A + 4))).mono fun n hn => ?_
  set j := Nat.log 2 n with hj
  have hj4 : 2 * A + 4 ≤ j := by
    have := Nat.log_mono_right (b := 2) hn
    rwa [Nat.log_pow (by norm_num)] at this
  have h1 : 2 ^ j ≤ n := Nat.pow_log_le_self 2 (by
    have : 0 < 2 ^ (2 * A + 4) := by positivity
    omega)
  have h2 := sq_le_two_pow j (by omega)
  unfold kLog
  rw [← hj]
  nlinarith

lemma isAdmissibleSeq_kLog (D A : ℕ) (hD : 3 ≤ D) (hDA : D ∣ A) (hA : 0 < A) :
    IsAdmissibleSeq D (kLog A) := by
  refine ⟨fun m n hmn => Nat.mul_le_mul_left A (Nat.log_mono_right hmn), fun n hn hDn => ?_⟩
  have hnD : D ≤ n := Nat.le_of_dvd hn hDn
  have hlog : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) (by omega)
  exact ⟨Nat.mul_pos hA hlog, Dvd.dvd.mul_right hDA _⟩

lemma three_le_of_satisfiesFr {D : ℕ} {ω : ℕ → Fin 3} (h : SatisfiesFr D ω) : 3 ≤ D := by
  obtain ⟨m, hm, -⟩ := h 0
  omega

end P6Dev

end ErschlerZheng
end

section
/-!
# Printed versions and boundary cases (group `printed`)

1. Theorem 8.3 as printed (p. 58), with the bounds `C n^{-1+ε}` and `exp(c n^{1-ε})`, from the
   mission's version with `2^n` in place of `n`, applied with the same `ε` if `ε ⩽ 1` and with
   `ε = 1/2` if `ε > 1`.
2. Lemma 7.17 (ii) without `n ⩾ 1` fails: `D = 3`, `ω = (201)^∞`, `k_0 = 0`, `n = ℓ = 0`.
3. The odd case of (2.3) as printed, `(wa, aw)ε`, fails: `ω = (012)^∞`, `n = 0`, `w = ad`.
4. Proposition 7.18 at distance `⩾ 3` and for `r ⩾ 3`, from the stated version at `⩾ 4`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace NewPrinted

open GrigBasic

/-! ### 1. Theorem 8.3 as printed -/

/-! ### 2. Lemma 7.17 (ii) at `n = 0` -/

/-! ### 3. The odd case of (2.3) at `ω = (012)^∞`, `w = ad` -/

/-! ### 4. Proposition 7.18 at distance `3` and for `3 ⩽ r < 4` -/

/-- `x^a ⩾ min(p^a, q^a)` for `0 < p ⩽ x ⩽ q`. -/
lemma min_rpow_le_rpow {p q x a : ℝ} (hp : 0 < p) (hpx : p ≤ x) (hxq : x ≤ q) :
    min (p ^ a) (q ^ a) ≤ x ^ a := by
  rcases le_or_gt 0 a with ha | ha
  · exact (min_le_left _ _).trans (Real.rpow_le_rpow hp.le hpx ha)
  · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (hp.trans_le hpx) hxq ha.le)

/-- On `[3, 4]`, `r^a (log₂ r)^e (log₂ log₂ r)^f` (`f ⩾ 0`) is bounded below by a positive
constant. -/
lemma exists_pos_le_on_three_four (a e f : ℝ) (hf : 0 ≤ f) :
    ∃ m > (0 : ℝ), ∀ r : ℝ, 3 ≤ r → r ≤ 4 →
      m ≤ r ^ a * Real.logb 2 r ^ e * Real.logb 2 (Real.logb 2 r) ^ f := by
  have hl3 : 1 < Real.logb 2 3 := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]; norm_num
  have hl4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
  have hll3 : 0 < Real.logb 2 (Real.logb 2 3) := Real.logb_pos (by norm_num) hl3
  refine ⟨min ((3 : ℝ) ^ a) ((4 : ℝ) ^ a) * min (Real.logb 2 3 ^ e) ((2 : ℝ) ^ e) *
    Real.logb 2 (Real.logb 2 3) ^ f, by positivity, fun r h3 h4 => ?_⟩
  have hlr3 : Real.logb 2 3 ≤ Real.logb 2 r :=
    Real.logb_le_logb_of_le (by norm_num) (by norm_num) h3
  have hlr4 : Real.logb 2 r ≤ 2 := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith) h4
    rwa [hl4] at this
  have hllr : Real.logb 2 (Real.logb 2 3) ≤ Real.logb 2 (Real.logb 2 r) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) hlr3
  have e1 := min_rpow_le_rpow (a := a) (by norm_num : (0 : ℝ) < 3) h3 h4
  have e2 := min_rpow_le_rpow (a := e) (by linarith) hlr3 hlr4
  have e3 := Real.rpow_le_rpow hll3.le hllr hf
  have p1 : 0 ≤ min ((3 : ℝ) ^ a) ((4 : ℝ) ^ a) := by positivity
  have p2 : 0 ≤ min (Real.logb 2 3 ^ e) ((2 : ℝ) ^ e) := by positivity
  have p3 : 0 ≤ Real.logb 2 (Real.logb 2 3) ^ f := by positivity
  have q1 : 0 ≤ r ^ a := Real.rpow_nonneg (by linarith) a
  have q2 : 0 ≤ Real.logb 2 r ^ e := Real.rpow_nonneg (by linarith) e
  exact mul_le_mul (mul_le_mul e1 e2 p2 q1) e3 p3 (mul_nonneg q1 q2)

/-- `r^a (log₂ r)^e (log₂ log₂ r)^f ⩾ 0` for `r ⩾ 2`. -/
lemma factor_nonneg (a e f : ℝ) {r : ℝ} (hr : 2 ≤ r) :
    0 ≤ r ^ a * Real.logb 2 r ^ e * Real.logb 2 (Real.logb 2 r) ^ f := by
  have h1 : 1 ≤ Real.logb 2 r := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hr
  have h2 : 0 ≤ Real.logb 2 (Real.logb 2 r) := Real.logb_nonneg (by norm_num) h1
  have q1 : 0 ≤ r ^ a := Real.rpow_nonneg (by linarith) a
  have q2 : 0 ≤ Real.logb 2 r ^ e := Real.rpow_nonneg (by linarith) e
  have q3 : 0 ≤ Real.logb 2 (Real.logb 2 r) ^ f := Real.rpow_nonneg h2 f
  positivity

/-- Enlarging the constant: `C F ⩽ C' F` for `F ⩾ 0` and `C ⩽ C'`, in the shape of the bounds. -/
lemma mul_factor_le {C C' u v w : ℝ} (hC : C ≤ C') (h : 0 ≤ u * v * w) :
    C * u * v * w ≤ C' * u * v * w := by
  have := mul_le_mul_of_nonneg_right hC h
  linarith [show C * u * v * w = C * (u * v * w) by ring,
    show C' * u * v * w = C' * (u * v * w) by ring]

/-- Covering a left side `⩽ 16` by a constant `C' ⩾ 16/m` where the factor is `⩾ m > 0`. -/
lemma le_mul_factor {L C' m u v w : ℝ} (hL : L ≤ 16) (hm : 0 < m) (hC' : 16 / m ≤ C')
    (h : m ≤ u * v * w) : L ≤ C' * u * v * w := by
  have h16 : 16 = 16 / m * m := by field_simp
  have hC0 : 0 ≤ 16 / m := by positivity
  calc L ≤ 16 := hL
    _ = 16 / m * m := h16
    _ ≤ C' * (u * v * w) := mul_le_mul hC' h hm.le (hC0.trans hC')
    _ = C' * u * v * w := by ring

end NewPrinted

open NewPrinted GrigBasic

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
open NewPrinted GrigBasic
theorem solution (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (β : ℝ) (hβ1 : 1 - 1 / (D : ℝ) < β) (hβ2 : β < 1) (A : ℕ) (hA : 0 < A)
    (hDA : D ∣ A) :
    ∃ C : ℝ,
      (∀ x y : orbitOne ω, 3 ≤ orbitDist ω x y →
        orbitKernel (grigorchuk ω) (muBeta D ω (kLog A) β) oneRay x y ≤
          C * orbitDist ω x y ^ (-1 - β) *
            Real.logb 2 (orbitDist ω x y) ^ (2 * (A : ℝ) * (1 - 1 / (D : ℝ) + β)) *
            Real.logb 2 (Real.logb 2 (orbitDist ω x y)) ^ (1 + 1 / (D : ℝ))) ∧
      (∀ x : orbitOne ω, ∀ r : ℝ, 3 ≤ r →
        ∑' y : orbitOne ω,
            (if r ≤ orbitDist ω x y then
              orbitKernel (grigorchuk ω) (muBeta D ω (kLog A) β) oneRay x y else 0) ≤
          C * r ^ (-β) * Real.logb 2 r ^ (2 * (A : ℝ) * (β - 1 / (D : ℝ))) *
            Real.logb 2 (Real.logb 2 r) ^ (1 + 1 / (D : ℝ))) ∧
      ∀ x : orbitOne ω, ∀ r : ℝ, 3 ≤ r →
        ∑' y : orbitOne ω,
            (if orbitDist ω x y ≤ r then
              orbitDist ω x y ^ 2 * orbitKernel (grigorchuk ω) (muBeta D ω (kLog A) β) oneRay x y
            else 0) ≤
          C * r ^ (2 - β) * Real.logb 2 r ^ (2 * (A : ℝ) * (β - 1 / (D : ℝ))) *
            Real.logb 2 (Real.logb 2 r) ^ (1 + 1 / (D : ℝ)) := by
  classical
  obtain ⟨C, h1, h2, h3⟩ := orbitKernel_muBeta_le_and_tail_le D ω hω β hβ1 hβ2 A hA hDA
  -- `μ_β` is a probability (Corollary 8.2), so each row of `P` sums to `1`
  have hD3 := P6Dev.three_le_of_satisfiesFr hω
  have hDr : (3 : ℝ) ≤ D := by exact_mod_cast hD3
  have hβ0 : 0 < β := by
    have : 1 / (D : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hDr
    linarith
  have hk := P6Dev.isAdmissibleSeq_kLog D A hD3 hDA hA
  obtain ⟨_, _, hJ⟩ := isProbability_and_hasFiniteEntropy_muBeta_and_mass_ball_compl_le D β hβ0
  have hμ : IsProbability (muBeta D ω (kLog A) β) :=
    (hJ ω hω (kLog A) hk (P6Dev.eventually_kLog_le A)).1
  set P := orbitKernel (grigorchuk ω) (muBeta D ω (kLog A) β) oneRay with hP
  have hrow : ∀ x, HasSum (fun y => P x y) 1 := fun x => by
    have := P6Dev.hasSum_orbitKernel_row (grigorchuk ω) hμ.1 hμ.2.summable oneRay x
    rwa [hμ.2.tsum_eq] at this
  have hPnn : ∀ x y, 0 ≤ P x y := fun x y => P6Dev.orbitKernel_nonneg' _ hμ.1 _ x y
  have hPle : ∀ x y, P x y ≤ 1 := fun x y => le_hasSum (hrow x) y (fun j _ => hPnn x j)
  have hd0 : ∀ x y, 0 ≤ orbitDist ω x y := fun x y => Nat.cast_nonneg _
  -- lower bounds of the three factors on `[3, 4]`
  have hf : (0 : ℝ) ≤ 1 + 1 / (D : ℝ) := by positivity
  obtain ⟨m1, hm1, hb1⟩ :=
    exists_pos_le_on_three_four (-1 - β) (2 * (A : ℝ) * (1 - 1 / (D : ℝ) + β)) _ hf
  obtain ⟨m2, hm2, hb2⟩ :=
    exists_pos_le_on_three_four (-β) (2 * (A : ℝ) * (β - 1 / (D : ℝ))) _ hf
  obtain ⟨m3, hm3, hb3⟩ :=
    exists_pos_le_on_three_four (2 - β) (2 * (A : ℝ) * (β - 1 / (D : ℝ))) _ hf
  have p1 : 0 ≤ 16 / m1 := by positivity
  have p2 : 0 ≤ 16 / m2 := by positivity
  have p3 : 0 ≤ 16 / m3 := by positivity
  refine ⟨max C 0 + 16 / m1 + 16 / m2 + 16 / m3, ?_, ?_, ?_⟩
  · intro x y hxy
    by_cases h4 : 4 ≤ orbitDist ω x y
    · exact (h1 x y h4).trans (mul_factor_le (by linarith [le_max_left C 0])
        (factor_nonneg _ _ _ (by linarith)))
    · exact le_mul_factor ((hPle x y).trans (by norm_num)) hm1 (by linarith [le_max_right C 0])
        (hb1 _ hxy (by linarith))
  · intro x r hr
    by_cases h4 : 4 ≤ r
    · exact (h2 x r h4).trans (mul_factor_le (by linarith [le_max_left C 0])
        (factor_nonneg _ _ _ (by linarith)))
    · have hs : ∑' y, (if r ≤ orbitDist ω x y then P x y else 0) ≤ 1 := by
        rw [← (hrow x).tsum_eq]
        refine Summable.tsum_le_tsum (fun y => ?_) ?_ (hrow x).summable
        · split_ifs
          · exact le_rfl
          · exact hPnn x y
        · refine Summable.of_nonneg_of_le (fun y => ?_) (fun y => ?_) (hrow x).summable
          · split_ifs
            · exact hPnn x y
            · exact le_rfl
          · split_ifs
            · exact le_rfl
            · exact hPnn x y
      exact le_mul_factor (hs.trans (by norm_num)) hm2 (by linarith [le_max_right C 0])
        (hb2 _ hr (by linarith))
  · intro x r hr
    by_cases h4 : 4 ≤ r
    · exact (h3 x r h4).trans (mul_factor_le (by linarith [le_max_left C 0])
        (factor_nonneg _ _ _ (by linarith)))
    · have hterm : ∀ y, (if orbitDist ω x y ≤ r then orbitDist ω x y ^ 2 * P x y else 0) ≤
          16 * P x y := by
        intro y
        split_ifs with hy
        · have hsq : orbitDist ω x y ^ 2 ≤ 16 := by nlinarith [hd0 x y]
          exact mul_le_mul_of_nonneg_right hsq (hPnn x y)
        · nlinarith [hPnn x y]
      have hnn : ∀ y, 0 ≤ (if orbitDist ω x y ≤ r then orbitDist ω x y ^ 2 * P x y else 0) := by
        intro y
        split_ifs
        · exact mul_nonneg (sq_nonneg _) (hPnn x y)
        · exact le_rfl
      have hs : ∑' y, (if orbitDist ω x y ≤ r then orbitDist ω x y ^ 2 * P x y else 0) ≤ 16 := by
        have h16 : HasSum (fun y => 16 * P x y) 16 := by simpa using (hrow x).mul_left 16
        rw [← h16.tsum_eq]
        exact Summable.tsum_le_tsum hterm
          (Summable.of_nonneg_of_le hnn hterm h16.summable) h16.summable
      exact le_mul_factor hs hm3 (by linarith [le_max_right C 0]) (hb3 _ hr (by linarith))
end
