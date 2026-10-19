-- Prove2me | solution 1 for FlatlyFoliated.compact_poisson_potential_three
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T19:48:14.516506+00:00
-- url     : https://prove2.me/submissions/c78bddcb-cf3e-4ddf-885d-085cdd30779d

import Definitions.Def_FlatlyFoliatedRelativity_basic
import Theorems.Thm_HunterPDE_Newtonian_newtonianPotential_poisson
import Theorems.Thm_HunterPDE_Harmonic_harmonic_higher_derivative_estimate
import Theorems.Thm_HunterPDE_Harmonic_harmonic_derivative_estimate

open scoped ContDiff Topology
open FlatlyFoliated MeasureTheory Metric Set Filter
open HunterPDE.Newtonian
open Laplacian

namespace CompactPoisson

private noncomputable abbrev e (i : Fin 3) : R3 := EuclideanSpace.single i 1

private lemma pd2 {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (x : R3) (i j : Fin 3) :
    pd i (pd j u) x = fderiv ℝ (fderiv ℝ u) x (e i) (e j) := by
  unfold pd
  have hd := (hu.fderiv_right (m := ∞) le_rfl).differentiable (by simp) x
  rw [(hd.hasFDerivAt.clm_apply (hasFDerivAt_const (e j) x)).fderiv]
  simp [e]

private lemma commute {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (x : R3) (i j : Fin 3) :
    pd i (pd j u) x = pd j (pd i u) x := by
  rw [pd2 hu, pd2 hu]
  exact hu.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top) _ _

private lemma lap_eq {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) : Δ u = lap u := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  funext x
  apply Finset.sum_congr rfl
  intro i _
  rw [pd2 hu]
  simp [iteratedFDeriv_two_apply, e, EuclideanSpace.basisFun_apply]

private lemma clm_bound (T : R3 →L[ℝ] ℝ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ i, ‖T (e i)‖ ≤ B) : ‖T‖ ≤ 3 * B := by
  apply T.opNorm_le_bound (by positivity)
  intro v
  have hv : (∑ i : Fin 3, v i • e i) = v := by
    ext j
    simp [e, Pi.single_apply]
  calc
    ‖T v‖ = ‖∑ i : Fin 3, v i • T (e i)‖ := by
      apply congrArg (fun a : ℝ => ‖a‖)
      calc
        T v = T (∑ i : Fin 3, v i • e i) := congrArg T hv.symm
        _ = _ := by simp
    _ ≤ ∑ i : Fin 3, ‖v i • T (e i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖v‖ * B := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le v i) (h i) (norm_nonneg _) (norm_nonneg _)
    _ = (3 * B) * ‖v‖ := by simp; ring

private lemma clm2_bound (T : R3 →L[ℝ] R3 →L[ℝ] ℝ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ i j, ‖T (e i) (e j)‖ ≤ B) : ‖T‖ ≤ 9 * B := by
  apply T.opNorm_le_bound (by positivity)
  intro v
  apply (clm_bound (T v) (3 * B * ‖v‖) (by positivity) ?_).trans_eq
    (by ring)
  intro j
  have hh := clm_bound (T.flip (e j)) B hB (fun i => h i j)
  exact (T.flip (e j)).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right hh (norm_nonneg _))

private lemma harmonic_bounds {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u)
    {Ω : Set R3} (ho : IsOpen Ω) (hh : InnerProductSpace.HarmonicOnNhd u Ω)
    {x : R3} {r M : ℝ} (hr : 0 < r) (hM0 : 0 ≤ M)
    (hb : closedBall x r ⊆ Ω) (hm : ∀ y ∈ closedBall x r, |u y| ≤ M) :
    ‖fderiv ℝ u x‖ ≤ 9 / r * M ∧
    ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ (162 * Real.exp 1 / r ^ 2) * M := by
  have h1 (i : Fin 3) : |pd i u x| ≤ (3 / r) * M :=
    HunterPDE.Harmonic.harmonic_derivative_estimate ho hh hr hb i hm
  have h2 (i j : Fin 3) : |pd i (pd j u) x| ≤ (18 * Real.exp 1 / r ^ 2) * M := by
    let α : Fin 3 → ℕ := fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0)
    have ha : ∑ k, α k = 2 := by simp [α, Finset.sum_add_distrib]
    have h := HunterPDE.Harmonic.harmonic_higher_derivative_estimate ho hh hr hb α 2 ha (by norm_num) hm
    have hs : HunterPDE.Shared.multiDeriv u α x = pd i (pd j u) x := by
      have hp : ∀ (v : R3 → ℝ) i, HunterPDE.Shared.partialDeriv v i = pd i v := fun _ _ => rfl
      fin_cases i <;> fin_cases j <;>
        simp [α, HunterPDE.Shared.multiDeriv, HunterPDE.Shared.multiIndexList,
          List.finRange_succ, HunterPDE.Shared.iteratedPartial, hp, commute hu x]
    rw [hs] at h
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Nat.factorial] at h
    convert h using 1; ring
  constructor
  · convert clm_bound (fderiv ℝ u x) ((3 / r) * M) (by positivity) h1 using 1; ring
  · have h := clm2_bound (fderiv ℝ (fderiv ℝ u) x)
      ((18 * Real.exp 1 / r ^ 2) * M) (by positivity) (fun i j => by
        simpa only [Real.norm_eq_abs, ← pd2 hu] using h2 i j)
    convert h using 1; ring

private lemma potential_bound (q : R3 → ℝ) (hq : ContDiff ℝ ∞ q)
    (hc : HasCompactSupport q) :
    ∃ R D : ℝ, 1 ≤ R ∧ 0 ≤ D ∧
      (∀ y, R < ‖y‖ → q y = 0) ∧
      ∀ x, 2 * R < ‖x‖ → |newtonianPotential 3 q x| ≤ D / ‖x‖ := by
  obtain ⟨R, hR, hs⟩ := hc.isCompact.isBounded.subset_closedBall_lt 1 (0 : R3)
  have hint := (newtonianPotential_poisson 3 (by norm_num) q hq hc).1
  have hqint := hq.continuous.integrable_of_hasCompactSupport (μ := volume) hc
  let a : ℝ := 1 / (3 * unitBallVolume 3)
  let D : ℝ := 2 * |a| * ∫ y, |q y|
  have hD : 0 ≤ D := mul_nonneg (by positivity) (integral_nonneg fun _ => abs_nonneg _)
  refine ⟨R, D, hR.le, hD, ?_, ?_⟩
  · intro y hy
    by_contra hn
    have := hs (subset_tsupport q (by simpa [Function.mem_support] using hn))
    simp only [mem_closedBall, dist_zero_right] at this
    linarith
  · intro x hx
    have hn : 0 < ‖x‖ := by linarith
    have hbound (y : R3) :
        ‖fundamentalSolution 3 (x - y) * q y‖ ≤ (2 * |a| / ‖x‖) * |q y| := by
      by_cases hy : q y = 0
      · simp [hy]
      have hyR := hs (subset_tsupport q (by simpa [Function.mem_support] using hy))
      simp only [mem_closedBall, dist_zero_right] at hyR
      have hd : ‖x‖ / 2 ≤ ‖x - y‖ := by
        have := norm_sub_norm_le x y
        linarith
      have hd0 : 0 < ‖x - y‖ := lt_of_lt_of_le (by positivity) hd
      have hg : |fundamentalSolution 3 (x - y)| ≤ 2 * |a| / ‖x‖ := by
        simp only [fundamentalSolution, show ¬(3 : ℕ) = 2 by decide, ↓reduceIte]
        norm_num only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
        change |a * (1 / ‖x - y‖)| ≤ _
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / ‖x - y‖)]
        calc
          |a| * (1 / ‖x - y‖) = |a| / ‖x - y‖ := by ring
          _ ≤ |a| / (‖x‖ / 2) := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hd
          _ = _ := by ring
      simpa only [Real.norm_eq_abs, abs_mul] using mul_le_mul_of_nonneg_right hg (abs_nonneg (q y))
    calc
      |newtonianPotential 3 q x| ≤ ∫ y, (2 * |a| / ‖x‖) * |q y| := by
        exact (norm_integral_le_integral_norm _).trans
          (integral_mono (hint x).norm (hqint.norm.const_mul _) hbound)
      _ = D / ‖x‖ := by rw [integral_const_mul]; dsimp [D]; ring

private lemma global_decay (u : R3 → ℝ) (hu : ContDiff ℝ ∞ u)
    (R D : ℝ) (hR : 1 ≤ R) (hD : 0 ≤ D)
    (hh : InnerProductSpace.HarmonicOnNhd u {x | R < ‖x‖})
    (hb : ∀ x, 2 * R < ‖x‖ → |u x| ≤ D / ‖x‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : R3,
      |u x| ≤ C / (1 + ‖x‖) ∧
      ‖fderiv ℝ u x‖ ≤ C / (1 + ‖x‖) ^ 2 ∧
      ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C / (1 + ‖x‖) ^ 3 := by
  have he : 0 < Real.exp 1 := Real.exp_pos _
  let A : ℝ := D + 72 * D + 5184 * Real.exp 1 * D
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hfar (x : R3) (hx : 4 * R < ‖x‖) :
      |u x| * (1 + ‖x‖) ≤ 8 * A ∧
      ‖fderiv ℝ u x‖ * (1 + ‖x‖) ^ 2 ≤ 8 * A ∧
      ‖fderiv ℝ (fderiv ℝ u) x‖ * (1 + ‖x‖) ^ 3 ≤ 8 * A := by
    have hn : 0 < ‖x‖ := by linarith
    have hn1 : 1 ≤ ‖x‖ := by linarith
    have hy (y : R3) (hy : y ∈ closedBall x (‖x‖ / 4)) :
        2 * R < ‖y‖ ∧ ‖x‖ / 2 ≤ ‖y‖ := by
      rw [mem_closedBall, dist_eq_norm] at hy
      have hnxy := norm_sub_norm_le x y
      rw [norm_sub_rev] at hy
      constructor <;> linarith
    have hm (y : R3) (hym : y ∈ closedBall x (‖x‖ / 4)) : |u y| ≤ 2 * D / ‖x‖ := by
      obtain ⟨hyR, hyn⟩ := hy y hym
      calc
        |u y| ≤ D / ‖y‖ := hb y hyR
        _ ≤ D / (‖x‖ / 2) := div_le_div_of_nonneg_left hD (by positivity) hyn
        _ = _ := by ring
    have hd := harmonic_bounds hu (isOpen_lt continuous_const continuous_norm) hh
      (x := x) (r := ‖x‖ / 4) (M := 2 * D / ‖x‖) (by positivity) (by positivity)
      (fun y hym => by have := (hy y hym).1; change R < ‖y‖; linarith) hm
    have h0 : |u x| ≤ D / ‖x‖ := hb x (by linarith)
    have h1 : ‖fderiv ℝ u x‖ ≤ 72 * D / ‖x‖ ^ 2 := by
      convert hd.1 using 1
      field_simp
      ring
    have h2 : ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ 5184 * Real.exp 1 * D / ‖x‖ ^ 3 := by
      convert hd.2 using 1
      field_simp
      ring
    have hED : 0 ≤ 5184 * Real.exp 1 * D := by positivity
    have ha0 : D ≤ A := by dsimp [A]; linarith
    have ha1 : 72 * D ≤ A := by dsimp [A]; linarith
    have ha2 : 5184 * Real.exp 1 * D ≤ A := by dsimp [A]; linarith
    have hs : 1 + ‖x‖ ≤ 2 * ‖x‖ := by linarith
    have hpow (k : ℕ) : (1 + ‖x‖) ^ k ≤ (2 * ‖x‖) ^ k := pow_le_pow_left₀ (by positivity) hs k
    refine ⟨?_, ?_, ?_⟩
    · calc
        _ ≤ (D / ‖x‖) * (2 * ‖x‖) := mul_le_mul h0 hs (by positivity) (by positivity)
        _ = 2 * D := by field_simp
        _ ≤ 8 * A := by linarith
    · calc
        _ ≤ (72 * D / ‖x‖ ^ 2) * (2 * ‖x‖) ^ 2 := mul_le_mul h1 (hpow 2) (by positivity) (by positivity)
        _ = 4 * (72 * D) := by field_simp; ring
        _ ≤ 8 * A := by linarith
    · calc
        _ ≤ (5184 * Real.exp 1 * D / ‖x‖ ^ 3) * (2 * ‖x‖) ^ 3 :=
          mul_le_mul h2 (hpow 3) (by positivity) (by positivity)
        _ = 8 * (5184 * Real.exp 1 * D) := by field_simp; ring
        _ ≤ 8 * A := by linarith
  let w : R3 → ℝ := fun x => |u x| * (1 + ‖x‖) +
    ‖fderiv ℝ u x‖ * (1 + ‖x‖) ^ 2 +
    ‖fderiv ℝ (fderiv ℝ u) x‖ * (1 + ‖x‖) ^ 3
  have hw : Continuous w := by
    apply Continuous.add
    · exact (hu.continuous.abs.mul (continuous_const.add continuous_norm)).add
        ((hu.fderiv_right (m := ∞) le_rfl).continuous.norm.mul
          ((continuous_const.add continuous_norm).pow 2))
    · exact ((hu.fderiv_right (m := ∞) le_rfl).fderiv_right (m := ∞) le_rfl).continuous.norm.mul
        ((continuous_const.add continuous_norm).pow 3)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : R3) (4 * R)).exists_bound_of_continuousOn hw.continuousOn
  let C : ℝ := 1 + |B| + 8 * A
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun x => ?_⟩
  have hc0 : |u x| * (1 + ‖x‖) ≤ C ∧
      ‖fderiv ℝ u x‖ * (1 + ‖x‖) ^ 2 ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ u) x‖ * (1 + ‖x‖) ^ 3 ≤ C := by
    by_cases hx : 4 * R < ‖x‖
    · have h := hfar x hx
      have hhC : 8 * A ≤ C := by dsimp [C]; linarith [abs_nonneg B]
      exact ⟨h.1.trans hhC, h.2.1.trans hhC, h.2.2.trans hhC⟩
    · have h := hB x (by simpa using le_of_not_gt hx)
      have hwB : w x ≤ |B| := (le_abs_self _).trans (h.trans (le_abs_self B))
      have hhC : |B| ≤ C := by dsimp [C]; linarith
      dsimp [w] at hwB
      have hp0 : 0 ≤ |u x| * (1 + ‖x‖) := by positivity
      have hp1 : 0 ≤ ‖fderiv ℝ u x‖ * (1 + ‖x‖) ^ 2 := by positivity
      have hp2 : 0 ≤ ‖fderiv ℝ (fderiv ℝ u) x‖ * (1 + ‖x‖) ^ 3 := by positivity
      exact ⟨by linarith, by linarith, by linarith⟩
  exact ⟨(le_div_iff₀ (by positivity)).mpr hc0.1,
    (le_div_iff₀ (by positivity)).mpr hc0.2.1,
    (le_div_iff₀ (by positivity)).mpr hc0.2.2⟩

end CompactPoisson

theorem solution
    (q : R3 → ℝ) (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) :
    ∃ h : R3 → ℝ, ContDiff ℝ ∞ h ∧ (∀ x, lap h x = q x) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ x : R3,
        |h x| ≤ C / (1 + ‖x‖) ∧
        ‖fderiv ℝ h x‖ ≤ C / (1 + ‖x‖) ^ 2 ∧
        ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ C / (1 + ‖x‖) ^ 3 := by
  obtain ⟨hi, hu, hp⟩ := newtonianPotential_poisson 3 (by norm_num) q hq hc
  let u : R3 → ℝ := fun x => -newtonianPotential 3 q x
  have hs : ContDiff ℝ ∞ u := hu.neg
  have hl : ∀ x, lap u x = q x := by
    intro x
    rw [← CompactPoisson.lap_eq hs]
    simpa only [u, show (fun x => -newtonianPotential 3 q x) = -newtonianPotential 3 q from rfl,
      InnerProductSpace.laplacian_neg, Pi.neg_apply] using hp x
  obtain ⟨R, D, hR, hD, hq0, hb⟩ := CompactPoisson.potential_bound q hq hc
  have hh : InnerProductSpace.HarmonicOnNhd u {x | R < ‖x‖} := by
    intro x hx
    refine ⟨hs.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top), ?_⟩
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    rw [CompactPoisson.lap_eq hs, hl y, hq0 y hy]
    rfl
  exact ⟨u, hs, hl, CompactPoisson.global_decay u hs R D hR hD hh
    (fun x hx => by simpa only [u, abs_neg] using hb x hx)⟩
