-- Prove2me | solution 1 for BroughanRH.bagchiHardyInterval
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T02:27:22.322333+00:00
-- url     : https://prove2.me/submissions/01e159e8-44ee-4b40-876a-69d4c0459900
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_HardyHalfPlane_paleyWiener_mellin_leftHardy_two
import Theorems.Thm_NymanBeurling_damped_spectral_vanishing_of_ratio_bound
import Theorems.Thm_NymanBeurling_damped_mellin_completion_of_polynomial_bound
import Mathlib.Analysis.Real.Pi.Bounds
import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_NymanAux_moebiusPolynomialBoundaryBound_of_riemannHypothesis
import Theorems.Thm_NymanAux_shiftedZetaRatioBound_of_riemannHypothesis

open MeasureTheory
open scoped BigOperators

theorem bagchiConst_of_bounds (hA : NymanBeurling.MoebiusPolynomialBoundaryBound)
    (hB : NymanBeurling.ShiftedZetaRatioBound) :
    let err (f : ℕ → ℂ) (N : ℕ) (a : Fin N → ℂ) (n : ℕ) :=
      ‖f n - ∑ j, a j * ((Int.fract ((n : ℝ)/(j.val+1 : ℕ)) : ℝ) : ℂ)‖^2 /
        ((n : ℝ)*(n+1))
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℂ,
      Summable (fun m : ℕ => err (fun _ => 1) N a (m+1)) ∧
      (∑' m : ℕ, err (fun _ => 1) N a (m+1)) < ε := by
  intro err ε hε
  obtain ⟨e₀, he₀, he₀h, hvan⟩ :=
    NymanBeurling.damped_spectral_vanishing_of_ratio_bound hB (ε / 8) (by linarith)
  set e : ℝ := e₀ / 2 with he
  have he0 : 0 < e := by positivity
  have hee : e < e₀ := by linarith
  have heh : e < 1/2 := by linarith
  obtain ⟨hint, hsmall⟩ := hvan e he0 hee
  obtain ⟨hcompl, hprof⟩ := NymanBeurling.damped_mellin_completion_of_polynomial_bound hA
  obtain ⟨N₀, hN₀⟩ := hcompl e he0 heh (ε / 8) (by linarith)
  obtain ⟨hsum, -, hpl⟩ := hprof e he0 heh
  set P := fun n : ℕ => (NymanBeurling.dampedResidualProfile e (n+1))^2 /
        ((n+1 : ℝ)*(n+2 : ℝ)) with hP
  have hPt : (∑' n, P n) < ε / 8 := by
    have h2 : (2 * Real.pi) * (∑' n, P n) < ε / 8 := by rw [← hpl]; exact hsmall
    have hpi : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hP0 : 0 ≤ ∑' n, P n := tsum_nonneg (fun n => by positivity)
    nlinarith
  refine ⟨N₀ + 1, fun j => if j.val = 0 then 0 else
      -(((ArithmeticFunction.moebius (j.val+1) : ℝ) / ((j.val+1 : ℕ) : ℝ)^e : ℝ) : ℂ), ?_⟩
  -- identify the error terms
  have key : ∀ m : ℕ, err (fun _ => 1) (N₀+1) (fun j => if j.val = 0 then 0 else
      -(((ArithmeticFunction.moebius (j.val+1) : ℝ) / ((j.val+1 : ℕ) : ℝ)^e : ℝ) : ℂ)) (m+1) =
      (NymanBeurling.dampedResidualFinite N₀ e (m+1))^2 / ((m+1 : ℝ)*(m+2 : ℝ)) := by
    intro m
    simp only [err]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, if_pos, zero_mul, zero_add, Fin.val_succ]
    have : ∀ i : Fin N₀, (if (i.val + 1 = 0) then (0:ℂ) else
        -(((ArithmeticFunction.moebius (i.val+1+1) : ℝ) / ((i.val+1+1 : ℕ) : ℝ)^e : ℝ) : ℂ)) *
        ((Int.fract (((m+1 : ℕ) : ℝ)/(i.val+1+1 : ℕ)) : ℝ) : ℂ) =
        -((((ArithmeticFunction.moebius (i.val+2) : ℝ) / (i.val+2 : ℝ)^e) *
          (((m+1) % (i.val+2) : ℕ) : ℝ) / (i.val+2 : ℝ) : ℝ) : ℂ) := by
      intro i
      rw [if_neg (by omega)]
      have h1 : (Int.fract (((m+1 : ℕ) : ℝ)/((i.val+1+1 : ℕ) : ℝ))) =
          (((m+1) % (i.val+2) : ℕ) : ℝ) / (i.val+2 : ℝ) := by
        rw [Int.fract_div_natCast_eq_div_natCast_mod]; push_cast; ring_nf
      rw [h1]; push_cast; ring_nf
    have hc : ((m+1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [show ((↑(m+1) : ℝ)) = ((m+1 : ℕ) : ℝ) from rfl] at *
    simp_rw [this]
    rw [Finset.sum_neg_distrib, sub_neg_eq_add]
    unfold NymanBeurling.dampedResidualFinite
    rw [show ((m+1 : ℕ) : ℝ) * (((m+1 : ℕ) : ℝ) + 1) = ((m+1 : ℝ)*(m+2 : ℝ)) by push_cast; ring]
    congr 1
    rw [← Complex.ofReal_sum, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hle : ∀ H : ℕ, ∑ m ∈ Finset.range H,
      (NymanBeurling.dampedResidualFinite N₀ e (m+1))^2 / ((m+1 : ℝ)*(m+2 : ℝ)) ≤ ε / 2 := by
    intro H
    have hw : ∀ m : ℕ, 0 < ((m+1 : ℝ)*(m+2 : ℝ)) := fun m => by positivity
    have h1 := hN₀ N₀ le_rfl H
    have h2 : ∑ m ∈ Finset.range H, P m ≤ ∑' n, P n :=
      hsum.sum_le_tsum _ (fun n _ => by positivity)
    calc ∑ m ∈ Finset.range H,
          (NymanBeurling.dampedResidualFinite N₀ e (m+1))^2 / ((m+1 : ℝ)*(m+2 : ℝ))
        ≤ ∑ m ∈ Finset.range H, (2 * ((NymanBeurling.dampedResidualFinite N₀ e (m+1) -
            NymanBeurling.dampedResidualProfile e (m+1))^2 / ((m+1 : ℝ)*(m+2 : ℝ))) + 2 * P m) := by
          apply Finset.sum_le_sum; intro m _
          rw [hP]; dsimp only
          rw [mul_div_assoc', mul_div_assoc', ← add_div]
          apply div_le_div_of_nonneg_right _ (hw m).le
          nlinarith [sq_nonneg (NymanBeurling.dampedResidualFinite N₀ e (m+1) -
            2 * NymanBeurling.dampedResidualProfile e (m+1))]
      _ = 2 * ∑ m ∈ Finset.range H, ((NymanBeurling.dampedResidualFinite N₀ e (m+1) -
            NymanBeurling.dampedResidualProfile e (m+1))^2 / ((m+1 : ℝ)*(m+2 : ℝ))) +
            2 * ∑ m ∈ Finset.range H, P m := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ ε / 2 := by linarith
  have hnn : ∀ m : ℕ, 0 ≤ (NymanBeurling.dampedResidualFinite N₀ e (m+1))^2 /
      ((m+1 : ℝ)*(m+2 : ℝ)) := fun m => by positivity
  simp_rw [key]
  refine ⟨summable_of_sum_range_le hnn hle, ?_⟩
  have := Real.tsum_le_of_sum_range_le hnn hle
  linarith


open MeasureTheory Set
open scoped BigOperators ENNReal

namespace NymanRecip

lemma fract_shift (m k : ℕ) (hk : 0 < k) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1) :
    Int.fract (((m : ℝ) + θ) / k) = Int.fract ((m : ℝ) / k) + θ / k := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  rw [Int.fract_div_natCast_eq_div_natCast_mod, Int.fract_eq_iff]
  have hmod : ((m % k : ℕ) : ℝ) + 1 ≤ k := by
    have := Nat.mod_lt m hk
    exact_mod_cast this
  refine ⟨by positivity, ?_, ?_⟩
  · rw [← add_div, div_lt_one hk']; linarith
  · refine ⟨((m / k : ℕ) : ℤ), ?_⟩
    have hdm : ((m : ℕ) : ℝ) = (k : ℝ) * ((m / k : ℕ) : ℝ) + ((m % k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod m k).symm
    rw [Int.cast_natCast, hdm]; field_simp; ring

/-- membership in the `n`-th piece. -/
lemma mem_piece_iff (x : ℝ) (hx : 0 < x) (n : ℕ) :
    x ∈ Ioc (1 / ((n:ℝ) + 2)) (1 / ((n:ℝ) + 1)) ↔ ⌊1 / x⌋₊ = n + 1 := by
  rw [Nat.floor_eq_iff (by positivity), mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · push_cast
      rw [le_div_iff₀ hx]; rw [le_div_iff₀ (by positivity)] at h2; linarith
    · push_cast
      rw [div_lt_iff₀ hx]; rw [div_lt_iff₀ (by positivity)] at h1; linarith
  · rintro ⟨h1, h2⟩
    push_cast at h1 h2
    constructor
    · rw [div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ hx] at h2; linarith
    · rw [le_div_iff₀ (by positivity)]; rw [le_div_iff₀ hx] at h1; linarith

theorem recip_of_bagchi
    (hb : let err (f : ℕ → ℂ) (N : ℕ) (a : Fin N → ℂ) (n : ℕ) :=
                ‖f n - ∑ j, a j * ((Int.fract ((n : ℝ)/(j.val+1 : ℕ)) : ℝ) : ℂ)‖^2 /
                  ((n : ℝ)*(n+1))
              ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℂ,
                Summable (fun m : ℕ => err (fun _ => 1) N a (m+1)) ∧
                (∑' m : ℕ, err (fun _ => 1) N a (m+1)) < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℝ,
      (∑ j, a j / ((j.val + 1 : ℕ) : ℝ)) = 0 ∧
      MeasureTheory.eLpNorm (fun x : ℝ =>
        (if x ∈ Set.Ioc 0 1 then (1 : ℝ) else 0) -
        ∑ j, a j * Int.fract (1 / (((j.val+1 : ℕ):ℝ)*x)))
        2 (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N, a, hsum, hlt⟩ := hb (ε ^ 2 / 2) (by positivity)
  -- real coefficients with the constraint
  set S : ℝ := ∑ i : Fin N, (if i.val = 0 then 0 else (a i).re / ((i.val + 1 : ℕ) : ℝ)) with hS
  set b : Fin N → ℝ := fun j => if j.val = 0 then -S else (a j).re with hbdef
  have hcon : ∑ j, b j / ((j.val + 1 : ℕ) : ℝ) = 0 := by
    have h1 : ∀ j : Fin N, b j / ((j.val + 1 : ℕ) : ℝ) =
        (if j.val = 0 then 0 else (a j).re / ((j.val + 1 : ℕ) : ℝ)) -
          (if j.val = 0 then S else 0) := by
      intro j
      by_cases hj : j.val = 0
      · simp [hbdef, hj]
      · simp [hbdef, hj]
    simp_rw [h1, Finset.sum_sub_distrib, ← hS]
    rcases N with _ | N
    · simp [hS]
    · rw [Fin.sum_univ_succ]; simp
  -- the discrete residual for b
  set R : ℕ → ℝ := fun m => 1 - ∑ j, b j * Int.fract ((m : ℝ) / ((j.val + 1 : ℕ) : ℝ)) with hR
  have hRle : ∀ m : ℕ, R (m+1) ^ 2 / (((m:ℝ)+1) * ((m:ℝ)+2)) ≤
      ‖(1:ℂ) - ∑ j, a j * ((Int.fract ((((m+1 : ℕ) : ℝ))/((j.val+1 : ℕ) : ℝ)) : ℝ) : ℂ)‖^2 /
        ((((m+1 : ℕ) : ℝ))*(((m+1 : ℕ) : ℝ)+1)) := by
    intro m
    have hden : (((m+1 : ℕ) : ℝ))*(((m+1 : ℕ) : ℝ)+1) = ((m:ℝ)+1) * ((m:ℝ)+2) := by
      push_cast; ring
    rw [hden]
    apply div_le_div_of_nonneg_right _ (by positivity)
    set z : ℂ := (1:ℂ) - ∑ j, a j * ((Int.fract ((((m+1 : ℕ) : ℝ))/((j.val+1 : ℕ) : ℝ)) : ℝ) : ℂ)
    have hzre : z.re = R (m+1) := by
      simp only [z, hR, Complex.sub_re, Complex.one_re, Complex.re_sum, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.val = 0
      · have : Int.fract ((((m+1 : ℕ) : ℝ))/((j.val+1 : ℕ) : ℝ)) = 0 := by
          rw [hj]; simp
        rw [this]; simp
      · simp [hbdef, hj]
    rw [← hzre]
    have := Complex.re_sq_le_normSq z
    rw [Complex.normSq_eq_norm_sq] at this
    nlinarith
  have hnn : ∀ m : ℕ, 0 ≤ R (m+1) ^ 2 / (((m:ℝ)+1) * ((m:ℝ)+2)) := fun m => by positivity
  have hRsum : Summable (fun m : ℕ => R (m+1) ^ 2 / (((m:ℝ)+1) * ((m:ℝ)+2))) :=
    Summable.of_nonneg_of_le hnn hRle hsum
  have hRlt : ∑' m : ℕ, R (m+1) ^ 2 / (((m:ℝ)+1) * ((m:ℝ)+2)) < ε ^ 2 / 2 :=
    lt_of_le_of_lt (hRsum.tsum_le_tsum hRle hsum) hlt
  refine ⟨N, b, hcon, ?_⟩
  set f : ℝ → ℝ := fun x => (if x ∈ Set.Ioc 0 1 then (1 : ℝ) else 0) -
        ∑ j, b j * Int.fract (1 / (((j.val+1 : ℕ):ℝ)*x)) with hf
  set I : ℕ → Set ℝ := fun n => Ioc (1 / ((n:ℝ) + 2)) (1 / ((n:ℝ) + 1)) with hI
  -- pointwise description
  have hpt : ∀ x ∈ Ioi (0:ℝ), ‖f x‖ₑ ^ (2:ℝ) =
      ∑' n : ℕ, (I n).indicator (fun _ => ENNReal.ofReal (R (n+1) ^ 2)) x := by
    intro x hx
    have hx0 : 0 < x := hx
    by_cases hx1 : 1 < x
    · have hfx : f x = 0 := by
        have hy0 : 0 ≤ 1 / x := by positivity
        have hy1 : 1 / x < 1 := by rw [div_lt_one hx0]; exact hx1
        have : ∀ j : Fin N, b j * Int.fract (1 / (((j.val+1 : ℕ):ℝ)*x)) =
            (1 / x) * (b j / ((j.val + 1 : ℕ) : ℝ)) := by
          intro j
          have hk : (1:ℝ) ≤ ((j.val+1 : ℕ):ℝ) := by exact_mod_cast Nat.succ_pos j.val
          rw [Int.fract_eq_self.mpr]
          · field_simp
          · constructor
            · positivity
            · rw [div_lt_one (by positivity)]; nlinarith
        simp only [hf]
        rw [if_neg (by rintro ⟨_, h⟩; linarith), Finset.sum_congr rfl (fun j _ => this j),
          ← Finset.mul_sum, hcon]
        simp
      rw [hfx]
      have hz : ∀ n : ℕ, (I n).indicator (fun _ => ENNReal.ofReal (R (n+1) ^ 2)) x = 0 := by
        intro n
        apply Set.indicator_of_notMem
        intro hmem
        have := hmem.2
        have h2 : 1 / ((n:ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
        linarith
      simp [hz]
    · push Not at hx1
      set m := ⌊1 / x⌋₊ with hm
      have hm1 : 1 ≤ m := by
        rw [hm, Nat.one_le_floor_iff, le_div_iff₀ hx0]; linarith
      obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
      have hmem : x ∈ I n := (mem_piece_iff x hx0 n).mpr (by rw [← hm, hn])
      have hfx : f x = R (n+1) := by
        have hfl := Nat.floor_le (show 0 ≤ 1 / x by positivity)
        have hfl2 := Nat.lt_floor_add_one (1 / x)
        rw [← hm] at hfl hfl2
        set θ := 1 / x - m with hθ
        have : ∀ j : Fin N, b j * Int.fract (1 / (((j.val+1 : ℕ):ℝ)*x)) =
            b j * Int.fract ((m : ℝ) / ((j.val + 1 : ℕ) : ℝ)) + θ * (b j / ((j.val + 1 : ℕ) : ℝ)) := by
          intro j
          have e1 : 1 / (((j.val+1 : ℕ):ℝ)*x) = ((m:ℝ) + θ) / ((j.val+1 : ℕ):ℝ) := by
            rw [hθ]; field_simp; ring
          rw [e1, fract_shift m (j.val+1) (Nat.succ_pos _) θ (by linarith) (by linarith)]
          ring
        simp only [hf, hR]
        rw [if_pos ⟨hx0, hx1⟩, Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib,
          ← Finset.mul_sum, hcon, mul_zero, add_zero, ← hn]
      rw [hfx, tsum_eq_single n]
      · rw [Set.indicator_of_mem hmem, Real.enorm_eq_ofReal_abs,
          ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
        congr 1
        rw [Real.rpow_two, sq_abs]
      · intro n' hn'
        apply Set.indicator_of_notMem
        rw [mem_piece_iff x hx0 n', ← hm, hn]
        omega
  have hlint : ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂(volume.restrict (Ioi (0:ℝ))) =
      ENNReal.ofReal (∑' m : ℕ, R (m+1) ^ 2 / (((m:ℝ)+1) * ((m:ℝ)+2))) := by
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
    rw [lintegral_tsum (fun n => (aemeasurable_const.indicator measurableSet_Ioc))]
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hRsum]
    congr 1
    funext n
    rw [lintegral_indicator_const measurableSet_Ioc,
      Measure.restrict_apply measurableSet_Ioc]
    have hsub : I n ∩ Ioi 0 = I n := by
      apply Set.inter_eq_left.mpr
      intro y hy; exact lt_trans (by positivity) hy.1
    rw [hsub, Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [hlint]
  have hV0 : 0 ≤ ∑' m : ℕ, R (m+1) ^ 2 / (((m:ℝ)+1) * ((m:ℝ)+2)) := tsum_nonneg hnn
  rw [ENNReal.ofReal_rpow_of_nonneg hV0 (by norm_num)]
  rw [ENNReal.ofReal_lt_ofReal_iff hε]
  calc (∑' m : ℕ, R (m+1) ^ 2 / (((m:ℝ)+1) * ((m:ℝ)+2))) ^ (1/2 : ℝ)
      < (ε ^ 2) ^ (1/2 : ℝ) := by
        apply Real.rpow_lt_rpow hV0 (by nlinarith) (by norm_num)
    _ = ε := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num

end NymanRecip

open MeasureTheory Set
open scoped BigOperators ENNReal


open MeasureTheory Set Complex Filter Topology
open scoped ENNReal

namespace NymanHardy

lemma LSeries_dvd (K : ℕ) (hK : 0 < K) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => if K ∣ n then (1:ℂ) else 0) s = (K:ℂ) ^ (-s) * riemannZeta s := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  rw [zeta_eq_tsum_one_div_nat_cpow hs, ← tsum_mul_left]
  unfold LSeries
  have hinj : Function.Injective (fun m : ℕ => K * m) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left hK h
  rw [← hinj.tsum_eq]
  · apply tsum_congr
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [zero_cpow hs0]
    · have hKm : K * m ≠ 0 := by positivity
      rw [LSeries.term_of_ne_zero hKm, if_pos (dvd_mul_right K m)]
      push_cast
      rw [Complex.natCast_mul_natCast_cpow, cpow_neg]
      field_simp
  · intro n hn
    rw [Function.mem_support] at hn
    by_cases hn0 : n = 0
    · subst hn0; simp at hn
    · rw [LSeries.term_of_ne_zero hn0] at hn
      by_cases hd : K ∣ n
      · obtain ⟨m, rfl⟩ := hd; exact ⟨m, rfl⟩
      · simp [hd] at hn

lemma sum_dvd_eq (K : ℕ) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (if K ∣ k then (1:ℂ) else 0)) = ((n / K : ℕ) : ℂ) := by
  rw [Finset.sum_boole]
  have : Finset.Icc 1 n = Finset.Ioc 0 n := by ext x; simp; omega
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]

lemma integral_floor (K : ℕ) (hK : 0 < K) {s : ℂ} (hs : 1 < s.re) :
    ∫ t in Ioi (1:ℝ), ((⌊t / K⌋₊ : ℕ) : ℂ) * (t:ℂ) ^ (-(s+1)) =
      (K:ℂ) ^ (-s) * riemannZeta s / s := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ‖(fun n => if K ∣ n then (1:ℂ) else 0) k‖)
      =O[atTop] fun n ↦ (n : ℝ) ^ (1:ℝ) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards with n
    rw [Real.rpow_one, Real.norm_natCast, one_mul]
    have h1 : ∑ k ∈ Finset.Icc 1 n, ‖(fun n => if K ∣ n then (1:ℂ) else 0) k‖ ≤
        ∑ k ∈ Finset.Icc 1 n, (1:ℝ) := by
      apply Finset.sum_le_sum; intro k _; dsimp only; split_ifs <;> simp
    have h0 : 0 ≤ ∑ k ∈ Finset.Icc 1 n, ‖(fun n => if K ∣ n then (1:ℂ) else 0) k‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    rw [Real.norm_of_nonneg h0]
    simpa using h1
  have h := LSeries_eq_mul_integral' (fun n => if K ∣ n then (1:ℂ) else 0) (r := 1)
    (by norm_num) hs hO
  rw [LSeries_dvd K hK hs] at h
  have hint : (fun t : ℝ => (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (if K ∣ k then (1:ℂ) else 0)) *
      (t:ℂ) ^ (-(s+1))) = fun t : ℝ => ((⌊t / K⌋₊ : ℕ) : ℂ) * (t:ℂ) ^ (-(s+1)) := by
    funext t
    rw [sum_dvd_eq K, Nat.floor_div_natCast]
  rw [hint] at h
  rw [h]; field_simp


/-- the reciprocal residual -/
noncomputable def gfun {N : ℕ} (b : Fin N → ℝ) (x : ℝ) : ℝ :=
  (if x ∈ Ioc 0 1 then (1 : ℝ) else 0) - ∑ j, b j * Int.fract (1 / (((j.val+1 : ℕ):ℝ)*x))

noncomputable def uf {N : ℕ} (b : Fin N → ℝ) (t : ℝ) : ℂ := ((gfun b t⁻¹ : ℝ) : ℂ)

lemma fract_eq_sub_floor {y : ℝ} (hy : 0 ≤ y) : Int.fract y = y - ⌊y⌋₊ := by
  unfold Int.fract
  rw [← Int.natCast_floor_eq_floor hy]; push_cast; ring

lemma gfun_inv {N : ℕ} (b : Fin N → ℝ) (hcon : ∑ j, b j / ((j.val + 1 : ℕ) : ℝ) = 0)
    {t : ℝ} (ht : 0 < t) :
    gfun b t⁻¹ = (if 1 ≤ t then 1 else 0) + ∑ j, b j * (⌊t / ((j.val+1 : ℕ) : ℝ)⌋₊ : ℝ) := by
  unfold gfun
  have h1 : (t⁻¹ ∈ Ioc (0:ℝ) 1) ↔ 1 ≤ t := by
    rw [mem_Ioc]; constructor
    · rintro ⟨_, h⟩; rwa [inv_le_one₀ ht] at h
    · intro h; exact ⟨inv_pos.mpr ht, (inv_le_one₀ ht).mpr h⟩
  have h2 : ∀ j : Fin N, b j * Int.fract (1 / (((j.val+1 : ℕ):ℝ)*t⁻¹)) =
      t * (b j / ((j.val + 1 : ℕ) : ℝ)) - b j * (⌊t / ((j.val+1 : ℕ) : ℝ)⌋₊ : ℝ) := by
    intro j
    have hk : (0:ℝ) < ((j.val+1 : ℕ):ℝ) := by positivity
    have e : 1 / (((j.val+1 : ℕ):ℝ)*t⁻¹) = t / ((j.val+1 : ℕ):ℝ) := by field_simp
    rw [e, fract_eq_sub_floor (by positivity)]
    ring
  simp_rw [h2]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcon, mul_zero, zero_sub, sub_neg_eq_add]
  congr 1
  by_cases h : 1 ≤ t
  · rw [if_pos (h1.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (h1.mp h')), if_neg h]

lemma integrableOn_floor (K : ℕ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => ((⌊t / K⌋₊ : ℕ) : ℂ) * (t:ℂ) ^ (-(s+1))) (Ioi 1) := by
  have hg : IntegrableOn (fun t : ℝ => t ^ (-s.re)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  refine hg.mono' ?_ ?_
  · apply AEStronglyMeasurable.mul
    · exact (Measurable.of_discrete.comp
        (Nat.measurable_floor.comp (measurable_id.div_const _))).aestronglyMeasurable
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro t ht
      apply ContinuousAt.continuousWithinAt
      exact continuousAt_ofReal_cpow_const _ _ (Or.inr (lt_trans one_pos ht).ne')
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have ht0 : 0 < t := lt_trans one_pos ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_natCast]
    have hfl : ((⌊t / K⌋₊ : ℕ) : ℝ) ≤ t := by
      rcases Nat.eq_zero_or_pos K with hK | hK
      · subst hK; simp; linarith
      · have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK
        calc ((⌊t / K⌋₊ : ℕ) : ℝ) ≤ t / K := Nat.floor_le (by positivity)
          _ ≤ t := div_le_self ht0.le hK'
    have hre : (-(s+1)).re = -s.re - 1 := by simp; ring
    rw [hre]
    have : t ^ (-s.re) = t * t ^ (-s.re - 1) := by
      rw [show -s.re = 1 + (-s.re - 1) by ring, Real.rpow_add ht0, Real.rpow_one]
      ring_nf
    rw [this]
    exact mul_le_mul_of_nonneg_right hfl (by positivity)

lemma mellin_uf_gt_one {N : ℕ} (b : Fin N → ℝ) (hcon : ∑ j, b j / ((j.val + 1 : ℕ) : ℝ) = 0)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (uf b) (-s) = s⁻¹ + ∑ j, (b j : ℂ) *
      ((((j.val+1 : ℕ) : ℂ)) ^ (-s) * riemannZeta s / s) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  unfold mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ici_subset_Ioi.mpr one_pos) (s := Ici 1)]
  swap
  · intro t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := by simpa using ht.2
    simp only [uf]
    rw [gfun_inv b hcon ht0, if_neg (by linarith)]
    have : ∀ j : Fin N, ⌊t / ((j:ℝ) + 1)⌋₊ = 0 := by
      intro j
      rw [Nat.floor_eq_zero, div_lt_one (by positivity)]
      have : (0:ℝ) ≤ (j:ℝ) := by positivity
      linarith
    simp [this]
  rw [integral_Ici_eq_integral_Ioi]
  have hcongr : ∀ t ∈ Ioi (1:ℝ), (t:ℂ) ^ (-s - 1) • uf b t =
      (t:ℂ) ^ (-(s+1)) + ∑ j, (b j : ℂ) *
        (((⌊t / ((j.val+1 : ℕ) : ℝ)⌋₊ : ℕ) : ℂ) * (t:ℂ) ^ (-(s+1))) := by
    intro t ht
    have ht0 : 0 < t := lt_trans one_pos ht
    simp only [uf, smul_eq_mul]
    rw [gfun_inv b hcon ht0, if_pos (le_of_lt ht)]
    push_cast
    rw [show -s - 1 = -(s+1) by ring, mul_add, mul_one, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro j _; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
  have hI1 : IntegrableOn (fun t : ℝ => (t:ℂ) ^ (-(s+1))) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  have hI2 : ∀ j : Fin N, IntegrableOn (fun t : ℝ => (b j : ℂ) *
      (((⌊t / ((j.val+1 : ℕ) : ℝ)⌋₊ : ℕ) : ℂ) * (t:ℂ) ^ (-(s+1)))) (Ioi 1) :=
    fun j => (integrableOn_floor (j.val+1) hs).const_mul _
  rw [integral_add hI1 (integrable_finsetSum _ (fun j _ => hI2 j)),
    integral_finsetSum _ (fun j _ => hI2 j)]
  congr 1
  · rw [integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
    simp only [ofReal_one, one_cpow]
    rw [show -(s+1) + 1 = -s by ring]
    field_simp
  · apply Finset.sum_congr rfl; intro j _
    rw [integral_const_mul, integral_floor (j.val+1) (Nat.succ_pos _) hs]


lemma lintegral_inv_Ioi (F : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ioi (0:ℝ), F x = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (-2:ℝ)) * F t⁻¹ := by
  have himg : (fun t : ℝ => t⁻¹) '' Ioi 0 = Ioi 0 := by
    ext x; simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact inv_pos.mpr ht
    · intro hx; exact ⟨x⁻¹, inv_pos.mpr hx, inv_inv x⟩
  conv_lhs => rw [← himg]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (f' := fun t => -(t^2)⁻¹) (fun x hx => (hasDerivAt_inv (ne_of_gt hx)).hasDerivWithinAt)
    inv_injective.injOn F]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  congr 2
  rw [abs_neg, abs_of_pos (by have : (0:ℝ) < t := ht; positivity), Real.rpow_neg (le_of_lt ht)]
  norm_cast

lemma lintegral_enorm_sq {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (f : α → E) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = eLpNorm f 2 μ ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

lemma enorm_ofReal_complex (x : ℝ) : ‖(x : ℂ)‖ₑ = ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]

lemma measurable_gfun {N : ℕ} (b : Fin N → ℝ) : Measurable (gfun b) := by
  unfold gfun
  apply Measurable.sub
  · exact Measurable.ite measurableSet_Ioc measurable_const measurable_const
  · apply Finset.measurable_sum
    intro j _
    exact ((measurable_const.div (measurable_const.mul measurable_id)).fract).const_mul _

theorem hardy_of_recip
    (hrec : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ b : Fin N → ℝ,
      (∑ j, b j / ((j.val + 1 : ℕ) : ℝ)) = 0 ∧
      MeasureTheory.eLpNorm (fun x : ℝ =>
        (if x ∈ Set.Ioc 0 1 then (1 : ℝ) else 0) -
        ∑ j, b j * Int.fract (1 / (((j.val+1 : ℕ):ℝ)*x)))
        2 (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) < ENNReal.ofReal ε) :
    let G (k : ℕ) (s : ℂ) : ℂ := if s = 1 then -(Real.log k : ℂ)/k
      else ((k : ℂ)^(-s) - (k : ℂ)⁻¹) * riemannZeta s / s
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℂ,
      ∀ σ : ℝ, 1/2 < σ →
        let err (t : ℝ) := let s := (σ : ℂ) + (t : ℂ)*Complex.I
                           ‖s⁻¹ - ∑ j, a j * G (j.val + 1 : ℕ) s‖^2
        MeasureTheory.Integrable err ∧ (∫ t : ℝ, err t) / (2*Real.pi) ≤ ε := by
  intro G ε hε
  obtain ⟨N, b, hcon, hL⟩ := hrec (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  refine ⟨N, fun j => -(b j : ℂ), ?_⟩
  intro σ hσ err
  have hmeas : AEStronglyMeasurable (uf b) (volume.restrict (Ioi 0)) :=
    (Complex.measurable_ofReal.comp ((measurable_gfun b).comp measurable_inv)).aestronglyMeasurable
  have hvan : ∀ᵐ t : ℝ ∂volume, t ∈ Ioo 0 1 → uf b t = 0 := by
    filter_upwards with t ht
    simp only [uf]
    rw [gfun_inv b hcon ht.1, if_neg (by linarith [ht.2])]
    have : ∀ j : Fin N, ⌊t / ((j:ℝ) + 1)⌋₊ = 0 := by
      intro j
      rw [Nat.floor_eq_zero, div_lt_one (by positivity)]
      have : (0:ℝ) ≤ (j:ℝ) := by positivity
      linarith [ht.2]
    simp [this]
  set I := ∫⁻ x in Ioi (0:ℝ), ‖gfun b x‖ₑ ^ 2 with hI
  have hIeq : (∫⁻ t in Ioi 0, ‖uf b t‖ₑ ^ 2 * ENNReal.ofReal (t ^ (2 * (-1/2:ℝ) - 1))) = I := by
    conv_rhs => rw [hI, lintegral_inv_Ioi]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [uf, enorm_ofReal_complex]
    rw [mul_comm]; norm_num
  have hIle : I ≤ ENNReal.ofReal ε := by
    rw [hI, lintegral_enorm_sq]
    have h1 : eLpNorm (gfun b) 2 (volume.restrict (Ioi 0)) ≤ ENNReal.ofReal (Real.sqrt ε) :=
      le_of_lt hL
    calc eLpNorm (gfun b) 2 (volume.restrict (Ioi 0)) ^ 2 ≤ ENNReal.ofReal (Real.sqrt ε) ^ 2 := by
          gcongr
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hε.le]
  have hfin : (∫⁻ t in Ioi 0, ‖uf b t‖ₑ ^ 2 * ENNReal.ofReal (t ^ (2 * (-1/2:ℝ) - 1))) < ⊤ := by
    rw [hIeq]; exact lt_of_le_of_lt hIle ENNReal.ofReal_lt_top
  obtain ⟨-, ⟨hdiff, -⟩, hnorm⟩ :=
    (HardyHalfPlane.paleyWiener_mellin_leftHardy_two (-1/2)).1 (uf b) hmeas hvan hfin
  rw [hIeq] at hnorm
  -- the identity on the half-plane
  have hid : ∀ s : ℂ, 1/2 < s.re → s ≠ 1 →
      mellin (uf b) (-s) = s⁻¹ - ∑ j, (-(b j : ℂ)) *
        ((((j.val+1 : ℕ) : ℂ)^(-s) - ((j.val+1 : ℕ) : ℂ)⁻¹) * riemannZeta s / s) := by
    set L : ℂ → ℂ := fun s => mellin (uf b) (-s) with hLdef
    set H : ℂ → ℂ := fun s => s⁻¹ - ∑ j, (-(b j : ℂ)) *
        ((((j.val+1 : ℕ) : ℂ)^(-s) - ((j.val+1 : ℕ) : ℂ)⁻¹) * riemannZeta s / s) with hHdef
    have hconC : ∑ j, (b j : ℂ) * (((j.val+1 : ℕ) : ℂ))⁻¹ = 0 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hcon
      push_cast at this
      simpa [div_eq_mul_inv] using this
    have hgt : ∀ s : ℂ, 1 < s.re → L s = H s := by
      intro s hs
      simp only [hLdef, hHdef]
      rw [mellin_uf_gt_one b hcon hs]
      have : ∀ j : Fin N, (-(b j : ℂ)) *
          ((((j.val+1 : ℕ) : ℂ)^(-s) - ((j.val+1 : ℕ) : ℂ)⁻¹) * riemannZeta s / s) =
          -((b j : ℂ) * ((((j.val+1 : ℕ) : ℂ)) ^ (-s) * riemannZeta s / s)) +
            ((b j : ℂ) * (((j.val+1 : ℕ) : ℂ))⁻¹) * (riemannZeta s / s) := by
        intro j; ring
      rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib, ← Finset.sum_mul,
        hconC, Finset.sum_neg_distrib]
      ring
    set D : Set ℂ := {s | 1/2 < s.re} ∩ {s | s ≠ 1} with hD
    have hDopen : IsOpen D :=
      (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
    have hLd : DifferentiableOn ℂ L D := by
      have := hdiff.comp (differentiable_neg.differentiableOn (s := D)) (by
        intro s hs; simp only [mem_ofPred_eq, neg_re]; linarith [hs.1.out])
      exact this
    have hHd : DifferentiableOn ℂ H D := by
      intro s hs
      have hs1 : s ≠ 1 := hs.2
      have hs0 : s ≠ 0 := by intro h; have := hs.1.out; rw [h] at this; simp at this; linarith
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.sub (differentiableAt_inv hs0)
      apply DifferentiableAt.fun_sum
      intro j _
      apply DifferentiableAt.const_mul
      apply DifferentiableAt.div _ differentiableAt_id hs0
      apply DifferentiableAt.mul _ (differentiableAt_riemannZeta hs1)
      apply DifferentiableAt.sub_const
      apply DifferentiableAt.const_cpow differentiableAt_id.neg
      left; exact_mod_cast Nat.succ_ne_zero j.val
    have key : ∀ S : Set ℂ, IsOpen S → Convex ℝ S → S ⊆ D → ∀ z₀ ∈ S, L =ᶠ[𝓝 z₀] H →
        EqOn L H S := by
      intro S hSo hSc hSD z₀ hz₀ hev
      exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
        ((hLd.mono hSD).analyticOnNhd hSo) ((hHd.mono hSD).analyticOnNhd hSo)
        hSc.isPreconnected hz₀ hev
    have hgt_ev : ∀ z₀ : ℂ, 1 < z₀.re → L =ᶠ[𝓝 z₀] H := by
      intro z₀ hz
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with s hs
      exact hgt s hs
    set S1 : Set ℂ := {s | 1/2 < s.re} ∩ {s | 0 < s.im}
    set S2 : Set ℂ := {s | 1/2 < s.re} ∩ {s | s.im < 0}
    set S3 : Set ℂ := {s | 1/2 < s.re} ∩ {s | s.re < 1}
    have hS1o : IsOpen S1 := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
    have hS2o : IsOpen S2 := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_im continuous_const)
    have hS3o : IsOpen S3 := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
    have hS1D : S1 ⊆ D := by
      intro s hs; refine ⟨hs.1, ?_⟩; intro h; have := hs.2.out; rw [h] at this; simp at this
    have hS2D : S2 ⊆ D := by
      intro s hs; refine ⟨hs.1, ?_⟩; intro h; have := hs.2.out; rw [h] at this; simp at this
    have hS3D : S3 ⊆ D := by
      intro s hs; refine ⟨hs.1, ?_⟩; intro h; have := hs.2.out; rw [h] at this; simp at this
    have hE1 : EqOn L H S1 := key S1 hS1o (Convex.inter (convex_halfSpace_re_gt (1/2)) (convex_halfSpace_im_gt 0))
      hS1D (2 + Complex.I) ⟨by norm_num, by norm_num⟩ (hgt_ev _ (by norm_num))
    have hE2 : EqOn L H S2 := key S2 hS2o (Convex.inter (convex_halfSpace_re_gt (1/2)) (convex_halfSpace_im_lt 0))
      hS2D (2 - Complex.I) ⟨by norm_num, by norm_num⟩ (hgt_ev _ (by norm_num))
    have hz3 : (3/4 + Complex.I : ℂ) ∈ S1 := ⟨by norm_num, by norm_num⟩
    have hE3 : EqOn L H S3 := key S3 hS3o (Convex.inter (convex_halfSpace_re_gt (1/2)) (convex_halfSpace_re_lt 1))
      hS3D (3/4 + Complex.I) ⟨by norm_num, by norm_num⟩ (by
        filter_upwards [hS1o.mem_nhds hz3] with s hs
        exact hE1 hs)
    intro s hs hs1
    rcases lt_trichotomy s.im 0 with him | him | him
    · exact hE2 ⟨hs, him⟩
    · rcases lt_trichotomy s.re 1 with hre | hre | hre
      · exact hE3 ⟨hs, hre⟩
      · exfalso; apply hs1; apply Complex.ext <;> simp [hre, him]
      · exact hgt s hre
    · exact hE1 ⟨hs, him⟩
  -- the line function
  set φ : ℝ → ℂ := fun y => mellin (uf b) (((-σ : ℝ) : ℂ) + (y : ℂ) * Complex.I) with hφ
  have hφcont : Continuous φ := by
    apply hdiff.continuousOn.comp_continuous (by fun_prop)
    intro y; simp; linarith
  have hφle : eLpNorm φ 2 volume ≤
      ENNReal.ofReal (Real.sqrt (2 * Real.pi)) * I ^ (1/2 : ℝ) := by
    rw [← hnorm]
    unfold HardyHalfPlane.leftHardyNorm
    exact le_iSup₂_of_le (-σ) (by linarith) le_rfl
  have hsq : ∫⁻ y, ‖φ y‖ₑ ^ 2 ≤ ENNReal.ofReal (2 * Real.pi * ε) := by
    rw [lintegral_enorm_sq]
    calc eLpNorm φ 2 volume ^ 2 ≤ (ENNReal.ofReal (Real.sqrt (2 * Real.pi)) * I ^ (1/2 : ℝ)) ^ 2 := by
          gcongr
      _ = ENNReal.ofReal (2 * Real.pi) * I := by
          rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity),
            ← ENNReal.rpow_natCast (I ^ (1/2:ℝ)), ← ENNReal.rpow_mul]
          norm_num
      _ ≤ ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal ε := by gcongr
      _ = ENNReal.ofReal (2 * Real.pi * ε) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  have hFm : AEStronglyMeasurable (fun y => ‖φ y‖ ^ 2) volume :=
    (hφcont.norm.pow 2).aestronglyMeasurable
  have hFint : Integrable (fun y => ‖φ y‖ ^ 2) := by
    refine ⟨hFm, ?_⟩
    unfold HasFiniteIntegral
    have : ∀ y, ‖‖φ y‖ ^ 2‖ₑ = ‖φ y‖ₑ ^ 2 := fun y => by
      rw [enorm_pow, enorm_norm]
    simp_rw [this]
    exact lt_of_le_of_lt hsq ENNReal.ofReal_lt_top
  have hFval : ∫ y, ‖φ y‖ ^ 2 ≤ 2 * Real.pi * ε := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun y => by positivity)) hFm]
    have : ∀ y, ENNReal.ofReal (‖φ y‖ ^ 2) = ‖φ y‖ₑ ^ 2 := fun y => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    simp_rw [this]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hsq
  have herr : err =ᵐ[volume] fun t => ‖φ (-t)‖ ^ 2 := by
    have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [h0] with t ht
    have hs1 : (σ : ℂ) + (t : ℂ) * Complex.I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; exact ht this
    have hre : 1/2 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simp; linarith
    have e1 : err t = ‖((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹ - ∑ j, (-(b j : ℂ)) *
        ((((j.val+1 : ℕ) : ℂ)^(-((σ : ℂ) + (t : ℂ) * Complex.I)) - ((j.val+1 : ℕ) : ℂ)⁻¹) *
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) / ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2 := by
      simp only [err, G, if_neg hs1]
    rw [e1, ← hid _ hre hs1]
    simp only [hφ]
    congr 3
    push_cast; ring
  refine ⟨?_, ?_⟩
  · exact (hFint.comp_neg).congr herr.symm
  · rw [integral_congr_ae herr, integral_neg_eq_self (fun t => ‖φ t‖ ^ 2)]
    rw [div_le_iff₀ (by positivity)]
    linarith

end NymanHardy

namespace NymanInterval

lemma G_agree (k : ℕ) (s : ℂ) :
    (if s = 1 then ((((1:ℝ) / ((k+1 : ℕ):ℝ)) * Real.log ((1:ℝ) / ((k+1 : ℕ):ℝ)) : ℝ) : ℂ)
      else ((((1:ℝ) / ((k+1 : ℕ):ℝ) : ℝ) : ℂ)^s - (((1:ℝ) / ((k+1 : ℕ):ℝ) : ℝ) : ℂ)) *
        riemannZeta s / s) =
    (if s = 1 then -(Real.log ((k+1 : ℕ) : ℝ) : ℂ)/((k+1 : ℕ) : ℂ)
      else ((((k+1 : ℕ) : ℂ))^(-s) - (((k+1 : ℕ) : ℂ))⁻¹) * riemannZeta s / s) := by
  split_ifs with hs
  · rw [one_div, Real.log_inv]; push_cast; ring
  · congr 2
    have h1 : ((((1:ℝ) / ((k+1 : ℕ):ℝ) : ℝ) : ℂ)) = (((k+1 : ℕ) : ℂ))⁻¹ := by push_cast; ring
    rw [h1, Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm),
      Complex.cpow_neg]

theorem interval_of_integers
    (h : let G (k : ℕ) (s : ℂ) : ℂ := if s = 1 then -(Real.log k : ℂ)/k
      else ((k : ℂ)^(-s) - (k : ℂ)⁻¹) * riemannZeta s / s
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℂ,
      ∀ σ : ℝ, 1/2 < σ →
        let err (t : ℝ) := let s := (σ : ℂ) + (t : ℂ)*Complex.I
                           ‖s⁻¹ - ∑ j, a j * G (j.val + 1 : ℕ) s‖^2
        MeasureTheory.Integrable err ∧ (∫ t : ℝ, err t) / (2*Real.pi) ≤ ε) :
    let G (p : ℝ) (s : ℂ) : ℂ := if s = 1 then ((p * Real.log p : ℝ) : ℂ)
      else ((p : ℂ)^s - (p : ℂ)) * riemannZeta s / s
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℂ,
      ∃ p : Fin N → Set.Icc (0 : ℝ) 1,
      ∀ σ : ℝ, 1/2 < σ →
        let err (t : ℝ) := let s := (σ : ℂ) + (t : ℂ)*Complex.I
                           ‖s⁻¹ - ∑ j, a j * G (p j) s‖^2
        MeasureTheory.Integrable err ∧ (∫ t : ℝ, err t) / (2*Real.pi) ≤ ε := by
  intro G ε hε
  obtain ⟨N, a, ha⟩ := h ε hε
  set p : Fin N → Set.Icc (0:ℝ) 1 := fun j => ⟨(1:ℝ) / ((j.val+1 : ℕ):ℝ), by positivity, by
    rw [div_le_one (by positivity)]; exact_mod_cast Nat.succ_pos j.val⟩ with hp
  refine ⟨N, a, p, ?_⟩
  intro σ hσ
  have hG : ∀ (j : Fin N) (s : ℂ), G (p j) s =
      (if s = 1 then -(Real.log ((j.val+1 : ℕ) : ℝ) : ℂ)/((j.val+1 : ℕ) : ℂ)
      else ((((j.val+1 : ℕ) : ℂ))^(-s) - (((j.val+1 : ℕ) : ℂ))⁻¹) * riemannZeta s / s) :=
    fun j s => G_agree j.val s
  simp only [hG]
  exact ha σ hσ

end NymanInterval

theorem solution :
    let G (p : ℝ) (s : ℂ) : ℂ := if s = 1 then ((p * Real.log p : ℝ) : ℂ)
      else ((p : ℂ)^s - (p : ℂ)) * riemannZeta s / s
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℂ,
      ∃ p : Fin N → Set.Icc (0 : ℝ) 1,
      ∀ σ : ℝ, 1/2 < σ →
        let err (t : ℝ) := let s := (σ : ℂ) + (t : ℂ)*Complex.I
                           ‖s⁻¹ - ∑ j, a j * G (p j) s‖^2
        MeasureTheory.Integrable err ∧ (∫ t : ℝ, err t) / (2*Real.pi) ≤ ε :=
  NymanInterval.interval_of_integers (NymanHardy.hardy_of_recip (NymanRecip.recip_of_bagchi (bagchiConst_of_bounds
    (NymanAux.moebiusPolynomialBoundaryBound_of_riemannHypothesis riemann_hypothesis)
    (NymanAux.shiftedZetaRatioBound_of_riemannHypothesis riemann_hypothesis))))
