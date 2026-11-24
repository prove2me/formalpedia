-- Prove2me | solution 1 for BroughanRH.beurlingReciprocals
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T01:58:55.422239+00:00
-- url     : https://prove2.me/submissions/fcf21e46-cf5e-461b-8783-d12f8121aaee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
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
  refine ⟨N, b, ?_⟩
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

theorem solution :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℝ,
      MeasureTheory.eLpNorm (fun x : ℝ =>
        (if x ∈ Set.Ioc 0 1 then (1 : ℝ) else 0) -
        ∑ j, a j * Int.fract (1 / (((j.val+1 : ℕ):ℝ)*x)))
        2 (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) < ENNReal.ofReal ε :=
  NymanRecip.recip_of_bagchi (bagchiConst_of_bounds
    (NymanAux.moebiusPolynomialBoundaryBound_of_riemannHypothesis riemann_hypothesis)
    (NymanAux.shiftedZetaRatioBound_of_riemannHypothesis riemann_hypothesis))
