-- Prove2me | solution 1 for BroughanRH.nyman
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T02:13:35.218726+00:00
-- url     : https://prove2.me/submissions/f10e273a-3ef1-4d54-b587-15c1b2b50ffa
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

namespace NymanBeur

/-- Approximability of `f` in `L²(0,1]` by admissible Beurling combinations. -/
def Approx (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ a θ : Fin n → ℝ, (∀ j, θ j ∈ Ioc (0:ℝ) 1) ∧
    (∑ j, a j * θ j) = 0 ∧
    eLpNorm (fun x : ℝ => f x - ∑ j, a j * Int.fract (θ j / x)) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) < ENNReal.ofReal ε

lemma measurable_B {n : ℕ} (a θ : Fin n → ℝ) :
    Measurable (fun x : ℝ => ∑ j, a j * Int.fract (θ j / x)) := by
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_const.div measurable_id).fract).const_mul _

lemma approx_zero : Approx (fun _ => 0) := by
  intro ε hε
  refine ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, ?_⟩
  simp [ENNReal.ofReal_pos.mpr hε]

lemma approx_add {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfa : Approx f) (hga : Approx g) : Approx (fun x => f x + g x) := by
  intro ε hε
  obtain ⟨n1, a1, θ1, hθ1, hc1, h1⟩ := hfa (ε/2) (by positivity)
  obtain ⟨n2, a2, θ2, hθ2, hc2, h2⟩ := hga (ε/2) (by positivity)
  refine ⟨n1 + n2, Fin.append a1 a2, Fin.append θ1 θ2, ?_, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using hθ1 i
    · simpa using hθ2 i
  · rw [Fin.sum_univ_add]; simp [hc1, hc2]
  · have heq : (fun x : ℝ => (f x + g x) -
        ∑ j, Fin.append a1 a2 j * Int.fract (Fin.append θ1 θ2 j / x)) =
        (fun x => f x - ∑ j, a1 j * Int.fract (θ1 j / x)) +
        (fun x => g x - ∑ j, a2 j * Int.fract (θ2 j / x)) := by
      funext x
      simp only [Pi.add_apply]
      rw [Fin.sum_univ_add]; simp; ring
    rw [heq]
    calc _ ≤ eLpNorm (fun x => f x - ∑ j, a1 j * Int.fract (θ1 j / x)) 2
            (volume.restrict (Ioc (0 : ℝ) 1)) +
          eLpNorm (fun x => g x - ∑ j, a2 j * Int.fract (θ2 j / x)) 2
            (volume.restrict (Ioc (0 : ℝ) 1)) :=
          eLpNorm_add_le ((hf.sub (measurable_B a1 θ1)).aestronglyMeasurable)
            ((hg.sub (measurable_B a2 θ2)).aestronglyMeasurable) (by norm_num)
      _ < ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) :=
          ENNReal.add_lt_add h1 h2
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

lemma approx_smul {f : ℝ → ℝ} (c : ℝ) (hfa : Approx f) : Approx (fun x => c * f x) := by
  intro ε hε
  obtain ⟨n, a, θ, hθ, hc, h⟩ := hfa (ε / (|c| + 1)) (by positivity)
  refine ⟨n, fun j => c * a j, θ, hθ, ?_, ?_⟩
  · simp_rw [mul_assoc]; rw [← Finset.mul_sum, hc, mul_zero]
  · have heq : (fun x : ℝ => c * f x - ∑ j, (c * a j) * Int.fract (θ j / x)) =
        c • (fun x => f x - ∑ j, a j * Int.fract (θ j / x)) := by
      funext x; simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_sub, Finset.mul_sum]; simp_rw [mul_assoc]
    rw [heq, eLpNorm_const_smul]
    calc ‖c‖ₑ * eLpNorm (fun x => f x - ∑ j, a j * Int.fract (θ j / x)) 2
            (volume.restrict (Ioc (0 : ℝ) 1))
        ≤ ENNReal.ofReal (|c| + 1) * eLpNorm (fun x => f x - ∑ j, a j * Int.fract (θ j / x)) 2
            (volume.restrict (Ioc (0 : ℝ) 1)) := by
          gcongr
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (by linarith)
      _ < ENNReal.ofReal (|c| + 1) * ENNReal.ofReal (ε / (|c| + 1)) := by
          exact ENNReal.mul_lt_mul_right (by simp; positivity) ENNReal.ofReal_ne_top h
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp

/-- Dilation: the `L²(0,1]` norm of `x ↦ g (x/α)` is at most the `L²(0,∞)` norm of `g`. -/
lemma eLpNorm_dilate_le {g : ℝ → ℝ} (hg : Measurable g) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    eLpNorm (fun x => g (x / α)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ≤
      eLpNorm g 2 (volume.restrict (Ioi (0 : ℝ))) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  set H : ℝ → ℝ≥0∞ := fun y => ‖g y‖ₑ ^ (2:ℝ)
  have hH : Measurable H := hg.enorm.pow_const _
  have hα' : α⁻¹ ≠ 0 := inv_ne_zero hα0.ne'
  calc ∫⁻ x in Ioc 0 1, H (x / α) ≤ ∫⁻ x in Ioi 0, H (x / α) :=
        lintegral_mono_set Ioc_subset_Ioi_self
    _ = ∫⁻ x, (Ioi (0:ℝ)).indicator H (α⁻¹ * x) := by
        rw [← lintegral_indicator measurableSet_Ioi]
        congr 1; funext x
        by_cases hx : 0 < x
        · have : 0 < α⁻¹ * x := by positivity
          rw [indicator_of_mem (show x ∈ Ioi (0:ℝ) from hx),
            indicator_of_mem (show α⁻¹ * x ∈ Ioi (0:ℝ) from this), div_eq_inv_mul]
        · have : ¬ 0 < α⁻¹ * x := by
            push Not at hx ⊢; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hx
          rw [indicator_of_notMem (show x ∉ Ioi (0:ℝ) from hx),
            indicator_of_notMem (show α⁻¹ * x ∉ Ioi (0:ℝ) from this)]
    _ = ∫⁻ y, (Ioi (0:ℝ)).indicator H y ∂(Measure.map (fun x => α⁻¹ * x) volume) :=
        (lintegral_map (hH.indicator measurableSet_Ioi) (measurable_const_mul _)).symm
    _ = ENNReal.ofReal α * ∫⁻ y, (Ioi (0:ℝ)).indicator H y := by
        rw [Real.map_volume_mul_left hα', lintegral_smul_measure, inv_inv, abs_of_pos hα0]
        rfl
    _ ≤ 1 * ∫⁻ y, (Ioi (0:ℝ)).indicator H y := by
        gcongr; exact ENNReal.ofReal_le_one.mpr hα1
    _ = ∫⁻ y in Ioi 0, H y := by rw [one_mul, lintegral_indicator measurableSet_Ioi]

lemma approx_ind_pos
    (hrec : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ b : Fin N → ℝ,
      (∑ j, b j / ((j.val + 1 : ℕ) : ℝ)) = 0 ∧
      MeasureTheory.eLpNorm (fun x : ℝ =>
        (if x ∈ Set.Ioc 0 1 then (1 : ℝ) else 0) -
        ∑ j, b j * Int.fract (1 / (((j.val+1 : ℕ):ℝ)*x)))
        2 (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) < ENNReal.ofReal ε)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    Approx ((Ioc (0:ℝ) α).indicator (fun _ => 1)) := by
  intro ε hε
  obtain ⟨N, b, hcon, hL⟩ := hrec ε hε
  refine ⟨N, b, fun j => α / ((j.val + 1 : ℕ) : ℝ), ?_, ?_, ?_⟩
  · intro j
    have hk : (1:ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j.val
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]; linarith
  · have : ∀ j : Fin N, b j * (α / ((j.val + 1 : ℕ) : ℝ)) = α * (b j / ((j.val + 1 : ℕ) : ℝ)) :=
      fun j => by ring
    simp_rw [this]; rw [← Finset.mul_sum, hcon, mul_zero]
  · set g : ℝ → ℝ := fun x => (if x ∈ Set.Ioc 0 1 then (1 : ℝ) else 0) -
        ∑ j, b j * Int.fract (1 / (((j.val+1 : ℕ):ℝ)*x)) with hgdef
    have hgm : Measurable g := by
      apply Measurable.sub
      · exact Measurable.ite measurableSet_Ioc measurable_const measurable_const
      · apply Finset.measurable_sum
        intro j _
        exact ((measurable_const.div (measurable_const.mul measurable_id)).fract).const_mul _
    have heq : (fun x : ℝ => (Ioc (0:ℝ) α).indicator (fun _ => (1:ℝ)) x -
        ∑ j, b j * Int.fract (α / ((j.val + 1 : ℕ) : ℝ) / x)) = fun x => g (x / α) := by
      funext x
      simp only [hgdef]
      congr 1
      · by_cases hx : x ∈ Ioc (0:ℝ) α
        · rw [indicator_of_mem hx, if_pos]
          refine ⟨div_pos hx.1 hα0, ?_⟩
          rw [div_le_one hα0]; exact hx.2
        · rw [indicator_of_notMem hx, if_neg]
          rintro ⟨h1, h2⟩
          apply hx
          refine ⟨?_, ?_⟩
          · rwa [div_pos_iff_of_pos_right hα0] at h1
          · rwa [div_le_one hα0] at h2
      · apply Finset.sum_congr rfl
        intro j _
        congr 2
        rcases eq_or_ne x 0 with rfl | hx
        · simp
        · field_simp
    rw [heq]
    exact lt_of_le_of_lt (eLpNorm_dilate_le hgm hα0 hα1) hL

lemma approx_ind
    (hrec : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ b : Fin N → ℝ,
      (∑ j, b j / ((j.val + 1 : ℕ) : ℝ)) = 0 ∧
      MeasureTheory.eLpNorm (fun x : ℝ =>
        (if x ∈ Set.Ioc 0 1 then (1 : ℝ) else 0) -
        ∑ j, b j * Int.fract (1 / (((j.val+1 : ℕ):ℝ)*x)))
        2 (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) < ENNReal.ofReal ε)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    Approx ((Ioc (0:ℝ) α).indicator (fun _ => 1)) := by
  rcases hα0.eq_or_lt with h | h
  · subst h
    have : (Ioc (0:ℝ) 0).indicator (fun _ => (1:ℝ)) = fun _ => 0 := by
      rw [Ioc_self, indicator_empty]
    rw [this]; exact approx_zero
  · exact approx_ind_pos hrec h hα1

lemma mem_step_iff {K : ℕ} (hK : 0 < K) (i : ℕ) (x : ℝ) :
    x ∈ Ioc ((i:ℝ) / K) (((i:ℝ) + 1) / K) ↔ ⌈(K:ℝ) * x⌉₊ = i + 1 := by
  have hK' : (0:ℝ) < K := by exact_mod_cast hK
  rw [Nat.ceil_eq_iff (by omega), mem_Ioc, div_lt_iff₀ hK', le_div_iff₀ hK']
  simp only [Nat.add_sub_cancel]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma approx_interval
    (hrec : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ b : Fin N → ℝ,
      (∑ j, b j / ((j.val + 1 : ℕ) : ℝ)) = 0 ∧
      MeasureTheory.eLpNorm (fun x : ℝ =>
        (if x ∈ Set.Ioc 0 1 then (1 : ℝ) else 0) -
        ∑ j, b j * Int.fract (1 / (((j.val+1 : ℕ):ℝ)*x)))
        2 (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) < ENNReal.ofReal ε)
    {β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ) (hγ : γ ≤ 1) :
    Approx ((Ioc β γ).indicator (fun _ => 1)) := by
  have h := approx_add (measurable_const.indicator measurableSet_Ioc)
    ((measurable_const.indicator measurableSet_Ioc).const_mul (-1))
    (approx_ind hrec (hβ.trans hβγ) hγ) (approx_smul (-1) (approx_ind hrec hβ (hβγ.trans hγ)))
  have heq : (fun x => (Ioc (0:ℝ) γ).indicator (fun _ => (1:ℝ)) x +
      -1 * (Ioc (0:ℝ) β).indicator (fun _ => (1:ℝ)) x) = (Ioc β γ).indicator (fun _ => 1) := by
    funext x
    simp only [indicator, mem_Ioc]
    by_cases hx0 : 0 < x <;> by_cases hxg : x ≤ γ <;> rcases lt_or_ge β x with hxb | hxb
    all_goals first
      | (have hn : ¬ x ≤ β := not_le.mpr hxb
         simp [hx0, hxg, hxb, hn])
      | (have hn : ¬ β < x := not_lt.mpr hxb
         simp [hx0, hxg, hxb, hn])
      | skip
    all_goals (exfalso; linarith)
  rwa [heq] at h

lemma approx_step
    (hrec : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ b : Fin N → ℝ,
      (∑ j, b j / ((j.val + 1 : ℕ) : ℝ)) = 0 ∧
      MeasureTheory.eLpNorm (fun x : ℝ =>
        (if x ∈ Set.Ioc 0 1 then (1 : ℝ) else 0) -
        ∑ j, b j * Int.fract (1 / (((j.val+1 : ℕ):ℝ)*x)))
        2 (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) < ENNReal.ofReal ε)
    (K : ℕ) (hK : 0 < K) (v : ℕ → ℝ) (M : ℕ) (hM : M ≤ K) :
    Approx (fun x => ∑ i ∈ Finset.range M,
      v i * (Ioc ((i:ℝ) / K) (((i:ℝ) + 1) / K)).indicator (fun _ => 1) x) := by
  have hK' : (0:ℝ) < K := by exact_mod_cast hK
  induction M with
  | zero => simpa using approx_zero
  | succ M ih =>
    have hm : ∀ M' : ℕ, Measurable (fun x => ∑ i ∈ Finset.range M',
        v i * (Ioc ((i:ℝ) / K) (((i:ℝ) + 1) / K)).indicator (fun _ => (1:ℝ)) x) := by
      intro M'
      apply Finset.measurable_sum
      intro i _
      exact (measurable_const.indicator measurableSet_Ioc).const_mul _
    have hMK : (M:ℝ) + 1 ≤ K := by exact_mod_cast hM
    have h := approx_add (hm M) ((measurable_const.indicator measurableSet_Ioc).const_mul (v M))
      (ih (by omega)) (approx_smul (v M) (approx_interval hrec (β := (M:ℝ)/K)
        (γ := ((M:ℝ)+1)/K) (by positivity)
        (by gcongr; linarith) (by rw [div_le_one hK']; exact hMK)))
    simp_rw [Finset.sum_range_succ]
    exact h

theorem beurling_of_recip
    (hrec : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ b : Fin N → ℝ,
      (∑ j, b j / ((j.val + 1 : ℕ) : ℝ)) = 0 ∧
      MeasureTheory.eLpNorm (fun x : ℝ =>
        (if x ∈ Set.Ioc 0 1 then (1 : ℝ) else 0) -
        ∑ j, b j * Int.fract (1 / (((j.val+1 : ℕ):ℝ)*x)))
        2 (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) < ENNReal.ofReal ε) :
    ∀ f : ℝ → ℝ, MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) →
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ a θ : Fin n → ℝ,
        (∀ j, θ j ∈ Set.Ioc 0 1) ∧ (∑ j, a j * θ j) = 0 ∧
        MeasureTheory.eLpNorm (fun x : ℝ => f x - ∑ j, a j * Int.fract (θ j / x))
          2 (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) < ENNReal.ofReal ε := by
  intro f hf ε hε
  have : IsFiniteMeasure (volume.restrict (Ioc (0:ℝ) 1)) := ⟨by simp⟩
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨g, hfg, -⟩ := hf.exists_boundedContinuous_eLpNorm_sub_le (by norm_num)
    (ENNReal.ofReal_pos.mpr hε3).ne'
  have huc : UniformContinuousOn g (Icc (0:ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous g.continuous.continuousOn
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 3) hε3
  obtain ⟨K0, hK0⟩ := exists_nat_one_div_lt hδ
  set K := K0 + 1 with hKdef
  have hK : 0 < K := Nat.succ_pos _
  have hK' : (0:ℝ) < K := by exact_mod_cast hK
  have hKδ : 1 / (K:ℝ) < δ := by rw [hKdef]; push_cast; exact hK0
  set v : ℕ → ℝ := fun i => g (((i:ℝ) + 1) / K) with hv
  set h : ℝ → ℝ := fun x => ∑ i ∈ Finset.range K,
      v i * (Ioc ((i:ℝ) / K) (((i:ℝ) + 1) / K)).indicator (fun _ => 1) x with hh
  have hhm : Measurable h := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_const.indicator measurableSet_Ioc).const_mul _
  -- pointwise estimate on (0,1]
  have hpt : ∀ x ∈ Ioc (0:ℝ) 1, ‖g x - h x‖ ≤ ε / 3 := by
    intro x hx
    set m := ⌈(K:ℝ) * x⌉₊ with hm
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by
      rw [hm]; exact (Nat.ceil_pos.mpr (mul_pos hK' hx.1)).ne')
    obtain ⟨i, hi⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    have hmK : m ≤ K := by
      rw [hm, Nat.ceil_le]; nlinarith [hx.2]
    have hmem : x ∈ Ioc ((i:ℝ) / K) (((i:ℝ) + 1) / K) := (mem_step_iff hK i x).mpr (by rw [← hm, hi])
    have hhx : h x = v i := by
      simp only [hh]
      rw [Finset.sum_eq_single i]
      · rw [indicator_of_mem hmem, mul_one]
      · intro i' _ hi'
        rw [indicator_of_notMem, mul_zero]
        rw [mem_step_iff hK i' x, ← hm, hi]; omega
      · intro hi'; exfalso; apply hi'; rw [Finset.mem_range]; omega
    rw [hhx]
    have hy : ((i:ℝ) + 1) / K ∈ Icc (0:ℝ) 1 := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hK']
      have : i + 1 ≤ K := by omega
      exact_mod_cast this
    have hd : dist x (((i:ℝ) + 1) / K) < δ := by
      rw [Real.dist_eq, abs_lt]
      have h1 := hmem.1; have h2 := hmem.2
      have : ((i:ℝ) + 1) / K - (i:ℝ) / K = 1 / K := by field_simp; ring
      constructor <;> linarith
    have := hδg x ⟨hx.1.le, hx.2⟩ _ hy hd
    rw [Real.dist_eq] at this
    simp only [hv, Real.norm_eq_abs]; exact this.le
  have hgh : eLpNorm (fun x => g x - h x) 2 (volume.restrict (Ioc (0:ℝ) 1)) ≤
      ENNReal.ofReal (ε / 3) := by
    have := eLpNorm_le_of_ae_bound (p := 2) (μ := volume.restrict (Ioc (0:ℝ) 1))
      (f := fun x => g x - h x) (C := ε / 3)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hpt))
    simpa using this
  obtain ⟨n, a, θ, hθ, hc, hB⟩ := approx_step hrec K hK v K le_rfl (ε / 3) hε3
  refine ⟨n, a, θ, hθ, hc, ?_⟩
  have heq : (fun x : ℝ => f x - ∑ j, a j * Int.fract (θ j / x)) =
      (f - (g : ℝ → ℝ)) + ((fun x => g x - h x) +
        (fun x => h x - ∑ j, a j * Int.fract (θ j / x))) := by
    funext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [heq]
  have hm1 : AEStronglyMeasurable (f - (g : ℝ → ℝ)) (volume.restrict (Ioc (0:ℝ) 1)) :=
    hf.1.sub g.continuous.aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun x => g x - h x) (volume.restrict (Ioc (0:ℝ) 1)) :=
    (g.continuous.measurable.sub hhm).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (fun x => h x - ∑ j, a j * Int.fract (θ j / x))
      (volume.restrict (Ioc (0:ℝ) 1)) :=
    (hhm.sub (measurable_B a θ)).aestronglyMeasurable
  calc _ ≤ eLpNorm (f - (g : ℝ → ℝ)) 2 (volume.restrict (Ioc (0:ℝ) 1)) +
        eLpNorm ((fun x => g x - h x) +
          (fun x => h x - ∑ j, a j * Int.fract (θ j / x))) 2 (volume.restrict (Ioc (0:ℝ) 1)) :=
        eLpNorm_add_le hm1 (hm2.add hm3) (by norm_num)
    _ ≤ eLpNorm (f - (g : ℝ → ℝ)) 2 (volume.restrict (Ioc (0:ℝ) 1)) +
        (eLpNorm (fun x => g x - h x) 2 (volume.restrict (Ioc (0:ℝ) 1)) +
         eLpNorm (fun x => h x - ∑ j, a j * Int.fract (θ j / x)) 2
          (volume.restrict (Ioc (0:ℝ) 1))) := by
        gcongr; exact eLpNorm_add_le hm2 hm3 (by norm_num)
    _ < ENNReal.ofReal (ε/3) + (ENNReal.ofReal (ε/3) + ENNReal.ofReal (ε/3)) := by
        apply ENNReal.add_lt_add_of_le_of_lt (lt_of_le_of_lt hfg ENNReal.ofReal_lt_top).ne hfg
        exact ENNReal.add_lt_add_of_le_of_lt (lt_of_le_of_lt hgh ENNReal.ofReal_lt_top).ne hgh hB
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

end NymanBeur

theorem solution :
    ∀ f : ℝ → ℝ, MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) →
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ a θ : Fin n → ℝ,
        (∀ j, θ j ∈ Set.Ioc 0 1) ∧ MeasureTheory.eLpNorm
          (fun x : ℝ => f x - ∑ j, a j * (Int.fract (θ j / x) - θ j * Int.fract (1 / x)))
          2 (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) < ENNReal.ofReal ε := by
  intro f hf ε hε
  obtain ⟨n, a, θ, hθ, hc, h⟩ := NymanBeur.beurling_of_recip (NymanRecip.recip_of_bagchi (bagchiConst_of_bounds
    (NymanAux.moebiusPolynomialBoundaryBound_of_riemannHypothesis riemann_hypothesis)
    (NymanAux.shiftedZetaRatioBound_of_riemannHypothesis riemann_hypothesis))) f hf ε hε
  refine ⟨n, a, θ, hθ, ?_⟩
  have heq : (fun x : ℝ => f x - ∑ j, a j * (Int.fract (θ j / x) - θ j * Int.fract (1 / x))) =
      (fun x : ℝ => f x - ∑ j, a j * Int.fract (θ j / x)) := by
    funext x
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, hc]
    ring
  rw [heq]; exact h
