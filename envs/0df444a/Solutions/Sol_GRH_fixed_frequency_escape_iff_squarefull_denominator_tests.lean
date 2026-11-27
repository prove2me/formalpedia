-- Prove2me | solution 1 for GRH.fixed_frequency_escape_iff_squarefull_denominator_tests
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T06:08:23.080425+00:00
-- url     : https://prove2.me/submissions/b6c673cd-dc8f-4ea1-87d3-ece3ce8a3c32

import Theorems.Thm_GRH_moebius_frequency_bounds_lift_to_squarefull_denominators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset Filter GRH.AdditiveMoebiusSpectrum GRH.SquarefullFrequencies

private theorem squareConstant (x : ℚ)
    (θ : ℝ) (hl : 1/2 < θ) 
    (H : ∃ U : ℕ, ∀ u : ℕ, U ≤ u → ‖transform false (u^2) x‖ ≤ ((u : ℝ)^2+1)^θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ, ‖transform false (u^2) x‖ ≤ C*((u : ℝ)^2+1)^θ := by
  obtain ⟨U,hU⟩ := H
  let D : ℝ := ∑ j ∈ range U, ‖transform false (j^2) x‖
  have hD : 0 ≤ D := sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨1+D,by linarith,fun u => ?_⟩
  have hX : 1 ≤ ((u : ℝ)^2+1)^θ :=
    Real.one_le_rpow (by linarith [sq_nonneg (u : ℝ)]) (by linarith)
  by_cases hu : U ≤ u
  · exact (hU u hu).trans (le_mul_of_one_le_left (by linarith) (by linarith))
  · have hsingle : ‖transform false (u^2) x‖ ≤ D :=
      single_le_sum (f:=fun j => ‖transform false (j^2) x‖)
        (fun k _ => norm_nonneg _) (mem_range.mpr (by omega))
    exact hsingle.trans ((show D ≤ 1+D by linarith).trans
      (le_mul_of_one_le_right (by linarith) hX))

private theorem phaseNorm (n : ℕ) (x : ℚ) : ‖phase n x‖ = 1 := by
  simp [phase,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

private theorem fromSquares (x : ℚ) (θ : ℝ) (hl : 1/2 < θ)
    (H : ∃ U : ℕ, ∀ u : ℕ, U ≤ u → ‖transform false (u^2) x‖ ≤ ((u : ℝ)^2+1)^θ) :
    boundAt x θ := by
  obtain ⟨C,hC,hs⟩ := squareConstant x θ hl H
  refine ⟨C+2,by linarith,fun N => ?_⟩
  let u := N.sqrt
  have hsquare : u^2 ≤ N := Nat.sqrt_le' N
  have hsreal : (u : ℝ)^2 ≤ N := by exact_mod_cast hsquare
  have hj : N-u^2 ≤ 2*u := by
    have h : N ≤ u^2+2*u := by simpa [u,pow_two,two_mul,add_assoc] using Nat.sqrt_le_add N
    omega
  have hprefix := hs u
  have hgrowth := Real.rpow_le_rpow (show 0 ≤ (u : ℝ)^2+1 by positivity)
    (show (u : ℝ)^2+1 ≤ (N : ℝ)+1 by linarith) (show 0 ≤ θ by linarith)
  have hroot : (u : ℝ) ≤ ((N : ℝ)+1)^θ := by
    calc
      _ ≤ Real.sqrt ((N : ℝ)+1) := (Real.le_sqrt (by positivity) (by positivity)).mpr (by linarith)
      _ ≤ _ := by rw [Real.sqrt_eq_rpow];exact Real.rpow_le_rpow_of_exponent_le (by simp) hl.le
  have hinc (s j : ℕ) : ‖transform false (s+j) x-transform false s x‖ ≤ (j : ℝ) := by
    simp only [transform,weight,Bool.false_eq_true,false_and,if_false,Complex.ofReal_intCast]
    rw [show s+j+1=s+1+j by omega,sum_range_add,add_sub_cancel_left]
    calc
      _ ≤ ∑ k ∈ range j, ‖(ArithmeticFunction.moebius (s+1+k) : ℂ)*phase (s+1+k) x‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ range j, (1 : ℝ) := by
        apply sum_le_sum
        intro k _
        have hh : |(ArithmeticFunction.moebius (s+1+k) : ℝ)| ≤ 1 := by
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=s+1+k))
        simpa only [norm_mul,phaseNorm,mul_one,Complex.norm_intCast,Int.cast_abs] using hh
      _ = _ := by simp
  have inc := hinc (u^2) (N-u^2)
  rw [Nat.add_sub_of_le hsquare] at inc
  have jreal : ((N-u^2 : ℕ) : ℝ) ≤ 2*(u : ℝ) := by exact_mod_cast hj
  have tri : ‖transform false N x‖ ≤ ‖transform false N x-transform false (u^2) x‖ + ‖transform false (u^2) x‖ := by
    calc
      _ = ‖transform false N x-transform false (u^2) x+transform false (u^2) x‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  linarith only [tri,inc,jreal,hroot,hprefix,mul_le_mul_of_nonneg_left hgrowth hC]

private theorem phaseFraction (n a q : ℕ) [NeZero q] :
    phase n ((a : ℚ)/q) = ZMod.stdAddChar ((n : ZMod q)*(a : ZMod q)) := by
  have he := ZMod.stdAddChar_coe (N:=q) ((n*a : ℕ) : ℤ)
  push_cast at he
  rw [he]
  unfold phase
  push_cast
  congr 1
  ring

private theorem reduceNumerator (q : ℕ) (hq : 0 < q) (a N : ℕ) :
    transform false N ((a : ℚ)/q) = transform false N (((a%q : ℕ) : ℚ)/q) := by
  let : NeZero q := ⟨hq.ne'⟩
  unfold transform
  apply sum_congr rfl
  intro n _
  congr 1
  change phase n ((a : ℚ)/q) = phase n (((a%q : ℕ) : ℚ)/q)
  rw [phaseFraction,phaseFraction,ZMod.natCast_mod]

private theorem eventualSquare (x : ℚ) (γ θ : ℝ) (hlt : γ < θ) (h : boundAt x γ) :
    ∃ U : ℕ, ∀ u : ℕ, U ≤ u → ‖transform false (u^2) x‖ ≤ ((u : ℝ)^2+1)^θ := by
  obtain ⟨C,_,hc⟩ := h
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^(θ-γ)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hlt)).comp tendsto_natCast_atTop_atTop
  obtain ⟨U,hU⟩ := eventually_atTop.mp (ht.eventually_ge_atTop C)
  refine ⟨U,fun u hu => ?_⟩
  let X : ℝ := (u : ℝ)^2+1
  have hX : 0 < X := by dsimp [X]; positivity
  have g : C ≤ X^(θ-γ) := (hU u hu).trans (Real.rpow_le_rpow (Nat.cast_nonneg _)
    (show (u : ℝ) ≤ X by dsimp [X]; nlinarith [sq_nonneg ((u : ℝ)-1/2)]) (sub_nonneg.mpr hlt.le))
  have hh := hc (u^2)
  rw [Nat.cast_pow] at hh
  calc
    _ ≤ C*X^γ := hh
    _ ≤ X^(θ-γ)*X^γ := mul_le_mul_of_nonneg_right g (Real.rpow_nonneg hX.le _)
    _ = _ := by rw [← Real.rpow_add hX,sub_add_cancel]

theorem solution : escapes ↔ squarefullTests := by
  constructor
  · intro H q hq _ a ha _ θ hl hr
    have hp : (0 : ℚ) < q := by exact_mod_cast hq
    exact H _ (div_nonneg (Nat.cast_nonneg _) hp.le)
      ((div_lt_one hp).mpr (by exact_mod_cast ha)) θ hl hr
  · intro H x hx _ θ hl hr
    let γ : ℝ := (1/2+θ)/2
    have hγ : 1/2 < γ := by dsimp [γ]; linarith
    have hγθ : γ < θ := by dsimp [γ]; linarith
    have all (q : ℕ) (hq : 0 < q) : level q γ := by
      apply (GRH.moebius_frequency_bounds_lift_to_squarefull_denominators q hq γ (by linarith)).2
      intro d _ hdq hd a ha
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq (pow_pos hq _)
      apply fromSquares _ _ hγ
      obtain ⟨U,hU⟩ := H d hd0 hd (a%d) (Nat.mod_lt _ hd0)
        ((ZMod.coprime_mod_iff_coprime a d).mpr ha) γ hγ (hγθ.trans hr)
      exact ⟨U,fun u hu => (reduceNumerator d hd0 a (u^2)) ▸ hU u hu⟩
    have hn := Rat.num_nonneg.mpr hx
    have hc : ((x.num.natAbs : ℕ) : ℤ) = x.num := (Int.natCast_natAbs _).trans (abs_of_nonneg hn)
    have eq : (x.num.natAbs : ℚ)/x.den = x := by
      have h := congrArg (fun z : ℤ => (z : ℚ)) hc
      simp only [Int.cast_natCast] at h
      rw [h,Rat.num_div_den]
    have h := all x.den x.den_pos x.num.natAbs x.reduced
    rw [eq] at h
    exact eventualSquare x γ θ hγθ h
