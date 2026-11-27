-- Prove2me | solution 1 for GRH.failure_of_centered_bound_forces_a_recurrent_fixed_rational_frequency
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T05:28:44.147797+00:00
-- url     : https://prove2.me/submissions/77cbdaf6-d0d3-434d-97b7-ecd2d0125aed

import Theorems.Thm_GRH_centered_bilinear_additive_modes_and_residue_inversion
import Theorems.Thm_GRH_moebius_large_sieve_energy_and_exceptional_farey_count
import Theorems.Thm_GRH_centered_moebius_bound_iff_square_mertens_residual
import Theorems.Thm_GRH_reduced_moebius_principal_bounds_of_dirichlet_prefixes
import Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_moebius_bound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/- The square-root power comparison follows the public square-residue proof
https://prove2.me/submissions/0176d409-98bf-44bc-b6fe-85633680ae6d .
Dirichlet-prefix convergence and reduced harmonic decay are imported as separate proved estimates. -/

open Finset Filter GRH.AdditiveMoebiusSpectrum

private theorem squareConstant (H : escapes) (x : ℚ) (hx : 0 ≤ x) (hx' : x < 1)
    (θ : ℝ) (hl : 1/2 < θ) (hr : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ, ‖transform false (u^2) x‖ ≤ C*((u : ℝ)^2+1)^θ := by
  obtain ⟨U,hU⟩ := H x hx hx' θ hl hr
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

private def ordinary (N : ℕ) : ℂ := ∑ n ∈ range (N+1), (ArithmeticFunction.moebius n : ℂ)

private theorem atZero (N : ℕ) : transform false N 0 = ordinary N := by
  simp [transform,ordinary,weight]

private theorem ordinaryBound (H : escapes) (θ : ℝ) (hl : 1/2 < θ) (hr : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ‖ordinary N‖ ≤ C*((N : ℝ)+1)^θ := by
  obtain ⟨C,hC,hs⟩ := squareConstant H 0 (by norm_num) (by norm_num) θ hl hr
  refine ⟨C+2,by linarith,fun N => ?_⟩
  let u := N.sqrt
  have hsquare : u^2 ≤ N := Nat.sqrt_le' N
  have hsreal : (u : ℝ)^2 ≤ N := by exact_mod_cast hsquare
  have hj : N-u^2 ≤ 2*u := by
    have h : N ≤ u^2+2*u := by simpa [u,pow_two,two_mul,add_assoc] using Nat.sqrt_le_add N
    omega
  have hprefix := hs u
  rw [atZero] at hprefix
  have hgrowth := Real.rpow_le_rpow (show 0 ≤ (u : ℝ)^2+1 by positivity)
    (show (u : ℝ)^2+1 ≤ (N : ℝ)+1 by linarith) (show 0 ≤ θ by linarith)
  have hroot : (u : ℝ) ≤ ((N : ℝ)+1)^θ := by
    calc
      _ ≤ Real.sqrt ((N : ℝ)+1) := (Real.le_sqrt (by positivity) (by positivity)).mpr (by linarith)
      _ ≤ _ := by rw [Real.sqrt_eq_rpow];exact Real.rpow_le_rpow_of_exponent_le (by simp) hl.le
  have hinc (s j : ℕ) : ‖ordinary (s+j)-ordinary s‖ ≤ (j : ℝ) := by
    unfold ordinary
    rw [show s+j+1=s+1+j by omega,sum_range_add,add_sub_cancel_left]
    calc
      _ ≤ ∑ k ∈ range j, ‖(ArithmeticFunction.moebius (s+1+k) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ range j, (1 : ℝ) := by
        apply sum_le_sum
        intro k _
        have hh : |(ArithmeticFunction.moebius (s+1+k) : ℝ)| ≤ 1 := by
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=s+1+k))
        simpa using hh
      _ = _ := by simp
  have inc := hinc (u^2) (N-u^2)
  rw [Nat.add_sub_of_le hsquare] at inc
  have jreal : ((N-u^2 : ℕ) : ℝ) ≤ 2*(u : ℝ) := by exact_mod_cast hj
  have tri : ‖ordinary N‖ ≤ ‖ordinary N-ordinary (u^2)‖ + ‖ordinary (u^2)‖ := by
    calc
      _ = ‖ordinary N-ordinary (u^2)+ordinary (u^2)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  linarith only [tri,inc,jreal,hroot,hprefix,mul_le_mul_of_nonneg_left hgrowth hC]

private theorem prefixBound (H : escapes) (σ : ℝ) (hl : 1/2 < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, |∑ j ∈ range n,
      (ArithmeticFunction.moebius j : ℝ)*(j : ℝ)^(-σ)| ≤ B := by
  have hM (ε : ℝ) (hε : 0 < ε) : Asymptotics.IsBigO atTop
      (fun N : ℕ => ∑ n ∈ Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
      (fun N : ℕ => (N : ℝ)^(1/2+ε)) := by
    let θ := min (3/4 : ℝ) (1/2+ε)
    have ht : 1/2 < θ := lt_min (by norm_num) (by linarith)
    have ht' : θ < 1 := (min_le_left ..).trans_lt (by norm_num)
    obtain ⟨C,hC,hs⟩ := ordinaryBound H θ ht ht'
    refine Asymptotics.IsBigO.of_bound (C*2^θ) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 := Nat.cast_nonneg (α:=ℝ) n
    have hi : range (n+1) = insert 0 (Icc 1 n) := by ext k; simp; omega
    have eq : (∑ k ∈ Icc 1 n, (ArithmeticFunction.moebius k : ℂ)) = ordinary n := by
      simp [ordinary,hi]
    change ‖∑ k ∈ Icc 1 n, (ArithmeticFunction.moebius k : ℂ)‖ ≤ (C*2^θ)*‖(n : ℝ)^(1/2+ε)‖
    rw [eq,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hn0 _)]
    calc
      _ ≤ C*((n : ℝ)+1)^θ := hs n
      _ ≤ C*((2 : ℝ)*n)^θ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)) hC
      _ = (C*2^θ)*(n : ℝ)^θ := by rw [Real.mul_rpow (by norm_num) hn0]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn' (min_le_right ..)) (by positivity)
  obtain ⟨L,hL⟩ := moebius_dirichlet_partialSum_tendsto_of_moebius_bound σ hl hM
  obtain ⟨B,hB⟩ := (Metric.isBounded_range_of_tendsto _ hL.abs).bddAbove
  refine ⟨max 0 B,le_max_left ..,?_⟩
  intro n
  cases n with
  | zero => simpa only [range_zero,sum_empty,abs_zero] using le_max_left (0 : ℝ) B
  | succ n =>
    have hi : range (n+1) = insert 0 (Icc 1 n) := by ext k; simp; omega
    rw [hi,sum_insert (by simp)]
    simp only [ArithmeticFunction.map_zero,Int.cast_zero,zero_mul,zero_add]
    exact (hB ⟨n,rfl⟩).trans (le_max_right ..)

private theorem residueBound (H : escapes) (q : ℕ) [NeZero q] (a : ZMod q)
    (σ : ℝ) (hl : 1/2 < σ) (hr : σ < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ, |fiber a (u^2) (weight false (u^2))| ≤ D*((u : ℝ)^2+1)^σ := by
  classical
  have hq : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have bounds (h : ZMod q) := squareConstant H (angle h)
    (div_nonneg (Nat.cast_nonneg _) hq.le)
    ((div_lt_one hq).mpr (by exact_mod_cast ZMod.val_lt h)) σ hl hr
  choose C hC hc using bounds
  refine ⟨∑ h, C h,sum_nonneg (fun h _ => hC h),fun u => ?_⟩
  let f := fiber a (u^2) (weight false (u^2))
  have inv := (GRH.centered_bilinear_additive_modes_and_residue_inversion q (u^2)).2.1 false a
  change (q : ℂ)*(f : ℂ) = _ at inv
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  calc
    |f| ≤ (q : ℝ)*|f| := le_mul_of_one_le_left (abs_nonneg _) hq1
    _ = ‖(q : ℂ)*(f : ℂ)‖ := by simp
    _ ≤ ∑ h : ZMod q, ‖ZMod.stdAddChar (-(a*h))*transform false (u^2) (angle h)‖ := by
      rw [inv]; exact norm_sum_le _ _
    _ = ∑ h : ZMod q, ‖transform false (u^2) (angle h)‖ := by simp [ZMod.stdAddChar_apply,Circle.norm_coe]
    _ ≤ ∑ h : ZMod q, C h*((u : ℝ)^2+1)^σ := sum_le_sum fun h _ => hc h u
    _ = _ := (sum_mul ..).symm

private theorem sqrtWeight (N : ℕ) (σ : ℝ) (hone : σ < 1) :
    (N : ℝ) * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2 ≤ ((N : ℝ) + 1) ^ σ := by
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hU : 0 < (N.sqrt : ℝ) + 1 := by positivity
  have hX : 0 < (N : ℝ) + 1 := by positivity
  have hsqrt : (N : ℝ) + 1 ≤ ((N.sqrt : ℝ) + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt' N
    have h' : N + 1 ≤ (N.sqrt + 1) ^ 2 := by simpa [Nat.succ_eq_add_one] using Nat.succ_le_iff.mpr h
    exact_mod_cast h'
  have hp : (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2 ≤
      ((N : ℝ) + 1) ^ (σ - 1) := by
    have h := Real.rpow_le_rpow_of_nonpos hX hsqrt (by linarith : σ - 1 ≤ 0)
    rw [← Real.rpow_natCast_mul hU.le] at h
    rw [← Real.rpow_mul_natCast hU.le]
    convert h using 1
    congr 1
    ring
  calc
    (N : ℝ) * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2
        ≤ (N : ℝ) * (((N : ℝ) + 1) ^ (σ - 1)) := mul_le_mul_of_nonneg_left hp hN
    _ ≤ ((N : ℝ) + 1) * (((N : ℝ) + 1) ^ (σ - 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hX.le _)
    _ = ((N : ℝ) + 1) ^ σ := by
      nth_rw 1 [← Real.rpow_one ((N : ℝ) + 1)]
      rw [← Real.rpow_add hX]
      congr 1
      ring

private theorem mainWeight (N : ℕ) (σ K x : ℝ) (hone : σ < 1)
    (hK : 0 ≤ K) (hx : |x| ≤ K * ((N.sqrt : ℝ) + 1) ^ (σ - 1)) :
    (N : ℝ) * x ^ 2 ≤ K ^ 2 * ((N : ℝ) + 1) ^ σ := by
  have hs : x ^ 2 ≤ K ^ 2 * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2 := by
    have h := sq_le_sq₀ (abs_nonneg x) (by positivity : 0 ≤ K * ((N.sqrt : ℝ) + 1) ^ (σ - 1))
    have := h.mpr hx
    simpa only [sq_abs, mul_pow] using this
  calc
    (N : ℝ) * x ^ 2 ≤ (N : ℝ) *
        (K ^ 2 * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg N)
    _ = K ^ 2 * ((N : ℝ) * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2) := by ring
    _ ≤ K ^ 2 * ((N : ℝ) + 1) ^ σ :=
      mul_le_mul_of_nonneg_left (sqrtWeight N σ hone) (sq_nonneg K)


private theorem transfer (H : escapes) (q : ℕ) [NeZero q] (a : ZMod q)
    (σ : ℝ) (hl : 1/2 < σ) (hr : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear q a N| ≤ C*((N : ℝ)+1)^σ := by
  obtain ⟨D,hD,hd⟩ := residueBound H q a σ hl hr
  obtain ⟨B,hB,hb⟩ := prefixBound H σ hl
  obtain ⟨K,hK,harm,_⟩ := GRH.reduced_moebius_principal_bounds_of_dirichlet_prefixes
    q σ B hl hr hB hb
  apply (GRH.centered_moebius_bound_iff_square_mertens_residual q a σ hl.le).2
  let v := 1/(q : ℝ)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  refine ⟨D+v*K^2,by positivity,fun u => ?_⟩
  let X := ((u : ℝ)^2+1)^σ
  let t := GRH.reducedMoebiusHarmonic q u
  have row := hd u
  simp only [fiber,weight,Bool.false_eq_true,false_and,if_false] at row
  have main := mainWeight (u^2) σ K (GRH.reducedMoebiusHarmonic q ((u^2).sqrt)) hr hK
    (harm ((u^2).sqrt))
  rw [Nat.sqrt_eq',Nat.cast_pow] at main
  have ht : |(u : ℝ)^2*(v*t^2)| ≤ v*K^2*X := by
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hv (sq_nonneg _)))]
    calc
      _ = v*((u : ℝ)^2*t^2) := by ring
      _ ≤ v*(K^2*X) := mul_le_mul_of_nonneg_left main hv
      _ = _ := by ring
  calc
    _ ≤ |∑ k ∈ range (u^2+1), if (k : ZMod q)=a then (ArithmeticFunction.moebius k : ℝ) else 0|
          + |(u : ℝ)^2*(v*t^2)| := abs_add_le _ _
    _ ≤ D*X + v*K^2*X := add_le_add row ht
    _ = _ := by change _ = (D+v*K^2)*X; ring

private theorem memFarey {x : ℚ} {Q : ℕ} :
    x ∈ fareySet Q ↔ 0 ≤ x ∧ x < 1 ∧ x.den ≤ Q := by
  classical
  refine ⟨fun h => (mem_filter.mp h).2,?_⟩
  rintro ⟨hx,hx1,hd⟩
  have hn : 0 ≤ x.num := Rat.num_nonneg.mpr hx
  have hc : ((x.num.natAbs : ℕ) : ℤ) = x.num := (Int.natCast_natAbs _).trans (abs_of_nonneg hn)
  have hrat : (x.num.natAbs : ℚ)/x.den = x := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) hc
    simp only [Int.cast_natCast] at h
    rw [h,Rat.num_div_den]
  have dp : (0 : ℚ) < x.den := by exact_mod_cast x.den_pos
  have hlt : x.num.natAbs < x.den := by
    have hr : (x.num.natAbs : ℚ)/x.den < 1 := by rwa [hrat]
    exact_mod_cast (div_lt_one dp).mp hr
  apply mem_filter.mpr
  refine ⟨mem_image.mpr ⟨(x.num.natAbs,x.den),?_,hrat⟩,hx,hx1,hd⟩
  exact mem_product.mpr ⟨mem_range.mpr (hlt.trans_le hd),mem_Icc.mpr ⟨x.den_pos,hd⟩⟩

private theorem sparse (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ) (hu : 2 ≤ u) :
    ((exceptional false (u^2) (fareySet u) (((u : ℝ)^2+1)^θ)).card : ℝ) ≤
      18*(u : ℝ)^(4-4*θ) := by
  have hh := ((GRH.moebius_large_sieve_energy_and_exceptional_farey_count u (u^2) hu).1
    false (fareySet u) (fun _ hx => memFarey.mp hx)).2 (((u : ℝ)^2+1)^θ) (by positivity)
  let c : ℝ := ((exceptional false (u^2) (fareySet u) (((u : ℝ)^2+1)^θ)).card : ℝ)
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast hu
  have hp : (0 : ℝ) < u := by linarith
  have hs : (u : ℝ)^(4*θ) ≤ (((u : ℝ)^2+1)^θ)^2 := by
    have h := Real.rpow_le_rpow (sq_nonneg (u : ℝ))
      (show (u : ℝ)^2 ≤ (u : ℝ)^2+1 by linarith) hθ
    calc
      _ = (((u : ℝ)^2)^θ)^2 := by
        rw [← Real.rpow_mul_natCast (by positivity),← Real.rpow_natCast_mul hp.le]
        congr 1
        push_cast
        ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) h 2
  rw [Nat.cast_pow] at hh
  change c * _ ≤ _ at hh
  have hub : c*(u : ℝ)^(4*θ) ≤ 18*(u : ℝ)^4 := by
    have hsmall : 13 ≤ 4*(u : ℝ)^2 := by nlinarith [sq_nonneg ((u : ℝ)-2)]
    exact (mul_le_mul_of_nonneg_left hs hc).trans
      (hh.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hsmall) (sq_nonneg (u : ℝ))]))
  have cancel : (18*(u : ℝ)^(4-4*θ))*(u : ℝ)^(4*θ) = 18*(u : ℝ)^4 := by
    rw [mul_assoc,← Real.rpow_add hp,show 4-4*θ+4*θ=(4:ℝ) by ring]
    norm_cast
  rw [← cancel] at hub
  exact le_of_mul_le_mul_right hub (Real.rpow_pos_of_pos hp _)

theorem solution :
    (escapes → ∀ (q : ℕ) [NeZero q] (a : ZMod q) (σ : ℝ), 1/2 < σ → σ < 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
        |GRH.centeredMoebiusBilinear q a N| ≤ C*((N : ℝ)+1)^σ) ∧
    (∀ (θ : ℝ), 0 ≤ θ → ∀ u : ℕ, 2 ≤ u →
      ((exceptional false (u^2) (fareySet u) (((u : ℝ)^2+1)^θ)).card : ℝ) ≤
        18*(u : ℝ)^(4-4*θ)) ∧
    (¬ GRH.OneSidedMoebius.centeredBound → ∃ x : ℚ, 0 ≤ x ∧ x < 1 ∧
      ∃ θ : ℝ, 1/2 < θ ∧ θ < 1 ∧ ∀ U : ℕ, ∃ u : ℕ, U ≤ u ∧
        x ∈ exceptional false (u^2) (fareySet u) (((u : ℝ)^2+1)^θ)) := by
  refine ⟨transfer,sparse,?_⟩
  intro h
  have no : ¬ escapes := fun he => h (fun q _ a _ σ hl hr => transfer he q a σ hl hr)
  unfold escapes at no
  push Not at no
  obtain ⟨x,hx,hx1,θ,hl,hr,h⟩ := no
  refine ⟨x,hx,hx1,θ,hl,hr,fun U => ?_⟩
  obtain ⟨u,hu,he⟩ := h (max U x.den)
  exact ⟨u,(le_max_left ..).trans hu,mem_filter.mpr
    ⟨memFarey.mpr ⟨hx,hx1,(le_max_right ..).trans hu⟩,he⟩⟩
