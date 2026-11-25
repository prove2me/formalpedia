-- Prove2me | solution 1 for DetDLP.d1_schedule_active_and_exponent
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T06:43:04.229503+00:00
-- url     : https://prove2.me/submissions/ddae2dfb-05c5-4c26-a5fb-f565df1945a0

import Definitions.Def_DetDLP_D1Schedule
import Theorems.Thm_DetDLP_d1_exact_radius_scan_poly
import Theorems.Thm_DetDLP_cauchy_hermite_recursion_budget

set_option autoImplicit false
namespace DetDLP.D1
open AppendixD4

theorem rootScan_eq (r : ℕ) : rootScan r = r.sqrt := by
  have aux (k : ℕ) : ((List.range k).filter (fun j => decide ((j+1)*(j+1) ≤ r))).length = min k r.sqrt := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ,List.filter_append,List.length_append,ih]
      by_cases h : k+1 ≤ r.sqrt
      · simp [Nat.le_sqrt.mp h]; omega
      · have hh := mt Nat.le_sqrt.mpr h; simp [hh]; omega
  simpa [rootScan,min_eq_right (Nat.sqrt_le_self r)] using aux r

theorem depth_spec (m H : ℕ) :
    m / 8^(depth m H) ≤ H ∧ ∀ d < depth m H, H < m/8^d := by
  let k := fuel m
  have existsStop : ∃ j, m/8^j ≤ H := ⟨k,by
    have h : m < 8^k := (Nat.lt_size_self m).trans_le (by
      dsimp [k,fuel]; rw [Nat.size_eq_bits_len]; exact (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)).trans (Nat.pow_le_pow_left (by decide) _))
    simp [Nat.div_eq_of_lt h]⟩
  let D := Nat.find existsStop
  have hD : m/8^D ≤ H := Nat.find_spec existsStop
  have pre (d : ℕ) (hd : d < D) : H < m/8^d := lt_of_not_ge (Nat.find_min existsStop hd)
  have post (d : ℕ) (hd : D ≤ d) : m/8^d ≤ H := (Nat.div_le_div_left (Nat.pow_le_pow_right (by decide) hd) (by positivity)).trans hD
  have hk : D ≤ k := by
    apply Nat.find_min'; have h : m < 8^k := (Nat.lt_size_self m).trans_le (by
      dsimp [k,fuel]; rw [Nat.size_eq_bits_len]; exact (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)).trans (Nat.pow_le_pow_left (by decide) _))
    simp [Nat.div_eq_of_lt h]
  have aux (n : ℕ) (hn : n ≤ k) : ((List.range n).filter fun d => decide (H < m / 8^(min d k))).length = min n D := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ,List.filter_append,List.length_append,ih (by omega),List.filter_singleton]
      rw [min_eq_left (by omega : n ≤ k)]
      by_cases h : n < D
      · simp [pre _ h]; omega
      · have hh : ¬ H < m / 8^n := Nat.not_lt.mpr (post n (by omega))
        simp [hh]; omega
  have eqD : depth m H = D := by simpa [depth,k,min_eq_right hk] using aux k le_rfl
  simpa only [eqD] using And.intro hD pre

theorem depth_fuel (m H : ℕ) : depth m H ≤ fuel m := by
  simpa [depth] using List.length_filter_le (fun d => decide (H < m / 8^(min d (fuel m)))) (List.range (fuel m))

theorem root_large (C r : ℕ) (hr : threshold C ≤ r) : 2^24 * (C+2)^2 ≤ r.sqrt := by
  rw [Nat.le_sqrt']; simpa [threshold,mul_pow,← pow_mul] using hr

theorem cube_bound (C b r d : ℕ) (hC : 0 < C) (hb : 0 < b) (hr : threshold C ≤ r)
    (hd : d < depth (C*b) (horizon b r)) : (2^d)^3 ≤ C*r.sqrt := by
  have ht := root_large C r hr
  have ht' : 0 < r.sqrt := lt_of_lt_of_le (by positivity) ht
  have ha := (depth_spec (C*b) (horizon b r)).2 d hd
  rw [horizon,rootScan_eq,max_eq_right ht'] at ha
  have hm := (Nat.le_div_iff_mul_le (by positivity : 0 < 8^d)).mp ha.le
  have hdiv := (Nat.div_lt_iff_lt_mul ht').mp (Nat.lt_succ_self (b/r.sqrt))
  have hh : b*8^d < C*r.sqrt*b := calc
    _ < ((b/r.sqrt+1)*r.sqrt)*8^d := Nat.mul_lt_mul_of_pos_right hdiv (by positivity)
    _ = ((b/r.sqrt+1)*8^d)*r.sqrt := by ring
    _ ≤ (C*b)*r.sqrt := Nat.mul_le_mul_right _ hm
    _ = _ := by ring
  rw [mul_comm b, Nat.mul_lt_mul_right hb] at hh
  rw [← pow_mul, mul_comm d 3,pow_mul]
  exact hh.le

theorem width_lower (C b r d : ℕ) (hC : 0 < C) (hb : 0 < b) (hr : threshold C ≤ r)
    (hd : d < depth (C*b) (horizon b r)) : r.sqrt ≤ width (C*b) r d := by
  let z := 2^d
  let t := r.sqrt
  have hc : z^3 ≤ C*t := cube_bound C b r d hC hb hr hd
  have ht : 2^24*(C+2)^2 ≤ t := root_large C r hr
  have ht' : 1024*C ≤ t := by dsimp [t] at *; nlinarith [sq_nonneg (C:ℤ),Nat.zero_le C]
  have hbig : 2^48 * (C+2)^4 ≤ r := hr
  have hq : 131072*z ≤ t := by
    by_contra! hn
    have hx : t^3 < (131072*z)^3 := Nat.pow_lt_pow_left hn (by decide)
    have hy : t^2 ≥ 131072^3 * C := by
      have hs := Nat.pow_le_pow_left ht 2
      have hv : 8*C ≤ (C+2)^4 := by nlinarith [Nat.zero_le (C^2),Nat.zero_le (C^3),Nat.zero_le (C^4)]
      calc _ ≤ 2^48*(C+2)^4 := by omega
           _ = (2^24*(C+2)^2)^2 := by ring
           _ ≤ t^2 := hs
    have hz := Nat.mul_le_mul_left (131072^3) hc
    have hw := Nat.mul_le_mul_right t hy
    nlinarith only [hx,hz,hw]
  unfold width; rw [min_eq_left (hd.le.trans (depth_fuel ..)),Nat.div_div_eq_div_mul]
  exact (Nat.le_div_iff_mul_le (by positivity)).mpr ((Nat.mul_le_mul_left t hq).trans (Nat.sqrt_le r))

theorem real_horizon {b r : ℕ} (hr : 1 ≤ r) (hrb : r ≤ b) :
    (horizon b r : ℝ) ≤ 3 * b / Real.sqrt r := by
  let t := r.sqrt
  have ht : 1 ≤ t := Nat.le_sqrt.mpr (by omega)
  have htr : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hr' : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hs := Real.sqrt_pos.mpr hr'
  have hsq : Real.sqrt (r:ℝ) ≤ (t:ℝ)+1 := by
    rw [Real.sqrt_le_iff]; exact ⟨by positivity, by exact_mod_cast (Nat.lt_succ_sqrt' r).le⟩
  have h1 : Real.sqrt (r:ℝ) ≤ b := by
    have hb' : (r:ℝ) ≤ b := by exact_mod_cast hrb
    have h2 : (1:ℝ) ≤ r := by exact_mod_cast hr
    nlinarith [Real.sq_sqrt hr'.le]
  have hdiv : ((b/t:ℕ):ℝ) * t ≤ b := by exact_mod_cast Nat.div_mul_le_self b t
  unfold horizon; rw [rootScan_eq,max_eq_right ht]; change (↑(b/t+1):ℝ) ≤ _
  rw [le_div_iff₀ hs]; push_cast
  have h3 : ((b/t:ℕ):ℝ)*Real.sqrt r ≤ (b/t:ℕ)*(2*(t:ℝ)) := by gcongr; linarith
  nlinarith

theorem exp_full {C b r : ℕ} (hC : 0 < C) (hb : 0 < b) (hr : threshold C ≤ r) (hrb : r ≤ b) :
    exponent (fullSchedule b r (C*b) (horizon b r)) b ≤ 1024*b / Real.sqrt r := by
  let m := C*b
  let H := horizon b r
  let D := depth m H
  have ht := root_large C r hr
  have h1 : 1 ≤ r.sqrt := lt_of_lt_of_le (by positivity) ht
  have hr1 : 1 ≤ r := h1.trans (Nat.sqrt_le_self r)
  have hr' : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hs := Real.sqrt_pos.mpr hr'
  have hH := real_horizon hr1 hrb
  have hu (d : ℕ) (hd : d < D) : (r:ℝ) / 262144 * ((1:ℝ)/2)^d ≤ width m r d := by
    let z := 2^d
    let K := 131072*z
    let u := width m r d
    have hk : 0 < K := by dsimp [K,z]; positivity
    have hfix : u = r/K := by dsimp [u,K,z,width]; rw [min_eq_left (hd.le.trans (depth_fuel ..)),Nat.div_div_eq_div_mul]
    have hu1 : 1 ≤ u := h1.trans (width_lower C b r d hC hb hr hd)
    have hu2 : r < (u+1)*K := (Nat.div_lt_iff_lt_mul hk).mp (by omega)
    have hx : r ≤ (2*u)*K := hu2.le.trans (Nat.mul_le_mul_right _ (by omega))
    have hy : (r:ℝ) ≤ (2*(u:ℝ))*(131072*(2:ℝ)^d) := by exact_mod_cast hx
    change _ ≤ (u:ℝ); rw [one_div,inv_pow,← div_eq_mul_inv,div_div,div_le_iff₀ (by positivity)]; linarith
  have hle : ∑ d ∈ Finset.range D, ((b:ℝ)/8^d)/Real.sqrt (width m r d) ≤
      ∑ d ∈ Finset.range (D+1), ((b:ℝ)*((1:ℝ)/8)^d)/Real.sqrt ((r/262144:ℝ)*((1:ℝ)/2)^d) := by
    apply le_trans (Finset.sum_le_sum (g:=fun d => ((b:ℝ)*((1:ℝ)/8)^d)/Real.sqrt ((r/262144:ℝ)*((1:ℝ)/2)^d)) _)
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ _)) (by intros; positivity)
    · intro d hd; rw [one_div,inv_pow,← div_eq_mul_inv]; apply div_le_div_of_nonneg_left (by positivity) (by positivity) (Real.sqrt_le_sqrt (hu d (Finset.mem_range.mp hd)))
  have hs' : Real.sqrt ((r:ℝ)/262144) = Real.sqrt (r:ℝ)/512 := by rw [Real.sqrt_div hr'.le]; norm_num
  have budget := cauchy_hermite_recursion_budget.1 D b (r/262144) (by positivity) (by positivity)
  rw [hs'] at budget
  change (H:ℝ) + ∑ d : Fin D, ((b:ℝ)/8^(0+d.val))/Real.sqrt (width m r d.val) ≤ _
  simp only [zero_add]; rw [Fin.sum_univ_eq_sum_range (fun d : ℕ => ((b:ℝ)/8^d)/Real.sqrt (width m r d)) D]
  have hsum := hle.trans budget
  have hz : (4/3:ℝ)*(b / (Real.sqrt r / 512)) = (2048/3:ℝ)*(b/Real.sqrt r) := by ring
  rw [hz] at hsum
  change (H:ℝ) ≤ _ at hH
  have hnon : (0:ℝ) ≤ b / Real.sqrt r := by positivity
  linarith [show (1024:ℝ)*b / Real.sqrt r = 1024*(b / Real.sqrt r) by ring,
    show 3*(b:ℝ) / Real.sqrt r = 3*(b / Real.sqrt r) by ring]

theorem scan_bounds (b deg : ℕ) (hb : 2 ≤ b) : 1 ≤ radiusScan (b,deg) ∧ radiusScan (b,deg) ≤ b := by
  constructor
  · rw [d1_exact_radius_scan_poly.1 _ _ hb]; exact le_max_left ..
  · unfold radiusScan
    rw [List.range_succ_eq_map,List.filter_cons]; simp only [show scanTest b deg 0 = false by simp [scanTest],Bool.false_eq_true,if_false]
    apply (List.length_filter_le ..).trans; rw [List.length_map,List.length_range,Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem exp_make {C b ne deg : ℕ} (hC : 0 < C) (hb : 2 ≤ b) (hne : ne ≤ C*b) :
    exponent (makeSchedule C b ne deg) b ≤ ((C*threshold C+1024:ℕ):ℝ)*b / Real.sqrt (radiusScan (b,deg)) := by
  let r := radiusScan (b,deg)
  have ⟨hr,hrb⟩ := scan_bounds b deg hb
  have hs : 0 < Real.sqrt (r:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < r by omega))
  have hc : (1024:ℝ) ≤ (C*threshold C+1024:ℕ) := by exact_mod_cast Nat.le_add_left 1024 _
  have heTriv : exponent (trivialSchedule ne) b = ne := by
    change (ne:ℝ) + (∑ d : Fin 0, _) = ne
    rw [Fin.sum_univ_zero,add_zero]
  unfold makeSchedule; dsimp only; split
  · rename_i h; rw [heTriv]
    rcases h with h|h
    · have ht : Real.sqrt (r:ℝ) ≤ threshold C := by
        have h2 : (r:ℝ) < threshold C := by exact_mod_cast h
        have h3 : (1:ℝ) ≤ r := by exact_mod_cast hr
        nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ r by positivity)]
      rw [le_div_iff₀ hs]; have he : (ne:ℝ) ≤ (C:ℝ)*b := by exact_mod_cast hne
      apply (mul_le_mul he ht (by positivity) (by positivity)).trans; push_cast; nlinarith
    · refine (Nat.cast_le.mpr h).trans ((real_horizon hr hrb).trans ?_)
      gcongr; linarith
  · rename_i h; exact (exp_full hC (by omega) (by simp only [not_or,not_lt] at h; exact h.1) hrb).trans (by gcongr)

open AppendixD4
theorem ceil_nine_tenths_le (b k : ℕ) :
    ⌈(b:ℝ)^((9:ℝ)/10)⌉₊ ≤ k ↔ b^9 ≤ k^10 := by
  rw [Nat.ceil_le, ← pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg k) (by decide : 10 ≠ 0)]
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg b)]
  norm_num
  norm_cast

theorem radiusTest_correct (b deg j : ℕ) (hb : 2 ≤ b) (hj : 2 ≤ j) :
    radiusTest b deg j = true ↔ j ≤ radius b deg := by
  let q := max deg ⌈(b:ℝ)^((9:ℝ)/10)⌉₊
  have hbr : (1:ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hp : 0 < (q:ℝ) := by
    have h1 := (Real.one_le_rpow hbr (by norm_num : (0:ℝ) ≤ 9/10)).trans (Nat.le_ceil _)
    have h2 : (⌈(b:ℝ)^((9:ℝ)/10)⌉₊ : ℝ) ≤ q := by exact_mod_cast le_max_right _ _
    linarith
  change decide _ = true ↔ j ≤ max 1 ⌊Real.logb 2 ((b:ℝ) / q)⌋₊
  rw [decide_eq_true_eq,le_max_iff,or_iff_right (by omega : ¬ j ≤ 1)]
  rw [Nat.le_floor_iff' (by omega), Real.le_logb_iff_rpow_le (by norm_num) (div_pos (by linarith) hp), Real.rpow_natCast, le_div_iff₀ hp]
  rw [← ceil_nine_tenths_le, ← max_le_iff]
  change q ≤ b / 2^j ↔ _
  rw [Nat.le_div_iff_mul_le (by positivity),mul_comm q]
  norm_cast



private theorem geom_div (n k : ℕ) {q : ℕ} (hq : 2 ≤ q) : ∑ j ∈ Finset.range k, n/q^j ≤ 2*n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ']; simp only [pow_zero,Nat.div_one]
    have h (j : ℕ) : n/q^(j+1) = (n/q)/q^j := by rw [Nat.div_div_eq_div_mul,pow_succ'];
    simp_rw [h]; have h1 := ih (n/q); have h2 := Nat.mul_div_le n q
    nlinarith [Nat.mul_le_mul_right (n/q) hq]

private def preShift (m r d : ℕ) := 2 * ∑ j ∈ Finset.range d, width m r j

private theorem shift_eq {m r H d : ℕ} (hd : d < depth m H) :
    shift (widths m r (depth m H)) d = preShift m r d + 2*width m r d := by
  unfold shift widths preShift
  rw [← List.map_take,List.take_range,min_eq_left hd,← List.sum_toFinset _ List.nodup_range]
  rw [List.toFinset_range,Finset.sum_range_succ,mul_add]

private theorem shift_prev {m r H j d : ℕ} (hj : j < d) (hd : d < depth m H) :
    shift (widths m r (depth m H)) j ≤ preShift m r d := by
  unfold shift widths preShift
  rw [← List.map_take,List.take_range,min_eq_left (by omega),← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]; gcongr
  exact hj

private theorem shift_small {m r H d : ℕ} (hd : d < depth m H) :
    shift (widths m r (depth m H)) d * 32768 ≤ r := by
  unfold shift widths
  rw [← List.map_take,List.take_range,min_eq_left hd,← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  have he : ∑ j ∈ Finset.range (d+1), width m r j = ∑ j ∈ Finset.range (d+1), (r/131072)/2^j := by
    apply Finset.sum_congr rfl; intro j hj; rw [Finset.mem_range] at hj
    rw [width,min_eq_left ((by omega : j ≤ d).trans (hd.le.trans (depth_fuel ..)))]
  rw [he]; have := geom_div (r/131072) (d+1) (q:=2) le_rfl
  omega

private theorem small_pow (n : ℕ) (hn : 10 ≤ n) : n^3 ≤ 2^n := by
  induction n,hn using Nat.le_induction with
  | base => decide
  | succ n hn ih => rw [pow_succ (2:ℕ)]; nlinarith [Nat.mul_le_mul_left (n*n) hn, Nat.mul_le_mul_left n hn]

private theorem poly_exp (a u i : ℕ) (hu : 1 ≤ u) (hau : 2*u ≤ a) (hi : i < u) :
    (a+1)*u ≤ 64*tileScale a i := by
  let v := a-i
  have hv : u ≤ v := by dsimp [v]; omega
  have hv' : a+1 ≤ 2*v+1 := by dsimp [v]; omega
  change _ ≤ 64*2^v
  by_cases hk : 10 ≤ v
  · have hx := small_pow v hk; nlinarith [Nat.mul_le_mul hv' hv, Nat.mul_le_mul_left (v*v) hk]
  · have hp (k : ℕ) (h : k < 10) : (2*k+1)*k ≤ 64*2^k := by interval_cases k <;> decide
    exact (Nat.mul_le_mul hv' hv).trans (hp _ (by omega))

private theorem inc_const {M a u i : ℕ} (hu : 0 < u) (hum : u ≤ M) (hau : 2*u ≤ a) (hi : i < u) :
    increase M a u i * u ≤ 544*M*tileScale a i := by
  have hmult : mult M u * u ≤ 4*M := (Nat.div_mul_le_self _ _).trans (by omega)
  have h1 := Nat.mul_le_mul_right (tileScale a i) hmult
  have h2 := Nat.mul_le_mul_left M (poly_exp a u i hu hau hi)
  unfold increase; nlinarith only [h1,h2]

private theorem inc_top {M a u : ℕ} (hu : 0 < u) (hum : u ≤ M) : increase M a u 0 ≤ 40*M*2^a := by
  have h1 : mult M u ≤ 4*M := (Nat.div_le_self _ _).trans (by omega)
  have h2 : a+1 ≤ 2^a := Nat.lt_two_pow_self
  unfold increase tileScale; rw [Nat.sub_zero]; nlinarith [Nat.mul_le_mul_right (2^a) h1,Nat.mul_le_mul_left M h2]

private theorem packing_nums {b r a u M : ℕ} (hrs : 10 ≤ r.sqrt) (hM : horizon b r < M)
    (ha : a*32768 ≤ r) (hau : 2*u ≤ a) (hcp : 2^r ≤ b/2^r) :
    u ≤ M ∧ 2*64^(4*a)*(b/2^r) ≤ M ∧ 2^a*64^(2*a) ≤ M ∧ 2*2^a ≤ b/2^r := by
  let t := r.sqrt
  have ht : 0 < t := by omega
  rw [horizon,rootScan_eq,max_eq_right ht] at hM
  have hbM : b < M*t := (Nat.div_lt_iff_lt_mul ht).mp (by dsimp [t]; omega)
  have hsq : t*t ≤ r := Nat.sqrt_le r
  have hs : 2*t ≤ r := (Nat.mul_le_mul_right t (by omega : 2 ≤ t)).trans hsq
  have hp : 2*64^(4*a)*t ≤ 2^r := calc
    _ ≤ 2*64^(4*a)*2^t := Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le
    _ = 2^(1+24*a+t) := by rw [pow_add,pow_add]; congr 2; rw [show 64 = 2^6 by decide,← pow_mul]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hz := (Nat.mul_le_mul_right (b/2^r) hp).trans (Nat.mul_div_le b (2^r))
  have hpM : 2*64^(4*a)*(b/2^r) ≤ M := by
    apply (Nat.le_of_mul_le_mul_right (c:=t) _ ht); nlinarith only [hz,hbM]
  have hq : 2^a*64^(2*a) ≤ 64^(4*a) := by
    rw [show 64=2^6 by decide,← pow_mul,← pow_add,← pow_mul]; apply Nat.pow_le_pow_right (by decide); omega
  have hpos : 1 ≤ b/2^r := (by positivity : 0 < 2^r).trans_le hcp
  have hqM : 2^a*64^(2*a) ≤ M := hq.trans ((Nat.le_mul_of_pos_right (64^(4*a)) hpos).trans ((by rw [mul_assoc]; omega : 64^(4*a)*(b/2^r) ≤ 2*64^(4*a)*(b/2^r)).trans hpM))
  have huM : u ≤ M := (by omega : u ≤ a).trans ((Nat.lt_two_pow_self (n:=a)).le.trans ((Nat.le_mul_of_pos_right _ (by positivity : 0 < 64^(2*a))).trans hqM))
  refine ⟨huM,hpM,hqM,?_⟩
  rw [← pow_succ']; exact (Nat.pow_le_pow_right (by decide) (by omega : a+1 ≤ r)).trans hcp

private theorem precision {b r C P H M : ℕ} (hH : H = horizon b r) (hP : P ≤ C*b) (ht : 10 ≤ r.sqrt)
    (d : Fin (depth (C*b) H)) (hM : H < M) (hMu : ∀ j : Fin (depth (C*b) H), width (C*b) r j.val ≤ C*b/8^j.val)
    (hu : r.sqrt ≤ width (C*b) r d.val) (hum : width (C*b) r d.val ≤ M) :
    let s := fullSchedule b r (C*b) H
    ∀ i < s.u d, (inherited s (C*b) P d.val + increase M (s.a d) (s.u d) i)*(s.u d) ≤ (81*C+544)*M*tileScale (s.a d) i := by
  let m := C*b
  let D := depth m H
  let v := preShift m r d.val
  let u := width m r d.val
  let a := shift (widths m r D) d.val
  change r.sqrt ≤ u at hu
  have hpos : 0 < u := by omega
  have ha : a = v+2*u := shift_eq d.isLt
  have hs (j : Fin D) (hj : j.val < d.val) : increase (m/8^j.val) (shift (widths m r D) j.val) (width m r j.val) 0 ≤ 40*(m/8^j.val)*2^v := by
    have hw : 1 ≤ width m r j.val := by
      have hjd : min j.val (fuel m) ≤ min d.val (fuel m) := min_le_min_right _ hj.le
      exact hpos.trans_le (Nat.div_le_div_left (Nat.pow_le_pow_right (by decide) hjd) (by positivity))
    exact (inc_top hw (hMu j)).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (shift_prev hj d.isLt)))
  have hsum : ∑ j : Fin D, (if j.val < d.val then increase (m/8^j.val) (shift (widths m r D) j.val) (width m r j.val) 0 else 0) ≤ (40*2^v)*(2*m) := by
    apply le_trans (Finset.sum_le_sum (g:=fun j : Fin D => (40*2^v)*(m/8^j.val)) _)
    · rw [← Finset.mul_sum,Fin.sum_univ_eq_sum_range (fun j => m/8^j)]; exact Nat.mul_le_mul_left _ (geom_div m D (by decide : 2 ≤ 8))
    · intro j _; split_ifs with h
      · exact (hs j h).trans_eq (by ring)
      · omega
  have hi0 : inherited (fullSchedule b r m H) m P d.val ≤ 81*m*2^v := by
    unfold inherited; simp only [fullSchedule,zero_add]; change P + _ ≤ _
    have h1 : 0 < 2^v := by positivity
    change P ≤ m at hP
    apply (Nat.add_le_add hP hsum).trans
    nlinarith only [Nat.le_mul_of_pos_right m h1]
  dsimp only
  intro i hi
  change i < u at hi
  change (_ + increase M a u i)*u ≤ (81*C+544)*M*tileScale a i
  have ht' : 0 < r.sqrt := by omega
  rw [hH,horizon,rootScan_eq,max_eq_right ht'] at hM
  have hbM : b ≤ M*r.sqrt := ((Nat.div_lt_iff_lt_mul ht').mp (by omega)).le
  have hu2 : r.sqrt*u ≤ 2^u := (Nat.mul_le_mul_right u hu).trans ((by nlinarith [Nat.mul_le_mul_left (u*u) (show 1 ≤ u by omega)] : u*u ≤ u^3).trans (small_pow u (by omega)))
  have htS : 2^v * 2^u ≤ tileScale a i := by rw [← pow_add,tileScale]; apply Nat.pow_le_pow_right (by decide); omega
  have hbu : b*u ≤ M*2^u := calc
    _ ≤ (M*r.sqrt)*u := Nat.mul_le_mul_right _ hbM
    _ = M*(r.sqrt*u) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hu2
  have hh := Nat.mul_le_mul_right u hi0
  have h1 := Nat.mul_le_mul_left (81*C*2^v) hbu
  have h2 := Nat.mul_le_mul_left (81*C*M) htS
  have h3 := inc_const hpos hum (show 2*u ≤ a by omega) hi
  dsimp [m] at hh; nlinarith only [hh,h1,h2,h3]

private theorem points_bound {m M a : ℕ} (hM : M ≤ m) (ha : 2*2^a ≤ m) : points M a ≤ 2^kappa m := by
  let s := m.bits.length
  have hs : m < 2^s := by simpa [s,Nat.size_eq_bits_len] using Nat.lt_size_self m
  have hp : 2^(a+1) ≤ m := by simpa [pow_succ'] using ha
  unfold points
  calc _ ≤ m*m + 1 := Nat.add_le_add_right (Nat.mul_le_mul hM (by omega)) 1
       _ ≤ (2^s)*(2^s) := by nlinarith [Nat.mul_le_mul (show m+1 ≤ 2^s from hs) (show m+1 ≤ 2^s from hs)]
       _ = 2^(s+s) := (pow_add ..).symm
       _ ≤ _ := Nat.pow_le_pow_right (by decide) (by change s+s ≤ 4*(s+2); omega)

private theorem kappa_bound (C b : ℕ) (hC : 0 < C) (hb : 2 ≤ b) : 2^kappa (C*b) ≤ (b+2)^(4*(8*C+1)) := by
  let m := C*b
  have hpos : 0 < m := by dsimp [m]; positivity
  have hs : 0 < m.size := Nat.size_pos.mpr hpos
  have hsm : 2^m.size ≤ 2*m := by
    have hx := Nat.lt_size.mp (by omega : m.size-1 < m.size)
    calc 2^m.size = 2^(m.size-1+1) := by congr 1; omega
         _ ≤ _ := by rw [pow_succ']; gcongr
  have hc : 8*C ≤ (b+2)^(8*C) := (Nat.lt_two_pow_self (n:=8*C)).le.trans (Nat.pow_le_pow_left (by omega) _)
  rw [kappa,Nat.size_eq_bits_len,mul_comm 4,pow_mul,mul_comm 4,pow_mul]
  apply Nat.pow_le_pow_left; rw [pow_add,pow_succ (b+2)]
  have hh := Nat.mul_le_mul hc (show b ≤ b+2 by omega)
  change 2^m.size*2^2 ≤ _; dsimp [m] at hsm ⊢; nlinarith only [hh,hsm]

theorem active_make {C b e deg P : ℕ} (hC : 0 < C) (hb : 2 ≤ b) (hp : P ≤ C*b) :
    let s := makeSchedule C b e deg
    s.H < e → deg ≤ s.cap ∧ s.cap ≤ C*b ∧ 0 < s.κ ∧ 2^s.κ ≤ (b+2)^(4*(8*C+1)) ∧ Active s (C*b) P (81*C+544) := by
  dsimp only
  let r := radiusScan (b,deg)
  let H := horizon b r
  let m := C*b
  by_cases h : r < threshold C ∨ e ≤ H
  · have he : makeSchedule C b e deg = trivialSchedule e := if_pos h
    rw [he]; exact fun hn => (lt_irrefl e hn).elim
  · have he : makeSchedule C b e deg = fullSchedule b r m H := if_neg h
    rw [he]; intro _
    have hr : threshold C ≤ r := le_of_not_gt (fun h' => h (Or.inl h'))
    have ht : 10 ≤ r.sqrt := by have h := root_large C r hr; nlinarith [Nat.zero_le (C^2)]
    have h1 : 2 ≤ r := (by omega : 2 ≤ r.sqrt).trans (Nat.sqrt_le_self r)
    have test := (radiusTest_correct b deg r hb h1).mpr (d1_exact_radius_scan_poly.1 b deg hb).le
    rw [radiusTest,decide_eq_true_eq] at test
    let cap := b/2^r
    have hx : cap*2^r ≤ b := Nat.div_mul_le_self ..
    have hcp0 : 0 < cap := by
      by_contra! hz
      have heq : b/2^r=0 := Nat.eq_zero_of_le_zero hz
      rw [heq] at test
      simp at test; omega
    have hcp : 2^r ≤ cap := by
      have hh := (Nat.pow_le_pow_left hx 9).trans test.2
      change (cap * 2^r)^9 ≤ cap^10 at hh; rw [mul_pow,show cap^10 = cap^9*cap by ring] at hh
      have hh' := Nat.le_of_mul_le_mul_left hh (by positivity : 0 < cap^9)
      have ha : 2^r ≤ (2^r)^9 := by simpa only [pow_one] using (Nat.pow_le_pow_right (by positivity : 0 < 2^r) (by decide : 1 ≤ 9))
      exact ha.trans hh'
    have hbm : b ≤ m := by dsimp [m]; simpa [mul_comm] using Nat.le_mul_of_pos_right b hC
    have hcm : cap ≤ m := (Nat.div_le_self ..).trans hbm
    refine ⟨test.1,hcm,by dsimp [fullSchedule,kappa]; omega,kappa_bound C b hC hb,?_⟩
    refine ⟨(by simpa [fullSchedule] using (depth_spec m H).1),?_⟩
    let D := depth m H
    have hw (d : Fin D) (M : ℕ) (hM : H < M) := packing_nums ht hM (shift_small d.isLt) (by rw [shift_eq d.isLt]; omega : 2*width m r d.val ≤ shift (widths m r D) d.val) hcp
    have hMu (d : Fin D) : width m r d.val ≤ m/8^d.val := (hw d _ ((depth_spec m H).2 _ d.isLt)).1
    intro d M hM hMm
    change M ≤ m / 8^(0+d.val) at hMm; rw [zero_add] at hMm
    have hule := width_lower C b r d.val hC (by omega) hr d.isLt
    obtain ⟨h1,h2,h3,h4⟩ := hw d M hM
    have haa := shift_eq (m:=m) (r:=r) (H:=H) d.isLt
    change r.sqrt ≤ width m r d.val at hule
    have hwu : 1 ≤ width m r d.val := (by omega : 1 ≤ r.sqrt).trans hule
    have hwa : width m r d.val ≤ shift (widths m r D) d.val := by rw [haa]; omega
    exact ⟨hwu,hwa,h1,h2,h3,h4,
      points_bound (hMm.trans (Nat.div_le_self ..)) (h4.trans hcm),precision rfl hp ht d hM hMu hule h1⟩

end DetDLP.D1
open DetDLP DetDLP.D1 DetDLP.AppendixD4
theorem solution {C b e deg P : ℕ} (hC : 0 < C) (hb : 2 ≤ b) (he : e ≤ C*b) (hp : P ≤ C*b) :
    let s := makeSchedule C b e deg
    s.start = 0 ∧ (s.H < e → deg ≤ s.cap ∧ s.cap ≤ C*b ∧ 0 < s.κ ∧
      2^s.κ ≤ (b+2)^(4*(8*C+1)) ∧ Active s (C*b) P (81*C+544)) ∧
    exponent s b ≤ ((C*threshold C+1024:ℕ):ℝ)*b / Real.sqrt (radius b deg) := by
  dsimp only
  refine ⟨?_,active_make hC hb hp,?_⟩
  · dsimp only [makeSchedule]; split <;> rfl
  · rw [← d1_exact_radius_scan_poly.1 b deg hb]; exact exp_make hC hb he
