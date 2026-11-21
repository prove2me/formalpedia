-- Prove2me | solution 1 for Erdos68.fixed_weight_minimum_and_range
-- status  : ACCEPTED   (prove)
-- author  : @Mceppaglia
-- created : 2026-11-21T00:46:24.932117+00:00
-- url     : https://prove2.me/submissions/22cff8f2-4a83-4336-b5bf-af1060a9c31b

import Mathlib

/-!
SPDX-License-Identifier: Apache-2.0

Matt directed the investigation. OpenAI Codex (Astra) developed the construction
and Lean formalization. Erdős problem 68 asks whether the original sum is
irrational. The result below characterizes its value as a minimum.
-/

noncomputable section

namespace SparseIntegerMoments
/-- The rounding step in the construction of multiplicities on sparse factorial rows.
Here x is the residual k-moment divided by the current factorial node to power k. -/
private theorem integer_step (u x r w : ℝ) (hu : 0 < u) (hr : 0 < r) (hr' : r ≤ 1 / 3)
    (hw : 0 < w) (hmesh : w ≤ r * u / 32)
    (hx : r * u / 2 ≤ x) (hx' : x ≤ 5 * u / 8) :
    ∃ m : ℕ,
      3 * u / 8 ≤ u - m*w ∧
      (u - m*w)/2 ≤ (x - m*w)/r ∧
      (x - m*w)/r ≤ 5*(u - m*w)/8 ∧
      (u/2 ≤ x → u - m*w ≤ 3*u/4 ∧ 2 ≤ m) := by
  let q := (x-r*u/2)/(1-r/2)
  have ha : 0 < 1-r/2 := by linarith
  have hq : q*(1-r/2) = x-r*u/2 := by exact div_mul_cancel₀ _ ha.ne'
  have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.mpr hx) ha.le
  have hqu : q ≤ 5*u/8 := by
    apply (div_le_iff₀ ha).mpr
    nlinarith [mul_nonneg hr.le hu.le]
  let m : ℕ := ⌊q/w⌋₊
  have hm0 : (m:ℝ)*w ≤ q := by
    apply (le_div_iff₀ hw).mp
    exact Nat.floor_le (div_nonneg hq0 hw.le)
  have hm1 : q < (m:ℝ)*w+w := by
    have hh := (div_lt_iff₀ hw).mp (Nat.lt_floor_add_one (q/w))
    dsimp [m]
    linarith
  have hir : 0 ≤ r*u := mul_nonneg hr.le hu.le
  have hru : r*u ≤ u/3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr') hu.le]
  have hrem : 3*u/8 ≤ u-(m:ℝ)*w := by linarith
  have hexact :
      x-(m:ℝ)*w - r*(u-(m:ℝ)*w)/2 = (1-r/2)*(q-(m:ℝ)*w) := by
    nlinarith only [hq]
  have hdiff : 0 ≤ (1-r/2)*(q-(m:ℝ)*w) := mul_nonneg ha.le (sub_nonneg.mpr hm0)
  have hupper : (1-r/2)*(q-(m:ℝ)*w) ≤ w := by
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hm0)]
  have hscaled : r*(3*u/8) ≤ r*(u-(m:ℝ)*w) := mul_le_mul_of_nonneg_left hrem hr.le
  refine ⟨m, hrem, (le_div_iff₀ hr).mpr (by nlinarith only [hexact, hdiff]),
    (div_le_iff₀ hr).mpr (by nlinarith only [hexact, hupper, hmesh, hscaled, hir]), ?_⟩
  intro hmid
  have hqu' : u/3 ≤ q := by
    apply (le_div_iff₀ ha).mpr
    nlinarith only [hmid, hru, hu]
  constructor
  · nlinarith only [hm1, hqu', hru, hmesh, hu]
  · by_contra hlt
    have hm : m ≤ 1 := by omega
    have hmreal : (m:ℝ) ≤ 1 := by exact_mod_cast hm
    have hmw : (m:ℝ)*w ≤ w := by nlinarith [mul_nonneg (sub_nonneg.mpr hmreal) hw.le]
    nlinarith only [hmw, hm1, hqu', hru, hmesh, hu]

end SparseIntegerMoments

namespace SparseIntegerMoments
open Filter Topology

private theorem hasSum_spent (u d : ℕ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hstep : ∀ i, u (i+1) = u i - d i) (hz : Tendsto u atTop (𝓝 0)) :
    HasSum d (u 0) := by
  have heq (n : ℕ) : ∑ i ∈ Finset.range n, d i = u 0 - u n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, hstep]; ring
  apply (hasSum_iff_tendsto_nat_of_nonneg hd _).2
  simpa only [heq, sub_zero] using (tendsto_const_nhds (x := u 0)).sub hz

private structure Residual (mesh : ℝ) where
  u : ℝ
  x : ℝ
  pos : 0 < u
  lower : u/2 ≤ x
  upper : x ≤ 5*u/8
  fine : mesh ≤ u/32

/-- From the normalized post-entrance invariant, integer multiplicities
realize both requested totals exactly. The first total is U, and the weighted
total is the normalized target X multiplied by the initial node b 0. -/
private theorem normalized_integer_realization (v b r : ℕ → ℝ) (U X : ℝ)
    (hv : ∀ i, 0 < v i) (hb : ∀ i, 0 < b i)
    (hr : ∀ i, 0 < r i) (hr' : ∀ i, r i ≤ 1/3)
    (hbr : ∀ i, b (i+1) = r i * b i)
    (hmesh : ∀ i, v (i+1)/r (i+1) ≤ (v i/r i)/4)
    (hU : 0 < U) (hlo : U/2 ≤ X) (hhi : X ≤ 5*U/8)
    (hstart : v 0/r 0 ≤ U/32) :
    ∃ m : ℕ → ℕ, (∀ i, 2 ≤ m i) ∧
      HasSum (fun i ↦ (m i:ℝ)*v i) U ∧
      HasSum (fun i ↦ b i*((m i:ℝ)*v i)) (b 0*X) := by
  classical
  let State (i : ℕ) := Residual (v i/r i)
  have advance (i : ℕ) (p : State i) : ∃ m : ℕ, ∃ q : State (i+1),
      q.u = p.u - m*v i ∧ r i*q.x = p.x - m*v i ∧
      q.u ≤ (3/4:ℝ)*p.u ∧ 2 ≤ m := by
    have hm : v i ≤ r i*p.u/32 := by
      have := (div_le_iff₀ (hr i)).mp p.fine
      linarith
    have hlow : r i*p.u/2 ≤ p.x := by
      have := mul_le_mul_of_nonneg_right (hr' i) p.pos.le
      linarith [p.lower, p.pos]
    obtain ⟨m, hnew, hmid, htop, hcontract⟩ :=
      integer_step p.u p.x (r i) (v i) p.pos (hr i) (hr' i) (hv i) hm hlow p.upper
    have hs : v (i+1)/r (i+1) ≤ (p.u-m*v i)/32 := by
      linarith [hmesh i, p.fine]
    let q : State (i+1) := ⟨p.u - m*v i, (p.x-m*v i)/r i, by linarith [p.pos],
      hmid, htop, hs⟩
    refine ⟨m, q, rfl, ?_, ?_, (hcontract p.lower).2⟩
    · change r i*((p.x-m*v i)/r i) = _
      field_simp [(hr i).ne']
    · change p.u - m*v i ≤ _
      linarith [(hcontract p.lower).1]
  let next (i : ℕ) (p : State i) := (advance i p).choose_spec.choose
  let state : (i : ℕ) → State i := Nat.rec ⟨U, X, hU, hlo, hhi, hstart⟩ next
  let m (i : ℕ) := (advance i (state i)).choose
  have step (i : ℕ) : (state (i+1)).u = (state i).u - m i*v i ∧
      r i*(state (i+1)).x = (state i).x - m i*v i ∧
      (state (i+1)).u ≤ (3/4:ℝ)*(state i).u ∧ 2 ≤ m i :=
    (advance i (state i)).choose_spec.choose_spec
  have ub (i : ℕ) : (state i).u ≤ (3/4:ℝ)^i*U := by
    induction i with
    | zero => simp [state]
    | succ i ih =>
      calc
        (state (i+1)).u ≤ (3/4:ℝ)*(state i).u := (step i).2.2.1
        _ ≤ (3/4:ℝ)*((3/4:ℝ)^i*U) := by gcongr
        _ = _ := by rw [pow_succ]; ring
  have hz : Tendsto (fun i ↦ (state i).u) atTop (𝓝 0) := by
    apply squeeze_zero (fun i ↦ (state i).pos.le) ub
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (show 0 ≤ (3/4:ℝ) by norm_num) (by norm_num)).mul_const U
  have bu (i : ℕ) : b i ≤ b 0 := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [hbr]
      have := mul_le_mul_of_nonneg_right (hr' i) (hb i).le
      linarith [hb i]
  have xnon (i : ℕ) : 0 ≤ (state i).x := by linarith [(state i).pos, (state i).lower]
  have hzw : Tendsto (fun i ↦ b i*(state i).x) atTop (𝓝 0) := by
    apply squeeze_zero (fun i ↦ mul_nonneg (hb i).le (xnon i))
      (fun i ↦ show b i*(state i).x ≤ b 0*(state i).u from
        mul_le_mul (bu i) (by linarith [(state i).upper, (state i).pos]) (xnon i) (hb 0).le)
    simpa using hz.const_mul (b 0)
  refine ⟨m, fun i ↦ (step i).2.2.2, ?_, ?_⟩
  · exact hasSum_spent _ _ (fun i ↦ mul_nonneg (Nat.cast_nonneg _) (hv i).le)
      (fun i ↦ (step i).1) hz
  · apply hasSum_spent (fun i ↦ b i*(state i).x) _
      (fun i ↦ mul_nonneg (hb i).le (mul_nonneg (Nat.cast_nonneg _) (hv i).le)) _ hzw
    intro i
    rw [hbr]
    have heq := congrArg (fun z : ℝ ↦ b i*z) (step i).2.1
    calc
      r i*b i*(state (i+1)).x = b i*(r i*(state (i+1)).x) := by ring
      _ = b i*((state i).x - m i*v i) := heq
      _ = _ := by ring

/-- The first row may start below the post-entrance interval. All later
multiplicities are at least two and both total masses are attained. -/
private theorem entrance_integer_realization (v b r : ℕ → ℝ) (U X : ℝ)
    (hv : ∀ i, 0 < v i) (hb : ∀ i, 0 < b i)
    (hr : ∀ i, 0 < r i) (hr' : ∀ i, r i ≤ 1/3)
    (hbr : ∀ i, b (i+1) = r i * b i)
    (hmesh : ∀ i, v (i+1)/r (i+1) ≤ (v i/r i)/4)
    (hU : 0 < U) (hlo : r 0*U/2 ≤ X) (hhi : X ≤ 5*U/8)
    (hstart : v 0/r 0 ≤ U/32) :
    ∃ m : ℕ → ℕ, (∀ i, 2 ≤ m (i+1)) ∧
      HasSum (fun i ↦ (m i:ℝ)*v i) U ∧
      HasSum (fun i ↦ b i*((m i:ℝ)*v i)) (b 0*X) := by
  have hweight : v 0 ≤ r 0*U/32 := by
    have := (div_le_iff₀ (hr 0)).mp hstart
    linarith
  obtain ⟨a, hpos, hl, hh, _⟩ := integer_step U X (r 0) (v 0) hU
    (hr 0) (hr' 0) (hv 0) hweight hlo hhi
  have hnext : v 1/r 1 ≤ (U-a*v 0)/32 := by linarith [hmesh 0]
  obtain ⟨tail, ht, hs₁, hs₂⟩ := normalized_integer_realization
    (fun i ↦ v (i+1)) (fun i ↦ b (i+1)) (fun i ↦ r (i+1))
    (U-a*v 0) ((X-a*v 0)/r 0)
    (fun i ↦ hv _) (fun i ↦ hb _) (fun i ↦ hr _) (fun i ↦ hr' _)
    (fun i ↦ hbr _) (fun i ↦ hmesh _) (by linarith) hl hh hnext
  let m : ℕ → ℕ := fun i ↦ Nat.casesOn i a tail
  refine ⟨m, ht, ?_, ?_⟩
  · apply (hasSum_nat_add_iff' 1).mp
    simpa [m, Finset.sum_range_one] using hs₁
  · apply (hasSum_nat_add_iff' 1).mp
    have heq : b 1*((X-a*v 0)/r 0) = b 0*X-b 0*(a*v 0) := by
      rw [hbr 0]
      field_simp [(hr 0).ne']
    rw [show b (0+1)*((X-a*v 0)/r 0) = _ from heq] at hs₂
    simpa [m, Finset.sum_range_one] using hs₂


/-- Starting before the entrance, the construction deletes an initial
nonempty block of rows, and uses at least two copies strictly after
the entrance. The two sums take the originally prescribed values. -/
private theorem sparse_two_mass_realization (v b r : ℕ → ℝ) (U V : ℝ)
    (hv : ∀ i, 0 < v i) (hb : ∀ i, 0 < b i)
    (hr : ∀ i, 0 < r i) (hr' : ∀ i, r i ≤ 1/3)
    (hbr : ∀ i, b (i+1) = r i * b i)
    (hmesh : ∀ i, v (i+1)/r (i+1) ≤ (v i/r i)/4)
    (hU : 0 < U) (hV : 0 < V) (hsmall : V < b 1*U/2)
    (hstart : v 0/r 0 ≤ U/32) :
    ∃ I : ℕ, 0 < I ∧ ∃ m : ℕ → ℕ,
      (∀ i < I, m i = 0) ∧ (∀ i > I, 2 ≤ m i) ∧
      HasSum (fun i ↦ (m i:ℝ)*v i) U ∧
      HasSum (fun i ↦ b i*((m i:ℝ)*v i)) V := by
  classical
  have hbdec (i : ℕ) : b (i+1) ≤ (1/3:ℝ)*b i := by
    rw [hbr]
    exact mul_le_mul_of_nonneg_right (hr' i) (hb i).le
  have hbpow (i : ℕ) : b i ≤ (1/3:ℝ)^i*b 0 := by
    induction i with
    | zero => simp
    | succ i ih =>
      calc
        b (i+1) ≤ (1/3:ℝ)*b i := hbdec i
        _ ≤ (1/3:ℝ)*((1/3:ℝ)^i*b 0) := by gcongr
        _ = _ := by rw [pow_succ]; ring
  have hbzero : Tendsto b atTop (𝓝 0) := by
    apply squeeze_zero (fun i ↦ (hb i).le) hbpow
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (show 0 ≤ (1/3:ℝ) by norm_num) (by norm_num)).mul_const (b 0)
  have hex : ∃ i : ℕ, b (i+1)*U/2 ≤ V := by
    obtain ⟨i, hi⟩ := (hbzero.eventually_lt_const (div_pos hV hU)).exists
    have hbu : b i*U < V := (lt_div_iff₀ hU).mp hi
    have hdec : b (i+1) ≤ b i := by linarith [hbdec i, hb i]
    have := mul_le_mul_of_nonneg_right hdec hU.le
    exact ⟨i, by linarith⟩
  let I := Nat.find hex
  have henter : b (I+1)*U/2 ≤ V := Nat.find_spec hex
  have hpos : 0 < I := by
    by_contra! h
    have hi : I = 0 := by omega
    rw [hi] at henter
    linarith
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hprior : V < b I*U/2 := by
    have h := Nat.find_min hex (show j < I by omega)
    rw [hj]
    exact lt_of_not_ge h
  have hs (i : ℕ) : v i/r i ≤ U/32 := by
    induction i with
    | zero => exact hstart
    | succ i ih => linarith [hmesh i]
  have hxlo : r I*U/2 ≤ V/b I := by
    apply (le_div_iff₀ (hb I)).mpr
    rw [hbr I] at henter
    linarith only [henter]
  have hxhi : V/b I ≤ 5*U/8 := by
    apply (div_le_iff₀ (hb I)).mpr
    nlinarith [mul_pos (hb I) hU]
  obtain ⟨tail, ht, hsm, hsw⟩ := entrance_integer_realization
    (fun i ↦ v (I+i)) (fun i ↦ b (I+i)) (fun i ↦ r (I+i))
    U (V/b I) (fun i ↦ hv _) (fun i ↦ hb _) (fun i ↦ hr _) (fun i ↦ hr' _)
    (fun i ↦ hbr _) (fun i ↦ hmesh _) hU hxlo hxhi (hs I)
  let m (i : ℕ) := if i<I then 0 else tail (i-I)
  have hpre (i : ℕ) (hi : i<I) : m i = 0 := by simp [m, hi]
  have htail (i : ℕ) : m (i+I) = tail i := by simp [m]
  refine ⟨I, hpos, m, hpre, ?_, ?_, ?_⟩
  · intro i hi
    let k := i-I-1
    have heq : i=k+1+I := by dsimp [k]; omega
    rw [heq, htail]
    exact ht k
  · apply (hasSum_nat_add_iff' I).mp
    have hz : ∑ i ∈ Finset.range I, (m i:ℝ)*v i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hpre i (Finset.mem_range.mp hi)]
    rw [hz, sub_zero]
    simpa only [htail, Nat.add_comm I] using hsm
  · apply (hasSum_nat_add_iff' I).mp
    have hz : ∑ i ∈ Finset.range I, b i*((m i:ℝ)*v i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hpre i (Finset.mem_range.mp hi)]
    rw [hz, sub_zero]
    have htgt : b (I+0)*(V/b I) = V := by
      simp only [Nat.add_zero]
      field_simp [(hb I).ne']
    rw [htgt] at hsw
    simpa only [htail, Nat.add_comm I] using hsw


end SparseIntegerMoments

namespace FactorialMinimum

private def W (i : ℕ) : ℝ := 1 / ((i+2).factorial - 1 : ℝ)
private def X (i : ℕ) : ℝ := 1 / ((i+2).factorial : ℝ)

private theorem fac_two (i : ℕ) : (2:ℝ) ≤ (i+2).factorial := by
  exact_mod_cast (Nat.factorial_le (show 2 ≤ i+2 by omega))

private theorem w_pos (i : ℕ) : 0 < W i := by
  unfold W
  exact one_div_pos.mpr (by linarith [fac_two i])

private theorem x_pos (i : ℕ) : 0 < X i := by
  unfold X
  positivity

private theorem w_step (i : ℕ) : W (i+1) ≤ (1/3:ℝ)*W i := by
  unfold W
  rw [show i+1+2=(i+2)+1 by omega, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
  have a := fac_two i
  have b : (3:ℝ) ≤ (i+2:ℕ)+1 := by exact_mod_cast (show 3 ≤ i+2+1 by omega)
  have c : 0 < ((i+2:ℕ)+1:ℝ)*((i+2).factorial:ℝ)-1 := by nlinarith
  have g : 0 < ((i+2).factorial:ℝ)-1 := by linarith
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr b) (show (0:ℝ) ≤ (i+2).factorial by positivity)]

private theorem x_step (i : ℕ) : X (i+1) ≤ (1/3:ℝ)*X i := by
  unfold X
  rw [show i+1+2=(i+2)+1 by omega, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
  have a := fac_two i
  have b : (3:ℝ) ≤ (i+2:ℕ)+1 := by exact_mod_cast (show 3 ≤ i+2+1 by omega)
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr b) (show (0:ℝ) ≤ (i+2).factorial by positivity)]

private theorem geometric (w : ℕ → ℝ) (hstep : ∀ i, w (i+1) ≤ (1/3:ℝ)*w i)
    (i t : ℕ) : w (i+t) ≤ w i * (1/3:ℝ)^t := by
  induction t with
  | zero => simp
  | succ t ih =>
    specialize hstep (i+t)
    rw [pow_succ, ← mul_assoc]
    change w (i+t+1) ≤ _
    linarith

private theorem w_summable (i : ℕ) : Summable (fun t => W (i+t)) := by
  apply Summable.of_nonneg_of_le (fun _ => (w_pos _).le) (geometric W w_step i)
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

private theorem tail_bound (i : ℕ) : (∑' t, W ((i+1)+t)) ≤ W i/2 := by
  have h := (w_summable (i+1)).tsum_le_tsum (geometric W w_step (i+1))
      ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/3) (by norm_num)).mul_left _)
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h
  linarith [w_step i]

private theorem first_row (w x c M z Z : ℝ) (n : ℕ)
    (hw : 0 < w) (hx : 0 < x) (hn : n ≠ 1)
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hz : z ≤ w/2)
    (hcb : c ≤ x/3 * z) (hMb : M ≤ x/3 * Z)
    (matched : (n:ℝ)*w*x + M = w*x+c) :
    n=0 ∧ w+z < (n:ℝ)*w + Z := by
  have hx3 : 0 < x/3 := by positivity
  have hwx : 0 < w*x := mul_pos hw hx
  have hcx : c ≤ x/3*(w/2) := hcb.trans (mul_le_mul_of_nonneg_left hz hx3.le)
  have hn0 : n=0 := by
    by_contra h
    have hn2 : (2:ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have hnw := mul_le_mul_of_nonneg_right hn2 hwx.le
    nlinarith only [hwx, hnw, hcx, matched, hM]
  subst n
  simp at matched ⊢
  by_contra! no
  have hhi := mul_le_mul_of_nonneg_left (show Z ≤ w+w/2 by linarith) hx3.le
  nlinarith only [matched, hhi, hc, hwx, hMb]

private theorem split_at (f : ℕ → ℝ) (hf : Summable f) (i : ℕ) :
    (∑' t, f t) = (∑ t ∈ Finset.range i, f t) + f i + ∑' t, f ((i+1)+t) := by
  simpa only [Finset.sum_range_succ, Nat.add_comm (i+1)] using (hf.sum_add_tsum_nat_add (i+1)).symm

private theorem shifted {f : ℕ → ℝ} (hf : Summable f) (i : ℕ) : Summable (fun t => f (i+t)) := by
  simpa only [Nat.add_comm i] using (summable_nat_add_iff i).mpr hf

private theorem x_bound (i : ℕ) : X i ≤ 1 := by
  unfold X
  exact (div_le_one (by positivity)).mpr (by linarith [fac_two i])

private theorem x_far (i t k : ℕ) (hk : 1 ≤ k) : X ((i+1)+t)^k ≤ (X i)^k/3 := by
  have h1 := geometric X x_step (i+1) t
  have h2 : (1/3:ℝ)^t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h3 : X ((i+1)+t) ≤ (1/3:ℝ)*X i := by
    have hh := mul_le_mul_of_nonneg_left h2 (x_pos (i+1)).le
    linarith [x_step i]
  have h4 := pow_le_pow_left₀ (x_pos _).le h3 k
  rw [mul_pow] at h4
  have h5 := pow_le_pow_of_le_one (by norm_num : 0 ≤ (1/3:ℝ)) (by norm_num) hk
  simp only [pow_one] at h5
  have hh := mul_le_mul_of_nonneg_right h5 (pow_nonneg (x_pos i).le k)
  linarith

private theorem moment_summable (f : ℕ → ℝ) (hf : Summable f) (hn : ∀ i, 0 ≤ f i) (k : ℕ) :
    Summable (fun i => f i*X i^k) := by
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (hn _) (pow_nonneg (x_pos i).le k)) _ hf
  intro i
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ (x_pos i).le (x_bound i)) (hn i)

private theorem moment_tail_bound (f : ℕ → ℝ) (hf : Summable f) (hn : ∀ i, 0 ≤ f i)
    (i k : ℕ) (hk : 1 ≤ k) :
    (∑' t, f ((i+1)+t)*X ((i+1)+t)^k) ≤ (X i)^k/3 * (∑' t, f ((i+1)+t)) := by
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (shifted (moment_summable f hf hn k) (i+1))
    ((shifted hf (i+1)).mul_left _)
  intro t
  rw [mul_comm (f _)]
  exact mul_le_mul_of_nonneg_right (x_far i t k hk) (hn _)

/-- Multiplicity one uniquely minimizes the total mass among nonnegative integer
multiplicities with any prescribed positive moment equal to its canonical value.
The index i represents the factorial row j=i+2. -/
private theorem canonical_mass_lt (m : ℕ → ℕ) (k : ℕ) (hk : 1 ≤ k)
    (hm : Summable (fun i => (m i:ℝ)*W i))
    (hmatch : (∑' i, (m i:ℝ)*W i*X i^k) = ∑' i, W i*X i^k)
    (hdiff : ∃ i, m i ≠ 1) :
    (∑' i, W i) < ∑' i, (m i:ℝ)*W i := by
  classical
  let i := Nat.find hdiff
  have hi : m i ≠ 1 := Nat.find_spec hdiff
  have hpre (j : ℕ) (hj : j < i) : m j = 1 := by
    by_contra h
    exact (Nat.find_min hdiff hj) h
  let f (j : ℕ) : ℝ := (m j:ℝ)*W j
  have hf : Summable f := hm
  have fn (j) : 0 ≤ f j := mul_nonneg (by positivity) (w_pos j).le
  have hw : Summable W := by simpa using w_summable 0
  have wn (j) : 0 ≤ W j := (w_pos j).le
  have first_mass : (∑ j ∈ Finset.range i, f j) = ∑ j ∈ Finset.range i, W j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [f, hpre j (Finset.mem_range.mp hj)]
  have first_moment : (∑ j ∈ Finset.range i, f j * X j ^ k) =
      ∑ j ∈ Finset.range i, W j * X j ^ k := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [f, hpre j (Finset.mem_range.mp hj)]
  change (∑' j, f j*X j^k) = ∑' j, W j*X j^k at hmatch
  rw [split_at _ (moment_summable f hf fn k) i,
    split_at _ (moment_summable W hw wn k) i, first_moment] at hmatch
  have rest : (m i:ℝ)*W i*X i^k + (∑' t, f ((i+1)+t)*X ((i+1)+t)^k) =
      W i*X i^k + ∑' t, W ((i+1)+t)*X ((i+1)+t)^k := by
    change f i*X i^k + _ = _
    linarith only [hmatch]
  have ht := first_row (W i) (X i^k) _ _ _ _ (m i) (w_pos i)
      (pow_pos (x_pos i) _) hi
      (tsum_nonneg (fun t => mul_nonneg (wn _) (pow_nonneg (x_pos _).le _)))
      (tsum_nonneg (fun t => mul_nonneg (fn _) (pow_nonneg (x_pos _).le _)))
      (tail_bound i) (moment_tail_bound W hw wn i k hk)
      (moment_tail_bound f hf fn i k hk) rest
  change (∑' j, W j) < ∑' j, f j
  rw [split_at W hw i, split_at f hf i, first_mass]
  change _ ∧ W i + _ < f i + _ at ht
  linarith only [ht.2]

end FactorialMinimum

namespace FactorialRange
open Filter Topology
open FactorialMinimum
private def R (i k : ℕ) : ℝ := (1 / ((i:ℝ)+3))^k
private def B (i k : ℕ) : ℝ := X i ^ k

private theorem rpos (i k : ℕ) : 0 < R i k := by unfold R; positivity
private theorem bpos (i k : ℕ) : 0 < B i k := pow_pos (x_pos i) _
private theorem rbound (i k : ℕ) (hk : 1 ≤ k) : R i k ≤ 1/3 := by
  have h : (1:ℝ)/((i:ℝ)+3) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) i])
  have p := pow_le_pow_of_le_one (by positivity : 0 ≤ (1:ℝ)/((i:ℝ)+3))
    (h.trans (by norm_num)) hk
  simpa [R] using p.trans (show ((1:ℝ)/((i:ℝ)+3))^1 ≤ 1/3 by simpa using h)

private theorem bstep (i k : ℕ) : B (i+1) k = R i k * B i k := by
  unfold B R X
  rw [show i+1+2=(i+2)+1 by omega, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
  rw [← mul_pow]
  congr 1
  push_cast
  field_simp
  ring

private theorem mesh_eq (i k : ℕ) : W i / R i k = W i * ((i:ℝ)+3)^k := by
  simp [R]

private theorem slow_weights (i : ℕ) : ((i:ℝ)+3)* W (i+1) ≤ W i := by
  unfold W
  rw [show i+1+2=(i+2)+1 by omega, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
  have ha : (2:ℝ) ≤ (i+2).factorial := by exact_mod_cast (Nat.factorial_le (show 2 ≤ i+2 by omega))
  push_cast
  have h1 : 0 < ((i+2).factorial:ℝ)-1 := by linarith
  have h2 : 0 < ((i:ℝ)+2+1)*((i+2).factorial:ℝ)-1 := by nlinarith
  field_simp
  linarith

private theorem mesh_contracts (i k : ℕ) (hi : 4*2^k ≤ i) :
    W (i+1)/R (i+1) k ≤ (W i/R i k)/4 := by
  rw [mesh_eq, mesh_eq, Nat.cast_add_one]
  have hbase : (i:ℝ)+1+3 ≤ 2*((i:ℝ)+3) := by linarith
  have hr := pow_le_pow_left₀ (show 0 ≤ (i:ℝ)+1+3 by positivity) hbase k
  rw [mul_pow] at hr
  have h1 := mul_le_mul_of_nonneg_left hr (w_pos (i+1)).le
  have hi' : 4*(2:ℝ)^k ≤ i := by exact_mod_cast hi
  have h2 : 4*(2:ℝ)^k * W (i+1) ≤ W i :=
    (mul_le_mul_of_nonneg_right (show 4*(2:ℝ)^k ≤ (i:ℝ)+3 by linarith) (w_pos _).le).trans
    (slow_weights i)
  have h3 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ ((i:ℝ)+3)^k by positivity)
  nlinarith only [h1,h3]

private theorem mesh_geo (I k : ℕ) (hi : 4*2^k ≤ I) (n : ℕ) :
    W (I+n)/R (I+n) k ≤ (1/4:ℝ)^n*(W I/R I k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := mesh_contracts (I+n) k (by omega)
    rw [pow_succ]
    change W (I+n+1)/R (I+n+1) k ≤ _
    linarith

private theorem small_mesh_past (J k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ I ≥ J, 4*2^k ≤ I ∧ W I/R I k ≤ δ/32 := by
  let N := J+4*2^k
  have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
    (by norm_num)).mul_const (W N/R N k)
  have hh' : Tendsto (fun n : ℕ => (1/4:ℝ)^n*(W N/R N k)) atTop (𝓝 0) := by simpa using hh
  obtain ⟨n, hn⟩ := ((hh'.eventually_lt_const (show 0 < δ/32 by positivity))).exists
  refine ⟨N+n, by dsimp [N]; omega, by dsimp [N]; omega, ?_⟩
  exact (mesh_geo N k (by dsimp [N]; omega) n).trans hn.le

private def splice (I : ℕ) (m : ℕ → ℕ) (j : ℕ) : ℕ := if j<I then 1 else m (j-I)

private theorem splice_sum (I : ℕ) (m : ℕ → ℕ) (w : ℕ → ℝ) (a : ℝ)
    (hs : HasSum (fun n => (m n:ℝ)*w (I+n)) a) :
    HasSum (fun j => (splice I m j:ℝ)*w j) ((∑ j ∈ Finset.range I, w j)+a) := by
  apply (hasSum_nat_add_iff' I).mp
  have pre : (∑ j ∈ Finset.range I, (splice I m j:ℝ)*w j) =
      ∑ j ∈ Finset.range I, w j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [splice, Finset.mem_range.mp hj]
  rw [pre, add_sub_cancel_left]
  simpa only [splice, Nat.not_lt.mpr (Nat.le_add_left I _), if_false, Nat.add_sub_cancel,
    Nat.add_comm I] using hs

private theorem attach_eq (f : ℕ → ℝ) (hf : Summable f) (I : ℕ) :
    (∑ j ∈ Finset.range I, f j) + ∑' n, f (I+n) = ∑' j, f j := by
  simpa only [Nat.add_comm I] using hf.sum_add_tsum_nat_add I

private theorem b_antitone (k : ℕ) (hk : 1 ≤ k) : Antitone (fun i => B i k) := by
  apply antitone_nat_of_succ_le
  intro i
  rw [bstep]
  have := mul_le_mul_of_nonneg_right (rbound i k hk) (bpos i k).le
  linarith [bpos i k]

/-- Any positive increase in the unweighted sum can be prescribed exactly,
keeping the original positive moment of order k and any prescribed prefix. -/
private theorem realize_excess (J k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ m : ℕ → ℕ, (∀ j < J, m j = 1) ∧
      HasSum (fun j => (m j:ℝ)*W j) ((∑' j, W j)+δ) ∧
      HasSum (fun j => (m j:ℝ)*(W j*X j^k)) (∑' j, W j*X j^k) := by
  obtain ⟨I, hIJ, hI, hmesh⟩ := small_mesh_past J k δ hδ
  let v (n : ℕ) := W (I+n)
  let b (n : ℕ) := B (I+n) k
  let r (n : ℕ) := R (I+n) k
  let U := δ + ∑' n, v n
  let V := ∑' n, v n*b n
  have hw : Summable W := by simpa using w_summable 0
  have hf := moment_summable W hw (fun i => (w_pos i).le) k
  have hv : Summable v := w_summable I
  have hVsum : Summable (fun n => v n*b n) := shifted hf I
  have hU : 0 < U := add_pos_of_pos_of_nonneg hδ (tsum_nonneg (fun n => (w_pos (I+n)).le))
  have hV : 0 < V := hVsum.tsum_pos
    (fun n => (mul_pos (w_pos (I+n)) (bpos (I+n) k)).le) 0 (mul_pos (w_pos _) (bpos _ _))
  have hδU : δ ≤ U := le_add_of_nonneg_right (tsum_nonneg (fun n => (w_pos (I+n)).le))
  have hVbound : V ≤ (∑' n, v n)*b 0 := by
    rw [← tsum_mul_right]
    apply hVsum.tsum_le_tsum _ (hv.mul_right _)
    intro n
    apply mul_le_mul_of_nonneg_left _ (w_pos _).le
    exact b_antitone k hk (show I+0 ≤ I+n by omega)
  have hWbound : (∑' n, v n) ≤ 2*v 0 := by
    have hg := hv.tsum_le_tsum (geometric W w_step I)
        ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/3) (by norm_num)).mul_left _)
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hg
    change _ ≤ 2 * W I
    linarith [w_pos I]
  have hv0 : v 0 ≤ r 0*δ/32 := by
    have h := (div_le_iff₀ (rpos I k)).mp hmesh
    change W I ≤ R I k*δ/32
    linarith only [h]
  have hsmall : V < b 1*U/2 := by
    have h1 := hVbound.trans (mul_le_mul_of_nonneg_right hWbound (bpos _ _).le)
    have h2 := mul_le_mul_of_nonneg_right hv0 (bpos (I+0) k).le
    have h3 := mul_le_mul_of_nonneg_left hδU (mul_nonneg (rpos (I+0) k).le (bpos (I+0) k).le)
    have hp := mul_pos (mul_pos (rpos (I+0) k) (bpos (I+0) k)) hδ
    have he : b 1 = r 0*b 0 := bstep I k
    rw [he]
    change V ≤ 2*v 0*b 0 at h1
    change v 0*b 0 ≤ r 0*δ/32*b 0 at h2
    change r 0*b 0*δ ≤ r 0*b 0*U at h3
    change 0 < r 0*b 0*δ at hp
    nlinarith only [h1,h2,h3,hp]
  obtain ⟨_, _, m, _, _, hm, hmm⟩ :=
    SparseIntegerMoments.sparse_two_mass_realization v b r U V
      (fun n => w_pos _) (fun n => bpos _ _) (fun n => rpos _ _) (fun n => rbound _ _ hk)
      (fun n => bstep (I+n) k) (fun n => mesh_contracts (I+n) k (by omega))
      hU hV hsmall (by change W I / R I k ≤ U / 32; linarith)
  refine ⟨splice I m, fun j hj => by simp [splice, show j<I by omega], ?_, ?_⟩
  · have hs := splice_sum I m W U hm
    have he := attach_eq W hw I
    have eq : (∑ j ∈ Finset.range I, W j) + U = (∑' j, W j)+δ := by
      dsimp [U,v]
      linarith only [he]
    rwa [eq] at hs
  · have hc : HasSum (fun n => (m n:ℝ)*(W (I+n)*X (I+n)^k)) V := by
      simpa only [b,v,B,mul_assoc,mul_comm,mul_left_comm] using hmm
    have hs := splice_sum I m (fun j => W j*X j^k) V hc
    exact (attach_eq _ hf I) ▸ hs

/-- The exact range of total masses is the closed real half-line beginning
at the original mass, under one fixed positive moment and any finite prefix. -/
private theorem prescribed_range (J k : ℕ) (hk : 1 ≤ k) (y : ℝ) :
    ((∃ m : ℕ → ℕ, (∀ j < J, m j = 1) ∧
      HasSum (fun j => (m j:ℝ)*W j) y ∧
      HasSum (fun j => (m j:ℝ)*(W j*X j^k)) (∑' j, W j*X j^k)) ↔
    (∑' j, W j) ≤ y) := by
  classical
  have hw : Summable W := by simpa using w_summable 0
  have hf := moment_summable W hw (fun i => (w_pos i).le) k
  constructor
  · rintro ⟨m, _, hm, hmk⟩
    by_cases h : ∃ i, m i ≠ 1
    · have eq : (∑' j, (m j:ℝ)*W j*X j^k) = ∑' j, W j*X j^k := by
        simpa only [mul_assoc] using hmk.tsum_eq
      have ht := canonical_mass_lt m k hk hm.summable eq h
      exact hm.tsum_eq ▸ ht.le
    · push Not at h
      simpa [h] using hm.tsum_eq.le
  · intro hy
    rcases hy.eq_or_lt with eq|lt
    · refine ⟨fun _ => 1, fun _ _ => rfl, ?_, ?_⟩
      · simpa [← eq] using hw.hasSum
      · simpa using hf.hasSum
    · have hδ : 0 < y - ∑' j, W j := by linarith
      obtain ⟨m, hpre, hs, ht⟩ := realize_excess J k hk _ hδ
      exact ⟨m, hpre, by simpa using hs, ht⟩

end FactorialRange

theorem solution (k : ℕ) (hk : 1 ≤ k) :
    let w : ℕ → ℝ := fun i => 1 / ((i + 2).factorial - 1 : ℝ)
    let x : ℕ → ℝ := fun i => 1 / ((i + 2).factorial : ℝ)
    let S : ℝ := ∑' i, w i
    let T : ℝ := ∑' i, w i * x i ^ k
    (∀ m : ℕ → ℕ, Summable (fun i => (m i : ℝ) * w i) →
      (∑' i, (m i : ℝ) * w i * x i ^ k) = T →
      (∃ i, m i ≠ 1) → S < ∑' i, (m i : ℝ) * w i) ∧
    (∀ (J : ℕ) (y : ℝ),
      (∃ m : ℕ → ℕ, (∀ i < J, m i = 1) ∧
        HasSum (fun i => (m i : ℝ) * w i) y ∧
        HasSum (fun i => (m i : ℝ) * (w i * x i ^ k)) T) ↔ S ≤ y) := by
  dsimp only
  constructor
  · intro m hm hmatch hdiff
    exact FactorialMinimum.canonical_mass_lt m k hk hm hmatch hdiff
  · intro J y
    exact FactorialRange.prescribed_range J k hk y

end
