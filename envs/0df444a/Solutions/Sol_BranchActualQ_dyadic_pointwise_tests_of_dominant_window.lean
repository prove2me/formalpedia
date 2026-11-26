-- Prove2me | solution 1 for BranchActualQ.dyadic_pointwise_tests_of_dominant_window
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T11:22:42.139572+00:00
-- url     : https://prove2.me/submissions/e096c484-0581-44d1-93ed-bfd83e045b5e

import Mathlib

open Filter
open scoped Topology

namespace DiagonalDyadic

theorem phase_fixed (θ : ℝ) (h : Real.cos θ = -(1/2 : ℝ)) (j : ℕ) :
    Real.cos ((2 : ℝ)^j * θ) = -(1/2 : ℝ) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [show (2 : ℝ)^(j+1)*θ = 2*((2 : ℝ)^j*θ) by ring,
      Real.cos_two_mul, ih]
    norm_num

theorem tail_neg (D : ℕ → ℝ) (R mass θ : ℝ)
    (hr : 0 < R) (hm : 0 < mass) (J : ℕ)
    (hphase : Real.cos ((2 : ℝ)^J * θ) = -(1/2 : ℝ))
    (err : ℕ → ℝ) (herr : Tendsto err atTop (𝓝 0))
    (hdec : ∀ j : ℕ, D (2^(J+j)) / R^(2^(J+j) : ℕ) =
      mass * Real.cos ((2 : ℝ)^(J+j)*θ) + err j) :
    ∀ᶠ j : ℕ in atTop, D (2^(J+j)) < 0 := by
  have small : ∀ᶠ j in atTop, err j < mass/2 :=
    (tendsto_order.mp herr).2 _ (by linarith)
  filter_upwards [small] with j hj
  have ph := phase_fixed ((2 : ℝ)^J * θ) hphase j
  rw [show (2 : ℝ)^j*((2 : ℝ)^J*θ) = (2 : ℝ)^(J+j)*θ by rw [pow_add]; ring] at ph
  have eqn := hdec j
  rw [ph] at eqn
  have hn : D (2^(J+j)) / R^(2^(J+j) : ℕ) < 0 := by linarith
  exact (div_neg_iff.mp hn).resolve_left (by intro h; linarith [pow_pos hr (2^(J+j) : ℕ)]) |>.1

theorem pointwise_criterion {X : Type*} (D : X → ℕ → ℝ) (RH : Prop)
    (positive : RH → ∀ x j, 0 ≤ D x (2^j))
    (entry : ¬ RH → ∃ x, ∀ᶠ j : ℕ in atTop, D x (2^j) < 0) :
    RH ↔ ∀ x J, ∃ j ≥ J, 0 ≤ D x (2^j) := by
  constructor
  · intro h x J
    exact ⟨J, le_rfl, positive h x J⟩
  · intro h
    by_contra hn
    obtain ⟨x, hx⟩ := entry hn
    obtain ⟨J, hJ⟩ := eventually_atTop.mp hx
    obtain ⟨j, hj, hpos⟩ := h x J
    exact (not_lt_of_ge hpos) (hJ j hj)

/-- A separated cluster can attain every sufficiently small phase with a
    lower-order remainder at a point fixed for that phase. -/
def DominantWindow {X : Type*} (D : X → ℕ → ℝ) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∀ θ : ℝ, 0 < θ → θ < η →
    ∃ (x : X) (R mass : ℝ), 0 < R ∧ 0 < mass ∧
      Tendsto (fun k : ℕ => D x k / R^k - mass * Real.cos ((k : ℝ)*θ))
        atTop (𝓝 0)

private theorem nat_lt_two_pow (n : ℕ) : n < 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ]
    have h := Nat.two_pow_pos n
    omega

theorem fixed_witness {X : Type*} {D : X → ℕ → ℝ} (hw : DominantWindow D) :
    ∃ x, ∀ᶠ j : ℕ in atTop, D x (2^j) < 0 := by
  obtain ⟨η,hη,hw⟩ := hw
  let c := 2 * (Real.pi / 3)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨J,hJ⟩ := exists_nat_gt (c/η)
  have hp : (J : ℝ) < (2 : ℝ)^J := by exact_mod_cast nat_lt_two_pow J
  have hbig : c < (2 : ℝ)^J * η := (div_lt_iff₀ hη).mp (hJ.trans hp)
  let θ := c/(2 : ℝ)^J
  have ht : 0 < θ := by dsimp [θ]; positivity
  have ht' : θ < η := (div_lt_iff₀ (by positivity)).mpr (by linarith)
  obtain ⟨x,R,m,hR,hm,hr⟩ := hw θ ht ht'
  have hc' : Real.cos ((2 : ℝ)^J*θ) = -(1/2 : ℝ) := by
    rw [show (2 : ℝ)^J*θ = c by dsimp [θ]; field_simp]
    dsimp [c]
    rw [Real.cos_two_mul, Real.cos_pi_div_three]
    norm_num
  have sub : Tendsto (fun j : ℕ => 2^(J+j)) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [eventually_ge_atTop n] with j hj
    exact le_trans (by omega : n ≤ J+j) (nat_lt_two_pow _).le
  let err := fun j : ℕ => D x (2^(J+j)) / R^(2^(J+j) : ℕ) -
    m * Real.cos ((2 : ℝ)^(J+j)*θ)
  have he : Tendsto err atTop (𝓝 0) := by
    convert hr.comp sub using 1 <;> simp [err, Function.comp_def]
  have hn := tail_neg (D x) R m θ hR hm J hc' err he
    (by intro j; dsimp [err]; ring)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hn
  refine ⟨x, eventually_atTop.mpr ⟨J+N, ?_⟩⟩
  intro j hj
  have H := hN (j-J) (by omega)
  simpa only [show J+(j-J)=j by omega] using H

theorem return_iff {X : Type*} (D : X → ℕ → ℝ) (R : Prop)
    (onLine : R → ∀ x j, 0 ≤ D x (2^j))
    (offLine : ¬ R → DominantWindow D) :
    R ↔ ∀ x J, ∃ j ≥ J, 0 ≤ D x (2^j) :=
  pointwise_criterion D R onLine (fun h => fixed_witness (offLine h))

theorem fixed_asymptotic {X : Type*} {D : X → ℕ → ℝ} (hw : DominantWindow D) :
    ∃ (x : X) (R m : ℝ) (J : ℕ), 0 < R ∧ 0 < m ∧
      Tendsto (fun j : ℕ => D x (2^(J+j))/R^(2^(J+j) : ℕ)) atTop (𝓝 (-(m/2))) := by
  obtain ⟨η,hη,hw⟩ := hw
  let c := 2 * (Real.pi / 3)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨J,hJ⟩ := exists_nat_gt (c/η)
  have hp : (J : ℝ) < (2 : ℝ)^J := by exact_mod_cast nat_lt_two_pow J
  have hbig : c < (2 : ℝ)^J * η := (div_lt_iff₀ hη).mp (hJ.trans hp)
  let θ := c/(2 : ℝ)^J
  have ht : 0 < θ := by dsimp [θ]; positivity
  have ht' : θ < η := (div_lt_iff₀ (by positivity)).mpr (by linarith)
  obtain ⟨x,R,m,hR,hm,hr⟩ := hw θ ht ht'
  have hc' : Real.cos ((2 : ℝ)^J*θ) = -(1/2 : ℝ) := by
    rw [show (2 : ℝ)^J*θ = c by dsimp [θ]; field_simp]
    dsimp [c]
    rw [Real.cos_two_mul, Real.cos_pi_div_three]
    norm_num
  have sub : Tendsto (fun j : ℕ => 2^(J+j)) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [eventually_ge_atTop n] with j hj
    exact le_trans (by omega : n ≤ J+j) (nat_lt_two_pow _).le
  let err := fun j : ℕ => D x (2^(J+j)) / R^(2^(J+j) : ℕ) -
    m * Real.cos ((2 : ℝ)^(J+j)*θ)
  have he : Tendsto err atTop (𝓝 0) := by
    convert hr.comp sub using 1 <;> simp [err, Function.comp_def]
  refine ⟨x,R,m,J,hR,hm,?_⟩
  have hx : Tendsto (fun j => err j + (-(m/2))) atTop (𝓝 (0 + (-(m/2)))) :=
    he.add tendsto_const_nhds
  rw [zero_add] at hx
  apply hx.congr
  intro j
  have ph := phase_fixed ((2 : ℝ)^J*θ) hc' j
  rw [show (2 : ℝ)^j*((2 : ℝ)^J*θ) = (2 : ℝ)^(J+j)*θ by rw [pow_add]; ring] at ph
  dsimp [err]
  rw [ph]
  ring

theorem soft_step_criterion {X : Type*} (D : X → ℕ → ℝ) (R : Prop)
    (onLine : R → ∀ x j, 0 ≤ D x (2^j))
    (offLine : ¬ R → DominantWindow D) :
    R ↔ ∀ x (ε : ℝ), 0 < ε → ∀ N : ℕ, ∃ j ≥ N,
      -(ε * (D x (2^j))^2) ≤ D x (2^(j+1)) := by
  constructor
  · intro hr x ε hε N
    exact ⟨N,le_rfl,le_trans (neg_nonpos.mpr (mul_nonneg hε.le (sq_nonneg _))) (onLine hr x (N+1))⟩
  · intro good
    by_contra bad
    obtain ⟨x,r,m,J,hr,hm,ha⟩ := fixed_asymptotic (offLine bad)
    let a := fun j : ℕ => D x (2^(J+j)) / r^(2^(J+j) : ℕ)
    change Tendsto a atTop (𝓝 (-(m/2))) at ha
    have shift : Tendsto (fun j : ℕ => j+1) atTop atTop := by
      apply tendsto_atTop.2
      intro n
      filter_upwards [eventually_ge_atTop n] with j hj
      omega
    have lim : Tendsto (fun j => a (j+1) + (1/m) * (a j)^2)
        atTop (𝓝 ((-(m/2)) + (1/m)* (-(m/2))^2)) :=
      (ha.comp shift).add (tendsto_const_nhds.mul (ha.pow 2))
    have below : (-(m/2)) + (1/m)* (-(m/2))^2 < 0 := by
      field_simp [hm.ne']; nlinarith
    obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp lim).2 0 below)
    obtain ⟨j,hj,hstep⟩ := good x (1/m) (by positivity) (J+N)
    have h := hN (j-J) (by omega)
    dsimp [a] at h
    rw [show J+(j-J+1)=j+1 by omega, show J+(j-J)=j by omega] at h
    have hp : r^(2^(j+1) : ℕ) = (r^(2^j : ℕ))^2 := by rw [pow_succ, pow_mul]
    rw [hp, div_pow, ← mul_div_assoc, ← add_div] at h
    have hsign := (div_lt_iff₀ (by positivity : 0 < (r^(2^j : ℕ))^2)).mp h
    linarith

end DiagonalDyadic
#print axioms DiagonalDyadic.tail_neg
#print axioms DiagonalDyadic.pointwise_criterion

#print axioms DiagonalDyadic.return_iff

theorem solution {X : Type*} (D : X → ℕ → ℝ) (R : Prop)
    (onLine : R → ∀ x j, 0 ≤ D x (2^j))
    (offLine : ¬ R → ∃ η : ℝ, 0 < η ∧ ∀ θ : ℝ, 0 < θ → θ < η →
      ∃ (x : X) (r mass : ℝ), 0 < r ∧ 0 < mass ∧
        Filter.Tendsto (fun k : ℕ => D x k / r^k - mass * Real.cos ((k : ℝ)*θ))
          Filter.atTop (nhds 0)) :
    (R ↔ ∀ x J, ∃ j ≥ J, 0 ≤ D x (2^j)) ∧
    (R ↔ ∀ x (ε : ℝ), 0 < ε → ∀ N : ℕ, ∃ j ≥ N,
      -(ε * (D x (2^j))^2) ≤ D x (2^(j+1))) :=
  ⟨DiagonalDyadic.return_iff D R onLine offLine, DiagonalDyadic.soft_step_criterion D R onLine offLine⟩
#print axioms solution
