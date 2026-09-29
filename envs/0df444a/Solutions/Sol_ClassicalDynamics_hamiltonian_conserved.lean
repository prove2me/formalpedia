-- Prove2me | solution 1 for ClassicalDynamics.hamiltonian_conserved
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T04:54:26.255656+00:00
-- url     : https://prove2.me/submissions/61ff23c8-df04-4e06-b695-38aa32afb726

import Definitions.Def_ClassicalDynamics_core

open ClassicalDynamics

theorem solution {n : ℕ} (L : Lagrangian n)
    (hL : IsSmoothLagrangian L)
    (hLt : ∀ (t : ℝ) (x v : Fin n → ℝ), deriv (fun s : ℝ => L s x v) t = 0)
    (q : ℝ → Fin n → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hmot : IsMotion L q) :
    IsConstantInTime (fun t => hamiltonian L t (q t) (vel q t)) := by
  classical
  set Lt : ℝ × (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p => L p.1 p.2.1 p.2.2 with hLtdef
  have hLs : ContDiff ℝ (⊤ : ℕ∞) Lt := hL
  have hLd : Differentiable ℝ Lt := hLs.differentiable (by simp)
  -- partial derivatives as directional derivatives
  have ht : ∀ t x v, deriv (fun s => L s x v) t = fderiv ℝ Lt (t, x, v) (1, 0, 0) := by
    intro t x v
    have hp : HasDerivAt (fun s : ℝ => (s, x, v)) ((1 : ℝ), (0 : Fin n → ℝ), (0 : Fin n → ℝ)) t :=
      (hasDerivAt_id t).prodMk ((hasDerivAt_const t x).prodMk (hasDerivAt_const t v))
    exact ((hLd (t, x, v)).hasFDerivAt.comp_hasDerivAt t hp).deriv
  have hdq : ∀ j t x v, dLdq L j t x v = fderiv ℝ Lt (t, x, v) (0, Pi.single j 1, 0) := by
    intro j t x v
    unfold dLdq
    have hp : HasDerivAt (fun y : ℝ => (t, Function.update x j y, v))
        ((0 : ℝ), (Pi.single j (1 : ℝ) : Fin n → ℝ), (0 : Fin n → ℝ)) (x j) :=
      (hasDerivAt_const _ t).prodMk ((hasDerivAt_update x j (x j)).prodMk (hasDerivAt_const _ v))
    have hl : HasFDerivAt Lt (fderiv ℝ Lt (t, x, v)) (t, Function.update x j (x j), v) := by
      rw [Function.update_eq_self]; exact (hLd _).hasFDerivAt
    exact (hl.comp_hasDerivAt (x j) hp).deriv
  have hdv : ∀ j t x v, dLdv L j t x v = fderiv ℝ Lt (t, x, v) (0, 0, Pi.single j 1) := by
    intro j t x v
    unfold dLdv
    have hp : HasDerivAt (fun y : ℝ => (t, x, Function.update v j y))
        ((0 : ℝ), (0 : Fin n → ℝ), (Pi.single j (1 : ℝ) : Fin n → ℝ)) (v j) :=
      (hasDerivAt_const _ t).prodMk ((hasDerivAt_const _ x).prodMk (hasDerivAt_update v j (v j)))
    have hl : HasFDerivAt Lt (fderiv ℝ Lt (t, x, v)) (t, x, Function.update v j (v j)) := by
      rw [Function.update_eq_self]; exact (hLd _).hasFDerivAt
    exact (hl.comp_hasDerivAt (v j) hp).deriv
  -- linear decomposition of directions
  have hsingle : ∀ w : Fin n → ℝ, w = ∑ j, w j • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
    intro w; ext i; simp [Finset.sum_apply, Pi.single_apply]
  have decq : ∀ p (w : Fin n → ℝ), fderiv ℝ Lt p (0, w, 0) =
      ∑ j, w j * fderiv ℝ Lt p (0, Pi.single j 1, 0) := by
    intro p w
    have e : ((0 : ℝ), w, (0 : Fin n → ℝ)) =
        ∑ j, w j • ((0 : ℝ), (Pi.single j (1 : ℝ) : Fin n → ℝ), (0 : Fin n → ℝ)) := by
      conv_lhs => rw [hsingle w]
      ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
    rw [e, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
  have decv : ∀ p (w : Fin n → ℝ), fderiv ℝ Lt p (0, 0, w) =
      ∑ j, w j * fderiv ℝ Lt p (0, 0, Pi.single j 1) := by
    intro p w
    have e : ((0 : ℝ), (0 : Fin n → ℝ), w) =
        ∑ j, w j • ((0 : ℝ), (0 : Fin n → ℝ), (Pi.single j (1 : ℝ) : Fin n → ℝ)) := by
      conv_lhs => rw [hsingle w]
      ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
    rw [e, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
  -- velocities and accelerations
  have hqi : ∀ i, ContDiff ℝ 2 (fun s => q s i) := fun i =>
    contDiff_infty.mp ((contDiff_apply ℝ ℝ i).comp hq) 2
  have hvel_d : ∀ i, Differentiable ℝ (fun s => vel q s i) := fun i =>
    ((hqi i).iterate_deriv' 1 1).differentiable one_ne_zero
  set a : ℝ → Fin n → ℝ := fun s i => deriv (fun r => vel q r i) s with hadef
  have hqd : ∀ t, HasDerivAt q (vel q t) t := fun t =>
    hasDerivAt_pi.mpr fun i => (((hqi i).differentiable (by norm_num)) t).hasDerivAt
  have hvd : ∀ t, HasDerivAt (vel q) (a t) t := fun t =>
    hasDerivAt_pi.mpr fun i => ((hvel_d i) t).hasDerivAt
  have hH : ∀ t, HasDerivAt (fun t => hamiltonian L t (q t) (vel q t)) 0 t := by
    intro t
    have hγ : HasDerivAt (fun s => (s, q s, vel q s)) ((1 : ℝ), vel q t, a t) t :=
      (hasDerivAt_id t).prodMk ((hqd t).prodMk (hvd t))
    have hLγ := (hLd (t, q t, vel q t)).hasFDerivAt.comp_hasDerivAt t hγ
    have hsum : HasDerivAt (fun s => ∑ j, vel q s j * dLdv L j s (q s) (vel q s))
        (∑ j, (a t j * dLdv L j t (q t) (vel q t) + vel q t j * dLdq L j t (q t) (vel q t))) t := by
      apply HasDerivAt.fun_sum
      intro j _
      exact ((hvel_d j) t).hasDerivAt.mul (hmot j t)
    unfold hamiltonian
    refine (hsum.fun_sub hLγ).congr_deriv ?_
    have e3 : ((1 : ℝ), vel q t, a t) = ((1 : ℝ), (0 : Fin n → ℝ), (0 : Fin n → ℝ)) +
        ((0 : ℝ), vel q t, (0 : Fin n → ℝ)) + ((0 : ℝ), (0 : Fin n → ℝ), a t) := by
      ext <;> simp
    rw [e3, map_add, map_add, decq, decv, ← ht, hLt]
    simp only [hdq, hdv, Finset.sum_add_distrib]
    ring
  exact fun t₁ t₂ => is_const_of_deriv_eq_zero (fun s => (hH s).differentiableAt)
    (fun s => (hH s).deriv) t₁ t₂
