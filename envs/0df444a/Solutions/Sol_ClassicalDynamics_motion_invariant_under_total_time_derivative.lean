-- Prove2me | solution 1 for ClassicalDynamics.motion_invariant_under_total_time_derivative
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T05:24:08.645099+00:00
-- url     : https://prove2.me/submissions/dd9b17ad-986e-417a-b4e4-207e356c1150

import Definitions.Def_ClassicalDynamics_core

open ClassicalDynamics

theorem solution {n : ℕ} (L : Lagrangian n)
    (hL : IsSmoothLagrangian L) (f : ℝ → (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => f p.1 p.2))
    (q : ℝ → Fin n → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    IsMotion L q ↔
      IsMotion (fun t x v =>
        L t x v + (deriv (fun s : ℝ => f s x) t + ∑ i : Fin n, v i * dfdq f i t x)) q := by
  classical
  set Lt : ℝ × (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p => L p.1 p.2.1 p.2.2 with hLtdef
  have hLs : ContDiff ℝ (⊤ : ℕ∞) Lt := hL
  have hLd : Differentiable ℝ Lt := hLs.differentiable (by simp)
  set F : ℝ × (Fin n → ℝ) → ℝ := fun p => f p.1 p.2 with hFdef
  have hF2 : ContDiff ℝ 2 F := contDiff_infty.mp hf 2
  have hFd : Differentiable ℝ F := hF2.differentiable (by norm_num)
  set D := fderiv ℝ F with hDdef
  have hDd : Differentiable ℝ D :=
    (hF2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  set D2 := fderiv ℝ D with hD2def
  have hsymm : ∀ p, ∀ a b, D2 p a b = D2 p b a := fun p =>
    (hF2.contDiffAt (x := p)).isSymmSndFDerivAt (by simp)
  -- the added term is `D (t, x) (1, v)`
  have hft : ∀ t x, deriv (fun s => f s x) t = D (t, x) (1, 0) := by
    intro t x
    have hp : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : Fin n → ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    exact ((hFd (t, x)).hasFDerivAt.comp_hasDerivAt t hp).deriv
  have hfq : ∀ j t x, dfdq f j t x = D (t, x) (0, Pi.single j 1) := by
    intro j t x
    unfold dfdq
    have hp : HasDerivAt (fun y : ℝ => (t, Function.update x j y))
        ((0 : ℝ), (Pi.single j (1 : ℝ) : Fin n → ℝ)) (x j) :=
      (hasDerivAt_const _ t).prodMk (hasDerivAt_update x j (x j))
    have hl : HasFDerivAt F (D (t, x)) (t, Function.update x j (x j)) := by
      rw [Function.update_eq_self]; exact (hFd _).hasFDerivAt
    exact (hl.comp_hasDerivAt (x j) hp).deriv
  have hsingle : ∀ w : Fin n → ℝ, w = ∑ j, w j • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
    intro w; ext i; simp [Finset.sum_apply, Pi.single_apply]
  have hextra : ∀ t x v, deriv (fun s : ℝ => f s x) t + ∑ i : Fin n, v i * dfdq f i t x =
      D (t, x) (1, v) := by
    intro t x v
    have e : ((1 : ℝ), v) = ((1 : ℝ), (0 : Fin n → ℝ)) +
        ∑ j, v j • ((0 : ℝ), (Pi.single j (1 : ℝ) : Fin n → ℝ)) := by
      conv_lhs => rw [hsingle v]
      ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
    rw [e, map_add, map_sum, hft]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, hfq]
  have hL' : (fun t x v =>
      L t x v + (deriv (fun s : ℝ => f s x) t + ∑ i : Fin n, v i * dfdq f i t x)) =
      fun t x v => L t x v + D (t, x) (1, v) := by
    funext t x v; rw [hextra]
  rw [hL']
  -- partial derivatives of the new Lagrangian
  have hv' : ∀ i t x v, dLdv (fun t x v => L t x v + D (t, x) (1, v)) i t x v =
      dLdv L i t x v + D (t, x) (0, Pi.single i 1) := by
    intro i t x v
    have hp : HasDerivAt (fun y : ℝ => (t, x, Function.update v i y))
        ((0 : ℝ), (0 : Fin n → ℝ), (Pi.single i (1 : ℝ) : Fin n → ℝ)) (v i) :=
      (hasDerivAt_const _ t).prodMk ((hasDerivAt_const _ x).prodMk (hasDerivAt_update v i (v i)))
    have hl : HasFDerivAt Lt (fderiv ℝ Lt (t, x, v)) (t, x, Function.update v i (v i)) := by
      rw [Function.update_eq_self]; exact (hLd _).hasFDerivAt
    have h0 := hl.comp_hasDerivAt (v i) hp
    have hdf : DifferentiableAt ℝ (fun y => L t x (Function.update v i y)) (v i) := h0.differentiableAt
    have hA : HasDerivAt (fun y => L t x (Function.update v i y)) (dLdv L i t x v) (v i) :=
      hdf.hasDerivAt
    have hp2 : HasDerivAt (fun y : ℝ => ((1 : ℝ), Function.update v i y))
        ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin n → ℝ)) (v i) :=
      (hasDerivAt_const _ (1 : ℝ)).prodMk (hasDerivAt_update v i (v i))
    have hB := (D (t, x)).hasFDerivAt.comp_hasDerivAt (v i) hp2
    exact (hA.add hB).deriv
  have hq' : ∀ i t x v, dLdq (fun t x v => L t x v + D (t, x) (1, v)) i t x v =
      dLdq L i t x v + D2 (t, x) (0, Pi.single i 1) (1, v) := by
    intro i t x v
    have hp : HasDerivAt (fun y : ℝ => (t, Function.update x i y, v))
        ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin n → ℝ), (0 : Fin n → ℝ)) (x i) :=
      (hasDerivAt_const _ t).prodMk ((hasDerivAt_update x i (x i)).prodMk (hasDerivAt_const _ v))
    have hl : HasFDerivAt Lt (fderiv ℝ Lt (t, x, v)) (t, Function.update x i (x i), v) := by
      rw [Function.update_eq_self]; exact (hLd _).hasFDerivAt
    have h0 := hl.comp_hasDerivAt (x i) hp
    have hdf : DifferentiableAt ℝ (fun y => L t (Function.update x i y) v) (x i) := h0.differentiableAt
    have hA : HasDerivAt (fun y => L t (Function.update x i y) v) (dLdq L i t x v) (x i) :=
      hdf.hasDerivAt
    have hp2 : HasDerivAt (fun y : ℝ => (t, Function.update x i y))
        ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin n → ℝ)) (x i) :=
      (hasDerivAt_const _ t).prodMk (hasDerivAt_update x i (x i))
    have hl2 : HasFDerivAt D (D2 (t, x)) (t, Function.update x i (x i)) := by
      rw [Function.update_eq_self]; exact (hDd _).hasFDerivAt
    have hB := (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), v)).hasFDerivAt.comp_hasDerivAt (x i)
      (hl2.comp_hasDerivAt (x i) hp2)
    exact (hA.add hB).deriv
  -- time derivative of the extra momentum along the path
  have hqi : ∀ i, ContDiff ℝ 2 (fun s => q s i) := fun i =>
    contDiff_infty.mp ((contDiff_apply ℝ ℝ i).comp hq) 2
  have hqd : ∀ t, HasDerivAt q (vel q t) t := fun t =>
    hasDerivAt_pi.mpr fun i => (((hqi i).differentiable (by norm_num)) t).hasDerivAt
  have hg : ∀ i t, HasDerivAt (fun s => D (s, q s) (0, Pi.single i 1))
      (D2 (t, q t) (0, Pi.single i 1) (1, vel q t)) t := by
    intro i t
    have hp : HasDerivAt (fun s : ℝ => (s, q s)) ((1 : ℝ), vel q t) t :=
      (hasDerivAt_id t).prodMk (hqd t)
    rw [hsymm]
    exact (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin n → ℝ))).hasFDerivAt.comp_hasDerivAt t
      ((hDd _).hasFDerivAt.comp_hasDerivAt t hp)
  unfold IsMotion
  refine forall_congr' fun i => forall_congr' fun t => ?_
  simp only [hv', hq']
  constructor
  · intro h; exact h.add (hg i t)
  · intro h
    have := h.fun_sub (hg i t)
    simp only [add_sub_cancel_right] at this
    exact this
