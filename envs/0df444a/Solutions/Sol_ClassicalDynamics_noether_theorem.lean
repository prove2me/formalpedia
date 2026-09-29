-- Prove2me | solution 1 for ClassicalDynamics.noether_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T05:12:32.051397+00:00
-- url     : https://prove2.me/submissions/859efe12-9ce0-4fe8-96db-90eeec30ef07

import Definitions.Def_ClassicalDynamics_core

open ClassicalDynamics

namespace NAux

/-- Mixed partials of a smooth function of two real variables commute, in the form needed:
`∂ᵤ (∂ₜ Φ)(u₀, t) = ∂ₜ (∂ᵤ Φ)(u₀, t)` as derivatives of the one-variable slices. -/
lemma mixed (Φ : ℝ × ℝ → ℝ) (hΦ : ContDiff ℝ 2 Φ) (u₀ t : ℝ) :
    HasDerivAt (fun u => deriv (fun r => Φ (u, r)) t)
      (deriv (fun r => deriv (fun u => Φ (u, r)) u₀) t) u₀ := by
  have hd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hsymm := (hΦ.contDiffAt (x := (u₀, t))).isSymmSndFDerivAt (by simp [minSmoothness])
  -- slices as directional derivatives
  have hr : ∀ u r, HasDerivAt (fun r => Φ (u, r)) (fderiv ℝ Φ (u, r) (0, 1)) r := by
    intro u r
    have hp : HasDerivAt (fun r : ℝ => (u, r)) ((0 : ℝ), (1 : ℝ)) r :=
      (hasDerivAt_const r u).prodMk (hasDerivAt_id r)
    exact (hd (u, r)).hasFDerivAt.comp_hasDerivAt r hp
  have hu : ∀ u r, HasDerivAt (fun u => Φ (u, r)) (fderiv ℝ Φ (u, r) (1, 0)) u := by
    intro u r
    have hp : HasDerivAt (fun u : ℝ => (u, r)) ((1 : ℝ), (0 : ℝ)) u :=
      (hasDerivAt_id u).prodMk (hasDerivAt_const u r)
    exact (hd (u, r)).hasFDerivAt.comp_hasDerivAt u hp
  have e1 : (fun u => deriv (fun r => Φ (u, r)) t) = fun u => fderiv ℝ Φ (u, t) (0, 1) := by
    funext u; exact (hr u t).deriv
  have e2 : (fun r => deriv (fun u => Φ (u, r)) u₀) = fun r => fderiv ℝ Φ (u₀, r) (1, 0) := by
    funext r; exact (hu u₀ r).deriv
  rw [e1, e2]
  -- derivatives of the directional-derivative slices
  have h1 : HasDerivAt (fun u => fderiv ℝ Φ (u, t) (0, 1))
      (fderiv ℝ (fderiv ℝ Φ) (u₀, t) (1, 0) (0, 1)) u₀ := by
    have hp : HasDerivAt (fun u : ℝ => (u, t)) ((1 : ℝ), (0 : ℝ)) u₀ :=
      (hasDerivAt_id u₀).prodMk (hasDerivAt_const u₀ t)
    have := (hD (u₀, t)).hasFDerivAt.comp_hasDerivAt u₀ hp
    exact (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).hasFDerivAt.comp_hasDerivAt u₀ this
  have h2 : HasDerivAt (fun r => fderiv ℝ Φ (u₀, r) (1, 0))
      (fderiv ℝ (fderiv ℝ Φ) (u₀, t) (0, 1) (1, 0)) t := by
    have hp : HasDerivAt (fun r : ℝ => (u₀, r)) ((0 : ℝ), (1 : ℝ)) t :=
      (hasDerivAt_const t u₀).prodMk (hasDerivAt_id t)
    have := (hD (u₀, t)).hasFDerivAt.comp_hasDerivAt t hp
    exact (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))).hasFDerivAt.comp_hasDerivAt t this
  rw [h2.deriv, ← hsymm]
  exact h1

end NAux

open NAux in
theorem solution {n : ℕ} (L : Lagrangian n) (hL : IsSmoothLagrangian L)
    (Q : ℝ → ℝ → Fin n → ℝ)
    (hQ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Q p.1 p.2))
    (hsym : IsContinuousSymmetry L Q) (hmot : IsMotion L (Q 0)) :
    IsConstantInTime (noetherCharge L Q) := by
  classical
  set Lt : ℝ × (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p => L p.1 p.2.1 p.2.2 with hLtdef
  have hLs : ContDiff ℝ (⊤ : ℕ∞) Lt := hL
  have hLd : Differentiable ℝ Lt := hLs.differentiable (by simp)
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
  -- coordinate functions of `Q`
  have hQ2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => Q p.1 p.2) := contDiff_infty.mp hQ 2
  have hQi : ∀ i, ContDiff ℝ 2 (fun p : ℝ × ℝ => Q p.1 p.2 i) := fun i =>
    (contDiff_apply ℝ ℝ i).comp hQ2
  have hQid : ∀ i, Differentiable ℝ (fun p : ℝ × ℝ => Q p.1 p.2 i) := fun i =>
    (hQi i).differentiable (by norm_num)
  -- slice derivatives
  have hsl_u : ∀ i u t, HasDerivAt (fun u => Q u t i) (deriv (fun u => Q u t i) u) u := by
    intro i u t
    have hp : DifferentiableAt ℝ (fun u : ℝ => (u, t)) u :=
      differentiableAt_id.prodMk (differentiableAt_const t)
    exact (((hQid i) (u, t)).comp u hp).hasDerivAt
  have hsl_t : ∀ i u t, HasDerivAt (fun r => Q u r i) (deriv (fun r => Q u r i) t) t := by
    intro i u t
    have hp : DifferentiableAt ℝ (fun r : ℝ => (u, r)) t :=
      (differentiableAt_const u).prodMk differentiableAt_id
    exact (((hQid i) (u, t)).comp t hp).hasDerivAt
  -- `w i t = ∂ᵤQᵢ(0, t)` and its time derivative, via mixed partials
  have hmix := fun i t => mixed (fun p : ℝ × ℝ => Q p.1 p.2 i) (hQi i) 0 t
  have hw : ∀ i t, HasDerivAt (fun r => deriv (fun u => Q u r i) 0)
      (deriv (fun r => deriv (fun u => Q u r i) 0) t) t := by
    intro i t
    -- differentiability of `r ↦ ∂ᵤQᵢ(0, r)`
    have hD : Differentiable ℝ (fderiv ℝ (fun p : ℝ × ℝ => Q p.1 p.2 i)) :=
      ((hQi i).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    have e : (fun r => deriv (fun u => Q u r i) 0) =
        fun r => fderiv ℝ (fun p : ℝ × ℝ => Q p.1 p.2 i) (0, r) (1, 0) := by
      funext r
      have hp : HasDerivAt (fun u : ℝ => (u, r)) ((1 : ℝ), (0 : ℝ)) 0 :=
        (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 r)
      exact ((hQid i (0, r)).hasFDerivAt.comp_hasDerivAt 0 hp).deriv
    rw [e]
    have hp : DifferentiableAt ℝ (fun r : ℝ => ((0 : ℝ), r)) t :=
      (differentiableAt_const 0).prodMk differentiableAt_id
    exact (((hD _).comp t hp).clm_apply (differentiableAt_const _)).hasDerivAt
  -- velocity of `Q u` and its `u`-derivative
  have hvelu : ∀ t, HasDerivAt (fun u => vel (Q u) t)
      (fun i => deriv (fun r => deriv (fun u => Q u r i) 0) t) 0 := by
    intro t
    rw [hasDerivAt_pi]
    intro i
    exact hmix i t
  have hQu : ∀ t, HasDerivAt (fun u => Q u t) (fun i => deriv (fun u => Q u t i) 0) 0 := by
    intro t; rw [hasDerivAt_pi]; intro i; exact hsl_u i 0 t
  -- the symmetry condition at `u = 0`, expanded by the chain rule
  have hsym0 : ∀ t, (∑ j, deriv (fun u => Q u t j) 0 * dLdq L j t (Q 0 t) (vel (Q 0) t)) +
      (∑ j, deriv (fun r => deriv (fun u => Q u r j) 0) t * dLdv L j t (Q 0 t) (vel (Q 0) t)) = 0 := by
    intro t
    have hγ : HasDerivAt (fun u => (t, Q u t, vel (Q u) t))
        ((0 : ℝ), (fun i => deriv (fun u => Q u t i) 0),
          (fun i => deriv (fun r => deriv (fun u => Q u r i) 0) t)) 0 :=
      (hasDerivAt_const 0 t).prodMk ((hQu t).prodMk (hvelu t))
    have hc := ((hLd (t, Q 0 t, vel (Q 0) t)).hasFDerivAt.comp_hasDerivAt 0 hγ).deriv
    have h0 := hsym 0 t
    simp only [Function.comp_def] at hc
    rw [hc] at h0
    have e3 : ((0 : ℝ), (fun i => deriv (fun u => Q u t i) 0),
        (fun i => deriv (fun r => deriv (fun u => Q u r i) 0) t)) =
        ((0 : ℝ), (fun i => deriv (fun u => Q u t i) 0), (0 : Fin n → ℝ)) +
        ((0 : ℝ), (0 : Fin n → ℝ), (fun i => deriv (fun r => deriv (fun u => Q u r i) 0) t)) := by
      ext <;> simp
    rw [e3, map_add, decq, decv] at h0
    simp only [hdq, hdv]
    exact h0
  -- derivative of the charge
  have hC : ∀ t, HasDerivAt (noetherCharge L Q) 0 t := by
    intro t
    unfold noetherCharge
    have hsum : HasDerivAt (fun s => ∑ i : Fin n,
        dLdv L i s (Q 0 s) (vel (Q 0) s) * deriv (fun u => Q u s i) 0)
        (∑ i : Fin n, (dLdq L i t (Q 0 t) (vel (Q 0) t) * deriv (fun u => Q u t i) 0 +
          dLdv L i t (Q 0 t) (vel (Q 0) t) * deriv (fun r => deriv (fun u => Q u r i) 0) t)) t := by
      apply HasDerivAt.fun_sum
      intro i _
      exact (hmot i t).mul (hw i t)
    refine hsum.congr_deriv ?_
    rw [Finset.sum_add_distrib]
    have := hsym0 t
    have e1 : ∑ i, dLdq L i t (Q 0 t) (vel (Q 0) t) * deriv (fun u => Q u t i) 0 =
        ∑ j, deriv (fun u => Q u t j) 0 * dLdq L j t (Q 0 t) (vel (Q 0) t) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    have e2 : ∑ i, dLdv L i t (Q 0 t) (vel (Q 0) t) * deriv (fun r => deriv (fun u => Q u r i) 0) t =
        ∑ j, deriv (fun r => deriv (fun u => Q u r j) 0) t * dLdv L j t (Q 0 t) (vel (Q 0) t) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e1, e2]
    linarith
  exact fun t₁ t₂ => is_const_of_deriv_eq_zero (fun s => (hC s).differentiableAt)
    (fun s => (hC s).deriv) t₁ t₂
