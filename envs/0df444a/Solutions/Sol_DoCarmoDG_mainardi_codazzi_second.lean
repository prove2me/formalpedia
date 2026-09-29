-- Prove2me | solution 1 for DoCarmoDG.mainardi_codazzi_second
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T19:19:49.963305+00:00
-- url     : https://prove2.me/submissions/5c0e6daa-642c-4d24-961b-1dc45e919c2a

import Mathlib
import Definitions.Def_DoCarmo_surface_patch

/-! 8554d523 DoCarmoDG.mainardi_codazzi_second (do Carmo §4-3, eq. (6a)).
Route: differentiate f = <N, x_uv> in v and g = <N, x_vv> in u; the third-order terms cancel
since x_uvv = x_vvu (Clairaut twice, via `ContDiffAt.isSymmSndFDerivAt`). The remaining
<N_v, x_uv> - <N_u, x_vv> is evaluated by expanding x_uv, x_vv with the Christoffel relations
and the identities <N_v,x_u> = -f, <N_v,x_v> = -g, <N_u,x_u> = -e, <N_u,x_v> = -f,
<N_u,N> = <N_v,N> = 0 obtained by differentiating <N,x_u> = <N,x_v> = 0 and |N|^2 = 1.
The unit normal is smooth on U because x_u ∧ x_v ≠ 0 there. Curried-partial lemmas reused
from the accepted Theorema Egregium proof (17a9a4b7). -/

set_option autoImplicit false

namespace CodazziTwoBuild

open DoCarmoDG Filter Topology

abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-! ## Curried partial derivatives of a smooth map on an open set -/

theorem eg_evU {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u v : ℝ} (hp : (u, v) ∈ U) :
    ∀ᶠ t in 𝓝 u, (t, v) ∈ U :=
  (Continuous.prodMk_left v).continuousAt.preimage_mem_nhds (hU.mem_nhds hp)

theorem eg_evV {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u v : ℝ} (hp : (u, v) ∈ U) :
    ∀ᶠ t in 𝓝 v, (u, t) ∈ U :=
  (Continuous.prodMk_right u).continuousAt.preimage_mem_nhds (hU.mem_nhds hp)

theorem eg_lineU (u v : ℝ) : HasDerivAt (fun t : ℝ => (t, v)) ((1 : ℝ), (0 : ℝ)) u :=
  (hasDerivAt_id u).prodMk (hasDerivAt_const u v)

theorem eg_lineV (u v : ℝ) : HasDerivAt (fun t : ℝ => (u, t)) ((0 : ℝ), (1 : ℝ)) v :=
  (hasDerivAt_const v u).prodMk (hasDerivAt_id v)

theorem eg_hasDerivAt_u {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    HasDerivAt (fun t => f t v) (fderiv ℝ (Function.uncurry f) (u, v) ((1 : ℝ), (0 : ℝ))) u := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (u, v) :=
    (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt u (eg_lineU u v)

theorem eg_hasDerivAt_v {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    HasDerivAt (fun t => f u t) (fderiv ℝ (Function.uncurry f) (u, v) ((0 : ℝ), (1 : ℝ))) v := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (u, v) :=
    (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt v (eg_lineV u v)

theorem eg_pU {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    HasDerivAt (fun t => f t v) (partialU f u v) u := by
  have h := eg_hasDerivAt_u hU hf hp
  rw [partialU, h.deriv]; exact h

theorem eg_pV {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    HasDerivAt (fun t => f u t) (partialV f u v) v := by
  have h := eg_hasDerivAt_v hU hf hp
  rw [partialV, h.deriv]; exact h

theorem eg_smoothU {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (partialU f)) U := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (Function.uncurry f)) U :=
    hf.fderiv_of_isOpen hU (by simp)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q => fderiv ℝ (Function.uncurry f) q ((1 : ℝ), (0 : ℝ))) U :=
    h1.clm_apply contDiffOn_const
  refine h2.congr ?_
  rintro ⟨u, v⟩ hp
  exact (eg_hasDerivAt_u hU hf hp).deriv

theorem eg_smoothV {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (partialV f)) U := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (Function.uncurry f)) U :=
    hf.fderiv_of_isOpen hU (by simp)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q => fderiv ℝ (Function.uncurry f) q ((0 : ℝ), (1 : ℝ))) U :=
    h1.clm_apply contDiffOn_const
  refine h2.congr ?_
  rintro ⟨u, v⟩ hp
  exact (eg_hasDerivAt_v hU hf hp).deriv

/-- Clairaut: `f_vu = f_uv` on `U`. -/
theorem eg_symm {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) U) {u v : ℝ} (hp : (u, v) ∈ U) :
    partialU (partialV f) u v = partialV (partialU f) u v := by
  have hD : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (Function.uncurry f)) U :=
    hf.fderiv_of_isOpen hU (by simp)
  have hDd : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) (u, v) :=
    (hD.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have e1 : (fun t => partialV f t v) =ᶠ[𝓝 u]
      (fun t => fderiv ℝ (Function.uncurry f) (t, v) ((0 : ℝ), (1 : ℝ))) := by
    filter_upwards [eg_evU hU hp] with t ht
    exact (eg_hasDerivAt_v hU hf ht).deriv
  have e2 : (fun t => partialU f u t) =ᶠ[𝓝 v]
      (fun t => fderiv ℝ (Function.uncurry f) (u, t) ((1 : ℝ), (0 : ℝ))) := by
    filter_upwards [eg_evV hU hp] with t ht
    exact (eg_hasDerivAt_u hU hf ht).deriv
  have d1 : HasDerivAt (fun t => fderiv ℝ (Function.uncurry f) (t, v) ((0 : ℝ), (1 : ℝ)))
      (fderiv ℝ (fderiv ℝ (Function.uncurry f)) (u, v) ((1 : ℝ), (0 : ℝ))
        ((0 : ℝ), (1 : ℝ))) u := by
    have h := (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3))
      ((0 : ℝ), (1 : ℝ))).hasFDerivAt.comp_hasDerivAt u
      (hDd.hasFDerivAt.comp_hasDerivAt u (eg_lineU u v))
    simpa [Function.comp_def] using h
  have d2 : HasDerivAt (fun t => fderiv ℝ (Function.uncurry f) (u, t) ((1 : ℝ), (0 : ℝ)))
      (fderiv ℝ (fderiv ℝ (Function.uncurry f)) (u, v) ((0 : ℝ), (1 : ℝ))
        ((1 : ℝ), (0 : ℝ))) v := by
    have h := (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3))
      ((1 : ℝ), (0 : ℝ))).hasFDerivAt.comp_hasDerivAt v
      (hDd.hasFDerivAt.comp_hasDerivAt v (eg_lineV u v))
    simpa [Function.comp_def] using h
  have hsymm := (hf.contDiffAt (hU.mem_nhds hp)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  show deriv (fun t => partialV f t v) u = deriv (fun t => partialU f u t) v
  rw [e1.deriv_eq, e2.deriv_eq, d1.deriv, d2.deriv]
  exact hsymm _ _


/-! ## The cross product and the unit normal -/

theorem contDiff_cross : ContDiff ℝ (⊤ : ℕ∞) (fun p : E3 × E3 => cross p.1 p.2) := by
  unfold cross
  refine PiLp.contDiff_toLp.comp (contDiff_pi.2 fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

theorem cross_apply (u v : E3) :
    cross u v 0 = u 1 * v 2 - u 2 * v 1 ∧ cross u v 1 = u 2 * v 0 - u 0 * v 2 ∧
      cross u v 2 = u 0 * v 1 - u 1 * v 0 := by
  simp [cross]

theorem inner_eq3 (u v : E3) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem cross_inner_left (u v : E3) : inner ℝ (cross u v) u = 0 := by
  rw [inner_eq3]; obtain ⟨h0, h1, h2⟩ := cross_apply u v; rw [h0, h1, h2]; ring

theorem cross_inner_right (u v : E3) : inner ℝ (cross u v) v = 0 := by
  rw [inner_eq3]; obtain ⟨h0, h1, h2⟩ := cross_apply u v; rw [h0, h1, h2]; ring

theorem normal_inner_u (x : ℝ → ℝ → E3) (a b : ℝ) :
    inner ℝ (unitNormal x a b) (partialU x a b) = 0 := by
  rw [unitNormal, real_inner_smul_left, cross_inner_left, mul_zero]

theorem normal_inner_v (x : ℝ → ℝ → E3) (a b : ℝ) :
    inner ℝ (unitNormal x a b) (partialV x a b) = 0 := by
  rw [unitNormal, real_inner_smul_left, cross_inner_right, mul_zero]

theorem normal_inner_self (x : ℝ → ℝ → E3) (a b : ℝ)
    (h : cross (partialU x a b) (partialV x a b) ≠ 0) :
    inner ℝ (unitNormal x a b) (unitNormal x a b) = 1 := by
  rw [real_inner_self_eq_norm_sq, unitNormal, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]
  norm_num

theorem normal_smooth {U : Set (ℝ × ℝ)} (hU : IsOpen U) {x : ℝ → ℝ → E3}
    (hx : IsRegularPatch U x) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (unitNormal x)) U := by
  have hn : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => cross (partialU x q.1 q.2) (partialV x q.1 q.2)) U :=
    contDiff_cross.comp_contDiffOn ((eg_smoothU hU hx.1).prodMk (eg_smoothV hU hx.1))
  have hm : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => ‖cross (partialU x q.1 q.2) (partialV x q.1 q.2)‖⁻¹) U :=
    (hn.norm ℝ (fun q hq => hx.2 q hq)).inv
      (fun q hq => norm_ne_zero_iff.2 (hx.2 q hq))
  exact hm.smul hn

/-! ## The second Mainardi–Codazzi equation -/

theorem codazzi_two (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x)
    (G111 G211 G112 G212 G122 G222 : ℝ → ℝ → ℝ)
    (hG : IsChristoffel U x G111 G211 G112 G212 G122 G222) :
    ∀ p ∈ U,
      deriv (fun t => coefff x p.1 t) p.2 - deriv (fun t => coeffg x t p.2) p.1 =
        coeffe x p.1 p.2 * G122 p.1 p.2 +
          coefff x p.1 p.2 * (G222 p.1 p.2 - G112 p.1 p.2) -
          coeffg x p.1 p.2 * G212 p.1 p.2 := by
  rintro ⟨u, v⟩ hp
  dsimp only
  have hxs := hx.1
  have hN := normal_smooth hU hx
  have hxu := eg_smoothU hU hxs
  have hxv := eg_smoothV hU hxs
  have hxuv := eg_smoothV hU hxu
  have hxvv := eg_smoothV hU hxv
  -- first-order derivatives
  have dNu := eg_pU hU hN hp
  have dNv := eg_pV hU hN hp
  have dAu := eg_pU hU hxu hp
  have dAv := eg_pV hU hxu hp
  have dbu := eg_pU hU hxv hp
  have dbv := eg_pV hU hxv hp
  rw [eg_symm hU hxs hp] at dbu
  have dB := eg_pV hU hxuv hp
  have dC := eg_pU hU hxvv hp
  -- third-order symmetry x_vvu = x_uvv
  have h3 : partialU (partialV (partialV x)) u v = partialV (partialV (partialU x)) u v := by
    rw [eg_symm hU hxv hp]
    show deriv (fun t => partialU (partialV x) u t) v = deriv (fun t => partialV (partialU x) u t) v
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [eg_evV hU hp] with t ht
    exact eg_symm hU hxs ht
  rw [h3] at dC
  -- f_v and g_u
  have hfv : deriv (fun t => coefff x u t) v =
      inner ℝ (unitNormal x u v) (partialV (partialV (partialU x)) u v) +
        inner ℝ (partialV (unitNormal x) u v) (partialV (partialU x) u v) :=
    (dNv.inner ℝ dB).deriv
  have hgu : deriv (fun t => coeffg x t v) u =
      inner ℝ (unitNormal x u v) (partialV (partialV (partialU x)) u v) +
        inner ℝ (partialU (unitNormal x) u v) (partialV (partialV x) u v) :=
    (dNu.inner ℝ dC).deriv
  -- relations from <N, x_u> = <N, x_v> = 0 and |N|² = 1
  have z0 : ∀ {g : ℝ → ℝ} {g' c s : ℝ}, HasDerivAt g g' s → (∀ᶠ t in 𝓝 s, g t = c) → g' = 0 :=
    fun {g g' c s} hg hc => (hg.congr_of_eventuallyEq
      (hc.mono fun t ht => ht.symm)).unique (hasDerivAt_const s c)
  have r1 : inner ℝ (unitNormal x u v) (partialV (partialU x) u v) +
      inner ℝ (partialV (unitNormal x) u v) (partialU x u v) = 0 :=
    z0 (dNv.inner ℝ dAv) (Eventually.of_forall fun t => normal_inner_u x u t)
  have r2 : inner ℝ (unitNormal x u v) (partialV (partialV x) u v) +
      inner ℝ (partialV (unitNormal x) u v) (partialV x u v) = 0 :=
    z0 (dNv.inner ℝ dbv) (Eventually.of_forall fun t => normal_inner_v x u t)
  have r3 : inner ℝ (unitNormal x u v) (partialU (partialU x) u v) +
      inner ℝ (partialU (unitNormal x) u v) (partialU x u v) = 0 :=
    z0 (dNu.inner ℝ dAu) (Eventually.of_forall fun t => normal_inner_u x t v)
  have r4 : inner ℝ (unitNormal x u v) (partialV (partialU x) u v) +
      inner ℝ (partialU (unitNormal x) u v) (partialV x u v) = 0 :=
    z0 (dNu.inner ℝ dbu) (Eventually.of_forall fun t => normal_inner_v x t v)
  have r5 : inner ℝ (unitNormal x u v) (partialV (unitNormal x) u v) +
      inner ℝ (partialV (unitNormal x) u v) (unitNormal x u v) = 0 := by
    refine z0 (c := 1) (dNv.inner ℝ dNv) ?_
    filter_upwards [eg_evV hU hp] with t ht
    exact normal_inner_self x u t (hx.2 (u, t) ht)
  have r6 : inner ℝ (unitNormal x u v) (partialU (unitNormal x) u v) +
      inner ℝ (partialU (unitNormal x) u v) (unitNormal x u v) = 0 := by
    refine z0 (c := 1) (dNu.inner ℝ dNu) ?_
    filter_upwards [eg_evU hU hp] with t ht
    exact normal_inner_self x t v (hx.2 (t, v) ht)
  rw [real_inner_comm (unitNormal x u v) (partialV (unitNormal x) u v)] at r5
  rw [real_inner_comm (unitNormal x u v) (partialU (unitNormal x) u v)] at r6
  -- Christoffel expansions
  obtain ⟨-, hB, hC⟩ := hG (u, v) hp
  dsimp only at hB hC
  have k1 : inner ℝ (partialV (unitNormal x) u v) (partialV (partialU x) u v) =
      G112 u v * inner ℝ (partialV (unitNormal x) u v) (partialU x u v) +
        G212 u v * inner ℝ (partialV (unitNormal x) u v) (partialV x u v) +
        coefff x u v * inner ℝ (partialV (unitNormal x) u v) (unitNormal x u v) := by
    rw [hB, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right]
  have k2 : inner ℝ (partialU (unitNormal x) u v) (partialV (partialV x) u v) =
      G122 u v * inner ℝ (partialU (unitNormal x) u v) (partialU x u v) +
        G222 u v * inner ℝ (partialU (unitNormal x) u v) (partialV x u v) +
        coeffg x u v * inner ℝ (partialU (unitNormal x) u v) (unitNormal x u v) := by
    rw [hC, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right]
  have ef : coefff x u v = inner ℝ (unitNormal x u v) (partialV (partialU x) u v) := rfl
  have eg : coeffg x u v = inner ℝ (unitNormal x u v) (partialV (partialV x) u v) := rfl
  have ee : coeffe x u v = inner ℝ (unitNormal x u v) (partialU (partialU x) u v) := rfl
  rw [hfv, hgu, k1, k2]
  have hr5 : inner ℝ (partialV (unitNormal x) u v) (unitNormal x u v) = 0 := by rw [real_inner_comm]; linarith
  have hr6 : inner ℝ (partialU (unitNormal x) u v) (unitNormal x u v) = 0 := by rw [real_inner_comm]; linarith
  rw [hr5, hr6]
  rw [ef, eg, ee]
  linear_combination G112 u v * r1 + G212 u v * r2 - G122 u v * r3 - G222 u v * r4

end CodazziTwoBuild

open DoCarmoDG in
theorem solution
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x)
    (G111 G211 G112 G212 G122 G222 : ℝ → ℝ → ℝ)
    (hG : IsChristoffel U x G111 G211 G112 G212 G122 G222) :
    ∀ p ∈ U,
      deriv (fun t => coefff x p.1 t) p.2 - deriv (fun t => coeffg x t p.2) p.1 =
        coeffe x p.1 p.2 * G122 p.1 p.2 +
          coefff x p.1 p.2 * (G222 p.1 p.2 - G112 p.1 p.2) -
          coeffg x p.1 p.2 * G212 p.1 p.2 := by
  exact CodazziTwoBuild.codazzi_two U hU x hx G111 G211 G112 G212 G122 G222 hG
