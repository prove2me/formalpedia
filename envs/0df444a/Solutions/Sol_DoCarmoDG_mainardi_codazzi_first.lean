-- Prove2me | solution 1 for DoCarmoDG.mainardi_codazzi_first
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T19:10:34.45837+00:00
-- url     : https://prove2.me/submissions/daa3d9fd-45e3-4a2c-9c11-98595d8ca75a

import Mathlib
import Definitions.Def_DoCarmo_surface_patch

/-! 13a271e0 DoCarmoDG.mainardi_codazzi_first (do Carmo §4-3).
With a = x_u, b = x_v, N the unit normal, A = x_uu, B = x_uv:
  e_v - f_u = <N_v, A> - <N_u, B>   (Clairaut on x_u: x_uuv = x_uvu),
and differentiating <N,a> = <N,b> = 0, <N,N> = 1 gives
  <N_u,a> = -e, <N_u,b> = -f, <N_v,a> = -f, <N_v,b> = -g, <N_u,N> = <N_v,N> = 0.
Expanding A and B in the Christoffel decomposition yields the claim.
Curried-partial toolkit reused from 17a9a4b7 (Theorema Egregium). -/

set_option autoImplicit false

namespace MainardiCodazziBuild

open DoCarmoDG Filter Topology

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

/-- Real functions that agree on the open set `U` have equal partial derivatives there. -/
theorem eg_congrU {U : Set (ℝ × ℝ)} (hU : IsOpen U) {g h : ℝ → ℝ → ℝ}
    (hgh : ∀ p ∈ U, g p.1 p.2 = h p.1 p.2) {u v : ℝ} (hp : (u, v) ∈ U) :
    deriv (fun t => g t v) u = deriv (fun t => h t v) u := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eg_evU hU hp] with t ht
  exact hgh _ ht

theorem eg_congrV {U : Set (ℝ × ℝ)} (hU : IsOpen U) {g h : ℝ → ℝ → ℝ}
    (hgh : ∀ p ∈ U, g p.1 p.2 = h p.1 p.2) {u v : ℝ} (hp : (u, v) ∈ U) :
    deriv (fun t => g u t) v = deriv (fun t => h u t) v := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eg_evV hU hp] with t ht
  exact hgh _ ht


theorem mc_inner3 (a b : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem mc_inner_cross_left (a b : EuclideanSpace ℝ (Fin 3)) : inner ℝ a (cross a b) = 0 := by
  rw [mc_inner3]; simp [cross]; ring

theorem mc_inner_cross_right (a b : EuclideanSpace ℝ (Fin 3)) : inner ℝ b (cross a b) = 0 := by
  rw [mc_inner3]; simp [cross]; ring

theorem mc_contDiff_cross :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      cross p.1 p.2) := by
  unfold cross
  refine PiLp.contDiff_toLp.comp (contDiff_pi.2 fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

theorem mc_smoothN {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)} (hx : IsRegularPatch U x) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (unitNormal x)) U := by
  have ha := eg_smoothU hU hx.1
  have hb := eg_smoothV hU hx.1
  have hc : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => cross (partialU x q.1 q.2) (partialV x q.1 q.2)) U :=
    mc_contDiff_cross.comp_contDiffOn (ha.prodMk hb)
  have hn : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => ‖cross (partialU x q.1 q.2) (partialV x q.1 q.2)‖) U :=
    hc.norm ℝ (fun q hq => hx.2 q hq)
  have hi : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => ‖cross (partialU x q.1 q.2) (partialV x q.1 q.2)‖⁻¹) U :=
    hn.inv (fun q hq => norm_ne_zero_iff.2 (hx.2 q hq))
  exact hi.smul hc

theorem mc_Na (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ) :
    inner ℝ (partialU x u v) (unitNormal x u v) = 0 := by
  simp only [unitNormal, inner_smul_right, mc_inner_cross_left, mul_zero]

theorem mc_Nb (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)) (u v : ℝ) :
    inner ℝ (partialV x u v) (unitNormal x u v) = 0 := by
  simp only [unitNormal, inner_smul_right, mc_inner_cross_right, mul_zero]

theorem mc_NN {U : Set (ℝ × ℝ)} {x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hx : IsRegularPatch U x) (p : ℝ × ℝ) (hp : p ∈ U) :
    inner ℝ (unitNormal x p.1 p.2) (unitNormal x p.1 p.2) = 1 := by
  have h0 := hx.2 p hp
  have hn : ‖cross (partialU x p.1 p.2) (partialV x p.1 p.2)‖ ≠ 0 := norm_ne_zero_iff.2 h0
  simp only [unitNormal, inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
  simp only [conj_trivial]
  field_simp

theorem mc_main (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x)
    (G111 G211 G112 G212 G122 G222 : ℝ → ℝ → ℝ)
    (hG : IsChristoffel U x G111 G211 G112 G212 G122 G222) :
    ∀ p ∈ U,
      deriv (fun t => coeffe x p.1 t) p.2 - deriv (fun t => coefff x t p.2) p.1 =
        coeffe x p.1 p.2 * G112 p.1 p.2 +
          coefff x p.1 p.2 * (G212 p.1 p.2 - G111 p.1 p.2) -
          coeffg x p.1 p.2 * G211 p.1 p.2 := by
  rintro ⟨u, v⟩ hp
  dsimp only
  have hxs := hx.1
  have hxu := eg_smoothU hU hxs
  have hxv := eg_smoothV hU hxs
  have hxuu := eg_smoothU hU hxu
  have hxuv := eg_smoothV hU hxu
  have hN := mc_smoothN hU hx
  -- first-order derivatives along the coordinate lines
  have hNu := eg_pU hU hN hp
  have hNv := eg_pV hU hN hp
  have haU := eg_pU hU hxu hp
  have haV := eg_pV hU hxu hp
  have hbU := eg_pU hU hxv hp
  have hbV := eg_pV hU hxv hp
  have hAV := eg_pV hU hxuu hp
  have hBU := eg_pU hU hxuv hp
  rw [eg_symm hU hxs hp] at hbU
  rw [eg_symm hU hxu hp] at hBU
  -- the two derivatives in the statement
  have hev : deriv (fun t => coeffe x u t) v =
      inner ℝ (partialV (unitNormal x) u v) (partialU (partialU x) u v) +
        inner ℝ (unitNormal x u v) (partialV (partialU (partialU x)) u v) := by
    rw [show (fun t => coeffe x u t) =
      fun t => inner ℝ (unitNormal x u t) (partialU (partialU x) u t) from rfl,
      (hNv.inner ℝ hAV).deriv]
    ring
  have hfu : deriv (fun t => coefff x t v) u =
      inner ℝ (partialU (unitNormal x) u v) (partialV (partialU x) u v) +
        inner ℝ (unitNormal x u v) (partialV (partialU (partialU x)) u v) := by
    rw [show (fun t => coefff x t v) =
      fun t => inner ℝ (unitNormal x t v) (partialV (partialU x) t v) from rfl,
      (hNu.inner ℝ hBU).deriv]
    ring
  -- derivatives of the orthogonality relations
  have z1 : deriv (fun t => inner ℝ (partialU x t v) (unitNormal x t v)) u = 0 := by
    rw [eg_congrU hU (g := fun a b => inner ℝ (partialU x a b) (unitNormal x a b))
      (h := fun _ _ => (0 : ℝ)) (fun q _ => mc_Na x q.1 q.2) hp]
    simp
  have z2 : deriv (fun t => inner ℝ (partialU x u t) (unitNormal x u t)) v = 0 := by
    rw [eg_congrV hU (g := fun a b => inner ℝ (partialU x a b) (unitNormal x a b))
      (h := fun _ _ => (0 : ℝ)) (fun q _ => mc_Na x q.1 q.2) hp]
    simp
  have z3 : deriv (fun t => inner ℝ (partialV x t v) (unitNormal x t v)) u = 0 := by
    rw [eg_congrU hU (g := fun a b => inner ℝ (partialV x a b) (unitNormal x a b))
      (h := fun _ _ => (0 : ℝ)) (fun q _ => mc_Nb x q.1 q.2) hp]
    simp
  have z4 : deriv (fun t => inner ℝ (partialV x u t) (unitNormal x u t)) v = 0 := by
    rw [eg_congrV hU (g := fun a b => inner ℝ (partialV x a b) (unitNormal x a b))
      (h := fun _ _ => (0 : ℝ)) (fun q _ => mc_Nb x q.1 q.2) hp]
    simp
  have z5 : deriv (fun t => inner ℝ (unitNormal x t v) (unitNormal x t v)) u = 0 := by
    rw [eg_congrU hU (g := fun a b => inner ℝ (unitNormal x a b) (unitNormal x a b))
      (h := fun _ _ => (1 : ℝ)) (fun q hq => mc_NN hx q hq) hp]
    simp
  have z6 : deriv (fun t => inner ℝ (unitNormal x u t) (unitNormal x u t)) v = 0 := by
    rw [eg_congrV hU (g := fun a b => inner ℝ (unitNormal x a b) (unitNormal x a b))
      (h := fun _ _ => (1 : ℝ)) (fun q hq => mc_NN hx q hq) hp]
    simp
  rw [(haU.inner ℝ hNu).deriv] at z1
  rw [(haV.inner ℝ hNv).deriv] at z2
  rw [(hbU.inner ℝ hNu).deriv] at z3
  rw [(hbV.inner ℝ hNv).deriv] at z4
  rw [(hNu.inner ℝ hNu).deriv] at z5
  rw [(hNv.inner ℝ hNv).deriv] at z6
  obtain ⟨hA, hB, -⟩ := hG (u, v) hp
  dsimp only at hA hB
  rw [hev, hfu]
  have eA : inner ℝ (partialV (unitNormal x) u v) (partialU (partialU x) u v) =
      G111 u v * inner ℝ (partialV (unitNormal x) u v) (partialU x u v) +
        G211 u v * inner ℝ (partialV (unitNormal x) u v) (partialV x u v) +
          coeffe x u v * inner ℝ (partialV (unitNormal x) u v) (unitNormal x u v) := by
    conv_lhs => rw [hA]
    simp only [inner_add_right, inner_smul_right]
  have eB : inner ℝ (partialU (unitNormal x) u v) (partialV (partialU x) u v) =
      G112 u v * inner ℝ (partialU (unitNormal x) u v) (partialU x u v) +
        G212 u v * inner ℝ (partialU (unitNormal x) u v) (partialV x u v) +
          coefff x u v * inner ℝ (partialU (unitNormal x) u v) (unitNormal x u v) := by
    conv_lhs => rw [hB]
    simp only [inner_add_right, inner_smul_right]
  rw [eA, eB]
  have ee : coeffe x u v = inner ℝ (unitNormal x u v) (partialU (partialU x) u v) := rfl
  have ef : coefff x u v = inner ℝ (unitNormal x u v) (partialV (partialU x) u v) := rfl
  have eg : coeffg x u v = inner ℝ (unitNormal x u v) (partialV (partialV x) u v) := rfl
  have c1 := real_inner_comm (partialU x u v) (partialU (unitNormal x) u v)
  have c2 := real_inner_comm (partialU x u v) (partialV (unitNormal x) u v)
  have c3 := real_inner_comm (partialV x u v) (partialU (unitNormal x) u v)
  have c4 := real_inner_comm (partialV x u v) (partialV (unitNormal x) u v)
  have c5 := real_inner_comm (unitNormal x u v) (partialU (unitNormal x) u v)
  have c6 := real_inner_comm (unitNormal x u v) (partialV (unitNormal x) u v)
  have d1 := real_inner_comm (partialU (partialU x) u v) (unitNormal x u v)
  have d2 := real_inner_comm (partialV (partialU x) u v) (unitNormal x u v)
  have d3 := real_inner_comm (partialV (partialV x) u v) (unitNormal x u v)
  have h5 : inner ℝ (partialU (unitNormal x) u v) (unitNormal x u v) = 0 := by linarith
  have h6 : inner ℝ (partialV (unitNormal x) u v) (unitNormal x u v) = 0 := by linarith
  have h1 : inner ℝ (partialU (unitNormal x) u v) (partialU x u v) = -coeffe x u v := by
    linarith
  have h2 : inner ℝ (partialV (unitNormal x) u v) (partialU x u v) = -coefff x u v := by
    linarith
  have h3 : inner ℝ (partialU (unitNormal x) u v) (partialV x u v) = -coefff x u v := by
    linarith
  have h4 : inner ℝ (partialV (unitNormal x) u v) (partialV x u v) = -coeffg x u v := by
    linarith
  rw [h1, h2, h3, h4, h5, h6]
  ring

end MainardiCodazziBuild

open DoCarmoDG in
theorem solution
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x)
    (G111 G211 G112 G212 G122 G222 : ℝ → ℝ → ℝ)
    (hG : IsChristoffel U x G111 G211 G112 G212 G122 G222) :
    ∀ p ∈ U,
      deriv (fun t => coeffe x p.1 t) p.2 - deriv (fun t => coefff x t p.2) p.1 =
        coeffe x p.1 p.2 * G112 p.1 p.2 +
          coefff x p.1 p.2 * (G212 p.1 p.2 - G111 p.1 p.2) -
          coeffg x p.1 p.2 * G211 p.1 p.2 := by
  exact MainardiCodazziBuild.mc_main U hU x hx G111 G211 G112 G212 G122 G222 hG
