-- Prove2me | solution 1 for ConvexOptimization.sc_suboptimality_from_decrement
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T17:33:21.083598+00:00
-- url     : https://prove2.me/submissions/4308cdfe-9fdd-4e40-8194-e2a05b005917

import Mathlib
import Definitions.Def_ConvexOptimization_IsBacktrackingStep
import Definitions.Def_ConvexOptimization_selfConcordance

open scoped RealInnerProductSpace ENNReal
open MeasureTheory
open ConvexOptimization

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000

namespace SCAux

open Set Filter
open scoped Topology

variable {n : ℕ}

/-! ### The slice of `Ω` along a line -/

theorem isOpen_slice {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩo : IsOpen Ω)
    (x v : EuclideanSpace ℝ (Fin n)) : IsOpen {t : ℝ | x + t • v ∈ Ω} :=
  hΩo.preimage (by fun_prop)

/-! ### Cauchy–Schwarz for the Hessian form -/

/-- The Riesz identification, as a plain continuous linear map. -/
noncomputable def rieszL (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) a)
      map_add' := fun a b => by
        ext w
        simp [inner_add_left]
      map_smul' := fun c a => by
        ext w
        simp [real_inner_smul_left] }

@[simp] theorem rieszL_apply (a b : EuclideanSpace ℝ (Fin n)) : rieszL n a b = ⟪a, b⟫ := rfl

/-- Symmetry of the second derivative, in the gradient/Hessian parametrisation. -/
theorem hess_symm {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩo : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) (a b : EuclideanSpace ℝ (Fin n)) :
    ⟪H x a, b⟫ = ⟪H x b, a⟫ := by
  have hf' : ∀ᶠ z in 𝓝 x, HasFDerivAt f (rieszL n (g z)) z := by
    filter_upwards [hΩo.mem_nhds hx] with z hz
    exact (hg z hz).hasFDerivAt
  have hf'' : HasFDerivAt (fun z => rieszL n (g z)) ((rieszL n).comp (H x)) x :=
    (rieszL n).hasFDerivAt.comp x (hH x hx)
  have hsymm := second_derivative_symmetric_of_eventually hf' hf'' a b
  simpa using hsymm

/-- Cauchy–Schwarz for a positive semidefinite symmetric bilinear form. -/
theorem quad_cs {A C B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ s : ℝ, 0 ≤ A + 2 * s * C + s ^ 2 * B) : C ^ 2 ≤ A * B := by
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · -- `B = 0` forces `C = 0`
    have hC : C = 0 := by
      by_contra hC
      have hkey := h (-(A + 1) / (2 * C))
      rw [← hB0] at hkey
      have hs : 2 * (-(A + 1) / (2 * C)) * C = -(A + 1) := by field_simp
      have hz : ((-(A + 1) / (2 * C)) ^ 2 * (0:ℝ)) = 0 := by ring
      rw [hs, hz, add_zero] at hkey
      linarith
    rw [hC]
    simpa using mul_nonneg hA hB
  · have hkey := h (-C / B)
    have hBne : B ≠ 0 := ne_of_gt hBpos
    have hs : 2 * (-C / B) * C + (-C / B) ^ 2 * B = -(C ^ 2 / B) := by
      field_simp
      ring
    rw [add_assoc, hs] at hkey
    have h2 : C ^ 2 / B ≤ A := by linarith
    rw [div_le_iff₀ hBpos] at h2
    linarith

end SCAux

namespace SCAux

open Set Filter
open scoped Topology

variable {n : ℕ}

/-- **The self-concordant lower bound** (B&V (9.44)): for a self-concordant `f`,
`f(y) ≥ f(x) + ∇f(x)ᵀ(y − x) + ω(‖y − x‖ₓ)` with `ω(z) = z − log(1 + z)`. -/
theorem line_lower_bound
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hsc : IsSelfConcordantOn Ω f)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (hHpd : ∀ x ∈ Ω, ∀ v, v ≠ 0 → 0 < ⟪H x v, v⟫)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ Ω) :
    f x + ⟪g x, y - x⟫ + (Real.sqrt ⟪H x (y - x), y - x⟫
      - Real.log (1 + Real.sqrt ⟪H x (y - x), y - x⟫)) ≤ f y := by
  classical
  by_cases hv0 : y - x = 0
  · have hyx : y = x := by
      have := sub_eq_zero.mp hv0
      exact this
    subst hyx
    simp
  set v : EuclideanSpace ℝ (Fin n) := y - x with hvdef
  -- the slice
  set S : Set ℝ := {t : ℝ | x + t • v ∈ Ω} with hS
  have hSopen : IsOpen S := isOpen_slice hΩo x v
  have hmemS : ∀ t ∈ S, x + t • v ∈ Ω := fun t ht => ht
  have hIcc : Set.Icc (0:ℝ) 1 ⊆ S := by
    intro t ht
    have hrw : x + t • v = (1 - t) • x + t • y := by rw [hvdef]; module
    show x + t • v ∈ Ω
    rw [hrw]
    exact hΩc hx hy (by linarith [ht.2]) ht.1 (by ring)
  have h0S : (0:ℝ) ∈ S := hIcc (by norm_num)
  have h1S : (1:ℝ) ∈ S := hIcc (by norm_num)
  -- the restriction and its first two derivatives
  set φ : ℝ → ℝ := fun t => f (x + t • v) with hφ
  set d1 : ℝ → ℝ := fun t => ⟪g (x + t • v), v⟫ with hd1
  set d2 : ℝ → ℝ := fun t => ⟪H (x + t • v) v, v⟫ with hd2
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v t := fun t => by
    exact (((hasDerivAt_id t).smul_const v).const_add x).congr_deriv (by first | rfl | simp | norm_num | ring)
  have hφd : ∀ t ∈ S, HasDerivAt φ (d1 t) t := by
    intro t ht
    have hgt := hg _ (hmemS t ht)
    have hcomp := (hgt.hasFDerivAt).comp_hasDerivAt t (hline t)
    exact hcomp.congr_deriv (by simp [hd1])
  have hd1d : ∀ t ∈ S, HasDerivAt d1 (d2 t) t := by
    intro t ht
    have hHt := hH _ (hmemS t ht)
    have h1 : HasDerivAt (fun s : ℝ => g (x + s • v)) (H (x + t • v) v) t :=
      hHt.comp_hasDerivAt t (hline t)
    exact (h1.inner ℝ (hasDerivAt_const t v)).congr_deriv (by simp [hd2])
  have hev : ∀ t ∈ S, deriv φ =ᶠ[𝓝 t] d1 := by
    intro t ht
    filter_upwards [hSopen.mem_nhds ht] with s hs using (hφd s hs).deriv
  have hu2 : ∀ t ∈ S, iteratedDeriv 2 φ t = d2 t := by
    intro t ht
    rw [iteratedDeriv_succ, iteratedDeriv_one, (hev t ht).deriv_eq]
    exact (hd1d t ht).deriv
  -- `φ` is `C³` on the slice, so `iteratedDeriv 2 φ` is differentiable there
  have hφC : ContDiffOn ℝ 3 φ S := by
    have hmap : Set.MapsTo (fun t : ℝ => x + t • v) S Ω := fun t ht => ht
    exact hsc.2.1.comp (by fun_prop) hmap
  have hdiff2 : ∀ t ∈ S, DifferentiableAt ℝ (iteratedDeriv 2 φ) t := by
    intro t ht
    have h1 : DifferentiableOn ℝ (iteratedDerivWithin 2 φ S) S :=
      hφC.differentiableOn_iteratedDerivWithin (by norm_num) hSopen.uniqueDiffOn
    have h2 : ∀ s ∈ S, iteratedDeriv 2 φ s = iteratedDerivWithin 2 φ S s :=
      fun s hs => (iteratedDerivWithin_of_isOpen hSopen hs).symm
    exact ((h1.congr h2) t ht).differentiableAt (hSopen.mem_nhds ht)
  set u : ℝ → ℝ := iteratedDeriv 2 φ with hu
  set u' : ℝ → ℝ := iteratedDeriv 3 φ with hu'
  have hud : ∀ t ∈ S, HasDerivAt u (u' t) t := by
    intro t ht
    have h := (hdiff2 t ht).hasDerivAt
    have hrw : u' t = deriv (iteratedDeriv 2 φ) t := by rw [hu', iteratedDeriv_succ]
    rw [hu, hrw]
    exact h
  have hupos : ∀ t ∈ S, 0 < u t := by
    intro t ht
    rw [hu2 t ht]
    simp only [hd2]
    exact hHpd _ (hmemS t ht) v hv0
  have hscb : ∀ t ∈ S, |u' t| ≤ 2 * (u t) ^ ((3:ℝ)/2) := by
    intro t ht
    have hshift : ∀ k : ℕ, iteratedDeriv k (fun s : ℝ => f ((x + t • v) + s • v)) 0
        = iteratedDeriv k φ t := by
      intro k
      have hfun : (fun s : ℝ => f ((x + t • v) + s • v)) = (fun z : ℝ => φ (t + z)) := by
        funext s
        rw [hφ]
        congr 1
        rw [add_smul]
        abel
      rw [hfun, iteratedDeriv_comp_const_add]
      simp
    have hb := hsc.2.2 _ (hmemS t ht) v
    rw [hshift 3, hshift 2] at hb
    exact hb
  -- the substitution `ψ = u^{-1/2}` is 1-Lipschitz
  set r : ℝ := Real.sqrt (u 0) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr (hupos 0 h0S)
  have hr2 : r ^ 2 = u 0 := Real.sq_sqrt (hupos 0 h0S).le
  set ψ : ℝ → ℝ := fun t => (Real.sqrt (u t))⁻¹ with hψ
  have hsqrtpos : ∀ t ∈ S, 0 < Real.sqrt (u t) := fun t ht => Real.sqrt_pos.mpr (hupos t ht)
  have hsq : ∀ t ∈ S, Real.sqrt (u t) ^ 2 = u t := fun t ht => Real.sq_sqrt (hupos t ht).le
  have hψd : ∀ t ∈ S,
      HasDerivAt ψ (-(u' t / (2 * Real.sqrt (u t))) / (u t)) t := by
    intro t ht
    have hs : HasDerivAt (fun s => Real.sqrt (u s)) (u' t / (2 * Real.sqrt (u t))) t := by
      have h0 := (Real.hasDerivAt_sqrt (ne_of_gt (hupos t ht))).comp t (hud t ht)
      have heq : 1 / (2 * Real.sqrt (u t)) * u' t = u' t / (2 * Real.sqrt (u t)) := by ring
      rw [heq] at h0
      exact h0
    have hne : Real.sqrt (u t) ≠ 0 := ne_of_gt (hsqrtpos t ht)
    have := hs.inv hne
    rw [hsq t ht] at this
    exact this
  have hψlip : ∀ t ∈ S, |(-(u' t / (2 * Real.sqrt (u t))) / (u t))| ≤ 1 := by
    intro t ht
    have hup := hupos t ht
    have hsp := hsqrtpos t ht
    have hb := hscb t ht
    have hpow : (u t) ^ ((3:ℝ)/2) = u t * Real.sqrt (u t) := by
      rw [show ((3:ℝ)/2) = 1 + 1/2 by norm_num, Real.rpow_add hup, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
    rw [hpow] at hb
    rw [abs_div, abs_neg, abs_div, abs_of_pos hup, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.sqrt (u t))]
    rw [div_div, div_le_one (by positivity)]
    calc |u' t| ≤ 2 * (u t * Real.sqrt (u t)) := hb
      _ = 2 * Real.sqrt (u t) * u t := by ring
  -- hence `ψ t ≤ ψ 0 + t` on `[0,1]`
  have hψbound : ∀ t ∈ Set.Icc (0:ℝ) 1, ψ t ≤ ψ 0 + t := by
    have hanti : AntitoneOn (fun t => ψ t - t) (Set.Icc (0:ℝ) 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
      · intro t ht
        exact (((hψd t (hIcc ht)).sub (hasDerivAt_id t)).continuousAt).continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (((hψd t (hIcc (Set.mem_Icc_of_Ioo ht))).sub
          (hasDerivAt_id t)).differentiableAt).differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htS : t ∈ S := hIcc (Set.mem_Icc_of_Ioo ht)
        have hd : HasDerivAt (fun s : ℝ => ψ s - s)
            (-(u' t / (2 * Real.sqrt (u t))) / (u t) - 1) t :=
          (hψd t htS).sub (hasDerivAt_id t)
        rw [hd.deriv]
        have := abs_le.mp (hψlip t htS)
        linarith [this.2]
    intro t ht
    have := hanti (Set.left_mem_Icc.mpr (by norm_num)) ht ht.1
    simp only at this
    linarith
  -- the resulting lower bound on the second derivative
  have hulow : ∀ t ∈ Set.Icc (0:ℝ) 1, r ^ 2 / (1 + r * t) ^ 2 ≤ u t := by
    intro t ht
    have htS : t ∈ S := hIcc ht
    have hψ0 : ψ 0 = r⁻¹ := by rw [hψ, hr]
    have hb := hψbound t ht
    rw [hψ0] at hb
    have hden : 0 < 1 + r * t := by nlinarith [ht.1, hrpos]
    have hb2 : (Real.sqrt (u t))⁻¹ ≤ (1 + r * t) / r := by
      rw [hψ] at hb
      calc (Real.sqrt (u t))⁻¹ ≤ r⁻¹ + t := hb
        _ = (1 + r * t) / r := by field_simp
    have hsp := hsqrtpos t htS
    have hkey : r / (1 + r * t) ≤ Real.sqrt (u t) := by
      rw [div_le_iff₀ hden]
      have h1 := mul_le_mul_of_nonneg_left hb2 (le_of_lt (mul_pos hrpos hsp))
      have h2 : (r * Real.sqrt (u t)) * (Real.sqrt (u t))⁻¹ = r := by field_simp
      have h3 : (r * Real.sqrt (u t)) * ((1 + r * t) / r)
          = Real.sqrt (u t) * (1 + r * t) := by field_simp
      rw [h2, h3] at h1
      exact h1
    calc r ^ 2 / (1 + r * t) ^ 2 = (r / (1 + r * t)) ^ 2 := (div_pow r (1 + r * t) 2).symm
      _ ≤ (Real.sqrt (u t)) ^ 2 := by
          exact pow_le_pow_left₀ (by positivity) hkey 2
      _ = u t := hsq t htS
  -- the comparison function
  set m1 : ℝ → ℝ := fun t => d1 0 + r - r / (1 + r * t) with hm1
  set m : ℝ → ℝ := fun t => φ 0 + t * d1 0 + (r * t - Real.log (1 + r * t)) with hm
  have hden : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < 1 + r * t := by
    intro t ht; nlinarith [ht.1, hrpos]
  have hm1d : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt m1 (r ^ 2 / (1 + r * t) ^ 2) t := by
    intro t ht
    have hd := hden t ht
    have hinner : HasDerivAt (fun s : ℝ => 1 + r * s) r t := by
      exact (((hasDerivAt_id t).const_mul r).const_add 1).congr_deriv (by first | rfl | simp | norm_num | ring)
    have := (hinner.inv (ne_of_gt hd)).const_mul r
    have hgoal : HasDerivAt (fun s : ℝ => r * (1 + r * s)⁻¹)
        (r * (-r / (1 + r * t) ^ 2)) t := this
    have hfin := (hasDerivAt_const t (d1 0 + r)).sub hgoal
    refine hfin.congr_deriv ?_
    field_simp
    ring
  have hmd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt m (m1 t) t := by
    intro t ht
    have hd := hden t ht
    have hinner : HasDerivAt (fun s : ℝ => 1 + r * s) r t := by
      exact (((hasDerivAt_id t).const_mul r).const_add 1).congr_deriv (by first | rfl | simp | norm_num | ring)
    have hlog : HasDerivAt (fun s : ℝ => Real.log (1 + r * s)) (r / (1 + r * t)) t := by
      have := hinner.log (ne_of_gt hd)
      exact this
    have h1 : HasDerivAt (fun s : ℝ => φ 0 + s * d1 0) (d1 0) t := by
      exact (((hasDerivAt_id t).mul_const (d1 0)).const_add (φ 0)).congr_deriv (by first | rfl | simp | norm_num | ring)
    have ha : HasDerivAt (fun s : ℝ => r * s) r t := by
      exact ((hasDerivAt_id t).const_mul r).congr_deriv (by first | rfl | simp | norm_num | ring)
    have h2 : HasDerivAt (fun s : ℝ => r * s - Real.log (1 + r * s))
        (r - r / (1 + r * t)) t := ha.sub hlog
    exact ((h1.add h2)).congr_deriv (by rw [hm1]; ring)
  -- first comparison: `d1 ≥ m1` on `[0,1]`
  have hD1 : ∀ t ∈ Set.Icc (0:ℝ) 1, m1 t ≤ d1 t := by
    have hmono : MonotoneOn (fun t => d1 t - m1 t) (Set.Icc (0:ℝ) 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
      · intro t ht
        exact (((hd1d t (hIcc ht)).sub (hm1d t ht)).continuousAt).continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htI : t ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc_of_Ioo ht
        exact (((hd1d t (hIcc htI)).sub (hm1d t htI)).differentiableAt).differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htI : t ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc_of_Ioo ht
        have hdd : HasDerivAt (fun s : ℝ => d1 s - m1 s)
            (d2 t - r ^ 2 / (1 + r * t) ^ 2) t := (hd1d t (hIcc htI)).sub (hm1d t htI)
        rw [hdd.deriv]
        have h1 := hulow t htI
        have h2 : d2 t = u t := (hu2 t (hIcc htI)).symm
        rw [h2]
        linarith
    intro t ht
    have hz : (fun t => d1 t - m1 t) 0 = 0 := by
      simp only [hm1]
      norm_num
    have := hmono (Set.left_mem_Icc.mpr (by norm_num)) ht ht.1
    rw [hz] at this
    simp only at this
    linarith
  -- second comparison: `φ ≥ m` on `[0,1]`
  have hD0 : m 1 ≤ φ 1 := by
    have hmono : MonotoneOn (fun t => φ t - m t) (Set.Icc (0:ℝ) 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
      · intro t ht
        exact (((hφd t (hIcc ht)).sub (hmd t ht)).continuousAt).continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htI : t ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc_of_Ioo ht
        exact (((hφd t (hIcc htI)).sub (hmd t htI)).differentiableAt).differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htI : t ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc_of_Ioo ht
        have hdd : HasDerivAt (fun s : ℝ => φ s - m s) (d1 t - m1 t) t :=
          (hφd t (hIcc htI)).sub (hmd t htI)
        rw [hdd.deriv]
        linarith [hD1 t htI]
    have hz : (fun t => φ t - m t) 0 = 0 := by
      simp only [hm]
      norm_num
    have := hmono (Set.left_mem_Icc.mpr (by norm_num))
      (Set.right_mem_Icc.mpr (by norm_num)) (by norm_num)
    rw [hz] at this
    simp only at this
    linarith
  -- unwind
  have hφ0 : φ 0 = f x := by rw [hφ]; simp
  have hφ1 : φ 1 = f y := by rw [hφ, hvdef]; simp
  have hd10 : d1 0 = ⟪g x, v⟫ := by rw [hd1]; simp
  have hru : r = Real.sqrt ⟪H x v, v⟫ := by
    rw [hr, hu2 0 h0S]
    simp only [hd2]
    norm_num
  simp only [hm] at hD0
  rw [hφ0, hφ1, hd10] at hD0
  simp only [one_mul, mul_one] at hD0
  rw [← hru]
  linarith [hD0]

end SCAux

namespace SCAux

open Set Filter
open scoped Topology

variable {n : ℕ}

/-! ### Cauchy–Schwarz in the Hessian norm -/

theorem hess_cs {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩo : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (hHpd : ∀ x ∈ Ω, ∀ v, v ≠ 0 → 0 < ⟪H x v, v⟫)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) (a b : EuclideanSpace ℝ (Fin n)) :
    |⟪H x a, b⟫| ≤ Real.sqrt ⟪H x a, a⟫ * Real.sqrt ⟪H x b, b⟫ := by
  have hnn : ∀ w : EuclideanSpace ℝ (Fin n), 0 ≤ ⟪H x w, w⟫ := by
    intro w
    by_cases hw : w = 0
    · subst hw; simp
    · exact (hHpd x hx w hw).le
  have hsym := hess_symm hΩo f g hg H hH x hx
  have hexp : ∀ s : ℝ, ⟪H x (a + s • b), a + s • b⟫
      = ⟪H x a, a⟫ + 2 * s * ⟪H x a, b⟫ + s ^ 2 * ⟪H x b, b⟫ := by
    intro s
    rw [map_add, map_smul]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [hsym b a]
    ring
  have hq : ∀ s : ℝ, 0 ≤ ⟪H x a, a⟫ + 2 * s * ⟪H x a, b⟫ + s ^ 2 * ⟪H x b, b⟫ := by
    intro s
    rw [← hexp s]
    exact hnn _
  have hd := quad_cs (hnn a) (hnn b) hq
  calc |⟪H x a, b⟫| = Real.sqrt (⟪H x a, b⟫ ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (⟪H x a, a⟫ * ⟪H x b, b⟫) := Real.sqrt_le_sqrt hd
    _ = Real.sqrt ⟪H x a, a⟫ * Real.sqrt ⟪H x b, b⟫ := Real.sqrt_mul (hnn a) _

/-! ### The scalar inequality `ω*(λ) ≤ λ²` for `λ ≤ 0.68` -/

theorem exp_gt : (3.125 : ℝ) < Real.exp 1.1424 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : (1 : ℝ) + 0.1424 + 0.1424 ^ 2 / 2 ≤ Real.exp 0.1424 :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have h3 : Real.exp 1 * Real.exp 0.1424 = Real.exp 1.1424 := by
    rw [← Real.exp_add]
    norm_num
  have hpos : (0:ℝ) < Real.exp 0.1424 := Real.exp_pos _
  calc (3.125 : ℝ) < 2.7182818283 * (1 + 0.1424 + 0.1424 ^ 2 / 2) := by norm_num
    _ ≤ Real.exp 1 * Real.exp 0.1424 := by
        apply mul_le_mul h1.le h2 (by norm_num) (Real.exp_pos 1).le
    _ = Real.exp 1.1424 := h3

theorem log_032 : (-1.1424 : ℝ) < Real.log 0.32 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have hpos : (0:ℝ) < Real.exp 1.1424 := Real.exp_pos _
  have hb := exp_gt
  have hneg : Real.exp (-1.1424) = (Real.exp 1.1424)⁻¹ := by
    rw [← Real.exp_neg]
  rw [hneg, inv_eq_one_div, div_lt_iff₀ hpos]
  nlinarith [hb]

/-- `ω*(λ) = -λ - log(1-λ) ≤ λ²` on `[0, 0.68]`  (B&V, the numerical bound behind (9.50)). -/
theorem omega_star_le_sq (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 0.68) :
    -lam - Real.log (1 - lam) ≤ lam ^ 2 := by
  set h : ℝ → ℝ := fun s => s ^ 2 + s + Real.log (1 - s) with hh
  have hd : ∀ s : ℝ, s < 1 → HasDerivAt h (2 * s + 1 + -1 / (1 - s)) s := by
    intro s hs
    have hne : (1:ℝ) - s ≠ 0 := by intro hc; linarith [sub_eq_zero.mp hc]
    have ha : HasDerivAt (fun z : ℝ => 1 - z) (-1) s := by
      exact ((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).congr_deriv (by first | rfl | simp | norm_num | ring)
    have hb : HasDerivAt (fun z : ℝ => Real.log (1 - z)) (-1 / (1 - s)) s := ha.log hne
    have hc : HasDerivAt (fun z : ℝ => z ^ 2 + z) (2 * s + 1) s := by
      exact ((hasDerivAt_pow 2 s).add (hasDerivAt_id s)).congr_deriv (by first | rfl | simp | norm_num | ring)
    exact hc.add hb
  have hmono : MonotoneOn h (Set.Icc (0:ℝ) (1/2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1/2)) ?_ ?_ ?_
    · intro s hs
      exact ((hd s (by linarith [hs.2])).continuousAt).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact ((hd s (by linarith [hs.2])).differentiableAt).differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs1 : s < 1 := by linarith [hs.2]
      rw [(hd s hs1).deriv]
      have hden : (0:ℝ) < 1 - s := by linarith
      rw [div_eq_mul_inv, ← sub_nonneg] at *
      have hkey : 0 ≤ (2 * s + 1) * (1 - s) - 1 := by nlinarith [hs.1, hs.2]
      have : (1:ℝ) / (1 - s) ≤ 2 * s + 1 := by
        rw [div_le_iff₀ hden]
        linarith
      have hinv : (1 - s)⁻¹ = 1 / (1 - s) := by rw [one_div]
      rw [hinv]
      nlinarith [this]
  have hanti : AntitoneOn h (Set.Icc (1/2:ℝ) 0.68) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc (1/2) 0.68) ?_ ?_ ?_
    · intro s hs
      exact ((hd s (by linarith [hs.2])).continuousAt).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact ((hd s (by linarith [hs.2])).differentiableAt).differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs1 : s < 1 := by linarith [hs.2]
      rw [(hd s hs1).deriv]
      have hden : (0:ℝ) < 1 - s := by linarith
      have hkey : (2 * s + 1) * (1 - s) - 1 ≤ 0 := by nlinarith [hs.1, hs.2]
      have hge : 2 * s + 1 ≤ 1 / (1 - s) := by
        rw [le_div_iff₀ hden]
        linarith
      have hinv : (-1 : ℝ) / (1 - s) = -(1 / (1 - s)) := by ring
      rw [hinv]
      linarith
  have hzero : h 0 = 0 := by simp [hh]
  have hend : 0 ≤ h 0.68 := by
    have hl := log_032
    have hrw : (1:ℝ) - 0.68 = 0.32 := by norm_num
    simp only [hh, hrw]
    nlinarith [hl]
  have hmain : 0 ≤ h lam := by
    rcases le_or_gt lam (1/2) with hc | hc
    · have hstep := hmono (Set.left_mem_Icc.mpr (by norm_num)) ⟨h0, hc⟩ h0
      rw [hzero] at hstep
      exact hstep
    · have hstep := hanti ⟨hc.le, h1⟩ (Set.right_mem_Icc.mpr (by norm_num)) h1
      linarith [hend]
  simp only [hh] at hmain
  linarith

end SCAux

open SCAux in
/-- **The Newton decrement bounds the suboptimality** (B&V §9.6.3, eq. (9.50)):
for a self-concordant `f` with `λ(x) ≤ 0.68`, `f(x) − p⋆ ≤ λ(x)²`. -/
theorem solution {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hsc : IsSelfConcordantOn Ω f)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (hHpd : ∀ x ∈ Ω, ∀ v, v ≠ 0 → 0 < ⟪H x v, v⟫)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ Ω)
    (hstar : IsMinOn f Ω xstar)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (Δ : EuclideanSpace ℝ (Fin n)) (hΔ : H x Δ = -g x)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam ^ 2 = ⟪g x, -Δ⟫)
    (hsmall : lam ≤ 0.68) :
    f x - f xstar ≤ lam ^ 2 := by
  have hlb := line_lower_bound Ω hΩo hΩc f hsc g hg H hH hHpd x hx xstar hxstar
  set v : EuclideanSpace ℝ (Fin n) := xstar - x with hv
  set r : ℝ := Real.sqrt ⟪H x v, v⟫ with hr
  have hrnn : 0 ≤ r := Real.sqrt_nonneg _
  have hgx : g x = -(H x Δ) := by rw [hΔ]; simp
  have hlamsq : ⟪H x Δ, Δ⟫ = lam ^ 2 := by
    rw [hlam, hgx, inner_neg_neg]
  have hsqrtlam : Real.sqrt ⟪H x Δ, Δ⟫ = lam := by
    rw [hlamsq]
    exact Real.sqrt_sq hlam0
  have hcs := hess_cs hΩo f g hg H hH hHpd x hx Δ v
  rw [hsqrtlam, ← hr] at hcs
  have hgv : ⟪g x, v⟫ = -⟪H x Δ, v⟫ := by rw [hgx, inner_neg_left]
  have hbound : -(lam * r) ≤ ⟪g x, v⟫ := by
    rw [hgv]
    have := (abs_le.mp hcs).2
    linarith
  have hstep : f x - f xstar ≤ lam * r - r + Real.log (1 + r) := by linarith [hlb, hbound]
  have hlt1 : lam < 1 := by linarith
  have hkey : lam * r - r + Real.log (1 + r) ≤ -lam - Real.log (1 - lam) := by
    have hpos1 : (0:ℝ) < 1 + r := by linarith
    have hpos2 : (0:ℝ) < 1 - lam := by linarith
    have hlog : Real.log ((1 + r) * (1 - lam)) ≤ (1 + r) * (1 - lam) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2)] at hlog
    nlinarith [hlog]
  have hfin := omega_star_le_sq lam hlam0 hsmall
  linarith
