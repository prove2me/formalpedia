-- Prove2me | solution 1 for EthierKurtz.oblique_graph_exponent_closure
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T06:26:46.063199+00:00
-- url     : https://prove2.me/submissions/a7033a57-955d-4284-b708-a81baacee6c9

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Theorems.Thm_EthierKurtz_oblique_global_c2_mollification
import Theorems.Thm_EthierKurtz_oblique_flat_lift_quantitative
import Theorems.Thm_EthierKurtz_oblique_local_corrector_quantitative
import Theorems.Thm_EthierKurtz_oblique_boundary_datum_c1_vanishing
import Theorems.Thm_EthierKurtz_componentHolder_extends_closure

/-! D2 reduction: EthierKurtz.oblique_graph_exponent_closure from four new children and
EthierKurtz.componentHolder_extends_closure. -/

set_option autoImplicit false

open Filter
open scoped Topology BoundedContinuousFunction Manifold ContDiff

namespace P50d2R

open EthierKurtz

variable {d : ℕ}


lemma restr_lin {Ω : Set (EuclideanSpace ℝ (Fin d))} (c₁ c₂ : ℝ) (f₁ f₂ : (closure Ω) →ᵇ ℝ) :
    closedRegionRestriction (c₁ • f₁ + c₂ • f₂) =
      fun y => c₁ * closedRegionRestriction f₁ y + c₂ * closedRegionRestriction f₂ y := by
  funext y
  unfold closedRegionRestriction
  split_ifs <;> simp

lemma restr_zero {Ω : Set (EuclideanSpace ℝ (Fin d))} :
    closedRegionRestriction (0 : (closure Ω) →ᵇ ℝ) = fun _ => 0 := by
  funext y
  unfold closedRegionRestriction
  split_ifs <;> simp

lemma compHolder_congr {Ω : Set (EuclideanSpace ℝ (Fin d))} {μ : ℝ} {F G : (EuclideanSpace ℝ (Fin d)) → ℝ} (hF : ComponentHolder Ω μ F)
    (h : ∀ x ∈ Ω, G x = F x) : ComponentHolder Ω μ G := by
  obtain ⟨hc, ρ₀, M, hρ, hM, hb⟩ := hF
  refine ⟨hc.congr h, ρ₀, M, hρ, hM, fun ρ h0 h1 x z hz y hy w hw => ?_⟩
  have hyΩ : y ∈ Ω := (connectedComponentIn_subset _ _ hy).1
  have hwΩ : w ∈ Ω := (connectedComponentIn_subset _ _ hw).1
  rw [h y hyΩ, h w hwΩ]
  exact hb ρ h0 h1 x z hz y hy w hw

lemma compHolder_lin {Ω : Set (EuclideanSpace ℝ (Fin d))} {μ : ℝ} (hμ : 0 < μ) {F G : (EuclideanSpace ℝ (Fin d)) → ℝ}
    (hF : ComponentHolder Ω μ F) (hG : ComponentHolder Ω μ G) (c₁ c₂ : ℝ) :
    ComponentHolder Ω μ (fun x => c₁ * F x + c₂ * G x) := by
  obtain ⟨hcF, ρ₁, M₁, hρ₁, hM₁, hb₁⟩ := hF
  obtain ⟨hcG, ρ₂, M₂, hρ₂, hM₂, hb₂⟩ := hG
  refine ⟨(continuousOn_const.mul hcF).add (continuousOn_const.mul hcG), min ρ₁ ρ₂,
    |c₁| * M₁ + |c₂| * M₂, lt_min hρ₁ hρ₂, by positivity, ?_⟩
  intro ρ h0 h1 x z hz y hy w hw
  have e1 := hb₁ ρ h0 (h1.trans (min_le_left _ _)) x z hz y hy w hw
  have e2 := hb₂ ρ h0 (h1.trans (min_le_right _ _)) x z hz y hy w hw
  have hp : 0 ≤ ρ ^ μ := Real.rpow_nonneg h0.le _
  calc |(c₁ * F y + c₂ * G y) - (c₁ * F w + c₂ * G w)|
      = |c₁ * (F y - F w) + c₂ * (G y - G w)| := by ring_nf
    _ ≤ |c₁ * (F y - F w)| + |c₂ * (G y - G w)| := abs_add_le _ _
    _ = |c₁| * |F y - F w| + |c₂| * |G y - G w| := by rw [abs_mul, abs_mul]
    _ ≤ |c₁| * (M₁ * ρ ^ μ) + |c₂| * (M₂ * ρ ^ μ) := by
        gcongr
    _ = (|c₁| * M₁ + |c₂| * M₂) * ρ ^ μ := by ring

/-- First derivatives of a linear combination on an open set. -/
lemma fderiv_lin {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) {F G : (EuclideanSpace ℝ (Fin d)) → ℝ} (hF : ContDiffOn ℝ 2 F U)
    (hG : ContDiffOn ℝ 2 G U) (c₁ c₂ : ℝ) {y : (EuclideanSpace ℝ (Fin d))} (hy : y ∈ U) :
    fderiv ℝ (fun y => c₁ * F y + c₂ * G y) y = c₁ • fderiv ℝ F y + c₂ • fderiv ℝ G y := by
  have dF : DifferentiableAt ℝ F y :=
    (hF.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)
  have dG : DifferentiableAt ℝ G y :=
    (hG.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)
  rw [fderiv_fun_add (dF.const_mul c₁) (dG.const_mul c₂), fderiv_const_mul dF,
    fderiv_const_mul dG]

/-- Second partials of a linear combination on an open set. -/
lemma partial2_lin {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) {F G : (EuclideanSpace ℝ (Fin d)) → ℝ} (hF : ContDiffOn ℝ 2 F U)
    (hG : ContDiffOn ℝ 2 G U) (c₁ c₂ : ℝ) {x : (EuclideanSpace ℝ (Fin d))} (hx : x ∈ U) (i j : Fin d) :
    fderiv ℝ (fun y => fderiv ℝ (fun y => c₁ * F y + c₂ * G y) y
      (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)
      = c₁ * fderiv ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1)
        + c₂ * fderiv ℝ (fun y => fderiv ℝ G y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1) := by
  have DF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hF.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (hU.mem_nhds hx)
  have DG : DifferentiableAt ℝ (fderiv ℝ G) x :=
    ((hG.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (hU.mem_nhds hx)
  have hev : (fun y => fderiv ℝ (fun y => c₁ * F y + c₂ * G y) y (EuclideanSpace.single j 1))
      =ᶠ[𝓝 x] (fun y => c₁ * fderiv ℝ F y (EuclideanSpace.single j 1)
        + c₂ * fderiv ℝ G y (EuclideanSpace.single j 1)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [fderiv_lin hU hF hG c₁ c₂ hy]
    simp
  rw [hev.fderiv_eq]
  have dFj : DifferentiableAt ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x :=
    DF.clm_apply (differentiableAt_const _)
  have dGj : DifferentiableAt ℝ (fun y => fderiv ℝ G y (EuclideanSpace.single j 1)) x :=
    DG.clm_apply (differentiableAt_const _)
  rw [fderiv_fun_add (dFj.const_mul c₁) (dGj.const_mul c₂), fderiv_const_mul dFj,
    fderiv_const_mul dGj]
  simp

lemma ctwice_congr {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω) {μ : ℝ}
    {F G : EuclideanSpace ℝ (Fin d) → ℝ} (hF : CTwiceHolder Ω μ F)
    (h : ∀ x ∈ Ω, G x = F x) : CTwiceHolder Ω μ G := by
  refine ⟨hF.1.congr h, fun i j => compHolder_congr (hF.2 i j) (fun x hx => ?_)⟩
  have hd : ∀ y ∈ Ω, fderiv ℝ G y = fderiv ℝ F y := fun y hy => by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact h z hz
  have hev : (fun y => fderiv ℝ G y (EuclideanSpace.single j 1)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) := by
    filter_upwards [hopen.mem_nhds hx] with z hz
    rw [hd z hz]
  rw [hev.fderiv_eq]

lemma ctwice_lin {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω) {μ : ℝ} (hμ : 0 < μ)
    {F G : EuclideanSpace ℝ (Fin d) → ℝ} (hF : CTwiceHolder Ω μ F) (hG : CTwiceHolder Ω μ G)
    (c₁ c₂ : ℝ) : CTwiceHolder Ω μ (fun x => c₁ * F x + c₂ * G x) :=
  ⟨(contDiffOn_const.mul hF.1).add (contDiffOn_const.mul hG.1), fun i j =>
    compHolder_congr (compHolder_lin hμ (hF.2 i j) (hG.2 i j) c₁ c₂)
      (fun x hx => partial2_lin hopen hF.1 hG.1 c₁ c₂ hx i j)⟩

lemma ctwice_add {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω) {μ : ℝ} (hμ : 0 < μ)
    {F G : EuclideanSpace ℝ (Fin d) → ℝ} (hF : CTwiceHolder Ω μ F) (hG : CTwiceHolder Ω μ G) :
    CTwiceHolder Ω μ (fun x => F x + G x) := by
  have := ctwice_lin hopen hμ hF hG 1 1
  simp only [one_mul] at this
  exact this

lemma ctwice_zero {Ω : Set (EuclideanSpace ℝ (Fin d))} {μ : ℝ} :
    CTwiceHolder Ω μ (fun _ => (0 : ℝ)) := by
  refine ⟨contDiffOn_const, fun i j => ?_⟩
  refine compHolder_congr (F := fun _ => 0) ⟨continuousOn_const, 1, 0, one_pos, le_rfl, ?_⟩ ?_
  · intro ρ _ _ x z _ y _ w _; simp
  · intro x _; simp

lemma ctwice_sum {Ω : Set (EuclideanSpace ℝ (Fin d))} (hopen : IsOpen Ω) {μ : ℝ} (hμ : 0 < μ)
    {ι : Type*} (s : Finset ι) (V : ι → EuclideanSpace ℝ (Fin d) → ℝ)
    (hV : ∀ i ∈ s, CTwiceHolder Ω μ (V i)) :
    CTwiceHolder Ω μ (fun x => ∑ i ∈ s, V i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (ctwice_zero (Ω := Ω) (μ := μ))
  | insert a s ha ih =>
    have e : (fun x => ∑ i ∈ insert a s, V i x) = fun x => V a x + ∑ i ∈ s, V i x := by
      funext x; rw [Finset.sum_insert ha]
    rw [e]
    exact ctwice_add hopen hμ (hV a (Finset.mem_insert_self a s))
      (ih fun i hi => hV i (Finset.mem_insert_of_mem hi))

/-- A `C^1` function is `ComponentHolder` on a bounded set (it is Lipschitz there). -/
lemma compHolder_of_contDiff {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hbounded : Bornology.IsBounded Ω) {μ : ℝ} (hμ : 0 < μ ∧ μ ≤ 1)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ 1 φ) : ComponentHolder Ω μ φ := by
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall 0
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) R).exists_bound_of_continuousOn
    ((hφ.continuous_fderiv one_ne_zero).continuousOn)
  refine ⟨hφ.continuous.continuousOn, 1, 2 * max C 0, one_pos, by positivity, ?_⟩
  intro ρ h0 h1 x z hz y hy w hw
  have hy' := connectedComponentIn_subset _ _ hy
  have hw' := connectedComponentIn_subset _ _ hw
  have hL : ‖φ y - φ w‖ ≤ max C 0 * ‖y - w‖ :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin d)) R).norm_image_sub_le_of_norm_fderiv_le
      (fun u _ => (hφ.differentiable one_ne_zero) u) (fun u hu => (hC u hu).trans (le_max_left _ _))
      (hR hw'.1) (hR hy'.1)
  have hyw : ‖y - w‖ ≤ 2 * ρ := by
    have a1 : dist y x < ρ := hy'.2
    have a2 : dist w x < ρ := hw'.2
    have := dist_triangle_right y w x
    rw [← dist_eq_norm]; linarith
  have hρμ : ρ ≤ ρ ^ μ := by
    have := Real.rpow_le_rpow_of_exponent_ge h0 h1 hμ.2
    simpa using this
  rw [Real.norm_eq_abs] at hL
  calc |φ y - φ w| ≤ max C 0 * ‖y - w‖ := hL
    _ ≤ max C 0 * (2 * ρ) := by gcongr
    _ ≤ max C 0 * (2 * ρ ^ μ) := by gcongr
    _ = 2 * max C 0 * ρ ^ μ := by ring

lemma ctwice_smooth {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hbounded : Bornology.IsBounded Ω) {μ : ℝ} (hμ : 0 < μ ∧ μ ≤ 1)
    {F : EuclideanSpace ℝ (Fin d) → ℝ} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) :
    CTwiceHolder Ω μ F := by
  refine ⟨(hF.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn, fun i j => ?_⟩
  apply compHolder_of_contDiff hbounded hμ
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) :=
    (contDiff_infty_iff_fderiv.1 hF).2.clm_apply contDiff_const
  have h2 := (contDiff_infty_iff_fderiv.1 h1).2.clm_apply
    (contDiff_const (c := (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin d))))
  exact h2.of_le (WithTop.coe_le_coe.mpr le_top)

lemma clm_expand (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    L v = ∑ i, v i * L (EuclideanSpace.single i 1) := by
  have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
    have := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.sum_repr v
    simpa using this.symm
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, smul_eq_mul]


/-! ## D2 assembly helpers (relay 10) -/

lemma restr_apply {Ω : Set (EuclideanSpace ℝ (Fin d))} (h : (closure Ω) →ᵇ ℝ) (x : closure Ω) :
    closedRegionRestriction h x = h x := by
  unfold closedRegionRestriction; rw [dif_pos x.2]

lemma dj_diff {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) {F : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : ContDiffOn ℝ 2 F U) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U) (j : Fin d) :
    DifferentiableAt ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x :=
  (((hF.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn (by norm_num)).differentiableAt
    (hU.mem_nhds hx)).clm_apply (differentiableAt_const _)

lemma diffAt_of {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {F : EuclideanSpace ℝ (Fin d) → ℝ} (hF : ContDiffOn ℝ 2 F U) {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∈ U) : DifferentiableAt ℝ F y :=
  (hF.differentiableOn (by norm_num) y hy).differentiableAt (hU.mem_nhds hy)

lemma partial2_add {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {F H : EuclideanSpace ℝ (Fin d) → ℝ} (hF : ContDiffOn ℝ 2 F U) (hH : ContDiffOn ℝ 2 H U)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U) (i j : Fin d) :
    fderiv ℝ (fun y => fderiv ℝ (fun y => F y + H y) y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1) =
      fderiv ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) +
      fderiv ℝ (fun y => fderiv ℝ H y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) := by
  have hev : (fun y => fderiv ℝ (fun y => F y + H y) y (EuclideanSpace.single j 1)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ F y (EuclideanSpace.single j 1) + fderiv ℝ H y (EuclideanSpace.single j 1)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [fderiv_fun_add (diffAt_of hU hF hy) (diffAt_of hU hH hy)]
    rfl
  rw [hev.fderiv_eq, fderiv_fun_add (dj_diff hU hF hx j) (dj_diff hU hH hx j)]
  rfl

lemma partial2_sum {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) {ι : Type*} (s : Finset ι)
    (V : ι → EuclideanSpace ℝ (Fin d) → ℝ) (hV : ∀ k ∈ s, ContDiffOn ℝ 2 (V k) U)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U) (i j : Fin d) :
    fderiv ℝ (fun y => fderiv ℝ (fun y => ∑ k ∈ s, V k y) y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1) =
      ∑ k ∈ s, fderiv ℝ (fun y => fderiv ℝ (V k) y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1) := by
  have hev : (fun y => fderiv ℝ (fun y => ∑ k ∈ s, V k y) y (EuclideanSpace.single j 1)) =ᶠ[𝓝 x]
      (fun y => ∑ k ∈ s, fderiv ℝ (V k) y (EuclideanSpace.single j 1)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [fderiv_fun_sum (fun k hk => diffAt_of hU (hV k hk) hy), ContinuousLinearMap.sum_apply]
  rw [hev.fderiv_eq, fderiv_fun_sum (fun k hk => dj_diff hU (hV k hk) hx j),
    ContinuousLinearMap.sum_apply]

lemma fderiv_congr_on {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {F G : EuclideanSpace ℝ (Fin d) → ℝ} (h : ∀ y ∈ U, G y = F y) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ U) : fderiv ℝ G x = fderiv ℝ F x :=
  Filter.EventuallyEq.fderiv_eq (by filter_upwards [hU.mem_nhds hx] with z hz; exact h z hz)

lemma partial2_congr {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {F G : EuclideanSpace ℝ (Fin d) → ℝ} (h : ∀ y ∈ U, G y = F y) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ U) (i j : Fin d) :
    fderiv ℝ (fun y => fderiv ℝ G y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) =
      fderiv ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) := by
  have hev : (fun y => fderiv ℝ G y (EuclideanSpace.single j 1)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    rw [fderiv_congr_on hU h hz]
  rw [hev.fderiv_eq]

lemma partial2_eq {g : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hg : DifferentiableAt ℝ (fderiv ℝ g) x) (i j : Fin d) :
    fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) =
      fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have h := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).hasFDerivAt.comp x
    hg.hasFDerivAt
  rw [show (fun y => fderiv ℝ g y (EuclideanSpace.single j 1)) =
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))) ∘ fderiv ℝ g from rfl, h.fderiv]
  rfl

lemma partial2_sub_le {F f : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hF : DifferentiableAt ℝ (fderiv ℝ F) x) (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (i j : Fin d) :
    |fderiv ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) -
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)| ≤
      ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ f) x‖ := by
  rw [partial2_eq hF, partial2_eq hf, ← Real.norm_eq_abs]
  have := (fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ f) x).le_opNorm₂
    (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))
  simpa using this

lemma lin_bound (A u α : Fin d → Fin d → ℝ) (B w β : Fin d → ℝ) {θ : ℝ}
    (hA : ∀ i j, |A i j| ≤ α i j) (hB : ∀ i, |B i| ≤ β i) (hu : ∀ i j, |u i j| ≤ θ)
    (hw : ∀ i, |w i| ≤ θ) :
    |(1 / 2 : ℝ) * (∑ i, ∑ j, A i j * u i j) + ∑ i, B i * w i| ≤
      ((1 / 2 : ℝ) * (∑ i, ∑ j, α i j) + ∑ i, β i) * θ := by
  have h1 : |∑ i, ∑ j, A i j * u i j| ≤ ∑ i, ∑ j, α i j * θ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (hA i j) (hu i j) (abs_nonneg _) ((abs_nonneg _).trans (hA i j))
  have h2 : |∑ i, B i * w i| ≤ ∑ i, β i * θ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (hB i) (hw i) (abs_nonneg _) ((abs_nonneg _).trans (hB i))
  have e1 : ∑ i, ∑ j, α i j * θ = (∑ i, ∑ j, α i j) * θ := by simp only [Finset.sum_mul]
  have e2 : ∑ i, β i * θ = (∑ i, β i) * θ := by rw [Finset.sum_mul]
  rw [e1] at h1
  rw [e2] at h2
  calc _ ≤ |(1 / 2 : ℝ) * (∑ i, ∑ j, A i j * u i j)| + |∑ i, B i * w i| := abs_add_le _ _
    _ = (1 / 2) * |∑ i, ∑ j, A i j * u i j| + |∑ i, B i * w i| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ (1 / 2) * ((∑ i, ∑ j, α i j) * θ) + (∑ i, β i) * θ := by linarith
    _ = _ := by ring

lemma bcf_le_of_dense {Ω : Set (EuclideanSpace ℝ (Fin d))} (h : (closure Ω) →ᵇ ℝ) {C : ℝ}
    (hC : 0 ≤ C) (H : ∀ x : closure Ω, (x : EuclideanSpace ℝ (Fin d)) ∈ Ω → |h x| ≤ C) :
    ‖h‖ ≤ C := by
  rw [BoundedContinuousFunction.norm_le hC]
  have hcl : IsClosed {x : closure Ω | |h x| ≤ C} :=
    isClosed_le (continuous_abs.comp h.continuous) continuous_const
  have hsub : {x : closure Ω | (x : EuclideanSpace ℝ (Fin d)) ∈ Ω} ⊆ {x | |h x| ≤ C} :=
    fun x hx => H x hx
  have hdense : ∀ x : closure Ω,
      x ∈ closure {x : closure Ω | (x : EuclideanSpace ℝ (Fin d)) ∈ Ω} := by
    intro x
    rw [closure_subtype]
    have e : ((↑) '' {x : closure Ω | (x : EuclideanSpace ℝ (Fin d)) ∈ Ω}) = Ω := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩; exact hz
      · intro hy; exact ⟨⟨y, subset_closure hy⟩, hy, rfl⟩
    rw [e]; exact x.2
  intro x
  rw [Real.norm_eq_abs]
  exact hcl.closure_subset_iff.2 hsub (hdense x)

end P50d2R

open EthierKurtz in
/-- D2: the exact graph at a smaller exponent lies in the closure of the exact graph. -/
theorem P50d2R.closure_of (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i)
    (μ' : ℝ) (hμ' : 0 < μ' ∧ μ' ≤ μ) :
    obliqueDiffusionGraph Ω μ' a b c ⊆ closure (obliqueDiffusionGraph Ω μ a b c) := by
  classical
  intro fg hfg
  have hfg' := hfg
  simp only [obliqueDiffusionGraph, Set.mem_ofPred_eq] at hfg'
  obtain ⟨⟨hf2, hfH⟩, hfg2, J₀, hJ₀c, hJ₀Ω, hJ₀b⟩ := hfg'
  set f := closedRegionRestriction fg.1 with hfdef
  have hK : IsCompact (closure Ω) := hbounded.isCompact_closure
  haveI : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp hK
  let J' : EuclideanSpace ℝ (Fin (n + 1)) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) :=
    fun x => if h : x ∈ closure Ω then J₀ ⟨x, h⟩ else 0
  have hJ'c : ContinuousOn J' (closure Ω) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have e : (closure Ω).domRestrict J' = J₀ := by
      funext x
      show (if h : (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ closure Ω then J₀ ⟨x, h⟩ else 0) = J₀ x
      rw [dif_pos x.2]
    rw [e]; exact hJ₀c
  have hJ'Ω : ∀ x ∈ Ω, fderiv ℝ f x = J' x := by
    intro x hx
    show _ = (if h : x ∈ closure Ω then J₀ ⟨x, h⟩ else 0)
    rw [dif_pos (subset_closure hx)]
    exact (hJ₀Ω ⟨x, subset_closure hx⟩ hx).symm
  have hJ'b : ∀ y ∈ frontier Ω, J' y (c y) = 0 := by
    intro y hy
    show (if h : y ∈ closure Ω then J₀ ⟨y, h⟩ else 0) (c y) = 0
    rw [dif_pos (frontier_subset_closure hy)]
    exact hJ₀b ⟨y, frontier_subset_closure hy⟩ hy
  -- mollified sequence
  choose Fk hFk hFkb using fun k : ℕ => EthierKurtz.oblique_global_c2_mollification (n + 1) Ω hbounded hopen normal hnormal μ'
    hμ'.1 f hf2 J' hJ'c hJ'Ω hfH (1 / ((k : ℝ) + 1)) (by positivity)
  obtain ⟨η, hηdef⟩ : ∃ η : ℕ → ℝ, η = fun k : ℕ => 1 / ((k : ℝ) + 1) := ⟨_, rfl⟩
  have hηt : Tendsto η atTop (𝓝 0) := by rw [hηdef]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : ∀ k, ∀ y ∈ Ω, ‖fderiv ℝ (Fk k) y - J' y‖ ≤ η k := fun k y hy => by
    rw [← hJ'Ω y hy, hηdef]; exact (hFkb k y hy).2.1
  have h2 : ∀ k l, ∀ y ∈ Ω,
      ‖fderiv ℝ (fderiv ℝ (Fk k)) y - fderiv ℝ (fderiv ℝ (Fk l)) y‖ ≤ η k + η l := by
    intro k l y hy
    have b1 := (hFkb k y hy).2.2
    have b2 := (hFkb l y hy).2.2
    have key := norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ (fderiv ℝ (Fk k)) y)
      (fderiv ℝ (fderiv ℝ f) y) (fderiv ℝ (fderiv ℝ (Fk l)) y)
    rw [norm_sub_rev (fderiv ℝ (fderiv ℝ f) y)] at key
    rw [hηdef]
    exact key.trans (add_le_add b1 b2)
  -- local correctors
  choose ρ hρ X r hr O hO hrO hX hcX hXf K1 hK1 hV using
    EthierKurtz.oblique_local_corrector_quantitative n Ω hopen μ hμ c normal hc hnormal hoblique (EthierKurtz.oblique_flat_lift_quantitative n μ hμ)
  have hfc : IsCompact (frontier Ω) :=
    hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨t, ht⟩ := hfc.elim_finite_subcover
    (fun p : frontier Ω => Metric.ball (p : EuclideanSpace ℝ (Fin (n + 1))) (ρ p p.2))
    (fun _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self (hρ x hx)⟩)
  let U : t → Set (EuclideanSpace ℝ (Fin (n + 1))) := fun k =>
    Metric.ball (k.1 : EuclideanSpace ℝ (Fin (n + 1))) (ρ k.1 k.1.2)
  have hcov : frontier Ω ⊆ ⋃ k, U k := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ζ, hζ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) isClosed_frontier U (fun _ => Metric.isOpen_ball) hcov
  have hζs : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ζ k) := fun k =>
    contMDiff_iff_contDiff.mp ((ζ k).contMDiff)
  have hE4 := fun k : t => EthierKurtz.oblique_boundary_datum_c1_vanishing n Ω c J' hJ'c hJ'b (X k.1 k.1.2) (O k.1 k.1.2) (hO _ _)
    (r _ _) (hr _ _) (hrO _ _) ((hX _ _).of_le (by norm_num)) (contDiffOn_euclidean.2 (hcX _ _))
    (hXf _ _) (ζ k) ((hζs k).of_le (WithTop.coe_le_coe.mpr le_top)) Fk
    (fun m => (hFk m).of_le (WithTop.coe_le_coe.mpr le_top)) η hηt h1 h2
  -- coefficient bounds
  choose ψa hψa using fun i j =>
    EthierKurtz.componentHolder_extends_closure n Ω hbounded hopen μ hμ.1 normal hnormal _ (haHolder i j)
  choose ψb hψb using fun i =>
    EthierKurtz.componentHolder_extends_closure n Ω hbounded hopen μ hμ.1 normal hnormal _ (hbHolder i)
  have haB : ∀ x ∈ Ω, ∀ i j, |a x i j| ≤ ‖ψa i j‖ := fun x hx i j => by
    rw [← hψa i j ⟨x, subset_closure hx⟩ hx, ← Real.norm_eq_abs]
    exact BoundedContinuousFunction.norm_coe_le_norm _ _
  have hbB : ∀ x ∈ Ω, ∀ i, |b x i| ≤ ‖ψb i‖ := fun x hx i => by
    rw [← hψb i ⟨x, subset_closure hx⟩ hx, ← Real.norm_eq_abs]
    exact BoundedContinuousFunction.norm_coe_le_norm _ _
  obtain ⟨Aa, hAa⟩ : ∃ A : ℝ, A = ∑ i, ∑ j, ‖ψa i j‖ := ⟨_, rfl⟩
  obtain ⟨Bb, hBb⟩ : ∃ B : ℝ, B = ∑ i, ‖ψb i‖ := ⟨_, rfl⟩
  have hAa0 : 0 ≤ Aa := by
    rw [hAa]; exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hBb0 : 0 ≤ Bb := by rw [hBb]; exact Finset.sum_nonneg fun i _ => norm_nonneg _
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = ε / (2 * (1 + Aa + Bb)) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθε : (1 + Aa + Bb) * θ = ε / 2 := by rw [hθ]; field_simp
  obtain ⟨Ks, hKs⟩ : ∃ K : ℝ, K = ∑ k : t, K1 k.1 k.1.2 := ⟨_, rfl⟩
  have hKs0 : 0 ≤ Ks := by rw [hKs]; exact Finset.sum_nonneg fun k _ => hK1 _ _
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = θ / (2 * (Ks + 1)) := ⟨_, rfl⟩
  have hS0 : 0 < S := by rw [hS]; positivity
  have hKsS : Ks * S ≤ θ / 2 := by
    have e : Ks * S = θ / 2 * (Ks / (Ks + 1)) := by rw [hS]; field_simp
    have : Ks / (Ks + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    rw [e]; nlinarith
  choose k₀ hk₀ using fun k : t => hE4 k S hS0
  obtain ⟨M₀, hM₀⟩ := exists_nat_one_div_lt (half_pos hθ0)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = M₀ + ∑ k : t, k₀ k := ⟨_, rfl⟩
  have hmk : ∀ k : t, k₀ k ≤ m := fun k => by
    have := Finset.single_le_sum (f := fun k : t => k₀ k) (fun k _ => Nat.zero_le _)
      (Finset.mem_univ k)
    rw [hm]; omega
  have hηm : (1 : ℝ) / ((m : ℝ) + 1) ≤ θ / 2 := by
    have hM : (M₀ : ℝ) ≤ m := by rw [hm]; exact_mod_cast Nat.le_add_right M₀ _
    have h' : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 / ((M₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    exact h'.trans hM₀.le
  obtain ⟨F, hF, hFb, hFz⟩ : ∃ F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
      (∀ x ∈ Ω, |F x - f x| ≤ θ / 2 ∧ ‖fderiv ℝ F x - fderiv ℝ f x‖ ≤ θ / 2 ∧
        ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ f) x‖ ≤ θ / 2) ∧
      ∀ k : t, ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (r k.1 k.1.2),
        |ζ k (X k.1 k.1.2 z) * fderiv ℝ F (X k.1 k.1.2 z) (c (X k.1 k.1.2 z))| ≤ S ∧
        ‖fderiv ℝ (fun z => ζ k (X k.1 k.1.2 z) * fderiv ℝ F (X k.1 k.1.2 z)
          (c (X k.1 k.1.2 z))) z‖ ≤ S :=
    ⟨Fk m, hFk m, fun x hx => ⟨((hFkb m x hx).1).trans hηm, ((hFkb m x hx).2.1).trans hηm,
      ((hFkb m x hx).2.2).trans hηm⟩, fun k z hz => hk₀ k m (hmk k) z hz⟩
  clear hE4 hk₀ h1 h2 hFkb hFk hηt
  choose V hV1 hV2 hV3 hV4 hV5 hV6 hV7 using fun k : t =>
    hV k.1 k.1.2 F (ζ k) hF (hζs k) (hζ k) S (hFz k)
  obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, G = fun x => F x + ∑ k, V k x :=
    ⟨_, rfl⟩
  have hG1 : ContDiff ℝ 1 G := by
    rw [hG]; exact (hF.of_le (WithTop.coe_le_coe.mpr le_top)).add (ContDiff.sum fun k _ => hV1 k)
  let f1 : (closure Ω) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => G x, hG1.continuous.comp continuous_subtype_val⟩
  have hf1 : ∀ x ∈ closure Ω, closedRegionRestriction f1 x = G x := by
    intro x hx
    unfold closedRegionRestriction
    rw [dif_pos hx]
    rfl
  have hf1Ω : ∀ x ∈ Ω, closedRegionRestriction f1 x = G x := fun x hx => hf1 x (subset_closure hx)
  have hCT : CTwiceHolder Ω μ (closedRegionRestriction f1) :=
    ctwice_congr hopen (ctwice_add hopen hμ.1 (ctwice_smooth hbounded hμ hF)
      (ctwice_sum hopen hμ.1 Finset.univ V (fun k _ => hV3 k))) (fun x hx => by rw [hf1Ω x hx, hG])
  have hfd : ∀ x ∈ Ω, fderiv ℝ (closedRegionRestriction f1) x = fderiv ℝ G x :=
    fun x hx => fderiv_congr_on hopen hf1Ω hx
  let J : (closure Ω) → (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) := fun x => fderiv ℝ G x
  have hJc : Continuous J := (hG1.continuous_fderiv one_ne_zero).comp continuous_subtype_val
  have dF : ∀ x, DifferentiableAt ℝ F x := fun x => (hF.differentiable (by simp)) x
  have dV : ∀ x, ∀ k ∈ (Finset.univ : Finset t), DifferentiableAt ℝ (V k) x :=
    fun x k _ => (hV1 k).differentiable one_ne_zero x
  have hDG : ∀ x, fderiv ℝ G x = fderiv ℝ F x + ∑ k, fderiv ℝ (V k) x := fun x => by
    rw [hG, fderiv_fun_add (dF x) (DifferentiableAt.fun_sum (dV x)), fderiv_fun_sum (dV x)]
  have hJb : ∀ x : closure Ω, (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ frontier Ω →
      J x (c x) = 0 := by
    intro x hx
    show fderiv ℝ G x (c x) = 0
    rw [hDG]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply]
    rw [Finset.sum_congr rfl (fun k _ => hV4 k x hx)]
    have hs := ζ.sum_eq_one hx
    rw [finsum_eq_sum_of_fintype] at hs
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hs]
    ring
  -- second coordinate
  choose ψf hψf using fun i j =>
    EthierKurtz.componentHolder_extends_closure n Ω hbounded hopen μ hμ.1 normal hnormal _ (hCT.2 i j)
  let Jb : Fin (n + 1) → (closure Ω) →ᵇ ℝ := fun i => BoundedContinuousFunction.mkOfCompact
    ⟨fun x => J x (EuclideanSpace.single i 1), hJc.clm_apply continuous_const⟩
  let g1 : (closure Ω) →ᵇ ℝ :=
    (1 / 2 : ℝ) • (∑ i, ∑ j, ψa i j * ψf i j) + ∑ i, ψb i * Jb i
  have hg1Ω : ∀ x (hx : x ∈ Ω), g1 ⟨x, subset_closure hx⟩ =
      (1 / 2 : ℝ) * (∑ i, ∑ j, a x i j *
        fderiv ℝ (fun y => fderiv ℝ (closedRegionRestriction f1) y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1)) +
      ∑ i, b x i * fderiv ℝ G x (EuclideanSpace.single i 1) := by
    intro x hx
    simp only [g1, BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_smul,
      BoundedContinuousFunction.coe_sum, BoundedContinuousFunction.coe_mul, Pi.add_apply,
      Finset.sum_apply, Pi.mul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hψa i j ⟨x, subset_closure hx⟩ hx, hψf i j ⟨x, subset_closure hx⟩ hx]]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hψb i ⟨x, subset_closure hx⟩ hx]
    rfl
  refine ⟨(f1, g1), ?_, ?_⟩
  · simp only [obliqueDiffusionGraph, Set.mem_ofPred_eq]
    refine ⟨hCT, ?_, J, hJc, fun x hx => (hfd x hx).symm, hJb⟩
    intro x hx
    have hxc : x ∈ closure Ω := subset_closure hx
    have hg : closedRegionRestriction g1 x = g1 ⟨x, hxc⟩ := by
      unfold closedRegionRestriction; rw [dif_pos hxc]
    rw [hg, hg1Ω x hx, clm_expand (fderiv ℝ (closedRegionRestriction f1) x) (b x), hfd x hx]
  -- distance bounds
  have hF2 : ContDiffOn ℝ 2 F Ω := (hF.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have hVs2 : ContDiffOn ℝ 2 (fun y => ∑ k, V k y) Ω := ContDiffOn.sum fun k _ => (hV3 k).1
  have hFd2 : ∀ x, DifferentiableAt ℝ (fderiv ℝ F) x := fun x =>
    ((hF.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiable (by norm_num)) x
  have hfd2 : ∀ x ∈ Ω, DifferentiableAt ℝ (fderiv ℝ f) x := fun x hx =>
    (((hf2.fderiv_of_isOpen hopen (m := 1) (by norm_num)).differentiableOn (by norm_num)) x
      hx).differentiableAt (hopen.mem_nhds hx)
  have hb0 : ∀ x ∈ Ω, |G x - f x| ≤ θ := by
    intro x hx
    have e : G x - f x = (F x - f x) + ∑ k, V k x := by rw [hG]; ring
    have hs : |∑ k, V k x| ≤ Ks * S :=
      (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ => hV5 k x).trans
        (le_of_eq (by rw [hKs, Finset.sum_mul])))
    rw [e]
    have := (hFb x hx).1
    calc _ ≤ |F x - f x| + |∑ k, V k x| := abs_add_le _ _
      _ ≤ θ / 2 + Ks * S := add_le_add this hs
      _ ≤ θ := by linarith
  have hb1 : ∀ x ∈ Ω, ‖fderiv ℝ G x - fderiv ℝ f x‖ ≤ θ := by
    intro x hx
    have e : fderiv ℝ G x - fderiv ℝ f x = (fderiv ℝ F x - fderiv ℝ f x) +
        ∑ k, fderiv ℝ (V k) x := by rw [hDG]; abel
    have hs : ‖∑ k, fderiv ℝ (V k) x‖ ≤ Ks * S :=
      (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => hV6 k x).trans
        (le_of_eq (by rw [hKs, Finset.sum_mul])))
    rw [e]
    have := (hFb x hx).2.1
    calc _ ≤ ‖fderiv ℝ F x - fderiv ℝ f x‖ + ‖∑ k, fderiv ℝ (V k) x‖ := norm_add_le _ _
      _ ≤ θ / 2 + Ks * S := add_le_add this hs
      _ ≤ θ := by linarith
  have hb2 : ∀ x ∈ Ω, ∀ i j,
      |fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) -
        fderiv ℝ (fun y => fderiv ℝ G y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1)| ≤ θ := by
    intro x hx i j
    have e := partial2_add hopen hF2 hVs2 hx i j
    rw [partial2_sum hopen Finset.univ V (fun k _ => (hV3 k).1) hx i j] at e
    have hs : |∑ k, fderiv ℝ (fun y => fderiv ℝ (V k) y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1)| ≤ Ks * S :=
      (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ => hV7 k x hx i j).trans
        (le_of_eq (by rw [hKs, Finset.sum_mul])))
    have hd := partial2_sub_le (hFd2 x) (hfd2 x hx) i j
    have hFb' := (hFb x hx).2.2
    rw [hG, e, abs_sub_comm]
    have e2 : ∀ p q r : ℝ, p + q - r = (p - r) + q := fun p q r => by ring
    rw [e2]
    calc _ ≤ |fderiv ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1) -
          fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1)| + |∑ k, fderiv ℝ (fun y => fderiv ℝ (V k) y
            (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)| := abs_add_le _ _
      _ ≤ θ / 2 + Ks * S := add_le_add (hd.trans hFb') hs
      _ ≤ θ := by linarith
  have hθ2 : θ ≤ ε / 2 := by
    have : θ ≤ (1 + Aa + Bb) * θ := by nlinarith
    linarith
  have hd1 : ‖fg.1 - f1‖ ≤ ε / 2 := by
    refine bcf_le_of_dense _ (by positivity) fun x hx => ?_
    have e1 : fg.1 x = f x := (restr_apply fg.1 x).symm
    have e2 : f1 x = G x := rfl
    rw [BoundedContinuousFunction.sub_apply, e1, e2, abs_sub_comm]
    exact (hb0 x hx).trans hθ2
  have hd2 : ‖fg.2 - g1‖ ≤ ε / 2 := by
    refine bcf_le_of_dense _ (by positivity) fun x hx => ?_
    have e1 : fg.2 x = closedRegionRestriction fg.2 x := (restr_apply fg.2 x).symm
    have e2 : g1 x = g1 ⟨x, subset_closure hx⟩ := rfl
    rw [BoundedContinuousFunction.sub_apply, e1, e2, hfg2 x hx, hg1Ω x hx,
      clm_expand (fderiv ℝ f x) (b x)]
    simp only [partial2_congr hopen hf1Ω hx]
    have e3 : (1 / 2 : ℝ) * (∑ i, ∑ j, a x i j *
          fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1)) +
        ∑ i, b x i * fderiv ℝ f x (EuclideanSpace.single i 1) -
        ((1 / 2 : ℝ) * (∑ i, ∑ j, a x i j *
          fderiv ℝ (fun y => fderiv ℝ G y (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1)) +
        ∑ i, b x i * fderiv ℝ G x (EuclideanSpace.single i 1)) =
        (1 / 2 : ℝ) * (∑ i, ∑ j, a x i j *
          (fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1) -
          fderiv ℝ (fun y => fderiv ℝ G y (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1))) +
        ∑ i, b x i * (fderiv ℝ f x (EuclideanSpace.single i 1) -
          fderiv ℝ G x (EuclideanSpace.single i 1)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    rw [e3]
    refine (lin_bound _ _ (fun i j => ‖ψa i j‖) _ _ (fun i => ‖ψb i‖) (haB x hx) (hbB x hx)
      (hb2 x hx) (fun i => ?_)).trans ?_
    · have h := (fderiv ℝ f x - fderiv ℝ G x).le_opNorm (EuclideanSpace.single i (1 : ℝ))
      rw [EuclideanSpace.norm_single, norm_one, mul_one, ContinuousLinearMap.sub_apply,
        Real.norm_eq_abs, norm_sub_rev] at h
      exact h.trans (hb1 x hx)
    · show ((1 / 2 : ℝ) * (∑ i, ∑ j, ‖ψa i j‖) + ∑ i, ‖ψb i‖) * θ ≤ ε / 2
      have hle : (1 / 2 : ℝ) * Aa + Bb ≤ 1 + Aa + Bb := by linarith
      calc ((1 / 2 : ℝ) * (∑ i, ∑ j, ‖ψa i j‖) + ∑ i, ‖ψb i‖) * θ = ((1 / 2 : ℝ) * Aa + Bb) * θ := by
            rw [hAa, hBb]
        _ ≤ (1 + Aa + Bb) * θ := mul_le_mul_of_nonneg_right hle hθ0.le
        _ = ε / 2 := hθε
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  rw [Prod.dist_eq]
  simp only
  rw [dist_eq_norm, dist_eq_norm]
  exact max_le hd1 hd2

open EthierKurtz in
theorem solution (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i)
    (μ' : ℝ) (hμ' : 0 < μ' ∧ μ' ≤ μ) :
    obliqueDiffusionGraph Ω μ' a b c ⊆ closure (obliqueDiffusionGraph Ω μ a b c) := by
  exact P50d2R.closure_of n Ω hbounded hopen μ hμ a b c normal haHolder hbHolder hc hnormal
    hoblique μ' hμ'
