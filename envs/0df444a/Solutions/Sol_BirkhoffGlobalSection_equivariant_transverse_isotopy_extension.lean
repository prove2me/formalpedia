-- Prove2me | solution 1 for BirkhoffGlobalSection.equivariant_transverse_isotopy_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-07T13:33:24.214391+00:00
-- url     : https://prove2.me/submissions/ea478b17-3193-4ab9-beae-b6d3f824d4f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_transverse_isotopy_contact_generator
import Theorems.Thm_FlowCalculus_compact_supported_flow_preserves_regular_level
import Theorems.Thm_GrayStability_pullback_family_hasDerivAt
import Theorems.Thm_FlowCalculus_exists_unique_global_trajectory_of_compact_support
import Theorems.Thm_FlowCalculus_uniform_spatial_lipschitz_of_compact_support
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Equivariant extension of a transverse Hopf isotopy

The child `transverse_isotopy_contact_generator` is the core step of the isotopy extension
theorem for contact submanifolds (Geiges, *Contact geometry*, Theorem 2.42 and its proof). It
asks for a smooth, compactly supported, odd, time-dependent vector field `X_t` that is tangent
to the sphere and is an infinitesimal automorphism of the radial contact structure there,
`L_{X_t} λ = μ_t λ`, and that equals the velocity of the knot along the moving knot.

Everything else is proved here from proved platform results on flows:

* `compact_supported_flow_preserves_regular_level` integrates `X` to a jointly smooth flow
  `ψ_t` preserving the sphere. The reversed field `-X_{1-t}` integrates to `φ_t`, and
  uniqueness of trajectories gives `φ_1 = ψ_1⁻¹`. Oddness of `X` gives `ψ_1(-y) = -ψ_1(y)`.
* `pullback_family_hasDerivAt` gives `d/dt (ψ_t^* λ) = ψ_t^*(L_{X_t} λ) = (μ_t ∘ ψ_t) ψ_t^* λ`
  on tangent vectors, so `ψ_1^* λ = exp(∫₀¹ μ_s ∘ ψ_s ds) λ` (Geiges, Corollary 2.23).
* The trajectory `t ↦ ψ_t(I(0,u))` and the knot `t ↦ I(t,u)` solve the same equation on
  `[0,1]`, so `ψ_1` maps the standard Hopf circle onto `K`.
-/

open BirkhoffGlobalSection GrayStability
open scoped ContDiff Topology

set_option autoImplicit false

namespace BirkhoffGlobalSection.IsotopyExtension

/-- The round sphere as the zero level of `|y|² - 1`. -/
noncomputable def sphereEq : E 4 → (Fin 1 → ℝ) := fun y _ => zNormSq y + wNormSq y - 1

lemma mem_levelSet_sphereEq {y : Phase} : y ∈ levelSet sphereEq ↔ y ∈ unitThreeSphere := by
  change sphereEq y = 0 ↔ zNormSq y + wNormSq y = 1
  constructor
  · intro h
    have := congrFun h 0
    simp only [sphereEq, Pi.zero_apply] at this
    linarith
  · intro h
    funext i
    simp only [sphereEq, Pi.zero_apply, h, sub_self]

/-- The derivative of the squared norm. -/
noncomputable def normSqDeriv (y : Phase) : Phase →L[ℝ] ℝ :=
  (2 * y 0) • ContinuousLinearMap.proj 0 + (2 * y 1) • ContinuousLinearMap.proj 1 +
    (2 * y 2) • ContinuousLinearMap.proj 2 + (2 * y 3) • ContinuousLinearMap.proj 3

lemma normSqDeriv_apply (y v : Phase) : normSqDeriv y v = 2 * phaseDot y v := by
  simp [normSqDeriv, phaseDot]
  ring

lemma hasFDerivAt_normSq (y : Phase) :
    HasFDerivAt (fun x : Phase => zNormSq x + wNormSq x) (normSqDeriv y) y := by
  have hp := fun i : Fin 4 =>
    (hasFDerivAt_apply (𝕜 := ℝ) i y).mul (hasFDerivAt_apply (𝕜 := ℝ) i y)
  have hN := ((hp 0).add (hp 1)).add ((hp 2).add (hp 3))
  refine (hN.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · refine ContinuousLinearMap.ext fun v => ?_
    simp [normSqDeriv]
    ring
  · simp [zNormSq, wNormSq]
    ring

lemma hasFDerivAt_sphereEq (y : Phase) :
    HasFDerivAt sphereEq (ContinuousLinearMap.pi fun _ : Fin 1 => normSqDeriv y) y :=
  hasFDerivAt_pi.2 fun _ => (hasFDerivAt_normSq y).sub_const 1

lemma mem_tangentSpace_sphereEq {y v : Phase} :
    v ∈ tangentSpace sphereEq y ↔ phaseDot y v = 0 := by
  change fderiv ℝ sphereEq y v = 0 ↔ phaseDot y v = 0
  rw [(hasFDerivAt_sphereEq y).fderiv]
  constructor
  · intro h
    have := congrFun h 0
    simp only [ContinuousLinearMap.pi_apply, normSqDeriv_apply, Pi.zero_apply] at this
    linarith
  · intro h
    funext i
    simp only [ContinuousLinearMap.pi_apply, normSqDeriv_apply, Pi.zero_apply, h, mul_zero]

lemma sphereEq_regular : IsCompactRegularLevel sphereEq := by
  refine ⟨?_, ?_, ?_⟩
  · refine contDiff_pi.2 fun _ => ?_
    show ContDiff ℝ ∞ (fun y : Phase => zNormSq y + wNormSq y - 1)
    unfold zNormSq wNormSq
    fun_prop
  · have hset : levelSet sphereEq = unitThreeSphere := Set.ext fun y => mem_levelSet_sphereEq
    rw [hset]
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_eq (by unfold zNormSq wNormSq; fun_prop) continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : Phase)) (r := 1)).subset fun y hy => ?_
      have h : zNormSq y + wNormSq y = 1 := hy
      simp only [zNormSq, wNormSq] at h
      have h0 : y 0 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y 1), sq_nonneg (y 2), sq_nonneg (y 3)]
      have h1 : y 1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 2), sq_nonneg (y 3)]
      have h2 : y 2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 3)]
      have h3 : y 3 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2)]
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs]
      refine (sq_le_one_iff_abs_le_one _).1 ?_
      fin_cases i
      exacts [h0, h1, h2, h3]
  · intro y hy w
    have hy' : zNormSq y + wNormSq y = 1 := mem_levelSet_sphereEq.1 hy
    have hyy : phaseDot y y = 1 := by
      simp only [zNormSq, wNormSq] at hy'
      simp only [phaseDot]
      linarith [hy']
    refine ⟨(w 0 / 2) • y, ?_⟩
    rw [(hasFDerivAt_sphereEq y).fderiv]
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp only [ContinuousLinearMap.pi_apply, map_smul, normSqDeriv_apply, smul_eq_mul, hyy]
    ring

/-- The radial contact form `λ_y(v) = -ω(y,v)/2` as a linear family of covectors. -/
noncomputable def radialForm : Phase →L[ℝ] (Phase →L[ℝ] ℝ) :=
  (-(1 / 2 : ℝ)) •
    ((ContinuousLinearMap.proj 0 : Phase →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.proj 2 : Phase →L[ℝ] ℝ) -
      (ContinuousLinearMap.proj 2 : Phase →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.proj 0 : Phase →L[ℝ] ℝ) +
      (ContinuousLinearMap.proj 1 : Phase →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.proj 3 : Phase →L[ℝ] ℝ) -
      (ContinuousLinearMap.proj 3 : Phase →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.proj 1 : Phase →L[ℝ] ℝ))

lemma radialForm_apply (y v : Phase) : radialForm y v = phaseRadialContact y v := by
  simp [radialForm, phaseRadialContact, phaseSymplecticForm]
  ring

/-- Trajectories of a smooth compactly supported field agreeing at one time agree. -/
lemma flow_uniq (X : ℝ → Phase → Phase) (hX : ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2))
    (hsupp : ∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0)
    {γ₁ γ₂ : ℝ → Phase} (t₀ : ℝ) (h₁ : ∀ t, HasDerivAt γ₁ (X t (γ₁ t)) t)
    (h₂ : ∀ t, HasDerivAt γ₂ (X t (γ₂ t)) t) (h0 : γ₁ t₀ = γ₂ t₀) : γ₁ = γ₂ := by
  obtain ⟨γ, -, huniq⟩ :=
    FlowCalculus.exists_unique_global_trajectory_of_compact_support X hX hsupp t₀ (γ₁ t₀)
  rw [huniq γ₁ ⟨rfl, h₁⟩, huniq γ₂ ⟨h0.symm, h₂⟩]

/-- The scalar linear equation `f' = a f` on `[0,1]` integrates to an exponential factor. -/
lemma exp_factor {f a : ℝ → ℝ} (ha : Continuous a)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (a t * f t) t) :
    f 1 = Real.exp (∫ s in (0 : ℝ)..1, a s) * f 0 := by
  set A : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, a s with hAdef
  have hA : ∀ t, HasDerivAt A (a t) t := fun t => (ha.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hA0 : A 0 = 0 := by simp [hAdef]
  set g : ℝ → ℝ := fun t => f t * Real.exp (-A t) with hgdef
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g 0 t := by
    intro t ht
    have h := (hf t ht).mul ((hA t).neg.exp)
    exact h.congr_deriv (by ring)
  have hgc : ContinuousOn g (Set.Icc 0 1) := HasDerivAt.continuousOn fun t ht => hg t ht
  have hconst := constant_of_has_deriv_right_zero hgc
    (fun t ht => (hg t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩
  simp only [hgdef, hA0, neg_zero, Real.exp_zero, mul_one] at hconst
  have he : Real.exp (A 1) * Real.exp (-A 1) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc f 1 = Real.exp (A 1) * (f 1 * Real.exp (-A 1)) := by
        rw [mul_comm (f 1), ← mul_assoc, he, one_mul]
    _ = Real.exp (A 1) * f 0 := by rw [hconst]

/-- **Integration of a time-dependent contact vector field** (Geiges, Corollary 2.23): the
time-one map of its flow is an equivariant contactomorphism of the sphere. -/
lemma integrate (X : ℝ → Phase → Phase) (μ : ℝ → Phase → ℝ)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2))
    (hμ : ContDiff ℝ ∞ (fun p : ℝ × Phase => μ p.1 p.2))
    (hsupp : ∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0)
    (hodd : ∀ t y, X t (-y) = -X t y)
    (htan : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (X t y) = 0)
    (hlie : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      phaseRadialContact (X t y) v + phaseRadialContact y (fderiv ℝ (X t) y v) =
        μ t y * phaseRadialContact y v) :
    ∃ F : EquivariantSphereContactomorphism, ∃ ψ : ℝ → Phase → Phase,
      F.toFun = ψ 1 ∧ (∀ y, ψ 0 y = y) ∧
        ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t := by
  -- the forward flow
  obtain ⟨ψ, hψc, hψ0, hψbij, hψflow, hψiso, hψtan⟩ :=
    FlowCalculus.compact_supported_flow_preserves_regular_level sphereEq sphereEq_regular X hX
      hsupp (fun t ht y hy => mem_tangentSpace_sphereEq.2
        (htan t ht y (mem_levelSet_sphereEq.1 hy)))
  -- the reversed field and its flow
  set Xr : ℝ → Phase → Phase := fun t y => -X (1 - t) y with hXr
  have hXrc : ContDiff ℝ ∞ (fun p : ℝ × Phase => Xr p.1 p.2) := by
    have h1 : ContDiff ℝ ∞ (fun p : ℝ × Phase => ((1 - p.1, p.2) : ℝ × Phase)) := by fun_prop
    exact (hX.comp h1).neg
  have hXrsupp : ∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → Xr t y = 0 := by
    obtain ⟨C, hC, hCX⟩ := hsupp
    exact ⟨C, hC, fun t y hy => by simp [hXr, hCX _ y hy]⟩
  have hXrtan : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet sphereEq,
      Xr t y ∈ tangentSpace sphereEq y := by
    intro t ht y hy
    rw [mem_tangentSpace_sphereEq]
    have h1 : 1 - t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h2 := htan (1 - t) h1 y (mem_levelSet_sphereEq.1 hy)
    simp only [hXr, phaseDot, Pi.neg_apply] at h2 ⊢
    linarith
  obtain ⟨φ, hφc, hφ0, -, hφflow, hφiso, -⟩ :=
    FlowCalculus.compact_supported_flow_preserves_regular_level sphereEq sphereEq_regular Xr hXrc
      hXrsupp hXrtan
  have hneg1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => 1 - s) (-1) s := fun s => by
    simpa using (hasDerivAt_id s).const_sub 1
  -- `ψ` run backwards is a trajectory of the reversed field, and conversely
  have hrevψ : ∀ y s, HasDerivAt (fun s => ψ (1 - s) y) (Xr s (ψ (1 - s) y)) s := by
    intro y s
    exact ((hψflow (1 - s) y).scomp s (hneg1 s)).congr_deriv (by simp [hXr])
  have hrevφ : ∀ z s, HasDerivAt (fun s => φ (1 - s) z) (X s (φ (1 - s) z)) s := by
    intro z s
    exact ((hφflow (1 - s) z).scomp s (hneg1 s)).congr_deriv (by simp [hXr])
  have hleft : ∀ y, φ 1 (ψ 1 y) = y := by
    intro y
    have e := flow_uniq Xr hXrc hXrsupp (γ₁ := fun s => φ s (ψ 1 y))
      (γ₂ := fun s => ψ (1 - s) y) 0 (fun s => hφflow s (ψ 1 y)) (hrevψ y)
      (by simp [hφ0])
    simpa [hψ0] using congrFun e 1
  have hright : ∀ z, ψ 1 (φ 1 z) = z := by
    intro z
    have e := flow_uniq X hX hsupp (γ₁ := fun s => ψ s (φ 1 z))
      (γ₂ := fun s => φ (1 - s) z) 0 (fun s => hψflow s (φ 1 z)) (hrevφ z)
      (by simp [hψ0])
    simpa [hφ0] using congrFun e 1
  have hanti : ∀ y, ψ 1 (-y) = -ψ 1 y := by
    intro y
    have e := flow_uniq X hX hsupp (γ₁ := fun s => ψ s (-y)) (γ₂ := fun s => -ψ s y) 0
      (fun s => hψflow s (-y))
      (fun s => (hψflow s y).neg.congr_deriv (by rw [hodd]))
      (by simp [hψ0])
    exact congrFun e 1
  have hψt : ∀ t, ContDiff ℝ ∞ (ψ t) := fun t =>
    hψc.comp (contDiff_const.prodMk contDiff_id)
  have hφt : ∀ t, ContDiff ℝ ∞ (φ t) := fun t =>
    hφc.comp (contDiff_const.prodMk contDiff_id)
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- the contact identity along the flow
  have hη : IsSmoothFamily (fun _ : ℝ => (⇑radialForm : OneForm 4)) := by
    show ContDiff ℝ ∞ (fun p : ℝ × Phase => radialForm p.2)
    exact radialForm.contDiff.comp contDiff_snd
  have hcontact : ∀ y ∈ unitThreeSphere, ∃ a : ℝ, 0 < a ∧ ∀ v : Phase, phaseDot y v = 0 →
      phaseRadialContact (ψ 1 y) (fderiv ℝ (ψ 1) y v) = a * phaseRadialContact y v := by
    intro y hy
    set a : ℝ → ℝ := fun s => μ s (ψ s y) with hadef
    have hac : Continuous a :=
      hμ.continuous.comp (continuous_id.prodMk
        (hψc.continuous.comp (continuous_id.prodMk continuous_const)))
    refine ⟨Real.exp (∫ s in (0 : ℝ)..1, a s), Real.exp_pos _, fun v hv => ?_⟩
    set f : ℝ → ℝ := fun s => phaseRadialContact (ψ s y) (fderiv ℝ (ψ s) y v) with hfdef
    have hfd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (a s * f s) s := by
      intro s hs
      have h := GrayStability.pullback_family_hasDerivAt (fun _ => ⇑radialForm) hη X hX ψ hψc
        hψ0 hψbij hψflow s y v
      have hz : ψ s y ∈ unitThreeSphere := mem_levelSet_sphereEq.1
        ((hψiso.2.2 s hs).1.mapsTo (mem_levelSet_sphereEq.2 hy))
      have hw : phaseDot (ψ s y) (fderiv ℝ (ψ s) y v) = 0 :=
        mem_tangentSpace_sphereEq.1
          (hψtan s hs y (mem_levelSet_sphereEq.2 hy) v (mem_tangentSpace_sphereEq.2 hv))
      have hval : formTimeDeriv (fun _ => ⇑radialForm) s (ψ s y) (fderiv ℝ (ψ s) y v) +
          lieDerivOneForm (X s) ⇑radialForm (ψ s y) (fderiv ℝ (ψ s) y v) = a s * f s := by
        simp only [formTimeDeriv, lieDerivOneForm, deriv_const, ContinuousLinearMap.fderiv,
          radialForm_apply, zero_add, hadef, hfdef]
        exact hlie s hs _ hz _ hw
      rw [hval] at h
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
      simp only [hfdef, pullback, radialForm_apply]
    have h01 := exp_factor hac hfd
    have hf0 : f 0 = phaseRadialContact y v := by
      have h0id : ψ 0 = id := funext hψ0
      simp only [hfdef, h0id, fderiv_id, ContinuousLinearMap.id_apply, id]
    rw [hf0] at h01
    exact h01
  refine ⟨{ toFun := ψ 1
            invFun := φ 1
            smooth := fun y _ => (hψt 1).contDiffAt
            inv_smooth := fun y _ => (hφt 1).contDiffAt
            maps_sphere := fun y hy => mem_levelSet_sphereEq.1
              ((hψiso.2.2 1 h1mem).1.mapsTo (mem_levelSet_sphereEq.2 hy))
            inv_maps_sphere := fun y hy => mem_levelSet_sphereEq.1
              ((hφiso.2.2 1 h1mem).1.mapsTo (mem_levelSet_sphereEq.2 hy))
            left_inv := fun y _ => hleft y
            right_inv := fun z _ => hright z
            antipodal := fun y _ => hanti y
            contact := hcontact }, ψ, rfl, hψ0, hψflow⟩

end BirkhoffGlobalSection.IsotopyExtension

open BirkhoffGlobalSection.IsotopyExtension

theorem solution (K : Set Phase) (I : EquivariantTransverseHopfIsotopy K) :
    ∃ F : EquivariantSphereContactomorphism,
      F.toFun '' (standardHopfCircle '' unitCircle) = K := by
  obtain ⟨X, μ, hX, hμ, hsupp, hodd, htan, hlie, hvel⟩ :=
    transverse_isotopy_contact_generator K I
  obtain ⟨F, ψ, hF, hψ0, hψflow⟩ := integrate X μ hX hμ hsupp hodd htan hlie
  obtain ⟨L, hL⟩ := FlowCalculus.uniform_spatial_lipschitz_of_compact_support X hX hsupp 0 1
  -- the flow carries the knot along the isotopy
  have hfollow : ∀ u ∈ unitCircle, ψ 1 (I.isotopy (0, u)) = I.isotopy (1, u) := by
    intro u hu
    have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun t => I.isotopy (t, u)) (X t (I.isotopy (t, u))) t := by
      intro t ht
      have hd : DifferentiableAt ℝ I.isotopy (t, u) :=
        (I.smooth t ht u hu).differentiableAt (by simp)
      have hc : HasDerivAt (fun t : ℝ => ((t, u) : ℝ × Plane)) ((1 : ℝ), (0 : Plane)) t :=
        (hasDerivAt_id t).prodMk (hasDerivAt_const t u)
      rw [hvel t ht u hu]
      exact hd.hasFDerivAt.comp_hasDerivAt t hc
    have heq := ODE_solution_unique_of_mem_Icc_right (v := X) (s := fun _ => Set.univ) (K := L)
      (f := fun t => ψ t (I.isotopy (0, u))) (g := fun t => I.isotopy (t, u))
      (fun t ht => (hL t (Set.Ico_subset_Icc_self ht)).lipschitzOnWith)
      (HasDerivAt.continuousOn fun t _ => hψflow t _)
      (fun t _ => (hψflow t _).hasDerivWithinAt) (fun _ _ => trivial)
      (HasDerivAt.continuousOn fun t ht => hb t ht)
      (fun t ht => (hb t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt) (fun _ _ => trivial)
      (by simp [hψ0])
    exact heq ⟨zero_le_one, le_rfl⟩
  refine ⟨F, ?_⟩
  rw [hF]
  ext z
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    rw [← I.start u hu, hfollow u hu]
    exact I.finish.subset ⟨u, hu, rfl⟩
  · intro hz
    obtain ⟨u, hu, rfl⟩ := I.finish.symm.subset hz
    exact ⟨standardHopfCircle u, ⟨u, hu, rfl⟩, by rw [← I.start u hu, hfollow u hu]⟩
