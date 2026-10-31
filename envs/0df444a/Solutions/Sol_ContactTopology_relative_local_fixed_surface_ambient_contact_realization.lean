-- Prove2me | solution 1 for ContactTopology.relative_local_fixed_surface_ambient_contact_realization
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T23:58:14.390565+00:00
-- url     : https://prove2.me/submissions/2b6e16d5-6be8-4d15-95fd-2c32b5bf82fa

import Theorems.Thm_ContactTopology_relative_compact_contact_embedding_isotopy_extension
import Definitions.Def_GrayStability_Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Compact
import Theorems.Thm_ContactTopology_local_fixed_surface_contact_field_homotopy
import Theorems.Thm_FlowCalculus_compact_supported_flow_preserves_regular_level
import Theorems.Thm_FlowCalculus_exists_unique_global_trajectory_of_compact_support
import Theorems.Thm_FlowCalculus_regular_level_trajectory_invariant
import Theorems.Thm_FlowCalculus_smooth_flow_spatial_derivative_injective
import Theorems.Thm_GrayStability_pullback_family_hasDerivAt
import Theorems.Thm_ParameterizedCalculus_smooth_scalar_linear_transport


/-! Three-dimensional contact-form deformations. The explicit Moser field below
is the analytic local input to deformation arguments for convex surfaces. No
bypass existence or tight-solid-torus uniqueness is assumed or claimed here. -/
namespace ContactTopology.ConvexDeformation
open Set Function GrayStability
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev V := Fin 3 → ℝ

def dot (a v : V) : ℝ := a 0*v 0+a 1*v 1+a 2*v 2

def cross (a b : V) : V :=
  ![a 1*b 2-a 2*b 1,a 2*b 0-a 0*b 2,a 0*b 1-a 1*b 0]

def covector : V →L[ℝ] (V →L[ℝ] ℝ) :=
  (ContinuousLinearMap.proj 0 : V →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj 0 : V →L[ℝ] ℝ)+
  (ContinuousLinearMap.proj 1 : V →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj 1 : V →L[ℝ] ℝ)+
  (ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ)

lemma covector_apply (a v : V) : covector a v = dot a v := by
  simp [covector,dot]

lemma vector_expansion (v : V) :
    v = v 0 • Pi.single 0 1+v 1 • Pi.single 1 1+v 2 • Pi.single 2 1 := by
  ext i
  fin_cases i <;> simp

def curlLinear (D : V →L[ℝ] V) : V :=
  ![D (Pi.single 1 1) 2-D (Pi.single 2 1) 1,
    D (Pi.single 2 1) 0-D (Pi.single 0 1) 2,
    D (Pi.single 0 1) 1-D (Pi.single 1 1) 0]

lemma exterior_cross (D : V →L[ℝ] V) (u v : V) :
    dot (D u) v-dot (D v) u = dot (curlLinear D) (cross u v) := by
  have hu : D u = u 0 • D (Pi.single 0 1)+u 1 • D (Pi.single 1 1)+u 2 • D (Pi.single 2 1) := by
    conv_lhs => rw [vector_expansion u]
    simp only [map_add,map_smul]
  have hv : D v = v 0 • D (Pi.single 0 1)+v 1 • D (Pi.single 1 1)+v 2 • D (Pi.single 2 1) := by
    conv_lhs => rw [vector_expansion v]
    simp only [map_add,map_smul]
  rw [hu,hv]
  simp [dot,curlLinear,cross]
  ring

lemma moser_algebra (a b c v : V) (h : dot a c ≠ 0) :
    dot a ((dot a c)⁻¹ • cross a b) = 0 ∧
    dot b v+dot c (cross ((dot a c)⁻¹ • cross a b) v) =
      (dot c b/dot a c)*dot a v := by
  constructor
  · simp [dot,cross]
    ring
  · have hp : dot c (cross ((dot a c)⁻¹ • cross a b) v) =
        (dot a c)⁻¹*(dot c b*dot a v-dot a c*dot b v) := by
      simp [dot,cross]
      ring
    rw [hp,div_eq_mul_inv]
    calc
      dot b v+(dot a c)⁻¹*(dot c b*dot a v-dot a c*dot b v) =
          (1-(dot a c)⁻¹*dot a c)*dot b v+(dot c b*(dot a c)⁻¹)*dot a v := by ring
      _ = _ := by rw [inv_mul_cancel₀ h]; ring

def spatialD (A : ℝ × V → V) (p : ℝ × V) : V →L[ℝ] V :=
  (fderiv ℝ A p).comp (ContinuousLinearMap.inr ℝ ℝ V)

def velocity (A : ℝ × V → V) (p : ℝ × V) : V := fderiv ℝ A p (1,0)
def curl (A : ℝ × V → V) (p : ℝ × V) : V := curlLinear (spatialD A p)
def volume (A : ℝ × V → V) (p : ℝ × V) : ℝ := dot (A p) (curl A p)
def form (A : ℝ × V → V) (t : ℝ) : OneForm 3 := fun y => covector (A (t,y))
def moser (A : ℝ × V → V) (p : ℝ × V) : V :=
  (volume A p)⁻¹ • cross (A p) (velocity A p)
def rate (A : ℝ × V → V) (p : ℝ × V) : ℝ :=
  dot (curl A p) (velocity A p)/volume A p

lemma spatialD_eq (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A) (t : ℝ) (y : V) :
    fderiv ℝ (fun z => A (t,z)) y = spatialD A (t,y) := by
  have hd := (hA.differentiable (by simp) (t,y)).hasFDerivAt.comp y
    ((hasFDerivAt_const (𝕜 := ℝ) t y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y))
  exact hd.fderiv

lemma form_fderiv (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A) (t : ℝ) (y u v : V) :
    fderiv ℝ (form A t) y u v = dot (spatialD A (t,y) u) v := by
  have hd := covector.hasFDerivAt.comp y
    ((hA.differentiable (by simp) (t,y)).hasFDerivAt.comp y
      ((hasFDerivAt_const (𝕜 := ℝ) t y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y)))
  change HasFDerivAt (form A t) _ y at hd
  rw [hd.fderiv]
  exact covector_apply _ _

lemma form_time_deriv (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A) (t : ℝ) (y v : V) :
    formTimeDeriv (form A) t y v = dot (velocity A (t,y)) v := by
  have hd := (hA.differentiable (by simp) (t,y)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  have hc := (covector.hasFDerivAt.comp_hasDerivAt t hd).clm_apply (hasDerivAt_const t v)
  change HasDerivAt (fun s => form A s y v) _ t at hc
  rw [formTimeDeriv,hc.deriv]
  simpa [velocity] using covector_apply (velocity A (t,y)) v

lemma curl_contDiff (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (curl A) := by
  have hd := hA.fderiv_right (by simp : (∞:WithTop ℕ∞) + 1 ≤ ∞)
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [curl,curlLinear,spatialD] <;> fun_prop

lemma velocity_contDiff (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (velocity A) :=
  (hA.fderiv_right (by simp)).clm_apply contDiff_const

lemma volume_contDiff (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (volume A) := by
  have hc := curl_contDiff A hA
  change ContDiff ℝ ∞ (fun p => A p 0*curl A p 0+A p 1*curl A p 1+A p 2*curl A p 2)
  fun_prop

lemma moser_contDiff (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (hvol : ∀ p, volume A p ≠ 0) : ContDiff ℝ ∞ (moser A) := by
  have hv := velocity_contDiff A hA
  have hi := (volume_contDiff A hA).inv hvol
  apply hi.smul
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [cross] <;> fun_prop

lemma rate_contDiff (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (hvol : ∀ p, volume A p ≠ 0) : ContDiff ℝ ∞ (rate A) := by
  have hc := curl_contDiff A hA
  have hv := velocity_contDiff A hA
  have hi := (volume_contDiff A hA).inv hvol
  change ContDiff ℝ ∞ (fun p =>
    (curl A p 0*velocity A p 0+curl A p 1*velocity A p 1+curl A p 2*velocity A p 2)*
      (volume A p)⁻¹)
  exact (show ContDiff ℝ ∞ (fun p =>
    curl A p 0*velocity A p 0+curl A p 1*velocity A p 1+curl A p 2*velocity A p 2) by fun_prop).mul hi

lemma moser_kernel (A : ℝ × V → V) (p : ℝ × V) : covector (A p) (moser A p) = 0 := by
  simp [covector_apply,moser,dot,cross]
  ring

lemma moser_lie_equation (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (hvol : ∀ p, volume A p ≠ 0) (t : ℝ) (y v : V) :
    formTimeDeriv (form A) t y v+
      lieDerivOneForm (fun z => moser A (t,z)) (form A t) y v =
        rate A (t,y)*form A t y v := by
  have hX := (moser_contDiff A hA hvol).comp (contDiff_const.prodMk contDiff_id :
    ContDiff ℝ ∞ (fun z : V => (t,z)))
  have hα := covector.contDiff.comp (hA.comp (contDiff_const.prodMk contDiff_id :
    ContDiff ℝ ∞ (fun z : V => (t,z))))
  have hz : (fun z : V => form A t z (moser A (t,z))) = fun _ => 0 :=
    funext fun z => moser_kernel A (t,z)
  change ContDiff ℝ ∞ (form A t) at hα
  change ContDiff ℝ ∞ (fun z => moser A (t,z)) at hX
  have hd := (hα.differentiable (by simp) y).hasFDerivAt.clm_apply
    (hX.differentiable (by simp) y).hasFDerivAt
  have hd0 : fderiv ℝ (fun z : V => form A t z (moser A (t,z))) y v = 0 := by
    rw [hz]
    simp
  change HasFDerivAt (fun z => form A t z (moser A (t,z))) _ y at hd
  rw [hd.fderiv] at hd0
  change form A t y (fderiv ℝ (fun z => moser A (t,z)) y v)+
    fderiv ℝ (form A t) y v (moser A (t,y)) = 0 at hd0
  rw [form_fderiv A hA] at hd0
  have hm := (moser_algebra (A (t,y)) (velocity A (t,y)) (curl A (t,y)) v (hvol (t,y))).2
  change dot (velocity A (t,y)) v+dot (curlLinear (spatialD A (t,y)))
    (cross (moser A (t,y)) v) = rate A (t,y)*form A t y v at hm
  rw [← exterior_cross (spatialD A (t,y)) (moser A (t,y)) v] at hm
  rw [form_time_deriv A hA]
  dsimp [lieDerivOneForm]
  rw [form_fderiv A hA]
  change dot (velocity A (t,y)) v+ (dot (spatialD A (t,y) (moser A (t,y))) v+
    form A t y (fderiv ℝ (fun z => moser A (t,z)) y v)) = _
  change dot (velocity A (t,y)) v+(dot (spatialD A (t,y) (moser A (t,y))) v-
    dot (spatialD A (t,y) v) (moser A (t,y))) =
      rate A (t,y)*form A t y v at hm
  linarith


lemma smooth_inverse_of_bijective_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → E) (hf : ContDiff ℝ ∞ f) (hb : Function.Bijective f)
    (hi : ∀ x, Function.Injective (fderiv ℝ f x)) :
    ∃ g : E → E, ContDiff ℝ ∞ g ∧ (∀ x, g (f x) = x) ∧ (∀ x, f (g x) = x) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let L : E → E ≃L[ℝ] E := fun x => (LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap
    ⟨hi x,LinearMap.injective_iff_surjective.mp (hi x)⟩).toContinuousLinearEquiv
  have hd : ∀ x, HasFDerivAt f (L x : E →L[ℝ] E) x := by
    intro x
    exact (hf.differentiable (by simp) x).hasFDerivAt
  have ho : IsOpenMap f := isOpenMap_of_hasStrictFDerivAt_equiv
    (fun x => hf.contDiffAt.hasStrictFDerivAt' (hd x) (by simp))
  let H : E ≃ₜ E := (Equiv.ofBijective f hb).toHomeomorphOfContinuousOpen hf.continuous ho
  have hH : ContDiff ℝ ∞ (H : E → E) := hf
  have hHd : ∀ x, HasFDerivAt (H : E → E) (L x : E →L[ℝ] E) x := hd
  exact ⟨H.symm,H.contDiff_symm hHd hH,H.symm_apply_apply,H.apply_symm_apply⟩

lemma smooth_joint_flow_inverse {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (X ψ : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y) (hb : ∀ t, Function.Bijective (ψ t))
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t) :
    ∃ ρ : ℝ → V → V, ContDiff ℝ ∞ (fun p : ℝ × V => ρ p.1 p.2) ∧
      (∀ t y, ρ t (ψ t y) = y) ∧ (∀ t y, ψ t (ρ t y) = y) := by
  let : CompleteSpace V := FiniteDimensional.complete ℝ V
  let F : ℝ × V → ℝ × V := fun p => (p.1,ψ p.1 p.2)
  have hF : ContDiff ℝ ∞ F := contDiff_fst.prodMk hψ
  have hFb : Function.Bijective F := by
    constructor
    · intro p q he
      change (p.1,ψ p.1 p.2) = (q.1,ψ q.1 q.2) at he
      have ht := congrArg (fun z : ℝ × V => z.1) he
      have hy := congrArg (fun z : ℝ × V => z.2) he
      refine Prod.ext ht ?_
      apply (hb p.1).1
      change ψ p.1 p.2 = ψ q.1 q.2 at hy
      rw [← ht] at hy
      exact hy
    · rintro ⟨t,y⟩
      obtain ⟨x,hx⟩ := (hb t).2 y
      exact ⟨(t,x),Prod.ext rfl hx⟩
  have hFi : ∀ p, Function.Injective (fderiv ℝ F p) := by
    intro p
    have hfd := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk ((hψ.differentiable (by simp) p).hasFDerivAt)
    change HasFDerivAt F _ p at hfd
    have hslice := ((hψ.differentiable (by simp) p).hasFDerivAt).comp p.2
      ((hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2))
    change HasFDerivAt (ψ p.1) _ p.2 at hslice
    have hsi := FlowCalculus.smooth_flow_spatial_derivative_injective X ψ hX hψ h0 hd p.1 p.2
    intro v w he
    rw [hfd.fderiv] at he
    change (v.1,(fderiv ℝ (fun q : ℝ × V => ψ q.1 q.2) p) v) =
      (w.1,(fderiv ℝ (fun q : ℝ × V => ψ q.1 q.2) p) w) at he
    have ht := congrArg (fun z : ℝ × V => z.1) he
    have hy := congrArg (fun z : ℝ × V => z.2) he
    have hz : (fderiv ℝ (fun q : ℝ × V => ψ q.1 q.2) p) (0,v.2-w.2) = 0 := by
      change (fderiv ℝ (fun q : ℝ × V => ψ q.1 q.2) p) v =
        (fderiv ℝ (fun q : ℝ × V => ψ q.1 q.2) p) w at hy
      have hsub := sub_eq_zero.mpr hy
      rw [← map_sub] at hsub
      have hvw : v-w = (0,v.2-w.2) := by
        apply Prod.ext
        · exact sub_eq_zero.mpr ht
        · rfl
      rw [hvw] at hsub
      exact hsub
    refine Prod.ext ht ?_
    have hsz : fderiv ℝ (ψ p.1) p.2 (v.2-w.2) = 0 := by
      rw [hslice.fderiv]
      exact hz
    have hzv : v.2-w.2 = 0 := hsi (by simpa only [map_zero] using hsz)
    exact sub_eq_zero.mp hzv
  obtain ⟨G,hG,hGF,hFG⟩ := smooth_inverse_of_bijective_derivative F hF hFb hFi
  have hGt : ∀ t y, (G (t,y)).1 = t := by
    intro t y
    exact congrArg Prod.fst (hFG (t,y))
  refine ⟨fun t y => (G (t,y)).2,contDiff_snd.comp hG,?_,?_⟩
  · intro t y
    exact congrArg Prod.snd (hGF (t,y))
  · intro t y
    have he := congrArg Prod.snd (hFG (t,y))
    simpa only [F,hGt] using he


/-- The ambient flow part of the existing regular-level theorem can be used
with an empty regular level; no compactness of the ambient space is required. -/
lemma exists_ambient_flow (X : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0) :
    ∃ ψ : ℝ → V → V, ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧ (∀ t, Bijective (ψ t)) ∧
      ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t := by
  let F : V → (Fin 1 → ℝ) := fun _ _ => 1
  have hempty : levelSet F = ∅ := by
    ext y
    simp only [levelSet,mem_ofPred_eq,mem_empty_iff_false,iff_false]
    intro h
    have hh := congrFun h 0
    norm_num [F] at hh
  have hF : IsCompactRegularLevel F := by
    refine ⟨contDiff_const,?_,?_⟩
    · rw [hempty]
      exact isCompact_empty
    · intro y hy
      rw [hempty] at hy
      exact hy.elim
  obtain ⟨ψ,hψ,h0,hbij,hflow,_⟩ :=
    FlowCalculus.compact_supported_flow_preserves_regular_level F hF X hX hsupp (by
      intro t ht y hy
      rw [hempty] at hy
      exact hy.elim)
  exact ⟨ψ,hψ,h0,hbij,hflow⟩

lemma ambient_flow_fixes (X ψ : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0)
    (h0 : ∀ y, ψ 0 y = y)
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t)
    (y : V) (hy : ∀ t, X t y = 0) : ∀ t, ψ t y = y := by
  have hp : (fun s => ψ s y) 0 = y ∧
      ∀ t, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t := ⟨h0 y,fun t => hflow t y⟩
  have hc : (fun _ : ℝ => y) 0 = y ∧
      ∀ t, HasDerivAt (fun _ : ℝ => y) (X t y) t := by
    refine ⟨rfl,?_⟩
    intro t
    rw [hy t]
    exact hasDerivAt_const t y
  have he : (fun s => ψ s y) = fun _ => y :=
    (FlowCalculus.exists_unique_global_trajectory_of_compact_support X hX hsupp 0 y).unique hp hc
  exact fun t => congrFun he t

theorem compact_supported_contact_deformation
    (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (hvol : ∀ p, volume A p ≠ 0)
    (K : Set V) (hK : IsCompact K)
    (hstationary : ∀ t y, y ∉ K → velocity A (t,y) = 0) :
    ∃ ψ ρ : ℝ → V → V, ∃ lam : ℝ → V → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧
      (∀ t y, ρ t (ψ t y) = y) ∧ (∀ t y, ψ t (ρ t y) = y) ∧
      (∀ t y, y ∉ K → ψ t y = y) ∧
      (∀ y, (∀ s, velocity A (s,y) = 0) → ∀ t, ψ t y = y) ∧
      (∀ t y, 0 < lam t y) ∧
      (∀ t y, Injective (fderiv ℝ (ψ t) y)) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ y v,
        pullback (ψ t) (form A t) y v = lam t y*form A 0 y v := by
  let X : ℝ → V → V := fun t y => moser A (t,y)
  have hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2) := moser_contDiff A hA hvol
  have hsupp : ∃ C : Set V, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0 := by
    refine ⟨K,hK,?_⟩
    intro t y hy
    simp [X,moser,hstationary t y hy,cross]
  obtain ⟨ψ,hψ,h0,hbij,hflow⟩ := exists_ambient_flow X hX hsupp
  obtain ⟨ρ,hρ,hρψ,hψρ⟩ := smooth_joint_flow_inverse X ψ hX hψ h0 hbij hflow
  let q : ℝ → V → ℝ := fun t y => rate A (t,ψ t y)
  have hq : ContDiff ℝ ∞ (fun p : ℝ × V => q p.1 p.2) :=
    (rate_contDiff A hA hvol).comp (contDiff_fst.prodMk hψ)
  obtain ⟨lam,hlam,hlam0,hpos,htransport⟩ :=
    ParameterizedCalculus.smooth_scalar_linear_transport q hq
  have hfix : ∀ y, (∀ s, velocity A (s,y) = 0) → ∀ t, ψ t y = y := by
    intro y hy
    apply ambient_flow_fixes X ψ hX hsupp h0 hflow y
    intro t
    simp [X,moser,hy t,cross]
  refine ⟨ψ,ρ,lam,hψ,hρ,hlam,h0,hρψ,hψρ,?_,hfix,hpos,?_,?_⟩
  · intro t y hy
    exact hfix y (fun s => hstationary s y hy) t
  · exact FlowCalculus.smooth_flow_spatial_derivative_injective X ψ hX hψ h0 hflow
  · intro t ht y v
    have hform : IsSmoothFamily (form A) := covector.contDiff.comp hA
    have hf : ∀ s ∈ Icc (0:ℝ) 1,
        HasDerivAt (fun r => pullback (ψ r) (form A r) y v)
          (q s y*pullback (ψ s) (form A s) y v) s := by
      intro s hs
      have hd := GrayStability.pullback_family_hasDerivAt (form A) hform X hX ψ hψ h0 hbij hflow s y v
      have he := moser_lie_equation A hA hvol s (ψ s y) (fderiv ℝ (ψ s) y v)
      change formTimeDeriv (form A) s (ψ s y) (fderiv ℝ (ψ s) y v)+
        lieDerivOneForm (X s) (form A s) (ψ s y) (fderiv ℝ (ψ s) y v) = _ at he
      rw [he] at hd
      exact hd
    have hinit : pullback (ψ 0) (form A 0) y v = form A 0 y v := by
      have hid : ψ 0 = id := funext h0
      simp [pullback,hid]
    simpa only [hinit] using htransport y (fun r => pullback (ψ r) (form A r) y v) hf t ht


lemma dot_self_pos (v : V) (hv : v ≠ 0) : 0 < dot v v := by
  have hn : 0 ≤ dot v v := by
    dsimp [dot]
    nlinarith [sq_nonneg (v 0),sq_nonneg (v 1),sq_nonneg (v 2)]
  by_contra h
  have hz : dot v v = 0 := le_antisymm (not_lt.mp h) hn
  dsimp [dot] at hz
  have h₀ : v 0 = 0 := by nlinarith [sq_nonneg (v 1),sq_nonneg (v 2)]
  have h₁ : v 1 = 0 := by nlinarith [sq_nonneg (v 0),sq_nonneg (v 2)]
  have h₂ : v 2 = 0 := by nlinarith [sq_nonneg (v 0),sq_nonneg (v 1)]
  apply hv
  ext i
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂

lemma contact_nondegenerate (a c u : V) (hvol : dot a c ≠ 0)
    (hu : dot a u = 0) (hne : u ≠ 0) :
    ∃ v : V, dot a v = 0 ∧ dot c (cross u v) ≠ 0 := by
  refine ⟨cross a u,?_,?_⟩
  · simp [dot,cross]
    ring
  · have he : dot c (cross u (cross a u)) = dot a c*dot u u-dot c u*dot a u := by
      simp [dot,cross]
      ring
    rw [he,hu,mul_zero,sub_zero]
    exact mul_ne_zero hvol (dot_self_pos u hne).ne'

lemma form_is_contact (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (hvol : ∀ p, volume A p ≠ 0) (t : ℝ) (y : V) :
    IsContactFormAt (fun _ : V => (0 : Fin 0 → ℝ)) (form A t) y := by
  have htan : ∀ v : V, v ∈ tangentSpace (fun _ : V => (0 : Fin 0 → ℝ)) y := by
    intro v
    simp [tangentSpace]
  refine ⟨⟨curl A (t,y),htan _,?_⟩,?_⟩
  · exact hvol (t,y)
  · intro u hu hne
    obtain ⟨v,hv,hb⟩ := contact_nondegenerate (A (t,y)) (curl A (t,y)) u (hvol (t,y)) hu.2 hne
    refine ⟨v,⟨htan v,hv⟩,?_⟩
    dsimp [extDerivOneForm]
    rw [form_fderiv A hA,form_fderiv A hA,exterior_cross]
    exact hb

/-- Flattened interpolation, constant outside the unit time interval. -/
def blend (a₀ a₁ : V → V) (p : ℝ × V) : V :=
  (1-Real.smoothTransition p.1) • a₀ p.2+Real.smoothTransition p.1 • a₁ p.2

lemma blend_contDiff (a₀ a₁ : V → V) (h₀ : ContDiff ℝ ∞ a₀) (h₁ : ContDiff ℝ ∞ a₁) :
    ContDiff ℝ ∞ (blend a₀ a₁) := by
  have hs : ContDiff ℝ ∞ (fun p : ℝ × V => Real.smoothTransition p.1) :=
    Real.smoothTransition.contDiff.comp contDiff_fst
  exact (contDiff_const.sub hs).smul (h₀.comp contDiff_snd) |>.add (hs.smul (h₁.comp contDiff_snd))

lemma curlLinear_combo (D₀ D₁ : V →L[ℝ] V) (r s : ℝ) :
    curlLinear (r • D₀+s • D₁) = r • curlLinear D₀+s • curlLinear D₁ := by
  ext i
  fin_cases i <;> simp [curlLinear] <;> ring

lemma blend_curl (a₀ a₁ : V → V) (h₀ : ContDiff ℝ ∞ a₀) (h₁ : ContDiff ℝ ∞ a₁)
    (t : ℝ) (y : V) :
    curl (blend a₀ a₁) (t,y) =
      (1-Real.smoothTransition t) • curlLinear (fderiv ℝ a₀ y)+
        Real.smoothTransition t • curlLinear (fderiv ℝ a₁ y) := by
  have hd := ((h₀.differentiable (by simp) y).hasFDerivAt.const_smul (1-Real.smoothTransition t)).add
    ((h₁.differentiable (by simp) y).hasFDerivAt.const_smul (Real.smoothTransition t))
  change HasFDerivAt (fun z => blend a₀ a₁ (t,z)) _ y at hd
  rw [curl,← spatialD_eq _ (blend_contDiff a₀ a₁ h₀ h₁),hd.fderiv,curlLinear_combo]

lemma dot_blend (a₀ a₁ c₀ c₁ : V) (s : ℝ) :
    dot ((1-s) • a₀+s • a₁) ((1-s) • c₀+s • c₁) =
      (1-s)*dot a₀ c₀+s*dot a₁ c₁-s*(1-s)*dot (a₁-a₀) (c₁-c₀) := by
  simp [dot]
  ring

lemma blend_volume_positive (a₀ a₁ : V → V) (h₀ : ContDiff ℝ ∞ a₀) (h₁ : ContDiff ℝ ∞ a₁)
    (hpos₀ : ∀ y, 0 < dot (a₀ y) (curlLinear (fderiv ℝ a₀ y)))
    (hpos₁ : ∀ y, 0 < dot (a₁ y) (curlLinear (fderiv ℝ a₁ y)))
    (hnull : ∀ y, dot (a₁ y-a₀ y)
      (curlLinear (fderiv ℝ a₁ y)-curlLinear (fderiv ℝ a₀ y)) = 0) :
    ∀ p, 0 < volume (blend a₀ a₁) p := by
  rintro ⟨t,y⟩
  rw [volume,blend_curl a₀ a₁ h₀ h₁]
  change 0 < dot ((1-Real.smoothTransition t) • a₀ y+Real.smoothTransition t • a₁ y) _
  rw [dot_blend,hnull,mul_zero,sub_zero]
  have hs₀ := Real.smoothTransition.nonneg t
  have hs₁ := Real.smoothTransition.le_one t
  have ha := hpos₀ y
  have hb := hpos₁ y
  by_cases hz : Real.smoothTransition t = 0
  · simpa [hz] using ha
  · have hp : 0 < Real.smoothTransition t := lt_of_le_of_ne hs₀ (Ne.symm hz)
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hs₁) ha.le) (mul_pos hp hb)

lemma velocity_zero_of_constant (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (y : V) (hconst : ∀ t, A (t,y) = A (0,y)) : ∀ t, velocity A (t,y) = 0 := by
  intro t
  have hd := (hA.differentiable (by simp) (t,y)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  change HasDerivAt (fun s => A (s,y)) (velocity A (t,y)) t at hd
  have he : (fun s => A (s,y)) = fun _ => A (0,y) := funext hconst
  rw [he] at hd
  exact hd.unique (hasDerivAt_const t (A (0,y)))

lemma blend_stationary (a₀ a₁ : V → V) (h₀ : ContDiff ℝ ∞ a₀) (h₁ : ContDiff ℝ ∞ a₁)
    (y : V) (hy : a₁ y = a₀ y) : ∀ t, velocity (blend a₀ a₁) (t,y) = 0 := by
  apply velocity_zero_of_constant _ (blend_contDiff a₀ a₁ h₀ h₁) y
  intro t
  simp only [blend,hy]
  ext i
  simp
  ring

theorem relative_integrable_contact_interpolation
    (a₀ a₁ : V → V) (h₀ : ContDiff ℝ ∞ a₀) (h₁ : ContDiff ℝ ∞ a₁)
    (hpos₀ : ∀ y, 0 < dot (a₀ y) (curlLinear (fderiv ℝ a₀ y)))
    (hpos₁ : ∀ y, 0 < dot (a₁ y) (curlLinear (fderiv ℝ a₁ y)))
    (hnull : ∀ y, dot (a₁ y-a₀ y)
      (curlLinear (fderiv ℝ a₁ y)-curlLinear (fderiv ℝ a₀ y)) = 0)
    (K : Set V) (hK : IsCompact K) (heq : ∀ y, y ∉ K → a₁ y = a₀ y) :
    ∃ ψ ρ : ℝ → V → V, ∃ lam : ℝ → V → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧
      (∀ t y, ρ t (ψ t y) = y) ∧ (∀ t y, ψ t (ρ t y) = y) ∧
      (∀ t y, y ∉ K → ψ t y = y) ∧
      (∀ y, a₁ y = a₀ y → ∀ t, ψ t y = y) ∧
      (∀ t y, 0 < lam t y) ∧
      (∀ t y, Injective (fderiv ℝ (ψ t) y)) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y v,
        dot (blend a₀ a₁ (t,ψ t y)) (fderiv ℝ (ψ t) y v) = lam t y*dot (a₀ y) v) ∧
      ∀ y v, dot (a₁ (ψ 1 y)) (fderiv ℝ (ψ 1) y v) = lam 1 y*dot (a₀ y) v := by
  have hA := blend_contDiff a₀ a₁ h₀ h₁
  have hvol : ∀ p, volume (blend a₀ a₁) p ≠ 0 :=
    fun p => (blend_volume_positive a₀ a₁ h₀ h₁ hpos₀ hpos₁ hnull p).ne'
  obtain ⟨ψ,ρ,lam,hψ,hρ,hlam,hinit,hρψ,hψρ,hfix,hstat,hpos,hinj,hpb⟩ :=
    compact_supported_contact_deformation (blend a₀ a₁) hA hvol K hK (by
      intro t y hy
      exact blend_stationary a₀ a₁ h₀ h₁ y (heq y hy) t)
  have hstart : ∀ y, blend a₀ a₁ (0,y) = a₀ y := by intro y; simp [blend]
  have hend : ∀ y, blend a₀ a₁ (1,y) = a₁ y := by intro y; simp [blend]
  have hp : ∀ t ∈ Icc (0:ℝ) 1, ∀ y v,
      dot (blend a₀ a₁ (t,ψ t y)) (fderiv ℝ (ψ t) y v) = lam t y*dot (a₀ y) v := by
    intro t ht y v
    simpa only [pullback,form,covector_apply,hstart] using hpb t ht y v
  refine ⟨ψ,ρ,lam,hψ,hρ,hlam,hinit,hρψ,hψρ,hfix,?_,hpos,hinj,hp,?_⟩
  · intro y hy
    exact hstat y (blend_stationary a₀ a₁ h₀ h₁ y hy)
  · intro y v
    simpa only [hend] using hp 1 (by simp) y v


abbrev P := Fin 2 → ℝ

/-- A horizontal one-form with a cutoff in the normal coordinate. -/
def horizontalTaper (b : P → P) (χ : ℝ → ℝ) (y : V) : V :=
  ![χ (y 2)*b ![y 0,y 1] 0,χ (y 2)*b ![y 0,y 1] 1,0]

lemma horizontalTaper_contDiff (b : P → P) (χ : ℝ → ℝ)
    (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (horizontalTaper b χ) := by
  have hx : ContDiff ℝ ∞ (fun y : V => (![y 0,y 1] : P)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  have hbc := hb.comp hx
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [horizontalTaper] <;> fun_prop

lemma horizontalTaper_integrable (b : P → P) (χ : ℝ → ℝ)
    (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ) (y : V) :
    dot (horizontalTaper b χ y) (curlLinear (fderiv ℝ (horizontalTaper b χ) y)) = 0 := by
  let d := horizontalTaper b χ
  have hd : Differentiable ℝ d := (horizontalTaper_contDiff b χ hb hχ).differentiable (by simp)
  have hlast : ∀ v, fderiv ℝ d y v 2 = 0 := by
    intro v
    have hh := (ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ).hasFDerivAt.comp y (hd y).hasFDerivAt
    have he : (fun z : V => d z 2) = fun _ => (0:ℝ) := rfl
    change HasFDerivAt (fun z : V => d z 2) _ y at hh
    have hf := hh.fderiv
    rw [he] at hf
    have hv := congrArg (fun L : V →L[ℝ] ℝ => L v) hf
    simpa using hv.symm
  let c : ℝ → V := fun s => ![y 0,y 1,s]
  have hc : HasDerivAt c (Pi.single 2 1) (y 2) := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [c] using hasDerivAt_const (y 2) (y 0)
    · simpa [c] using hasDerivAt_const (y 2) (y 1)
    · convert! (hasDerivAt_id (𝕜 := ℝ) (y 2)) using 1
  have hcy : c (y 2) = y := by ext i; fin_cases i <;> rfl
  have hleft := (hd (c (y 2))).hasFDerivAt.comp_hasDerivAt (y 2) hc
  rw [hcy] at hleft
  have heq : (d ∘ c) = fun s => χ s • (![b ![y 0,y 1] 0,b ![y 0,y 1] 1,0] : V) := by
    ext s i
    fin_cases i <;> simp [d,horizontalTaper,c]
  have hright := (hχ.differentiable (by simp) (y 2)).hasDerivAt.smul_const
    (![b ![y 0,y 1] 0,b ![y 0,y 1] 1,0] : V)
  rw [← heq] at hright
  have hz := hleft.unique hright
  dsimp [dot,curlLinear]
  rw [hlast,hlast,hz]
  simp [horizontalTaper]
  ring

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function GrayStability
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- A compactly supported smooth flow preserves a vertical fibre whenever its
vector field is vertical on that fibre. The fibre itself need not be compact. -/
lemma flow_preserves_vertical_fibre (X ψ : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0)
    (h0 : ∀ y, ψ 0 y = y)
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t)
    (y : V) (hvertical : ∀ t z, X t ![y 0,y 1,z] 0 = 0 ∧ X t ![y 0,y 1,z] 1 = 0) :
    ∀ t, ψ t y 0 = y 0 ∧ ψ t y 1 = y 1 := by
  let Z : ℝ → ℝ → ℝ := fun t z => X t ![y 0,y 1,z] 2
  have hchart : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1,(![y 0,y 1,p.2] : V))) := by
    apply contDiff_fst.prodMk
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  have hZ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Z p.1 p.2) :=
    (contDiff_apply ℝ ℝ 2).comp (hX.comp hchart)
  obtain ⟨K,hK,hKX⟩ := hsupp
  have hZsupp : ∃ C : Set ℝ, IsCompact C ∧ ∀ t z, z ∉ C → Z t z = 0 := by
    refine ⟨(fun v : V => v 2) '' K,hK.image (continuous_apply 2),?_⟩
    intro t z hz
    have hn : (![y 0,y 1,z] : V) ∉ K := by
      intro h
      exact hz ⟨![y 0,y 1,z],h,rfl⟩
    have he := congrFun (hKX t ![y 0,y 1,z] hn) 2
    exact he
  obtain ⟨γ,hγ,_⟩ := FlowCalculus.exists_unique_global_trajectory_of_compact_support Z hZ hZsupp 0 (y 2)
  let c : ℝ → V := fun t => ![y 0,y 1,γ t]
  have hc0 : c 0 = y := by
    ext i
    fin_cases i <;> simp [c,hγ.1]
  have hc : ∀ t, HasDerivAt c (X t (c t)) t := by
    intro t
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [c,(hvertical t (γ t)).1] using hasDerivAt_const t (y 0)
    · simpa [c,(hvertical t (γ t)).2] using hasDerivAt_const t (y 1)
    · exact hγ.2 t
  have he : (fun t => ψ t y) = c :=
    (FlowCalculus.exists_unique_global_trajectory_of_compact_support X hX ⟨K,hK,hKX⟩ 0 y).unique
      ⟨h0 y,fun t => hflow t y⟩ ⟨hc0,hc⟩
  intro t
  have ht := congrFun he t
  exact ⟨congrFun ht 0,congrFun ht 1⟩

lemma moser_vertical_on_zero_fibre (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (y : V) (hzero : ∀ t z, A (t,![y 0,y 1,z]) 2 = 0) :
    ∀ t z, moser A (t,![y 0,y 1,z]) 0 = 0 ∧ moser A (t,![y 0,y 1,z]) 1 = 0 := by
  intro t z
  have hv : velocity A (t,![y 0,y 1,z]) 2 = 0 := by
    have hd := (hA.differentiable (by simp) (t,![y 0,y 1,z])).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t (![y 0,y 1,z] : V)))
    have hs := (ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hd
    change HasDerivAt (fun s => A (s,![y 0,y 1,z]) 2) (velocity A (t,![y 0,y 1,z]) 2) t at hs
    have he : (fun s => A (s,![y 0,y 1,z]) 2) = fun _ => 0 := funext fun s => hzero s z
    rw [he] at hs
    exact hs.unique (hasDerivAt_const t (0:ℝ))
  constructor <;> simp [moser,cross,hzero,hv]

lemma moser_flow_preserves_zero_fibre (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (hvol : ∀ p, volume A p ≠ 0) (ψ : ℝ → V → V)
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → moser A (t,y) = 0)
    (h0 : ∀ y, ψ 0 y = y)
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (moser A (t,ψ t y)) t)
    (y : V) (hzero : ∀ t z, A (t,![y 0,y 1,z]) 2 = 0) :
    ∀ t, ψ t y 0 = y 0 ∧ ψ t y 1 = y 1 :=
  flow_preserves_vertical_fibre (fun t y => moser A (t,y)) ψ (moser_contDiff A hA hvol)
    hsupp h0 hflow y (moser_vertical_on_zero_fibre A hA y hzero)

/-- The same fibre is mapped onto itself, not just into itself. Completeness
of the scalar normal equation gives a preimage for every point of the fibre. -/
lemma flow_surjective_on_vertical_fibre (X ψ : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0)
    (h0 : ∀ y, ψ 0 y = y)
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t)
    (y : V) (hvertical : ∀ t z, X t ![y 0,y 1,z] 0 = 0 ∧ X t ![y 0,y 1,z] 1 = 0)
    (t : ℝ) : ∃ v : V, v 0 = y 0 ∧ v 1 = y 1 ∧ ψ t v = y := by
  let Z : ℝ → ℝ → ℝ := fun s z => X s ![y 0,y 1,z] 2
  have hchart : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1,(![y 0,y 1,p.2] : V))) := by
    apply contDiff_fst.prodMk
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  have hZ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Z p.1 p.2) :=
    (contDiff_apply ℝ ℝ 2).comp (hX.comp hchart)
  obtain ⟨K,hK,hKX⟩ := hsupp
  have hZsupp : ∃ C : Set ℝ, IsCompact C ∧ ∀ s z, z ∉ C → Z s z = 0 := by
    refine ⟨(fun v : V => v 2) '' K,hK.image (continuous_apply 2),?_⟩
    intro s z hz
    have hn : (![y 0,y 1,z] : V) ∉ K := by
      intro h
      exact hz ⟨![y 0,y 1,z],h,rfl⟩
    exact congrFun (hKX s ![y 0,y 1,z] hn) 2
  obtain ⟨γ,hγ,_⟩ := FlowCalculus.exists_unique_global_trajectory_of_compact_support Z hZ hZsupp t (y 2)
  let c : ℝ → V := fun s => ![y 0,y 1,γ s]
  have hct : c t = y := by
    ext i
    fin_cases i <;> simp [c,hγ.1]
  have hc : ∀ s, HasDerivAt c (X s (c s)) s := by
    intro s
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [c,(hvertical s (γ s)).1] using hasDerivAt_const s (y 0)
    · simpa [c,(hvertical s (γ s)).2] using hasDerivAt_const s (y 1)
    · exact hγ.2 s
  have he : (fun s => ψ s (c 0)) = c :=
    (FlowCalculus.exists_unique_global_trajectory_of_compact_support X hX ⟨K,hK,hKX⟩ 0 (c 0)).unique
      ⟨h0 (c 0),fun s => hflow s (c 0)⟩ ⟨rfl,hc⟩
  exact ⟨c 0,rfl,rfl,(congrFun he t).trans hct⟩

/-- Both directions of transport preserve the zero dividing cylinder for a
common normal coefficient u(x,y), including at its singular zero points. -/
theorem moser_flow_preserves_dividing_cylinder
    (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A) (hvol : ∀ p, volume A p ≠ 0)
    (u : P → ℝ) (hnormal : ∀ t y, A (t,y) 2 = u ![y 0,y 1])
    (ψ ρ : ℝ → V → V)
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → moser A (t,y) = 0)
    (h0 : ∀ y, ψ 0 y = y)
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (moser A (t,ψ t y)) t)
    (hρψ : ∀ t y, ρ t (ψ t y) = y) :
    ∀ t y, u ![y 0,y 1] = 0 →
      (ψ t y 0 = y 0 ∧ ψ t y 1 = y 1) ∧
      (ρ t y 0 = y 0 ∧ ρ t y 1 = y 1) := by
  intro t y hy
  have hz : ∀ s z, A (s,![y 0,y 1,z]) 2 = 0 := by
    intro s z
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one] using (hnormal s ![y 0,y 1,z]).trans hy
  have hv := moser_vertical_on_zero_fibre A hA y hz
  have hforward := flow_preserves_vertical_fibre (fun s v => moser A (s,v)) ψ
    (moser_contDiff A hA hvol) hsupp h0 hflow y hv t
  obtain ⟨v,hv₀,hv₁,hvψ⟩ := flow_surjective_on_vertical_fibre (fun s v => moser A (s,v)) ψ
    (moser_contDiff A hA hvol) hsupp h0 hflow y hv t
  have hr : ρ t y = v := by rw [← hvψ,hρψ]
  exact ⟨hforward,by simpa only [hr] using And.intro hv₀ hv₁⟩

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def cutoffBase (z : ℝ) : ℝ := Real.smoothTransition (z+2)*Real.smoothTransition (2-z)

lemma cutoffBase_contDiff : ContDiff ℝ ∞ cutoffBase := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  exact (hs.comp (contDiff_id.add contDiff_const)).mul
    (hs.comp (contDiff_const.sub contDiff_id))

lemma cutoffBase_bounds (z : ℝ) : 0 ≤ cutoffBase z ∧ cutoffBase z ≤ 1 := by
  have h₀ := Real.smoothTransition.nonneg (z+2)
  have h₁ := Real.smoothTransition.le_one (z+2)
  have h₂ := Real.smoothTransition.nonneg (2-z)
  have h₃ := Real.smoothTransition.le_one (2-z)
  exact ⟨mul_nonneg h₀ h₂,by dsimp [cutoffBase]; nlinarith [mul_nonneg (sub_nonneg.mpr h₁) h₂]⟩

lemma cutoffBase_one (z : ℝ) (hz : |z| ≤ 1) : cutoffBase z = 1 := by
  have hl := (abs_le.mp hz).1
  have hr := (abs_le.mp hz).2
  simp [cutoffBase,Real.smoothTransition.one_of_one_le (show 1 ≤ z+2 by linarith),
    Real.smoothTransition.one_of_one_le (show 1 ≤ 2-z by linarith)]

lemma cutoffBase_zero (z : ℝ) (hz : 2 ≤ |z|) : cutoffBase z = 0 := by
  rcases (le_abs.mp hz) with hl | hr
  · simp [cutoffBase,Real.smoothTransition.zero_of_nonpos (show 2-z ≤ 0 by linarith)]
  · simp [cutoffBase,Real.smoothTransition.zero_of_nonpos (show z+2 ≤ 0 by linarith)]

lemma cutoffBase_compact : HasCompactSupport cutoffBase := by
  apply HasCompactSupport.intro' (K := Icc (-2:ℝ) 2) isCompact_Icc isClosed_Icc
  intro z hz
  apply cutoffBase_zero
  by_contra h
  have ha := abs_lt.mp (not_le.mp h)
  exact hz ⟨by linarith [ha.1],by linarith [ha.2]⟩

lemma exists_slow_cutoff (ε : ℝ) (hε : 0 < ε) :
    ∃ χ : ℝ → ℝ, ∃ L : ℝ,
      ContDiff ℝ ∞ χ ∧ 1 ≤ L ∧ HasCompactSupport χ ∧
      (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
      (∀ z, |z| ≤ 1 → χ z = 1) ∧
      (∀ z, 2*L ≤ |z| → χ z = 0) ∧
      ∀ z, |deriv χ z| < ε := by
  obtain ⟨B,hB⟩ := (cutoffBase_contDiff.continuous_deriv (by simp)).abs.bddAbove_range_of_hasCompactSupport
    cutoffBase_compact.deriv.abs
  let L : ℝ := (|B|+1)/ε+1
  have hL₁ : 1 ≤ L := by
    dsimp [L]
    have hp : 0 ≤ (|B|+1)/ε := div_nonneg (by positivity) hε.le
    linarith
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL₁
  have hBL : B < ε*L := by
    dsimp [L]
    have hm : ε*((|B|+1)/ε) = |B|+1 := by field_simp
    nlinarith [le_abs_self B]
  let χ : ℝ → ℝ := fun z => cutoffBase (z/L)
  have hχ : ContDiff ℝ ∞ χ := cutoffBase_contDiff.comp (contDiff_id.div_const L)
  have hzero : ∀ z, 2*L ≤ |z| → χ z = 0 := by
    intro z hz
    apply cutoffBase_zero
    rw [abs_div,abs_of_pos hL]
    exact (le_div_iff₀ hL).mpr (by linarith)
  have hcompact : HasCompactSupport χ := by
    apply HasCompactSupport.intro' (K := Icc (-2*L) (2*L)) isCompact_Icc isClosed_Icc
    intro z hz
    apply hzero
    by_contra h
    have ha := abs_lt.mp (not_le.mp h)
    exact hz ⟨by linarith [ha.1],by linarith [ha.2]⟩
  refine ⟨χ,L,hχ,hL₁,hcompact,fun z => cutoffBase_bounds (z/L),?_,hzero,?_⟩
  · intro z hz
    apply cutoffBase_one
    rw [abs_div,abs_of_pos hL]
    exact (div_le_iff₀ hL).mpr (by linarith)
  · intro z
    have hd := (cutoffBase_contDiff.differentiable (by simp) (z/L)).hasDerivAt.comp z
      ((hasDerivAt_id z).div_const L)
    change HasDerivAt χ _ z at hd
    rw [hd.deriv]
    change |deriv cutoffBase (z/L)*(1/L)| < ε
    rw [abs_mul,abs_div,abs_one,abs_of_pos hL]
    have hb : |deriv cutoffBase (z/L)| ≤ B := hB ⟨z/L,rfl⟩
    have he : |deriv cutoffBase (z/L)|/L < ε := (div_lt_iff₀ hL).mpr (by nlinarith)
    simpa [div_eq_mul_inv] using he

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def xyMap : V →L[ℝ] P := ContinuousLinearMap.pi
  ![(ContinuousLinearMap.proj 0 : V →L[ℝ] ℝ),ContinuousLinearMap.proj 1]

@[simp] lemma xyMap_apply (y : V) : xyMap y = ![y 0,y 1] := by ext i; fin_cases i <;> simp [xyMap]
@[simp] lemma xyMap_e0 : xyMap (Pi.single 0 1) = Pi.single 0 1 := by ext i; fin_cases i <;> simp [xyMap]
@[simp] lemma xyMap_e1 : xyMap (Pi.single 1 1) = Pi.single 1 1 := by ext i; fin_cases i <;> simp [xyMap]
@[simp] lemma xyMap_e2 : xyMap (Pi.single 2 1) = 0 := by ext i; fin_cases i <;> simp [xyMap]

def invariantCoefficients (u : P → ℝ) (β : P → P) (y : V) : V :=
  ![β (xyMap y) 0,β (xyMap y) 1,u (xyMap y)]

def collarCoefficients (u : P → ℝ) (β₀ β₁ : P → P) (χ : ℝ → ℝ) (y : V) : V :=
  ![β₀ (xyMap y) 0+χ (y 2)*(β₁ (xyMap y) 0-β₀ (xyMap y) 0),
    β₀ (xyMap y) 1+χ (y 2)*(β₁ (xyMap y) 1-β₀ (xyMap y) 1),u (xyMap y)]

def invariantVolume (u : P → ℝ) (β : P → P) (x : P) : ℝ :=
  β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
    u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)

def cutoffError (β₀ β₁ : P → P) (x : P) : ℝ :=
  β₀ x 1*(β₁ x 0-β₀ x 0)-β₀ x 0*(β₁ x 1-β₀ x 1)

lemma invariantCoefficients_contDiff (u : P → ℝ) (β : P → P)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) : ContDiff ℝ ∞ (invariantCoefficients u β) := by
  have huc := hu.comp xyMap.contDiff
  have hβc := hβ.comp xyMap.contDiff
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [invariantCoefficients] <;> fun_prop

lemma collarCoefficients_contDiff (u : P → ℝ) (β₀ β₁ : P → P) (χ : ℝ → ℝ)
    (hu : ContDiff ℝ ∞ u) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁)
    (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (collarCoefficients u β₀ β₁ χ) := by
  have huc := hu.comp xyMap.contDiff
  have hβc₀ := h₀.comp xyMap.contDiff
  have hβc₁ := h₁.comp xyMap.contDiff
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [collarCoefficients] <;> fun_prop

lemma invariantVolume_contDiff (u : P → ℝ) (β : P → P)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) : ContDiff ℝ ∞ (invariantVolume u β) := by
  have hdu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hdβ : ContDiff ℝ ∞ (fderiv ℝ β) := hβ.fderiv_right (by simp)
  unfold invariantVolume
  fun_prop

lemma cutoffError_contDiff (β₀ β₁ : P → P) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁) :
    ContDiff ℝ ∞ (cutoffError β₀ β₁) := by unfold cutoffError; fun_prop

lemma collarCoefficients_fderiv (u : P → ℝ) (β₀ β₁ : P → P) (χ : ℝ → ℝ)
    (hu : ContDiff ℝ ∞ u) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁)
    (hχ : ContDiff ℝ ∞ χ) (y v : V) :
    fderiv ℝ (collarCoefficients u β₀ β₁ χ) y v =
      ![fderiv ℝ β₀ (xyMap y) (xyMap v) 0+
          (deriv χ (y 2)*v 2)*(β₁ (xyMap y) 0-β₀ (xyMap y) 0)+
          χ (y 2)*(fderiv ℝ β₁ (xyMap y) (xyMap v) 0-fderiv ℝ β₀ (xyMap y) (xyMap v) 0),
        fderiv ℝ β₀ (xyMap y) (xyMap v) 1+
          (deriv χ (y 2)*v 2)*(β₁ (xyMap y) 1-β₀ (xyMap y) 1)+
          χ (y 2)*(fderiv ℝ β₁ (xyMap y) (xyMap v) 1-fderiv ℝ β₀ (xyMap y) (xyMap v) 1),
        fderiv ℝ u (xyMap y) (xyMap v)] := by
  have hb₀ := (h₀.differentiable (by simp) (xyMap y)).hasFDerivAt.comp y xyMap.hasFDerivAt
  have hb₁ := (h₁.differentiable (by simp) (xyMap y)).hasFDerivAt.comp y xyMap.hasFDerivAt
  have hb₀₀ := (ContinuousLinearMap.proj 0 : P →L[ℝ] ℝ).hasFDerivAt.comp y hb₀
  have hb₀₁ := (ContinuousLinearMap.proj 1 : P →L[ℝ] ℝ).hasFDerivAt.comp y hb₀
  have hb₁₀ := (ContinuousLinearMap.proj 0 : P →L[ℝ] ℝ).hasFDerivAt.comp y hb₁
  have hb₁₁ := (ContinuousLinearMap.proj 1 : P →L[ℝ] ℝ).hasFDerivAt.comp y hb₁
  have hr := (hχ.differentiable (by simp) (y 2)).hasDerivAt.hasFDerivAt.comp y
    (ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ).hasFDerivAt
  have hU := (hu.differentiable (by simp) (xyMap y)).hasFDerivAt.comp y xyMap.hasFDerivAt
  have hd₀ := hb₀₀.add (hr.mul (hb₁₀.sub hb₀₀))
  have hd₁ := hb₀₁.add (hr.mul (hb₁₁.sub hb₀₁))
  let f₀ : V → ℝ := fun q => β₀ (xyMap q) 0+χ (q 2)*(β₁ (xyMap q) 0-β₀ (xyMap q) 0)
  let f₁ : V → ℝ := fun q => β₀ (xyMap q) 1+χ (q 2)*(β₁ (xyMap q) 1-β₀ (xyMap q) 1)
  change HasFDerivAt f₀ _ y at hd₀
  change HasFDerivAt f₁ _ y at hd₁
  have hD : HasFDerivAt (collarCoefficients u β₀ β₁ χ)
      (ContinuousLinearMap.pi ![fderiv ℝ f₀ y,fderiv ℝ f₁ y,
        (fderiv ℝ u (xyMap y)).comp xyMap]) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · change HasFDerivAt f₀ (fderiv ℝ f₀ y) y
      exact hd₀.differentiableAt.hasFDerivAt
    · change HasFDerivAt f₁ (fderiv ℝ f₁ y) y
      exact hd₁.differentiableAt.hasFDerivAt
    · exact hU
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp [hd₀.fderiv,hd₁.fderiv] <;> ring

lemma collar_volume_formula (u : P → ℝ) (β₀ β₁ : P → P) (χ : ℝ → ℝ)
    (hu : ContDiff ℝ ∞ u) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁)
    (hχ : ContDiff ℝ ∞ χ) (y : V) :
    dot (collarCoefficients u β₀ β₁ χ y)
      (curlLinear (fderiv ℝ (collarCoefficients u β₀ β₁ χ) y)) =
      (1-χ (y 2))*invariantVolume u β₀ (xyMap y)+χ (y 2)*invariantVolume u β₁ (xyMap y)+
        deriv χ (y 2)*cutoffError β₀ β₁ (xyMap y) := by
  dsimp [dot,curlLinear]
  rw [collarCoefficients_fderiv u β₀ β₁ χ hu h₀ h₁ hχ,
    collarCoefficients_fderiv u β₀ β₁ χ hu h₀ h₁ hχ,
    collarCoefficients_fderiv u β₀ β₁ χ hu h₀ h₁ hχ]
  simp only [xyMap_e0,xyMap_e1,xyMap_e2,map_zero]
  simp [invariantVolume,cutoffError,collarCoefficients]
  ring

lemma invariant_volume_formula (u : P → ℝ) (β : P → P)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (y : V) :
    dot (invariantCoefficients u β y) (curlLinear (fderiv ℝ (invariantCoefficients u β) y)) =
      invariantVolume u β (xyMap y) := by
  have he : collarCoefficients u β β (fun _ => 0) = invariantCoefficients u β := by
    ext q i
    fin_cases i <;> simp [collarCoefficients,invariantCoefficients]
  simpa only [he,deriv_const,mul_zero,zero_mul,add_zero,sub_zero,one_mul] using
    collar_volume_formula u β β (fun _ => 0) hu hβ hβ contDiff_const y

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function GrayStability
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma exists_positive_collar_cutoff (u : P → ℝ) (β₀ β₁ : P → P)
    (hu : ContDiff ℝ ∞ u) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁)
    (hpos₀ : ∀ x, 0 < invariantVolume u β₀ x) (hpos₁ : ∀ x, 0 < invariantVolume u β₁ x)
    (K : Set P) (hK : IsCompact K) (heq : ∀ x, x ∉ K → β₁ x = β₀ x) :
    ∃ χ : ℝ → ℝ, ∃ L : ℝ,
      ContDiff ℝ ∞ χ ∧ 1 ≤ L ∧
      (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧ (∀ z, |z| ≤ 1 → χ z = 1) ∧
      (∀ z, 2*L ≤ |z| → χ z = 0) ∧
      (∀ y, 0 < dot (collarCoefficients u β₀ β₁ χ y)
        (curlLinear (fderiv ℝ (collarCoefficients u β₀ β₁ χ) y))) ∧
      ∃ C : Set V, IsCompact C ∧
        ∀ y, y ∉ C → horizontalTaper (fun x => β₁ x-β₀ x) χ y = 0 := by
  obtain ⟨m₀,hm₀,hbound₀⟩ := hK.exists_forall_le'
    (invariantVolume_contDiff u β₀ hu h₀).continuous.continuousOn (fun x _ => hpos₀ x)
  obtain ⟨m₁,hm₁,hbound₁⟩ := hK.exists_forall_le'
    (invariantVolume_contDiff u β₁ hu h₁).continuous.continuousOn (fun x _ => hpos₁ x)
  let m : ℝ := min m₀ m₁
  have hm : 0 < m := lt_min hm₀ hm₁
  obtain ⟨B,hB⟩ := hK.bddAbove_image (cutoffError_contDiff β₀ β₁ h₀ h₁).continuous.abs.continuousOn
  let M : ℝ := |B|+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hE : ∀ x ∈ K, |cutoffError β₀ β₁ x| ≤ M := by
    intro x hx
    have hb := hB ⟨x,hx,rfl⟩
    dsimp [M]
    linarith [le_abs_self B]
  let ε : ℝ := m/(2*M)
  have hε : 0 < ε := div_pos hm (mul_pos (by norm_num) hM)
  obtain ⟨χ,L,hχ,hL,hcompact,hrange,hone,hzero,hderiv⟩ := exists_slow_cutoff ε hε
  refine ⟨χ,L,hχ,hL,hrange,hone,hzero,?_,?_⟩
  · intro y
    rw [collar_volume_formula u β₀ β₁ χ hu h₀ h₁ hχ]
    have hr₀ := (hrange (y 2)).1
    have hr₁ := (hrange (y 2)).2
    by_cases hx : xyMap y ∈ K
    · have ha : m ≤ invariantVolume u β₀ (xyMap y) :=
        (min_le_left _ _).trans (hbound₀ _ hx)
      have hb : m ≤ invariantVolume u β₁ (xyMap y) :=
        (min_le_right _ _).trans (hbound₁ _ hx)
      have hbase : m ≤ (1-χ (y 2))*invariantVolume u β₀ (xyMap y)+
          χ (y 2)*invariantVolume u β₁ (xyMap y) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hr₁) (sub_nonneg.mpr ha),
          mul_nonneg hr₀ (sub_nonneg.mpr hb)]
      have herr : |deriv χ (y 2)*cutoffError β₀ β₁ (xyMap y)| < ε*M := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (hE _ hx) (abs_nonneg _)).trans_lt
          (mul_lt_mul_of_pos_right (hderiv _) hM)
      have hEM : ε*M = m/2 := by dsimp [ε]; field_simp
      rw [hEM] at herr
      linarith [(abs_lt.mp herr).1]
    · have hz : cutoffError β₀ β₁ (xyMap y) = 0 := by
        dsimp only [cutoffError]
        rw [heq _ hx]
        ring
      rw [hz,mul_zero,add_zero]
      have ha := hpos₀ (xyMap y)
      have hb := hpos₁ (xyMap y)
      by_cases hr : χ (y 2) = 0
      · simpa [hr] using ha
      · have hp : 0 < χ (y 2) := lt_of_le_of_ne hr₀ (Ne.symm hr)
        exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hr₁) ha.le) (mul_pos hp hb)
  · let join : P × ℝ → V := fun q => ![q.1 0,q.1 1,q.2]
    have hjoin : Continuous join := by
      apply continuous_pi
      intro i
      fin_cases i <;> dsimp [join] <;> fun_prop
    refine ⟨join '' (K ×ˢ Icc (-2*L) (2*L)),(hK.prod isCompact_Icc).image hjoin,?_⟩
    intro y hy
    by_cases hx : xyMap y ∈ K
    · have hz : 2*L ≤ |y 2| := by
        by_contra hn
        have ha := abs_lt.mp (not_le.mp hn)
        apply hy
        refine ⟨(xyMap y,y 2),⟨hx,by constructor <;> linarith [ha.1,ha.2]⟩,?_⟩
        ext i
        fin_cases i <;> simp [join]
      simp [horizontalTaper,hzero _ hz]
    · have hh := heq _ hx
      rw [xyMap_apply] at hh
      simp [horizontalTaper,hh]

lemma given_moser_flow_pullback (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (hvol : ∀ p, volume A p ≠ 0) (ψ : ℝ → V → V)
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y) (hbij : ∀ t, Bijective (ψ t))
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (moser A (t,ψ t y)) t) :
    ∃ lam : ℝ → V → ℝ, ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) ∧
      (∀ t y, 0 < lam t y) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ y v,
        pullback (ψ t) (form A t) y v = lam t y*form A 0 y v := by
  let X : ℝ → V → V := fun t y => moser A (t,y)
  have hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2) := moser_contDiff A hA hvol
  let q : ℝ → V → ℝ := fun t y => rate A (t,ψ t y)
  have hq : ContDiff ℝ ∞ (fun p : ℝ × V => q p.1 p.2) :=
    (rate_contDiff A hA hvol).comp (contDiff_fst.prodMk hψ)
  obtain ⟨lam,hlam,_,hpos,htransport⟩ := ParameterizedCalculus.smooth_scalar_linear_transport q hq
  refine ⟨lam,hlam,hpos,?_⟩
  intro t ht y v
  have hform : IsSmoothFamily (form A) := covector.contDiff.comp hA
  have hf : ∀ s ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun r => pullback (ψ r) (form A r) y v)
        (q s y*pullback (ψ s) (form A s) y v) s := by
    intro s hs
    have hd := GrayStability.pullback_family_hasDerivAt (form A) hform X hX ψ hψ h0 hbij hflow s y v
    have he := moser_lie_equation A hA hvol s (ψ s y) (fderiv ℝ (ψ s) y v)
    change formTimeDeriv (form A) s (ψ s y) (fderiv ℝ (ψ s) y v)+
      lieDerivOneForm (X s) (form A s) (ψ s y) (fderiv ℝ (ψ s) y v) = _ at he
    rw [he] at hd
    exact hd
  have hinit : pullback (ψ 0) (form A 0) y v = form A 0 y v := by
    have hid : ψ 0 = id := funext h0
    simp [pullback,hid]
  simpa only [hinit] using htransport y (fun r => pullback (ψ r) (form A r) y v) hf t ht

theorem global_invariant_collar_realization (u : P → ℝ) (β₀ β₁ : P → P)
    (hu : ContDiff ℝ ∞ u) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁)
    (hpos₀ : ∀ x, 0 < invariantVolume u β₀ x) (hpos₁ : ∀ x, 0 < invariantVolume u β₁ x)
    (K : Set P) (hK : IsCompact K) (heq : ∀ x, x ∉ K → β₁ x = β₀ x) :
    ∃ H G : ℝ → V → V, ∃ σ : ℝ → V → ℝ, ∃ C : Set V,
      ContDiff ℝ ∞ (fun p : ℝ × V => H p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => G p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => σ p.1 p.2) ∧
      IsCompact C ∧ (∀ y, H 0 y = y) ∧
      (∀ t y, H t (G t y) = y) ∧ (∀ t y, G t (H t y) = y) ∧
      (∀ t y, y ∉ C → H t y = y) ∧
      (∀ t y, 0 < σ t y) ∧
      (∀ t y, u (xyMap y) = 0 →
        (H t y 0 = y 0 ∧ H t y 1 = y 1) ∧ (G t y 0 = y 0 ∧ G t y 1 = y 1)) ∧
      ∀ y, |y 2| ≤ 1 → ∀ v,
        dot (invariantCoefficients u β₀ (H 1 y)) (fderiv ℝ (H 1) y v) =
          σ 1 y*dot (invariantCoefficients u β₁ y) v := by
  obtain ⟨χ,L,hχ,hL,hrange,hone,hzero,hpositive,C,hC,hsupport⟩ :=
    exists_positive_collar_cutoff u β₀ β₁ hu h₀ h₁ hpos₀ hpos₁ K hK heq
  let a₀ := invariantCoefficients u β₀
  let a₁ := collarCoefficients u β₀ β₁ χ
  have ha₀ : ContDiff ℝ ∞ a₀ := invariantCoefficients_contDiff u β₀ hu h₀
  have ha₁ : ContDiff ℝ ∞ a₁ := collarCoefficients_contDiff u β₀ β₁ χ hu h₀ h₁ hχ
  have heqa : a₁ = fun y => a₀ y+horizontalTaper (fun x => β₁ x-β₀ x) χ y := by
    ext y i
    fin_cases i <;> simp [a₀,a₁,collarCoefficients,invariantCoefficients,horizontalTaper]
  have hnull : ∀ y, dot (a₁ y-a₀ y)
      (curlLinear (fderiv ℝ a₁ y)-curlLinear (fderiv ℝ a₀ y)) = 0 := by
    intro y
    have hd := horizontalTaper_contDiff (fun x => β₁ x-β₀ x) χ (h₁.sub h₀) hχ
    have hder := ((ha₀.differentiable (by simp) y).hasFDerivAt.add
      (hd.differentiable (by simp) y).hasFDerivAt).fderiv
    change fderiv ℝ (fun z => a₀ z+horizontalTaper (fun x => β₁ x-β₀ x) χ z) y = _ at hder
    rw [← heqa] at hder
    have hc : curlLinear (fderiv ℝ a₁ y) = curlLinear (fderiv ℝ a₀ y)+
        curlLinear (fderiv ℝ (horizontalTaper (fun x => β₁ x-β₀ x) χ) y) := by
      rw [hder]
      simpa using curlLinear_combo (fderiv ℝ a₀ y)
        (fderiv ℝ (horizontalTaper (fun x => β₁ x-β₀ x) χ) y) 1 1
    rw [hc,heqa]
    simpa only [add_sub_cancel_left,add_sub_cancel_right] using
      horizontalTaper_integrable (fun x => β₁ x-β₀ x) χ (h₁.sub h₀) hχ y
  let A := blend a₀ a₁
  have hA : ContDiff ℝ ∞ A := blend_contDiff a₀ a₁ ha₀ ha₁
  have hvol : ∀ p, volume A p ≠ 0 := by
    apply fun p => (blend_volume_positive a₀ a₁ ha₀ ha₁ ?_ hpositive hnull p).ne'
    intro y
    rw [invariant_volume_formula u β₀ hu h₀]
    exact hpos₀ _
  let X : ℝ → V → V := fun t y => moser A (t,y)
  have hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2) := moser_contDiff A hA hvol
  have hXout : ∀ t y, y ∉ C → X t y = 0 := by
    intro t y hy
    have he : a₁ y = a₀ y := by
      rw [heqa]
      dsimp only
      rw [hsupport y hy,add_zero]
    have hv := blend_stationary a₀ a₁ ha₀ ha₁ y he t
    simp [X,moser,A,hv,cross]
  have hsupp : ∃ D : Set V, IsCompact D ∧ ∀ t y, y ∉ D → X t y = 0 := ⟨C,hC,hXout⟩
  obtain ⟨ψ,hψ,hψ0,hbij,hflow⟩ := exists_ambient_flow X hX hsupp
  obtain ⟨ρ,hρ,hρψ,hψρ⟩ := smooth_joint_flow_inverse X ψ hX hψ hψ0 hbij hflow
  obtain ⟨lam,hlam,hpos,hpb⟩ := given_moser_flow_pullback A hA hvol ψ hψ hψ0 hbij hflow
  let σ : ℝ → V → ℝ := fun t y => (lam t (ρ t y))⁻¹
  have hσ : ContDiff ℝ ∞ (fun p : ℝ × V => σ p.1 p.2) :=
    (hlam.comp (contDiff_fst.prodMk hρ)).inv (fun p => (hpos p.1 (ρ p.1 p.2)).ne')
  have hnormal : ∀ t y, A (t,y) 2 = u (xyMap y) := by
    intro t y
    simp [A,blend,a₀,a₁,collarCoefficients,invariantCoefficients]
    ring
  have hdiv := moser_flow_preserves_dividing_cylinder A hA hvol u (by
    intro t y
    rw [hnormal,xyMap_apply]) ψ ρ hsupp hψ0 hflow hρψ
  have hfix : ∀ t y, y ∉ C → ψ t y = y := by
    intro t y hy
    exact ambient_flow_fixes X ψ hX hsupp hψ0 hflow y (fun s => hXout s y hy) t
  refine ⟨ρ,ψ,σ,C,hρ,hψ,hσ,hC,?_,hρψ,hψρ,?_,?_,?_,?_⟩
  · intro y
    simpa only [hψ0] using hψρ 0 y
  · intro t y hy
    have hh := hρψ t y
    rw [hfix t y hy] at hh
    exact hh
  · intro t y
    exact inv_pos.mpr (hpos t (ρ t y))
  · intro t y hy
    rw [xyMap_apply] at hy
    exact (hdiv t y hy).symm
  · intro y hy v
    have hψs : ContDiff ℝ ∞ (ψ 1) := hψ.comp (contDiff_const.prodMk contDiff_id :
      ContDiff ℝ ∞ (fun z : V => ((1:ℝ),z)))
    have hρs : ContDiff ℝ ∞ (ρ 1) := hρ.comp (contDiff_const.prodMk contDiff_id :
      ContDiff ℝ ∞ (fun z : V => ((1:ℝ),z)))
    have hchain : fderiv ℝ (ψ 1) (ρ 1 y) (fderiv ℝ (ρ 1) y v) = v := by
      have hd := fderiv_comp y (hψs.differentiable (by simp) _) (hρs.differentiable (by simp) _)
      have hid : ψ 1 ∘ ρ 1 = id := funext (hψρ 1)
      have hh := congrArg (fun T : V →L[ℝ] V => T v) hd
      simpa [hid,id_eq] using hh.symm
    have hp := hpb 1 (by simp) (ρ 1 y) (fderiv ℝ (ρ 1) y v)
    have hstart : ∀ z, A (0,z) = a₀ z := by intro z; simp [A,blend]
    change dot (A (1,ψ 1 (ρ 1 y))) (fderiv ℝ (ψ 1) (ρ 1 y) (fderiv ℝ (ρ 1) y v)) =
      lam 1 (ρ 1 y)*dot (A (0,ρ 1 y)) (fderiv ℝ (ρ 1) y v) at hp
    rw [hψρ,hchain,hstart] at hp
    have hend : A (1,y) = invariantCoefficients u β₁ y := by
      simp [A,blend,a₁,collarCoefficients,invariantCoefficients,hone _ hy]
    rw [hend] at hp
    change dot (a₀ (ρ 1 y)) (fderiv ℝ (ρ 1) y v) =
      (lam 1 (ρ 1 y))⁻¹*dot (invariantCoefficients u β₁ y) v
    rw [hp,← mul_assoc,inv_mul_cancel₀ (hpos 1 (ρ 1 y)).ne',one_mul]

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function GrayStability
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def planarCharacteristic (u : P → ℝ) (β : P → P) (x : P) : P :=
  (u x/invariantVolume u β x) • ![β x 1,-β x 0]

lemma planarCharacteristic_boundary_tangent (u : P → ℝ) (β : P → P) (x : P)
    (hLegendrian : β x 0*(-x 1)+β x 1*x 0 = 0) :
    x 0*planarCharacteristic u β x 0+x 1*planarCharacteristic u β x 1 = 0 := by
  dsimp [planarCharacteristic]
  nlinarith [mul_eq_zero_of_right (u x/invariantVolume u β x) hLegendrian]

/-- The coefficient-level contact Hamiltonian field. -/
def hamiltonianAlgebra (a c : V) (H : ℝ) (g : V) : V :=
  (dot a c)⁻¹ • (H • c+cross a g)

lemma hamiltonian_algebra (a c g v : V) (H : ℝ) (hQ : dot a c ≠ 0) :
    dot a (hamiltonianAlgebra a c H g) = H ∧
    dot g v+dot c (cross (hamiltonianAlgebra a c H g) v) =
      (dot c g/dot a c)*dot a v := by
  have hα : dot a (hamiltonianAlgebra a c H g) = (dot a c)⁻¹*(H*dot a c) := by
    simp [hamiltonianAlgebra,dot,cross,Matrix.vecHead,Matrix.vecTail]
    ring
  refine ⟨?_,?_⟩
  · rw [hα]
    calc (dot a c)⁻¹*(H*dot a c) = H*((dot a c)⁻¹*dot a c) := by ring
      _ = H := by rw [inv_mul_cancel₀ hQ,mul_one]
  · have he : dot c (cross (hamiltonianAlgebra a c H g) v) =
        dot c (cross ((dot a c)⁻¹ • cross a g) v) := by
      simp [hamiltonianAlgebra,dot,cross,Matrix.vecHead,Matrix.vecTail]
      ring
    rw [he]
    exact (moser_algebra a g c v hQ).2

/-- For H=h(z)u(x,y), the contact field has normal velocity exactly h(z).
Its horizontal part is the characteristic field times h'(z). -/
lemma invariant_compression_field_formula (u : P → ℝ) (β : P → P)
    (h : ℝ → ℝ) (y : V) (hQ : invariantVolume u β (xyMap y) ≠ 0) :
    let x := xyMap y
    let c : V := ![fderiv ℝ u x (Pi.single 1 1),-fderiv ℝ u x (Pi.single 0 1),
      fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0]
    let g : V := ![h (y 2)*fderiv ℝ u x (Pi.single 0 1),
      h (y 2)*fderiv ℝ u x (Pi.single 1 1),deriv h (y 2)*u x]
    hamiltonianAlgebra (invariantCoefficients u β y) c (h (y 2)*u x) g =
      ![deriv h (y 2)*planarCharacteristic u β x 0,
        deriv h (y 2)*planarCharacteristic u β x 1,h (y 2)] := by
  dsimp only
  have hvol : dot (invariantCoefficients u β y)
      ![fderiv ℝ u (xyMap y) (Pi.single 1 1),-fderiv ℝ u (xyMap y) (Pi.single 0 1),
        fderiv ℝ β (xyMap y) (Pi.single 0 1) 1-fderiv ℝ β (xyMap y) (Pi.single 1 1) 0] =
      invariantVolume u β (xyMap y) := by
    simp [dot,invariantCoefficients,invariantVolume]
    ring
  unfold hamiltonianAlgebra
  rw [hvol]
  ext i
  fin_cases i
  · simp [invariantCoefficients,planarCharacteristic,cross,div_eq_mul_inv]
    ring
  · simp [invariantCoefficients,planarCharacteristic,cross,div_eq_mul_inv]
    ring
  · change (invariantVolume u β (xyMap y))⁻¹ * _ = h (y 2)
    have hn : (h (y 2)*u (xyMap y))*
          (fderiv ℝ β (xyMap y) (Pi.single 0 1) 1-fderiv ℝ β (xyMap y) (Pi.single 1 1) 0)+
        (cross (invariantCoefficients u β y)
          ![h (y 2)*fderiv ℝ u (xyMap y) (Pi.single 0 1),
            h (y 2)*fderiv ℝ u (xyMap y) (Pi.single 1 1),deriv h (y 2)*u (xyMap y)]) 2 =
        h (y 2)*invariantVolume u β (xyMap y) := by
      simp [cross,invariantCoefficients,invariantVolume]
      ring
    change (invariantVolume u β (xyMap y))⁻¹ *
      ((h (y 2)*u (xyMap y))*
        (fderiv ℝ β (xyMap y) (Pi.single 0 1) 1-fderiv ℝ β (xyMap y) (Pi.single 1 1) 0)+
        (cross (invariantCoefficients u β y)
          ![h (y 2)*fderiv ℝ u (xyMap y) (Pi.single 0 1),
            h (y 2)*fderiv ℝ u (xyMap y) (Pi.single 1 1),deriv h (y 2)*u (xyMap y)]) 2) = h (y 2)
    rw [hn]
    calc (invariantVolume u β (xyMap y))⁻¹*(h (y 2)*invariantVolume u β (xyMap y)) =
        h (y 2)*((invariantVolume u β (xyMap y))⁻¹*invariantVolume u β (xyMap y)) := by ring
      _ = h (y 2) := by rw [inv_mul_cancel₀ hQ,mul_one]

def gradient3 (H : V → ℝ) (y : V) : V :=
  ![fderiv ℝ H y (Pi.single 0 1),fderiv ℝ H y (Pi.single 1 1),fderiv ℝ H y (Pi.single 2 1)]

lemma gradient3_pair (H : V → ℝ) (y v : V) : dot (gradient3 H y) v = fderiv ℝ H y v := by
  have he : fderiv ℝ H y v = v 0*fderiv ℝ H y (Pi.single 0 1)+
      v 1*fderiv ℝ H y (Pi.single 1 1)+v 2*fderiv ℝ H y (Pi.single 2 1) := by
    conv_lhs => rw [vector_expansion v]
    simp
  rw [he]
  simp [dot,gradient3]
  ring

def hamiltonianField (a : V → V) (H : V → ℝ) (y : V) : V :=
  hamiltonianAlgebra (a y) (curlLinear (fderiv ℝ a y)) (H y) (gradient3 H y)

lemma cross_contDiff (f g : V → V) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun y => cross (f y) (g y)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [cross] <;> fun_prop

lemma hamiltonianField_contDiff (a : V → V) (H : V → ℝ)
    (ha : ContDiff ℝ ∞ a) (hH : ContDiff ℝ ∞ H)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0) :
    ContDiff ℝ ∞ (hamiltonianField a H) := by
  have hda : ContDiff ℝ ∞ (fderiv ℝ a) := ha.fderiv_right (by simp)
  have hdH : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (by simp)
  have hc : ContDiff ℝ ∞ (fun y => curlLinear (fderiv ℝ a y)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [curlLinear] <;> fun_prop
  have hg : ContDiff ℝ ∞ (gradient3 H) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [gradient3] <;> fun_prop
  have hq : ContDiff ℝ ∞ (fun y => dot (a y) (curlLinear (fderiv ℝ a y))) := by
    unfold dot
    fun_prop
  exact (hq.inv hQ).smul ((hH.smul hc).add (cross_contDiff a (gradient3 H) ha hg))

/-- Cartan's identity is checked in the ambient coefficient formulation,
including the derivative of the nonzero Hamiltonian. -/
theorem hamiltonianField_lie (a : V → V) (H : V → ℝ)
    (ha : ContDiff ℝ ∞ a) (hH : ContDiff ℝ ∞ H)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0) (y v : V) :
    lieDerivOneForm (hamiltonianField a H) (fun z => covector (a z)) y v =
      (dot (curlLinear (fderiv ℝ a y)) (gradient3 H y)/
        dot (a y) (curlLinear (fderiv ℝ a y)))*covector (a y) v := by
  let α : OneForm 3 := fun z => covector (a z)
  let X := hamiltonianField a H
  have hα : ContDiff ℝ ∞ α := covector.contDiff.comp ha
  have hX : ContDiff ℝ ∞ X := hamiltonianField_contDiff a H ha hH hQ
  have hD : ∀ r w, fderiv ℝ α y r w = dot (fderiv ℝ a y r) w := by
    intro r w
    have hd := covector.hasFDerivAt.comp y (ha.differentiable (by simp) y).hasFDerivAt
    change HasFDerivAt α _ y at hd
    rw [hd.fderiv]
    exact covector_apply _ _
  have hp : (fun z => α z (X z)) = H := by
    ext z
    exact (hamiltonian_algebra (a z) (curlLinear (fderiv ℝ a z)) (gradient3 H z) (0:V) (H z) (hQ z)).1
  have hd := (hα.differentiable (by simp) y).hasFDerivAt.clm_apply
    (hX.differentiable (by simp) y).hasFDerivAt
  have hval := congrArg (fun L : V →L[ℝ] ℝ => L v) hd.fderiv
  rw [hp] at hval
  change fderiv ℝ H y v = α y (fderiv ℝ X y v)+fderiv ℝ α y v (X y) at hval
  rw [hD] at hval
  have hm := (hamiltonian_algebra (a y) (curlLinear (fderiv ℝ a y))
    (gradient3 H y) v (H y) (hQ y)).2
  rw [gradient3_pair,← exterior_cross] at hm
  change fderiv ℝ H y v+(dot (fderiv ℝ a y (X y)) v-dot (fderiv ℝ a y v) (X y)) = _ at hm
  change fderiv ℝ α y (X y) v+α y (fderiv ℝ X y v) = _
  rw [hD,covector_apply (a y) v]
  linarith

lemma invariant_curl_formula (u : P → ℝ) (β : P → P)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (y : V) :
    curlLinear (fderiv ℝ (invariantCoefficients u β) y) =
      ![fderiv ℝ u (xyMap y) (Pi.single 1 1),-fderiv ℝ u (xyMap y) (Pi.single 0 1),
        fderiv ℝ β (xyMap y) (Pi.single 0 1) 1-fderiv ℝ β (xyMap y) (Pi.single 1 1) 0] := by
  have he : collarCoefficients u β β (fun _ => 0) = invariantCoefficients u β := by
    ext q i
    fin_cases i <;> simp [collarCoefficients,invariantCoefficients]
  have hD := collarCoefficients_fderiv u β β (fun _ => 0) hu hβ hβ contDiff_const y
  rw [he] at hD
  ext i
  fin_cases i <;> dsimp [curlLinear] <;> rw [hD,hD] <;>
    simp only [xyMap_e0,xyMap_e1,xyMap_e2,map_zero] <;> simp

def normalHamiltonian (u : P → ℝ) (h : ℝ → ℝ) (y : V) : ℝ := h (y 2)*u (xyMap y)

lemma normalHamiltonian_gradient (u : P → ℝ) (h : ℝ → ℝ)
    (hu : ContDiff ℝ ∞ u) (hh : ContDiff ℝ ∞ h) (y : V) :
    gradient3 (normalHamiltonian u h) y =
      ![h (y 2)*fderiv ℝ u (xyMap y) (Pi.single 0 1),
        h (y 2)*fderiv ℝ u (xyMap y) (Pi.single 1 1),deriv h (y 2)*u (xyMap y)] := by
  have hr := (hh.differentiable (by simp) (y 2)).hasDerivAt.hasFDerivAt.comp y
    (ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ).hasFDerivAt
  have hU := (hu.differentiable (by simp) (xyMap y)).hasFDerivAt.comp y xyMap.hasFDerivAt
  have hd := hr.mul hU
  change HasFDerivAt (normalHamiltonian u h) _ y at hd
  unfold gradient3
  rw [hd.fderiv]
  ext i
  fin_cases i <;>
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
      xyMap_e0,xyMap_e1,xyMap_e2,map_zero] <;> simp [mul_comm]

def compressionField (u : P → ℝ) (β : P → P) (h : ℝ → ℝ) (y : V) : V :=
  ![deriv h (y 2)*planarCharacteristic u β (xyMap y) 0,
    deriv h (y 2)*planarCharacteristic u β (xyMap y) 1,h (y 2)]

theorem compressionField_is_contact (u : P → ℝ) (β : P → P) (h : ℝ → ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hh : ContDiff ℝ ∞ h)
    (hpositive : ∀ x, 0 < invariantVolume u β x) :
    ContDiff ℝ ∞ (compressionField u β h) ∧
      ∀ y, ∃ μ : ℝ, ∀ v,
        lieDerivOneForm (compressionField u β h) (fun z => covector (invariantCoefficients u β z)) y v =
          μ*covector (invariantCoefficients u β y) v := by
  let a := invariantCoefficients u β
  let H := normalHamiltonian u h
  have ha : ContDiff ℝ ∞ a := invariantCoefficients_contDiff u β hu hβ
  have hH : ContDiff ℝ ∞ H :=
    (hh.comp (contDiff_apply ℝ ℝ 2)).mul (hu.comp xyMap.contDiff)
  have hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0 := by
    intro y
    rw [invariant_volume_formula u β hu hβ]
    exact (hpositive _).ne'
  have he : hamiltonianField a H = compressionField u β h := by
    funext y
    dsimp only [hamiltonianField,a,H]
    rw [invariant_curl_formula u β hu hβ,normalHamiltonian_gradient u h hu hh]
    simpa only [normalHamiltonian,compressionField] using
      invariant_compression_field_formula u β h y (hpositive _).ne'
  constructor
  · rw [← he]
    exact hamiltonianField_contDiff a H ha hH hQ
  · intro y
    refine ⟨dot (curlLinear (fderiv ℝ a y)) (gradient3 H y)/dot (a y) (curlLinear (fderiv ℝ a y)),?_⟩
    intro v
    rw [← he]
    exact hamiltonianField_lie a H ha hH hQ y v

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def diskSq (x : P) : ℝ := x 0^2+x 1^2
def diskCutoff (x : P) : ℝ := Real.smoothTransition (4-diskSq x)

lemma diskSq_contDiff : ContDiff ℝ ∞ diskSq := by unfold diskSq; fun_prop
lemma diskCutoff_contDiff : ContDiff ℝ ∞ diskCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub diskSq_contDiff)

lemma diskCutoff_one (x : P) (hx : diskSq x < 2) : diskCutoff x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma diskCutoff_compact : HasCompactSupport diskCutoff := by
  apply HasCompactSupport.intro' (K := Icc (![-2,-2]:P) ![2,2]) isCompact_Icc isClosed_Icc
  intro x hx
  by_cases hr : 4 ≤ diskSq x
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · have hs : diskSq x < 4 := not_le.mp hr
    have h₀ : -2 ≤ x 0 ∧ x 0 ≤ 2 := by dsimp [diskSq] at hs; constructor <;> nlinarith [sq_nonneg (x 1)]
    have h₁ : -2 ≤ x 1 ∧ x 1 ≤ 2 := by dsimp [diskSq] at hs; constructor <;> nlinarith [sq_nonneg (x 0)]
    apply (hx ?_).elim
    constructor
    · intro i
      fin_cases i
      · exact h₀.1
      · exact h₁.1
    · intro i
      fin_cases i
      · exact h₀.2
      · exact h₁.2


def normalSpeed (ε z : ℝ) : ℝ := expNegInvGlue (ε^2-z^2)/expNegInvGlue (ε^2)

lemma normalSpeed_contDiff (ε : ℝ) : ContDiff ℝ ∞ (normalSpeed ε) :=
  (expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))).div_const _

lemma normalSpeed_nonneg (ε z : ℝ) : 0 ≤ normalSpeed ε z :=
  div_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

lemma normalSpeed_zero (ε z : ℝ) (hε : 0 < ε) (hz : ε ≤ |z|) : normalSpeed ε z = 0 := by
  have hs : ε^2 ≤ z^2 := by nlinarith [sq_nonneg (|z|-ε),sq_abs z]
  simp [normalSpeed,expNegInvGlue.zero_of_nonpos (show ε^2-z^2 ≤ 0 by linarith)]

lemma normalSpeed_pos (ε z : ℝ) (hε : 0 < ε) (hz : |z| < ε) : 0 < normalSpeed ε z := by
  have hs : 0 < ε^2-z^2 := by
    have ha := abs_lt.mp hz
    nlinarith [mul_pos (sub_pos.mpr ha.2) (by linarith : 0 < ε+z)]
  exact div_pos (expNegInvGlue.pos_of_pos hs) (expNegInvGlue.pos_of_pos (sq_pos_of_pos hε))

lemma normalSpeed_at_zero (ε : ℝ) (hε : 0 < ε) : normalSpeed ε 0 = 1 := by
  simp [normalSpeed,(expNegInvGlue.pos_of_pos (sq_pos_of_pos hε)).ne']

lemma normalSpeed_deriv_zero (ε z : ℝ) (hε : 0 < ε) (hz : ε ≤ |z|) :
    deriv (normalSpeed ε) z = 0 := by
  have hmin : IsLocalMin (normalSpeed ε) z := Eventually.of_forall fun w => by
    rw [normalSpeed_zero ε z hε hz]
    exact normalSpeed_nonneg ε w
  exact hmin.deriv_eq_zero

lemma normalSpeed_compact (ε : ℝ) (hε : 0 < ε) : HasCompactSupport (normalSpeed ε) := by
  apply HasCompactSupport.intro' (K := Icc (-ε) ε) isCompact_Icc isClosed_Icc
  intro z hz
  apply normalSpeed_zero ε z hε
  by_contra hn
  exact hz (abs_le.mp (not_le.mp hn).le)

def localizedHamiltonian (u : P → ℝ) (ε : ℝ) (y : V) : ℝ :=
  diskCutoff (xyMap y)*normalHamiltonian u (normalSpeed ε) y

lemma localizedHamiltonian_contDiff (u : P → ℝ) (hu : ContDiff ℝ ∞ u) (ε : ℝ) :
    ContDiff ℝ ∞ (localizedHamiltonian u ε) :=
  (diskCutoff_contDiff.comp xyMap.contDiff).mul
    (((normalSpeed_contDiff ε).comp (contDiff_apply ℝ ℝ 2)).mul (hu.comp xyMap.contDiff))

lemma localizedHamiltonian_compact (u : P → ℝ) (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (localizedHamiltonian u ε) := by
  let join : P × ℝ → V := fun q => ![q.1 0,q.1 1,q.2]
  have hjoin : Continuous join := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [join] <;> fun_prop
  let C := join '' (tsupport diskCutoff ×ˢ Icc (-ε) ε)
  have hC : IsCompact C := (diskCutoff_compact.prod isCompact_Icc).image hjoin
  apply HasCompactSupport.intro' hC hC.isClosed
  intro y hy
  by_cases hx : xyMap y ∈ tsupport diskCutoff
  · have hz : ε ≤ |y 2| := by
      by_contra hn
      apply hy
      refine ⟨(xyMap y,y 2),⟨hx,abs_le.mp (not_le.mp hn).le⟩,?_⟩
      ext i
      fin_cases i <;> simp [join]
    simp [localizedHamiltonian,normalHamiltonian,normalSpeed_zero ε (y 2) hε hz]
  · have hz := image_eq_zero_of_notMem_tsupport hx
    simp only [localizedHamiltonian,hz,zero_mul]

lemma hamiltonianField_compact (a : V → V) (H : V → ℝ) (hH : HasCompactSupport H) :
    HasCompactSupport (hamiltonianField a H) := by
  apply HasCompactSupport.intro' hH (isClosed_tsupport H)
  intro y hy
  have hv := image_eq_zero_of_notMem_tsupport hy
  have hd := fderiv_of_notMem_tsupport ℝ hy
  simp [hamiltonianField,hamiltonianAlgebra,gradient3,hv,hd,cross]

lemma localizedHamiltonian_agrees (u : P → ℝ) (ε : ℝ) (y : V) (hy : diskSq (xyMap y) ≤ 1) :
    localizedHamiltonian u ε =ᶠ[𝓝 y] normalHamiltonian u (normalSpeed ε) := by
  have ho : IsOpen {z : V | diskSq (xyMap z) < 2} :=
    isOpen_lt (diskSq_contDiff.continuous.comp xyMap.continuous) continuous_const
  filter_upwards [ho.mem_nhds (show diskSq (xyMap y) < 2 by linarith)] with z hz
  simp only [localizedHamiltonian,diskCutoff_one _ hz,one_mul]

lemma localizedField_agrees (u : P → ℝ) (β : P → P) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β)
    (hpos : ∀ x, 0 < invariantVolume u β x) (y : V) (hy : diskSq (xyMap y) ≤ 1) :
    hamiltonianField (invariantCoefficients u β) (localizedHamiltonian u ε) y =
      compressionField u β (normalSpeed ε) y := by
  have he := localizedHamiltonian_agrees u ε y hy
  have hg : gradient3 (localizedHamiltonian u ε) y = gradient3 (normalHamiltonian u (normalSpeed ε)) y := by
    unfold gradient3
    rw [he.fderiv_eq]
  unfold hamiltonianField
  rw [he.eq_of_nhds,hg,invariant_curl_formula u β hu hβ,
    normalHamiltonian_gradient u (normalSpeed ε) hu (normalSpeed_contDiff ε)]
  simpa only [normalHamiltonian,compressionField] using
    invariant_compression_field_formula u β (normalSpeed ε) y (hpos _).ne'

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def hamiltonianRate (a : V → V) (H : V → ℝ) (y : V) : ℝ :=
  dot (curlLinear (fderiv ℝ a y)) (gradient3 H y)/dot (a y) (curlLinear (fderiv ℝ a y))

lemma hamiltonianRate_contDiff (a : V → V) (H : V → ℝ)
    (ha : ContDiff ℝ ∞ a) (hH : ContDiff ℝ ∞ H)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0) :
    ContDiff ℝ ∞ (hamiltonianRate a H) := by
  have hda : ContDiff ℝ ∞ (fderiv ℝ a) := ha.fderiv_right (by simp)
  have hdH : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (by simp)
  have hc : ContDiff ℝ ∞ (fun y => curlLinear (fderiv ℝ a y)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [curlLinear] <;> fun_prop
  have hg : ContDiff ℝ ∞ (gradient3 H) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [gradient3] <;> fun_prop
  have hq : ContDiff ℝ ∞ (fun y => dot (a y) (curlLinear (fderiv ℝ a y))) := by
    unfold dot
    fun_prop
  have hn : ContDiff ℝ ∞ (fun y => dot (curlLinear (fderiv ℝ a y)) (gradient3 H y)) := by
    unfold dot
    fun_prop
  exact hn.div hq hQ

lemma hamiltonian_derivative (a : V → V) (H : V → ℝ)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0) (y : V) :
    fderiv ℝ H y (hamiltonianField a H y) = hamiltonianRate a H y*H y := by
  have hX := hamiltonian_algebra (a y) (curlLinear (fderiv ℝ a y)) (gradient3 H y)
    (hamiltonianField a H y) (H y) (hQ y)
  have hz : cross (hamiltonianField a H y) (hamiltonianField a H y) = 0 := by
    ext i
    fin_cases i <;> simp [cross] <;> ring
  have he := hX.2
  change dot (gradient3 H y) (hamiltonianField a H y)+
    dot (curlLinear (fderiv ℝ a y)) (cross (hamiltonianField a H y) (hamiltonianField a H y)) = _ at he
  rw [gradient3_pair,hz] at he
  have hvalue : dot (a y) (hamiltonianField a H y) = H y := hX.1
  have hz0 : dot (curlLinear (fderiv ℝ a y)) (0:V) = 0 := by simp [dot]
  rw [hz0,add_zero,hvalue] at he
  exact he

/-- Complete compactly supported contact flow, with a conformal factor and
Hamiltonian transport at EVERY real time, obtained by rescaling unit time. -/
theorem integrate_hamiltonian_all_time (a : V → V) (H : V → ℝ)
    (ha : ContDiff ℝ ∞ a) (hH : ContDiff ℝ ∞ H) (hcH : HasCompactSupport H)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0) :
    ∃ ψ ρ : ℝ → V → V, ∃ lam : ℝ → V → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧ (∀ t, Bijective (ψ t)) ∧
      (∀ t y, ρ t (ψ t y) = y) ∧ (∀ t y, ψ t (ρ t y) = y) ∧
      (∀ t y, HasDerivAt (fun s => ψ s y) (hamiltonianField a H (ψ t y)) t) ∧
      (∀ t y, 0 < lam t y) ∧
      (∀ t y v, covector (a (ψ t y)) (fderiv ℝ (ψ t) y v) = lam t y*covector (a y) v) ∧
      ∀ t y, H (ψ t y) = lam t y*H y := by
  let X : ℝ → V → V := fun _ y => hamiltonianField a H y
  have hXs := hamiltonianField_contDiff a H ha hH hQ
  have hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2) := hXs.comp contDiff_snd
  have hsupp : ∃ C : Set V, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0 := by
    refine ⟨tsupport (hamiltonianField a H),hamiltonianField_compact a H hcH,?_⟩
    intro t y hy
    exact image_eq_zero_of_notMem_tsupport hy
  obtain ⟨ψ,hψ,h0,hbij,hflow⟩ := exists_ambient_flow X hX hsupp
  obtain ⟨ρ,hρ,hρψ,hψρ⟩ := smooth_joint_flow_inverse X ψ hX hψ h0 hbij hflow
  let α : OneForm 3 := fun y => covector (a y)
  let μ := hamiltonianRate a H
  have hμ : ContDiff ℝ ∞ μ := hamiltonianRate_contDiff a H ha hH hQ
  let q : ℝ → (ℝ × V) → ℝ := fun s p => p.1*μ (ψ (s*p.1) p.2)
  have harg : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => (p.1*p.2.1,p.2.2)) := by fun_prop
  have hq : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => q p.1 p.2) :=
    (contDiff_fst.comp contDiff_snd).mul (hμ.comp (hψ.comp harg))
  obtain ⟨Λ,hΛ,hΛ0,hpos,htransport⟩ := ParameterizedCalculus.smooth_scalar_linear_transport q hq
  let lam : ℝ → V → ℝ := fun t y => Λ 1 (t,y)
  have hlam : ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) :=
    hΛ.comp (contDiff_const.prodMk contDiff_id)
  have hα : ContDiff ℝ ∞ α := covector.contDiff.comp ha
  have hη : IsSmoothFamily (fun _ => α) := hα.comp contDiff_snd
  have hdiff : ∀ t y v, HasDerivAt (fun s => pullback (ψ s) α y v)
      (μ (ψ t y)*pullback (ψ t) α y v) t := by
    intro t y v
    have hd := GrayStability.pullback_family_hasDerivAt (fun _ => α) hη X hX ψ hψ h0 hbij hflow t y v
    simp only [formTimeDeriv,deriv_const,zero_add] at hd
    have hl := hamiltonianField_lie a H ha hH hQ (ψ t y) (fderiv ℝ (ψ t) y v)
    change lieDerivOneForm (X t) α (ψ t y) (fderiv ℝ (ψ t) y v) = _ at hl
    rw [hl] at hd
    exact hd
  have hHdiff : ∀ t y, HasDerivAt (fun s => H (ψ s y)) (μ (ψ t y)*H (ψ t y)) t := by
    intro t y
    have hd := (hH.differentiable (by simp) (ψ t y)).hasFDerivAt.comp_hasDerivAt t (hflow t y)
    rw [hamiltonian_derivative a H hQ] at hd
    exact hd
  refine ⟨ψ,ρ,lam,hψ,hρ,hlam,h0,hbij,hρψ,hψρ,hflow,fun t y => hpos 1 (t,y),?_,?_⟩
  · intro T y v
    have hf : ∀ s ∈ Icc (0:ℝ) 1,
        HasDerivAt (fun r => pullback (ψ (r*T)) α y v)
          (q s (T,y)*pullback (ψ (s*T)) α y v) s := by
      intro s hs
      have hd := (hdiff (s*T) y v).comp s ((hasDerivAt_id s).mul_const T)
      convert! hd using 1 <;> dsimp [q] <;> ring
    have hh := htransport (T,y) (fun s => pullback (ψ (s*T)) α y v) hf 1 (by simp)
    have hid : ψ 0 = id := funext h0
    simpa [lam,pullback,hid] using hh
  · intro T y
    have hf : ∀ s ∈ Icc (0:ℝ) 1,
        HasDerivAt (fun r => H (ψ (r*T) y)) (q s (T,y)*H (ψ (s*T) y)) s := by
      intro s hs
      have hd := (hHdiff (s*T) y).comp s ((hasDerivAt_id s).mul_const T)
      convert! hd using 1 <;> dsimp [q] <;> ring
    have hh := htransport (T,y) (fun s => H (ψ (s*T) y)) hf 1 (by simp)
    simpa [lam,h0] using hh

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def center : V →L[ℝ] V := ContinuousLinearMap.pi
  ![(ContinuousLinearMap.proj 0 : V →L[ℝ] ℝ),ContinuousLinearMap.proj 1,0]
@[simp] lemma center_apply (y : V) : center y = ![y 0,y 1,0] := by ext i; fin_cases i <;> simp [center]
@[simp] lemma xyMap_center (y : V) : xyMap (center y) = xyMap y := by ext i; fin_cases i <;> simp [center]
@[simp] lemma center_two (y : V) : center y 2 = 0 := by simp [center]


end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def surfaceDisk : Set V := {y | diskSq (xyMap y) ≤ 1 ∧ y 2=0}

lemma surfaceDisk_compact : IsCompact surfaceDisk := by
  have hc : IsClosed surfaceDisk :=
    (isClosed_le (diskSq_contDiff.continuous.comp xyMap.continuous) continuous_const).inter
      (isClosed_eq (continuous_apply 2) continuous_const)
  apply isCompact_Icc.of_isClosed_subset hc (s := Icc (![-1,-1,-1]:V) ![1,1,1])
  intro y hy
  have hs : y 0^2+y 1^2 ≤ 1 := hy.1
  constructor <;> intro i <;> fin_cases i
  · dsimp; nlinarith [sq_nonneg (y 1)]
  · dsimp; nlinarith [sq_nonneg (y 0)]
  · simpa [hy.2]
  · dsimp; nlinarith [sq_nonneg (y 1)]
  · dsimp; nlinarith [sq_nonneg (y 0)]
  · simpa [hy.2]


end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma exists_ambient_flow_fin {n : ℕ} (X : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => X p.1 p.2))
    (hsupp : ∃ K : Set (Fin n → ℝ), IsCompact K ∧ ∀ t y, y ∉ K → X t y=0) :
    ∃ ψ : ℝ → (Fin n → ℝ) → (Fin n → ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => ψ p.1 p.2) ∧
      (∀ y, ψ 0 y=y) ∧ (∀ t, Bijective (ψ t)) ∧
      ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t := by
  let F : (Fin n → ℝ) → (Fin 1 → ℝ) := fun _ _ => 1
  have hempty : levelSet F=∅ := by
    ext y
    simp only [levelSet,mem_ofPred_eq,mem_empty_iff_false,iff_false]
    intro h
    have hh := congrFun h 0
    norm_num [F] at hh
  have hF : IsCompactRegularLevel F := by
    refine ⟨contDiff_const,?_,?_⟩
    · rw [hempty]; exact isCompact_empty
    · intro y hy; rw [hempty] at hy; exact hy.elim
  obtain ⟨ψ,hψ,h0,hbij,hd,_⟩ :=
    FlowCalculus.compact_supported_flow_preserves_regular_level F hF X hX hsupp (by
      intro t ht y hy; rw [hempty] at hy; exact hy.elim)
  exact ⟨ψ,hψ,h0,hbij,hd⟩

lemma exists_ambient_flow_pair (Z : (ℝ × V) → (ℝ × V)) (hZ : ContDiff ℝ ∞ Z)
    (hcZ : HasCompactSupport Z) :
    ∃ Φ : ℝ → (ℝ × V) → (ℝ × V),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => Φ p.1 p.2) ∧
      (∀ y, Φ 0 y=y) ∧ (∀ t, Bijective (Φ t)) ∧
      ∀ t y, HasDerivAt (fun s => Φ s y) (Z (Φ t y)) t := by
  let E : (ℝ × V) ≃L[ℝ] (Fin 4 → ℝ) := Fin.consEquivL ℝ (fun _ : Fin 4 => ℝ)
  let T : (Fin 4 → ℝ) → (Fin 4 → ℝ) := fun y => E (Z (E.symm y))
  have hT : ContDiff ℝ ∞ T := E.contDiff.comp (hZ.comp E.symm.contDiff)
  have hC : IsCompact (E '' tsupport Z) := hcZ.image E.continuous
  have hs : ∀ (t : ℝ) (y : Fin 4 → ℝ), y ∉ E '' tsupport Z → T y=0 := by
    intro t y hy
    have hz : E.symm y ∉ tsupport Z := by
      intro hh
      exact hy ⟨E.symm y,hh,E.apply_symm_apply y⟩
    simp [T,image_eq_zero_of_notMem_tsupport hz]
  obtain ⟨Ψ,hΨ,h0,hbij,hd⟩ := exists_ambient_flow_fin (fun _ => T)
    (hT.comp contDiff_snd) ⟨E '' tsupport Z,hC,hs⟩
  let Φ : ℝ → (ℝ × V) → (ℝ × V) := fun t y => E.symm (Ψ t (E y))
  refine ⟨Φ,E.symm.contDiff.comp (hΨ.comp (contDiff_fst.prodMk (E.contDiff.comp contDiff_snd))),
    fun y => by simp [Φ,h0],fun t => E.symm.bijective.comp ((hbij t).comp E.bijective),?_⟩
  intro t y
  have hh := E.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hd t (E y))
  convert! hh using 1 <;> simp [Φ,T]

theorem exists_smooth_frozen_flows (X : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hsupp : ∃ C : Set V, IsCompact C ∧ ∀ s y, y ∉ C → X s y=0) :
    ∃ ψ ρ : ℝ → ℝ → V → V,
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => ψ p.1 p.2.1 p.2.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => ρ p.1 p.2.1 p.2.2) ∧
      (∀ s y, ψ s 0 y=y) ∧
      (∀ s t y, ρ s t (ψ s t y)=y) ∧ (∀ s t y, ψ s t (ρ s t y)=y) ∧
      ∀ s ∈ Icc (0:ℝ) 1, ∀ t y,
        HasDerivAt (fun r => ψ s r y) (X s (ψ s t y)) t := by
  obtain ⟨C,hC,hc⟩ := hsupp
  let Z : (ℝ × V) → (ℝ × V) := fun p => (0,cutoffBase p.1 • X p.1 p.2)
  have hZ : ContDiff ℝ ∞ Z := contDiff_const.prodMk ((cutoffBase_contDiff.comp contDiff_fst).smul hX)
  have hCZ : HasCompactSupport Z := by
    apply HasCompactSupport.intro (isCompact_Icc.prod hC)
    intro p hp
    by_cases hpar : p.1 ∈ Icc (-2:ℝ) 2
    · have hy : p.2 ∉ C := fun hh => hp ⟨hpar,hh⟩
      simp [Z,hc p.1 p.2 hy]
    · have hlarge : 2 ≤ |p.1| := by
        simp only [mem_Icc,not_and_or,not_le] at hpar
        rcases hpar with hh|hh
        · rw [abs_of_neg (by linarith)]; linarith
        · exact le_trans (le_of_lt hh) (le_abs_self _)
      simp [Z,cutoffBase_zero p.1 hlarge]
  obtain ⟨Φ,hΦ,h0,hbij,hd⟩ := exists_ambient_flow_pair Z hZ hCZ
  obtain ⟨R,hR,hRΦ,hΦR⟩ := smooth_joint_flow_inverse (fun _ => Z) Φ (hZ.comp contDiff_snd) hΦ h0 hbij hd
  have hfirst (t : ℝ) (p : ℝ × V) : (Φ t p).1=p.1 := by
    have hh (r : ℝ) : HasDerivAt (fun q => (Φ q p).1) 0 r := by
      have hd' := (ContinuousLinearMap.fst ℝ ℝ V).hasFDerivAt.comp_hasDerivAt r (hd r p)
      convert! hd' using 1 <;> simp [Z]
    have heq := is_const_of_deriv_eq_zero (fun r => (hh r).differentiableAt)
      (fun r => (hh r).deriv) t 0
    simpa only [h0] using heq
  have hRfirst (t : ℝ) (p : ℝ × V) : (R t p).1=p.1 := by
    have hh := hfirst t (R t p)
    rw [hΦR t p] at hh
    exact hh.symm
  let ψ : ℝ → ℝ → V → V := fun s t y => (Φ t (s,y)).2
  let ρ : ℝ → ℝ → V → V := fun s t y => (R t (s,y)).2
  have harg : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => (p.2.1,(p.1,p.2.2))) := by fun_prop
  refine ⟨ψ,ρ,(hΦ.comp harg).snd,(hR.comp harg).snd,fun s y => by simp [ψ,h0],?_,?_,?_⟩
  · intro s t y
    have hh := congrArg Prod.snd (hRΦ t (s,y))
    change (R t (s,(Φ t (s,y)).2)).2=y
    have hp : (s,(Φ t (s,y)).2)=Φ t (s,y) := by
      exact Prod.ext (hfirst t (s,y)).symm rfl
    rw [hp]
    exact hh
  · intro s t y
    have hh := congrArg Prod.snd (hΦR t (s,y))
    change (Φ t (s,(R t (s,y)).2)).2=y
    have hp : (s,(R t (s,y)).2)=R t (s,y) := by
      exact Prod.ext (hRfirst t (s,y)).symm rfl
    rw [hp]
    exact hh
  · intro s hs t y
    have hh := (ContinuousLinearMap.snd ℝ ℝ V).hasFDerivAt.comp_hasDerivAt t (hd t (s,y))
    have hk : cutoffBase s=1 := cutoffBase_one s (by rw [abs_of_nonneg hs.1]; exact hs.2)
    convert! hh using 1 <;> simp only [Z,hfirst t (s,y),hk,one_smul] <;> rfl

end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem integrate_contact_field_family (α : V → V →L[ℝ] ℝ) (hα : ContDiff ℝ ∞ α)
    (X : ℝ → V → V) (μ : ℝ → V → ℝ)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hμ : ContDiff ℝ ∞ (fun p : ℝ × V => μ p.1 p.2))
    (hsupp : ∃ C : Set V, IsCompact C ∧ ∀ s y, y ∉ C → X s y=0)
    (hLie : ∀ s y v, lieDerivOneForm (X s) α y v=μ s y*α y v) :
    ∃ ψ ρ : ℝ → ℝ → V → V, ∃ lam : ℝ → ℝ → V → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => ψ p.1 p.2.1 p.2.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => ρ p.1 p.2.1 p.2.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => lam p.1 p.2.1 p.2.2) ∧
      (∀ s y, ψ s 0 y=y) ∧
      (∀ s t y, ρ s t (ψ s t y)=y) ∧ (∀ s t y, ψ s t (ρ s t y)=y) ∧
      (∀ s t y, 0 < lam s t y) ∧
      ∀ s ∈ Icc (0:ℝ) 1,
        (∀ t y, HasDerivAt (fun r => ψ s r y) (X s (ψ s t y)) t) ∧
        (∀ t y v, α (ψ s t y) (fderiv ℝ (ψ s t) y v)=lam s t y*α y v) ∧
        ∀ t y, α (ψ s t y) (X s (ψ s t y))=lam s t y*α y (X s y) := by
  obtain ⟨ψ,ρ,hψ,hρ,h0,hρψ,hψρ,hd⟩ := exists_smooth_frozen_flows X hX hsupp
  let q : ℝ → (ℝ × (ℝ × V)) → ℝ := fun r p => p.2.1*μ p.1 (ψ p.1 (r*p.2.1) p.2.2)
  have hq : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × (ℝ × V)) => q p.1 p.2) := by
    have harg : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × (ℝ × V)) =>
        (p.2.1,(p.1*p.2.2.1,p.2.2.2))) := by fun_prop
    have hsarg : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × (ℝ × V)) => p.2.1) := by fun_prop
    exact (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × (ℝ × V)) => p.2.2.1)).mul
      (hμ.comp (hsarg.prodMk (hψ.comp harg)))
  obtain ⟨Λ,hΛ,hΛ0,hpos,htransport⟩ := ParameterizedCalculus.smooth_scalar_linear_transport q hq
  let lam : ℝ → ℝ → V → ℝ := fun s t y => Λ 1 (s,(t,y))
  have hlam : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => lam p.1 p.2.1 p.2.2) :=
    hΛ.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨ψ,ρ,lam,hψ,hρ,hlam,h0,hρψ,hψρ,fun s t y => hpos _ _,?_⟩
  intro s hs
  have hψs : ContDiff ℝ ∞ (fun p : ℝ × V => ψ s p.1 p.2) :=
    hψ.comp (f := fun p : ℝ × V => (s,p)) (contDiff_const.prodMk contDiff_id)
  have hXs : ContDiff ℝ ∞ (X s) := hX.comp (f := fun y : V => (s,y)) (contDiff_const.prodMk contDiff_id)
  have hXf : ContDiff ℝ ∞ (fun p : ℝ × V => X s p.2) := hXs.comp contDiff_snd
  have hbij (t : ℝ) : Bijective (ψ s t) :=
    ⟨(Function.LeftInverse.injective (hρψ s t)),Function.RightInverse.surjective (hψρ s t)⟩
  have hpbd (t : ℝ) (y v : V) : HasDerivAt (fun r => pullback (ψ s r) α y v)
      (μ s (ψ s t y)*pullback (ψ s t) α y v) t := by
    have hh := GrayStability.pullback_family_hasDerivAt (fun _ => α) (hα.comp contDiff_snd)
      (fun _ => X s) hXf (ψ s) hψs (h0 s) hbij (hd s hs) t y v
    simp only [formTimeDeriv,deriv_const,zero_add] at hh
    rw [hLie] at hh
    exact hh
  let H : V → ℝ := fun y => α y (X s y)
  have hH : ContDiff ℝ ∞ H := hα.clm_apply hXs
  have hHd (t : ℝ) (y : V) : HasDerivAt (fun r => H (ψ s r y))
      (μ s (ψ s t y)*H (ψ s t y)) t := by
    have hh := ((hα.differentiable (by simp) _).hasFDerivAt.clm_apply
      (hXs.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt t (hd s hs t y)
    have hl := hLie s (ψ s t y) (X s (ψ s t y))
    change fderiv ℝ α (ψ s t y) (X s (ψ s t y)) (X s (ψ s t y))+
      α (ψ s t y) (fderiv ℝ (X s) (ψ s t y) (X s (ψ s t y)))=_ at hl
    convert! hh using 1
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_apply]
    dsimp only [H]
    linarith
  refine ⟨hd s hs,?_,?_⟩
  · intro T y v
    have hf : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt
        (fun a => pullback (ψ s (a*T)) α y v) (q r (s,(T,y))*pullback (ψ s (r*T)) α y v) r := by
      intro r hr
      have hh := (hpbd (r*T) y v).comp r ((hasDerivAt_id r).mul_const T)
      convert! hh using 1 <;> dsimp only [q] <;> ring
    have hh := htransport (s,(T,y)) (fun r => pullback (ψ s (r*T)) α y v) hf 1 (by simp)
    have hid : ψ s 0=id := funext (h0 s)
    simpa [lam,pullback,hid] using hh
  · intro T y
    have hf : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt
        (fun a => H (ψ s (a*T) y)) (q r (s,(T,y))*H (ψ s (r*T) y)) r := by
      intro r hr
      have hh := (hHd (r*T) y).comp r ((hasDerivAt_id r).mul_const T)
      convert! hh using 1 <;> dsimp only [q] <;> ring
    have hh := htransport (s,(T,y)) (fun r => H (ψ s (r*T) y)) hf 1 (by simp)
    simpa only [H,lam,one_mul,zero_mul,h0] using hh

end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

lemma smooth_injective_derivative_local_chart_general (F : E → E) (hF : ContDiff ℝ ∞ F)
    (p : E) (hinj : Injective (fderiv ℝ F p)) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = F ∧ p ∈ e.source := by
  let A : E ≃L[ℝ] E := (LinearEquiv.ofBijective (fderiv ℝ F p).toLinearMap
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt F (A : E →L[ℝ] E) p := (hF.differentiable (by simp) p).hasFDerivAt
  exact ⟨hF.contDiffAt.toOpenPartialHomeomorph F hd (by simp),
    hF.contDiffAt.toOpenPartialHomeomorph_coe hd (by simp),
    hF.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)⟩

/-- Local invertibility and injectivity on a compact set give one genuine smooth
chart around the entire compact set, inside any prescribed good open domain. -/
theorem compact_smooth_embedding_chart_general (F : E → E) (hF : ContDiff ℝ ∞ F)
    (S W : Set E) (hS : IsCompact S) (hW : IsOpen W) (hSW : S ⊆ W)
    (hinj : InjOn F S) (hder : ∀ p ∈ W, Injective (fderiv ℝ F p)) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = F ∧ S ⊆ e.source ∧
      e.source ⊆ W ∧ ∀ y ∈ e.target, ContDiffAt ℝ ∞ e.symm y := by
  have hloc : ∀ p ∈ S, ∃ O ∈ 𝓝 p, InjOn F O := by
    intro p hp
    obtain ⟨e,he,hp⟩ := smooth_injective_derivative_local_chart_general F hF p (hder p (hSW hp))
    exact ⟨e.source,e.open_source.mem_nhds hp,he ▸ e.injOn⟩
  obtain ⟨O,hO,hSO,hOi⟩ := hinj.exists_isOpen_superset hS (fun _ _ => hF.continuous.continuousAt) hloc
  let U := O ∩ W
  have hU : IsOpen U := hO.inter hW
  have hUi : InjOn F U := hOi.mono inter_subset_left
  have hopen : IsOpenMap (U.domRestrict F) := by
    apply IsOpenMap.of_nhds_le
    intro x
    obtain ⟨e,he,hx⟩ := smooth_injective_derivative_local_chart_general F hF x (hder x x.property.2)
    have hm : map F (𝓝 x.val) = 𝓝 (F x.val) := by
      simpa only [he] using e.map_nhds_eq hx
    have hs : map (fun x : U => (x : E)) (𝓝 x) = 𝓝 (x : E) :=
      hU.isOpenEmbedding_subtypeVal.map_nhds_eq x
    change 𝓝 (F x.val) ≤ map (fun z : U => F z.val) (𝓝 x)
    rw [show (fun z : U => F z.val) = F ∘ Subtype.val from rfl,← map_map,hs,hm]
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hUi.toPartialEquiv F U) hF.continuous.continuousOn hopen hU
  have he : (e : E → E) = F := rfl
  refine ⟨e,he,fun x hx => ⟨hSO hx,hSW hx⟩,inter_subset_right,?_⟩
  intro y hy
  have hp : e.symm y ∈ W := (e.map_target hy).2
  let A : E ≃L[ℝ] E := (LinearEquiv.ofBijective (fderiv ℝ F (e.symm y)).toLinearMap
    ⟨hder _ hp,LinearMap.injective_iff_surjective.mp (hder _ hp)⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt e (A : E →L[ℝ] E) (e.symm y) := (hF.differentiable (by simp) _).hasFDerivAt
  exact e.contDiffAt_symm hy hd hF.contDiffAt

end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
lemma autonomous_flow_add (X : V → V) (hX : ContDiff ℝ ∞ X) (hcX : HasCompactSupport X)
    (ψ : ℝ → V → V) (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) :
    ∀ t s y, ψ (t+s) y = ψ t (ψ s y) := by
  have hX' : ContDiff ℝ ∞ (fun p : ℝ × V => X p.2) := hX.comp contDiff_snd
  have hsupp : ∃ C : Set V, IsCompact C ∧ ∀ (t : ℝ) y, y ∉ C → X y = 0 :=
    ⟨tsupport X,hcX,fun _ _ hy => image_eq_zero_of_notMem_tsupport hy⟩
  intro t s y
  have hshift : (fun r => ψ (r+s) y) 0 = ψ s y ∧
      ∀ r, HasDerivAt (fun v => ψ (v+s) y) (X (ψ (r+s) y)) r := by
    refine ⟨by simp,?_⟩
    intro r
    have harg : HasDerivAt (fun v : ℝ => v+s) (1:ℝ) r := by
      convert! (hasDerivAt_id (𝕜 := ℝ) r).add_const s using 1
    convert! (hd (r+s) y).scomp r harg using 1 <;> simp
  have he : (fun r => ψ (r+s) y) = fun r => ψ r (ψ s y) :=
    (FlowCalculus.exists_unique_global_trajectory_of_compact_support (fun _ z => X z) hX' hsupp 0 (ψ s y)).unique
      hshift ⟨h0 _,fun r => hd r _⟩
  exact congrFun he t

lemma autonomous_flow_neg (X : V → V) (hX : ContDiff ℝ ∞ X) (hcX : HasCompactSupport X)
    (ψ : ℝ → V → V) (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) :
    ∀ t y, ψ (-t) (ψ t y) = y := by
  intro t y
  simpa [h0] using (autonomous_flow_add X hX hcX ψ h0 hd (-t) t y).symm


def flowCollar (ψ : ℝ → V → V) (y : V) : V := ψ (y 2) (center y)

lemma flowCollar_contDiff (ψ : ℝ → V → V) (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2)) :
    ContDiff ℝ ∞ (flowCollar ψ) := hψ.comp ((contDiff_apply ℝ ℝ 2).prodMk center.contDiff)

lemma autonomous_flow_transports_field (X : V → V) (hX : ContDiff ℝ ∞ X) (hcX : HasCompactSupport X)
    (ψ : ℝ → V → V) (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y) (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) :
    ∀ t y, fderiv ℝ (ψ t) y (X y) = X (ψ t y) := by
  intro t y
  have hs : ContDiff ℝ ∞ (ψ t) := hψ.comp (contDiff_const.prodMk contDiff_id :
    ContDiff ℝ ∞ (fun z : V => (t,z)))
  have harg : HasDerivAt (fun s : ℝ => t+s) (1:ℝ) 0 := by
    convert! (hasDerivAt_id (𝕜 := ℝ) 0).const_add t using 1
  have hleft := (hd (t+0) y).scomp 0 harg
  have hright := (hs.differentiable (by simp) (ψ 0 y)).hasFDerivAt.comp_hasDerivAt 0 (hd 0 y)
  have he : (fun s => ψ (t+s) y) = fun s => ψ t (ψ s y) :=
    funext fun s => autonomous_flow_add X hX hcX ψ h0 hd t s y
  change HasDerivAt (fun s => ψ (t+s) y) _ 0 at hleft
  rw [he] at hleft
  have hh := hleft.unique hright
  simpa [h0] using hh.symm

lemma flowCollar_fderiv (X : V → V) (ψ : ℝ → V → V)
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) (y v : V) :
    fderiv ℝ (flowCollar ψ) y v =
      v 2 • X (flowCollar ψ y)+fderiv ℝ (ψ (y 2)) (center y) (center v) := by
  let t := y 2
  let x := center y
  let D := fderiv ℝ (fun p : ℝ × V => ψ p.1 p.2) (t,x)
  have hJ := (hψ.differentiable (by simp) (t,x)).hasFDerivAt
  have hT := hJ.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have ht : D (1,0) = X (ψ t x) := hT.unique (hd t x)
  have hsp := hJ.comp x ((hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
  have hspace : ∀ w : V, D (0,w) = fderiv ℝ (ψ t) x w := by
    intro w
    have hh := congrArg (fun L : V →L[ℝ] V => L w) hsp.fderiv
    exact hh.symm
  have hF := hJ.comp y ((ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ).hasFDerivAt.prodMk center.hasFDerivAt)
  change HasFDerivAt (flowCollar ψ) _ y at hF
  rw [hF.fderiv]
  change D (v 2,center v) = _
  have hp : (v 2,center v) = v 2 • ((1:ℝ),(0:V))+(0,center v) := by ext <;> simp
  rw [hp,map_add,map_smul,ht,hspace]
  rfl


lemma transverse_flowCollar_derivative
    (X : V → V) (hX : ContDiff ℝ ∞ X) (hcX : HasCompactSupport X)
    (ψ : ℝ → V → V) (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t)
    (y : V) (hn : X (center y) 2 ≠ 0) :
    Injective (fderiv ℝ (flowCollar ψ) y) := by
  have hinj := FlowCalculus.smooth_flow_spatial_derivative_injective (fun _ z => X z) ψ
    (hX.comp contDiff_snd) hψ h0 hd (y 2) (center y)
  have htrans := autonomous_flow_transports_field X hX hcX ψ hψ h0 hd (y 2) (center y)
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  rw [flowCollar_fderiv X ψ hψ hd] at hv
  have he : fderiv ℝ (ψ (y 2)) (center y) (center v+v 2 • X (center y)) = 0 := by
    rw [map_add,map_smul,htrans]
    simpa only [flowCollar,add_comm] using hv
  have hk : center v+v 2 • X (center y) = 0 := hinj (by simpa only [map_zero] using he)
  have hz : v 2 = 0 := by
    have hh := congrFun hk 2
    change center v 2+v 2*X (center y) 2 = 0 at hh
    simp only [center_two,zero_add] at hh
    exact (mul_eq_zero.mp hh).resolve_right hn
  simp only [hz,zero_smul,add_zero] at hk
  ext i
  fin_cases i
  · simpa using congrFun hk 0
  · simpa using congrFun hk 1
  · exact hz


end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma parameter_lift_derivative_injective (f : ℝ → V → V)
    (hf : ContDiff ℝ ∞ (fun p : ℝ × V => f p.1 p.2))
    (s : ℝ) (y : V) (hi : Injective (fderiv ℝ (f s) y)) :
    Injective (fderiv ℝ (fun p : ℝ × V => (p.1,f p.1 p.2)) (s,y)) := by
  let J : (ℝ × V) → V := fun p => f p.1 p.2
  have hJ := (hf.differentiable (by simp) (s,y)).hasFDerivAt
  have hF := (hasFDerivAt_fst (𝕜 := ℝ) (p := (s,y))).prodMk hJ
  have hsp := hJ.comp y ((hasFDerivAt_const (𝕜 := ℝ) s y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y))
  have hspace (v : V) : fderiv ℝ J (s,y) (0,v)=fderiv ℝ (f s) y v := by
    have hh := congrArg (fun D : V →L[ℝ] V => D v) hsp.fderiv
    exact hh.symm
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  rw [hF.fderiv] at hv
  have hfst : v.1=0 := congrArg Prod.fst hv
  have hsnd : fderiv ℝ J (s,y) v=0 := congrArg Prod.snd hv
  have hvp : v=(0,v.2) := Prod.ext hfst rfl
  rw [hvp,hspace] at hsnd
  have hv2 : v.2=0 := hi (by simpa only [map_zero] using hsnd)
  exact Prod.ext hfst hv2

theorem exists_contact_collar_family (u : P → ℝ) (β : P → P)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β)
    (X : ℝ → V → V) (μ : ℝ → V → ℝ)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hμ : ContDiff ℝ ∞ (fun p : ℝ × V => μ p.1 p.2))
    (C W : Set V) (hC : IsCompact C) (hc : ∀ s y, y ∉ C → X s y=0)
    (hW : IsOpen W) (hDW : surfaceDisk ⊆ W)
    (hLie : ∀ s y v, lieDerivOneForm (X s) (fun z => covector (invariantCoefficients u β z)) y v=
      μ s y*covector (invariantCoefficients u β y) v)
    (hplane : ∀ s y, y ∈ W → y 2=0 → X s y 2=1 ∧
      covector (invariantCoefficients u β y) (X s y)=u (xyMap y)) :
    ∃ f : ℝ → V → V, ∃ lam : ℝ → V → ℝ, ∃ N : Set V,
    ∃ E : OpenPartialHomeomorph (ℝ × V) (ℝ × V),
      ContDiff ℝ ∞ (fun p : ℝ × V => f p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) ∧
      (∀ s y, 0 < lam s y) ∧ IsOpen N ∧ surfaceDisk ⊆ N ∧
      (∀ y ∈ N, center y ∈ W) ∧
      (E : (ℝ × V) → (ℝ × V))=(fun p => (p.1,f p.1 p.2)) ∧
      Icc (0:ℝ) 1 ×ˢ N ⊆ E.source ∧
      (∀ p ∈ E.target, ContDiffAt ℝ ∞ E.symm p) ∧
      (∀ s y, y 2=0 → f s y=y) ∧
      ∀ s ∈ Icc (0:ℝ) 1,
        (∀ y ∈ N, Injective (fderiv ℝ (f s) y)) ∧
        (∀ y ∈ N, ∀ v, covector (invariantCoefficients u β (f s y)) (fderiv ℝ (f s) y v)=
          lam s y*covector (invariantCoefficients u β y) v) ∧
        ∀ y, y 2=0 → ∀ (t : ℝ), HasDerivAt (fun r : ℝ => f s (y+r • (Pi.single 2 1 : V)))
          (X s (f s (y+t • (Pi.single 2 1 : V)))) t := by
  let α : V → V →L[ℝ] ℝ := fun y => covector (invariantCoefficients u β y)
  have hα : ContDiff ℝ ∞ α := covector.contDiff.comp (invariantCoefficients_contDiff u β hu hβ)
  obtain ⟨ψ,ρ,Λ,hψ,hρ,hΛ,h0,hρψ,hψρ,hpos,hdata⟩ :=
    integrate_contact_field_family α hα X μ hX hμ ⟨C,hC,hc⟩ hLie
  let f : ℝ → V → V := fun s => flowCollar (ψ s)
  let lam : ℝ → V → ℝ := fun s y => Λ s (y 2) (center y)
  have harg : ContDiff ℝ ∞ (fun p : ℝ × V => (p.1,(p.2 2,center p.2))) := by fun_prop
  have hf : ContDiff ℝ ∞ (fun p : ℝ × V => f p.1 p.2) := hψ.comp harg
  have hlam : ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) := hΛ.comp harg
  have hfix (s : ℝ) (y : V) (hy : y 2=0) : f s y=y := by
    simp only [f,flowCollar,hy,h0,center_apply]
    ext i
    fin_cases i <;> simp [hy]
  have hfs (s : ℝ) : ContDiff ℝ ∞ (fun p : ℝ × V => ψ s p.1 p.2) :=
    hψ.comp (f := fun p : ℝ × V => (s,p)) (contDiff_const.prodMk contDiff_id)
  have hder (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (y : V) (hy : center y ∈ W) :
      Injective (fderiv ℝ (f s) y) := by
    have hXs : ContDiff ℝ ∞ (X s) := hX.comp (f := fun z : V => (s,z)) (contDiff_const.prodMk contDiff_id)
    have hcX : HasCompactSupport (X s) := HasCompactSupport.intro hC (hc s)
    exact transverse_flowCollar_derivative (X s) hXs hcX (ψ s) (hfs s) (h0 s) (hdata s hs).1 y
      (by rw [(hplane s (center y) hy (center_two y)).1]; norm_num)
  let F : (ℝ × V) → (ℝ × V) := fun p => (p.1,f p.1 p.2)
  have hF : ContDiff ℝ ∞ F := contDiff_fst.prodMk hf
  let S : Set (ℝ × V) := Icc (0:ℝ) 1 ×ˢ surfaceDisk
  have hS : IsCompact S := isCompact_Icc.prod surfaceDisk_compact
  have hcent (y : V) (hy : y ∈ surfaceDisk) : center y=y := by
    rw [center_apply]
    ext i
    fin_cases i <;> simp [hy.2]
  have hFS : ∀ p ∈ S, F p=p := by
    intro p hp
    exact Prod.ext rfl (hfix _ _ hp.2.2)
  have hiS : InjOn F S := by
    intro p hp q hq heq
    simpa only [hFS p hp,hFS q hq] using heq
  let U : Set (ℝ × V) := {p | IsUnit (fderiv ℝ F p)}
  have hDF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hU : IsOpen U := Units.isOpen.preimage hDF.continuous
  have hSU : S ⊆ U := by
    intro p hp
    have hh := parameter_lift_derivative_injective f hf p.1 p.2
      (hder p.1 hp.1 p.2 (by rw [hcent p.2 hp.2]; exact hDW hp.2))
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hh,LinearMap.injective_iff_surjective.mp hh⟩
  obtain ⟨E,hE,hSE,hEU,hR⟩ := compact_smooth_embedding_chart_general F hF S U hS hU hSU hiS
    (fun p hp => (ContinuousLinearMap.isUnit_iff_bijective.mp hp).1)
  obtain ⟨A,B,hA,hB,hIA,hDB,hAB⟩ := generalized_tube_lemma isCompact_Icc surfaceDisk_compact E.open_source hSE
  let N := B ∩ center ⁻¹' W
  have hN : IsOpen N := hB.inter (hW.preimage center.continuous)
  have hDN : surfaceDisk ⊆ N := fun y hy => ⟨hDB hy,by change center y ∈ W; rw [hcent y hy]; exact hDW hy⟩
  refine ⟨f,lam,N,E,hf,hlam,fun s y => hpos _ _ _,hN,hDN,fun _ hy => hy.2,hE,?_,hR,hfix,?_⟩
  · intro p hp
    exact hAB ⟨hIA hp.1,hp.2.1⟩
  · intro s hs
    refine ⟨fun y hy => hder s hs y hy.2,?_,?_⟩
    · intro y hy v
      obtain ⟨hd,hpb,hH⟩ := hdata s hs
      rw [flowCollar_fderiv (X s) (ψ s) (hfs s) hd,map_add,map_smul]
      change v 2*α (flowCollar (ψ s) y) (X s (flowCollar (ψ s) y))+
        α (ψ s (y 2) (center y)) (fderiv ℝ (ψ s (y 2)) (center y) (center v))=_
      rw [hpb]
      have hH' := hH (y 2) (center y)
      change α (flowCollar (ψ s) y) (X s (flowCollar (ψ s) y))=_ at hH'
      rw [hH',(hplane s (center y) hy.2 (center_two y)).2]
      simp [α,lam,covector_apply,dot,invariantCoefficients]
      ring
    · intro y hy t
      have heq (r : ℝ) : f s (y+r • (Pi.single 2 1 : V))=ψ s r y := by
        have ht : (y+r • (Pi.single 2 1 : V)) 2=r := by simp [hy]
        have hc' : center (y+r • (Pi.single 2 1 : V))=y := by
          rw [center_apply]
          ext i
          fin_cases i <;> simp [hy]
        simp only [f,flowCollar,ht,hc']
      simpa only [heq] using (hdata s hs).1 t y


end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma center_add_normal (y : V) : center y+y 2 • (Pi.single 2 1 : V)=y := by
  ext i
  fin_cases i <;> simp [center]

theorem collar_endpoints_near_disk
    (e : OpenPartialHomeomorph V V) (he : ContDiffOn ℝ ∞ (e : V → V) e.source)
    (hD : surfaceDisk ⊆ e.source) (hfix : ∀ y ∈ e.source, y 2=0 → e y=y)
    (X f : ℝ → V → V) (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (C W : Set V) (hC : IsCompact C) (hc : ∀ s y, y ∉ C → X s y=0)
    (hW : IsOpen W) (hDW : surfaceDisk ⊆ W)
    (hAgree : ∀ s, ∀ y ∈ W, X s y=(1-s) • (Pi.single 2 1 : V)+
      s • fderiv ℝ (e : V → V) (e.symm y) (Pi.single 2 1))
    (hf : ∀ s y, y 2=0 → f s y=y)
    (hODE : ∀ s ∈ Icc (0:ℝ) 1, ∀ y, y 2=0 → ∀ (t : ℝ),
      HasDerivAt (fun r : ℝ => f s (y+r • (Pi.single 2 1 : V))) (X s (f s (y+t • (Pi.single 2 1 : V)))) t) :
    ∃ N : Set V, IsOpen N ∧ surfaceDisk ⊆ N ∧ N ⊆ e.source ∧
      ∀ y ∈ N, f 0 y=y ∧ f 1 y=e y := by
  let T := W ∩ (e.source ∩ e ⁻¹' W)
  have hT : IsOpen T := hW.inter (e.isOpen_inter_preimage hW)
  have hDT : surfaceDisk ⊆ T := by
    intro y hy
    refine ⟨hDW hy,hD hy,?_⟩
    change e y ∈ W
    rw [hfix y (hD hy) hy.2]
    exact hDW hy
  let J : (V × ℝ) → V := fun p => center p.1+p.2 • (Pi.single 2 1 : V)
  have hJ : Continuous J := (center.continuous.comp continuous_fst).add (continuous_snd.smul continuous_const)
  have hDT0 : surfaceDisk ×ˢ ({0}:Set ℝ) ⊆ J ⁻¹' T := by
    rintro ⟨y,t⟩ ⟨hy,ht⟩
    change y ∈ surfaceDisk at hy
    have hy0 : y 2=0 := hy.2
    have ht0 : t=0 := ht
    have hc' : center y=y := by
      ext i
      fin_cases i <;> simp [center,hy0]
    change center y+t • (Pi.single 2 1 : V) ∈ T
    rw [ht0,zero_smul,add_zero,hc']
    exact hDT hy
  obtain ⟨A,B,hA,hB,hDA,h0B,hAB⟩ := generalized_tube_lemma surfaceDisk_compact isCompact_singleton
    (hT.preimage hJ) hDT0
  have hzB : (0:ℝ) ∈ B := h0B (by simp)
  obtain ⟨δ,hδ,hδB⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds hzB)
  let N : Set V := {y | center y ∈ A ∧ |y 2| < δ}
  have hN : IsOpen N := (hA.preimage center.continuous).inter
    (isOpen_lt ((continuous_apply 2).abs) continuous_const)
  have hDN : surfaceDisk ⊆ N := by
    intro y hy
    have hc' : center y=y := by
      ext i
      fin_cases i <;> simp [center,hy.2]
    exact ⟨by rw [hc']; exact hDA hy,by simpa only [hy.2,abs_zero] using hδ⟩
  have hstrip (y : V) (hy : y ∈ N) (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
      center y+t • (Pi.single 2 1 : V) ∈ T := by
    have htB : t ∈ B := hδB (by simpa [Metric.mem_ball,Real.dist_eq,abs_lt] using ht)
    have hh := hAB (show (center y,t) ∈ A ×ˢ B from ⟨hy.1,htB⟩)
    change center (center y)+t • (Pi.single 2 1 : V) ∈ T at hh
    have hcc : center (center y)=center y := by simp [center_apply]
    simpa only [J,hcc] using hh
  have hNS : N ⊆ e.source := by
    intro y hy
    have ht : y 2 ∈ Ioo (-δ) δ := abs_lt.mp hy.2
    have hh := (hstrip y hy (y 2) ht).2.1
    simpa only [center_add_normal] using hh
  obtain ⟨K,hK⟩ := FlowCalculus.uniform_spatial_lipschitz_of_compact_support X hX ⟨C,hC,hc⟩ 0 1
  have hlin (p : V) (t : ℝ) : HasDerivAt (fun r : ℝ => p+r • (Pi.single 2 1 : V)) (Pi.single 2 1 : V) t := by
    convert! (hasDerivAt_const t p).add ((hasDerivAt_id t).smul_const (Pi.single 2 1 : V)) using 1 <;> simp
  have hX0 (z : V) (hz : z ∈ W) : X 0 z=Pi.single 2 1 := by simpa using hAgree 0 z hz
  have hX1 (z : V) (hz : z ∈ T) : X 1 (e z)=fderiv ℝ (e : V → V) z (Pi.single 2 1) := by
    have hh := hAgree 1 (e z) hz.2.2
    simpa only [sub_self,zero_smul,one_smul,zero_add,e.left_inv hz.2.1] using hh
  refine ⟨N,hN,hDN,hNS,?_⟩
  intro y hy
  let p := center y
  have hp : p 2=0 := center_two y
  have hzero : (0:ℝ) ∈ Ioo (-δ) δ := by constructor <;> linarith
  have hpt : p ∈ T := by simpa only [zero_smul,add_zero] using hstrip y hy 0 hzero
  have hfg0 : f 0 p=p := hf 0 p hp
  have hfg1 : f 1 p=p := hf 1 p hp
  have hep : e p=p := hfix p hpt.2.1 hp
  have heq0 : EqOn (fun t => f 0 (p+t • (Pi.single 2 1 : V)))
      (fun t => p+t • (Pi.single 2 1 : V)) (Ioo (-δ) δ) := by
    apply ODE_solution_unique_of_mem_Ioo (v := fun _ => X 0) (s := fun _ => Set.univ)
      (fun _ _ => (hK 0 (by simp)).lipschitzOnWith) hzero
    · intro t ht
      exact ⟨hODE 0 (by simp) p hp t,mem_univ _⟩
    · intro t ht
      refine ⟨?_,mem_univ _⟩
      rw [hX0 _ (hstrip y hy t ht).1]
      exact hlin p t
    · simpa only [zero_smul,add_zero] using hfg0
  have heq1 : EqOn (fun t => f 1 (p+t • (Pi.single 2 1 : V)))
      (fun t => e (p+t • (Pi.single 2 1 : V))) (Ioo (-δ) δ) := by
    apply ODE_solution_unique_of_mem_Ioo (v := fun _ => X 1) (s := fun _ => Set.univ)
      (fun _ _ => (hK 1 (by simp)).lipschitzOnWith) hzero
    · intro t ht
      exact ⟨hODE 1 (by simp) p hp t,mem_univ _⟩
    · intro t ht
      refine ⟨?_,mem_univ _⟩
      rw [hX1 _ (hstrip y hy t ht)]
      have hEp := he.contDiffAt (e.open_source.mem_nhds (hstrip y hy t ht).2.1)
      exact (hEp.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hlin p t)
    · simpa only [zero_smul,add_zero,hep] using hfg1
  have ht : y 2 ∈ Ioo (-δ) δ := abs_lt.mp hy.2
  exact ⟨by simpa only [p,center_add_normal] using heq0 ht,
    by simpa only [p,center_add_normal] using heq1 ht⟩

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma inverse_contact_pullback (α : V → V →L[ℝ] ℝ) (F G : V → V)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (hFG : ∀ y, F (G y)=y)
    (L : V → ℝ) (hpos : ∀ y, 0 < L y)
    (hpb : ∀ y v, α (F y) (fderiv ℝ F y v)=L y*α y v) :
    ∀ y v, α (G y) (fderiv ℝ G y v)=(L (G y))⁻¹*α y v := by
  intro y v
  have heq : F ∘ G=id := funext hFG
  have hd := fderiv_comp y (hF.differentiable (by simp) _) (hG.differentiable (by simp) y)
  rw [heq] at hd
  have hv : fderiv ℝ F (G y) (fderiv ℝ G y v)=v := by
    have hh := congrArg (fun D : V →L[ℝ] V => D v) hd
    simpa using hh.symm
  have hp := hpb (G y) (fderiv ℝ G y v)
  rw [hFG,hv] at hp
  have hn := (hpos (G y)).ne'
  apply (eq_inv_mul_iff_mul_eq₀ hn).mpr
  exact hp.symm


end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem collar_stationary_near_compact (X f : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (C : Set V) (hC : IsCompact C) (hc : ∀ s y, y ∉ C → X s y=0)
    (B S : Set V) (hB : IsOpen B) (hS : IsCompact S) (hSB : S ⊆ B)
    (hSplane : ∀ y ∈ S, y 2=0)
    (hvertical : ∀ s, ∀ y ∈ B, X s y=Pi.single 2 1)
    (hf : ∀ s y, y 2=0 → f s y=y)
    (hODE : ∀ s ∈ Icc (0:ℝ) 1, ∀ y, y 2=0 → ∀ (t : ℝ),
      HasDerivAt (fun r : ℝ => f s (y+r • (Pi.single 2 1 : V)))
        (X s (f s (y+t • (Pi.single 2 1 : V)))) t) :
    ∃ V0 : Set V, IsOpen V0 ∧ S ⊆ V0 ∧ V0 ⊆ B ∧
      ∀ s ∈ Icc (0:ℝ) 1, ∀ y ∈ V0, f s y=y := by
  let J : (V × ℝ) → V := fun p => center p.1+p.2 • (Pi.single 2 1 : V)
  have hJ : Continuous J := (center.continuous.comp continuous_fst).add (continuous_snd.smul continuous_const)
  have hS0 : S ×ˢ ({0}:Set ℝ) ⊆ J ⁻¹' B := by
    rintro ⟨y,t⟩ ⟨hy,ht⟩
    change y ∈ S at hy
    have hy0 := hSplane y hy
    have ht0 : t=0 := ht
    have hcent : center y=y := by ext i; fin_cases i <;> simp [center,hy0]
    change center y+t • (Pi.single 2 1 : V) ∈ B
    rw [ht0,zero_smul,add_zero,hcent]
    exact hSB hy
  obtain ⟨A,T,hA,hT,hSA,h0T,hAT⟩ := generalized_tube_lemma hS isCompact_singleton (hB.preimage hJ) hS0
  have hzT : (0:ℝ) ∈ T := h0T (by simp)
  obtain ⟨δ,hδ,hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds hzT)
  let V0 : Set V := {y | center y ∈ A ∧ |y 2| < δ}
  have hV0 : IsOpen V0 := (hA.preimage center.continuous).inter
    (isOpen_lt (continuous_apply 2).abs continuous_const)
  have hSV0 : S ⊆ V0 := by
    intro y hy
    have hy0 := hSplane y hy
    have hcent : center y=y := by ext i; fin_cases i <;> simp [center,hy0]
    exact ⟨by rw [hcent]; exact hSA hy,by simpa only [hy0,abs_zero] using hδ⟩
  have hstrip (y : V) (hy : y ∈ V0) (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
      center y+t • (Pi.single 2 1 : V) ∈ B := by
    have htT : t ∈ T := hδT (by simpa [Metric.mem_ball,Real.dist_eq,abs_lt] using ht)
    have hh := hAT (show (center y,t) ∈ A ×ˢ T from ⟨hy.1,htT⟩)
    change center (center y)+t • (Pi.single 2 1 : V) ∈ B at hh
    have hcc : center (center y)=center y := by simp [center_apply]
    simpa only [hcc] using hh
  have hV0B : V0 ⊆ B := by
    intro y hy
    have hh := hstrip y hy (y 2) (abs_lt.mp hy.2)
    simpa only [center_add_normal] using hh
  obtain ⟨L,hL⟩ := FlowCalculus.uniform_spatial_lipschitz_of_compact_support X hX ⟨C,hC,hc⟩ 0 1
  refine ⟨V0,hV0,hSV0,hV0B,?_⟩
  intro s hs y hy
  let p := center y
  have hp : p 2=0 := center_two y
  have hzero : (0:ℝ) ∈ Ioo (-δ) δ := by constructor <;> linarith
  have hlin (t : ℝ) : HasDerivAt (fun r : ℝ => p+r • (Pi.single 2 1 : V)) (Pi.single 2 1 : V) t := by
    convert! (hasDerivAt_const t p).add ((hasDerivAt_id t).smul_const (Pi.single 2 1 : V)) using 1 <;> simp
  have heq : EqOn (fun t => f s (p+t • (Pi.single 2 1 : V)))
      (fun t => p+t • (Pi.single 2 1 : V)) (Ioo (-δ) δ) := by
    apply ODE_solution_unique_of_mem_Ioo (v := fun _ => X s) (s := fun _ => Set.univ)
      (fun _ _ => (hL s hs).lipschitzOnWith) hzero
    · intro t ht
      exact ⟨hODE s hs p hp t,mem_univ _⟩
    · intro t ht
      refine ⟨?_,mem_univ _⟩
      rw [hvertical s _ (hstrip y hy t ht)]
      exact hlin t
    · simpa only [zero_smul,add_zero] using hf s p hp
  simpa only [p,center_add_normal] using heq (abs_lt.mp hy.2)

end
end ContactTopology.ConvexDeformation


open Set Filter Topology
open scoped ContDiff

theorem ContactTopology.relative_disk_contact_embedding_family_internal
    (u : (Fin 2 → ℝ) → ℝ) (β : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β)
    (hQ : ∀ x, β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
      u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0) ≠ 0)
    (e : OpenPartialHomeomorph (Fin 3 → ℝ) (Fin 3 → ℝ))
    (he : ContDiffOn ℝ ∞ (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) e.source)
    (hG : ContDiffOn ℝ ∞ (e.symm : (Fin 3 → ℝ) → (Fin 3 → ℝ)) e.target)
    (hD : {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ e.source)
    (hfix : ∀ y ∈ e.source, y 2=0 → e y=y)
    (L : (Fin 3 → ℝ) → ℝ) (hL : ContDiffOn ℝ ∞ L e.source)
    (hpositive : ∀ y ∈ e.source, 0 < L y)
    (S Brel : Set (Fin 3 → ℝ)) (hS : IsCompact S)
    (hSD : S ⊆ {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0})
    (hBrel : IsOpen Brel) (hSB : S ⊆ Brel) (hBe : Brel ⊆ e.source)
    (hBfix : ∀ y ∈ Brel, e y=y)
    (U : Set (Fin 3 → ℝ)) (hU : IsOpen U)
    (hDU : {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ U) :
    let A : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y => ![β ![y 0,y 1] 0,β ![y 0,y 1] 1,u ![y 0,y 1]]
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun a v => a 0*v 0+a 1*v 1+a 2*v 2
    (∀ y ∈ e.source, ∀ v, B (A (e y)) (fderiv ℝ (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) y v)=L y*B (A y) v) →
    ∃ f : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ), ∃ lam : ℝ → (Fin 3 → ℝ) → ℝ,
    ∃ N : Set (Fin 3 → ℝ),
    ∃ E : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ)), ∃ V0 : Set (Fin 3 → ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => f p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => lam p.1 p.2) ∧
      (∀ s y, 0 < lam s y) ∧ IsOpen N ∧
      {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ N ∧ N ⊆ e.source ∧
      (E : (ℝ × (Fin 3 → ℝ)) → (ℝ × (Fin 3 → ℝ)))=(fun p => (p.1,f p.1 p.2)) ∧
      Icc (0:ℝ) 1 ×ˢ N ⊆ E.source ∧
      (∀ p ∈ E.target, ContDiffAt ℝ ∞ E.symm p) ∧
      (∀ s y, y 2=0 → f s y=y) ∧
      (∀ y ∈ N, f 0 y=y ∧ f 1 y=e y) ∧
      IsOpen V0 ∧ S ⊆ V0 ∧ V0 ⊆ N ∧ (∀ s ∈ Icc (0:ℝ) 1, ∀ y ∈ V0, f s y=y) ∧
      ∀ s ∈ Icc (0:ℝ) 1,
        (∀ y ∈ N, f s y ∈ U) ∧
        (∀ y ∈ N, Function.Injective (fderiv ℝ (f s) y)) ∧
        (∀ y ∈ N, ∀ z ∈ N, f s y=f s z → y=z) ∧
        ∀ y ∈ N, ∀ v, B (A (f s y)) (fderiv ℝ (f s) y v)=lam s y*B (A y) v := by


  dsimp only
  intro hpb
  obtain ⟨X,μ,C,W,hX,hμ,hC,hc,hW,hDW,hWE,hLie,hAgree,hplane⟩ :=
    ContactTopology.local_fixed_surface_contact_field_homotopy u β hu hβ hQ e he hG hD hfix L hL hpositive hpb
  let a := ContactTopology.ConvexDeformation.invariantCoefficients u β
  have ha := ContactTopology.ConvexDeformation.invariantCoefficients_contDiff u β hu hβ
  have hcoef : a = (fun y : Fin 3 → ℝ => ![β ![y 0,y 1] 0,β ![y 0,y 1] 1,u ![y 0,y 1]]) := by
    funext y
    simp only [a,ContactTopology.ConvexDeformation.invariantCoefficients,
      ContactTopology.ConvexDeformation.xyMap_apply]
  have hLie' : ∀ s y v, GrayStability.lieDerivOneForm (X s)
      (fun z => ContactTopology.ConvexDeformation.covector (a z)) y v=
      μ s y*ContactTopology.ConvexDeformation.covector (a y) v := by
    intro s y v
    have hd := ContactTopology.ConvexDeformation.covector.hasFDerivAt.comp y (ha.differentiable (by simp) y).hasFDerivAt
    change HasFDerivAt (fun z => ContactTopology.ConvexDeformation.covector (a z)) _ y at hd
    unfold GrayStability.lieDerivOneForm
    rw [hd.fderiv]
    change ContactTopology.ConvexDeformation.covector (fderiv ℝ a y (X s y)) v+
      ContactTopology.ConvexDeformation.covector (a y) (fderiv ℝ (X s) y v)=
      μ s y*ContactTopology.ConvexDeformation.covector (a y) v
    rw [hcoef]
    simpa only [ContactTopology.ConvexDeformation.covector_apply,ContactTopology.ConvexDeformation.dot] using hLie s y v
  have hplane' : ∀ s y, y ∈ W → y 2=0 → X s y 2=1 ∧
      ContactTopology.ConvexDeformation.covector (a y) (X s y)=u (ContactTopology.ConvexDeformation.xyMap y) := by
    intro s y hy hy0
    simpa only [hcoef,ContactTopology.ConvexDeformation.xyMap_apply,
      ContactTopology.ConvexDeformation.covector_apply,ContactTopology.ConvexDeformation.dot] using hplane s y hy hy0
  obtain ⟨f,lam,N0,E,hf,hlam,hpos,hN0,hDN0,hcenter,hE,hEN0,hR,hfplane,hdata⟩ :=
    ContactTopology.ConvexDeformation.exists_contact_collar_family u β hu hβ X μ hX hμ C W hC hc hW hDW hLie' hplane'
  have hvertical : ∀ s, ∀ z ∈ Brel ∩ W, X s z=Pi.single 2 1 := by
    intro s z hz
    have hEz : e z=z := hBfix z hz.1
    have hGz : e.symm z=z := by
      have hh := e.left_inv (hBe hz.1)
      simpa only [hEz] using hh
    have hgerm : (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) =ᶠ[𝓝 z] id := by
      filter_upwards [hBrel.mem_nhds hz.1] with q hq
      exact hBfix q hq
    rw [hAgree s z hz.2,hGz,hgerm.fderiv_eq]
    ext i
    fin_cases i <;> simp <;> ring
  obtain ⟨V2,hV2,hSV2,hV2BW,hV2fix⟩ := ContactTopology.ConvexDeformation.collar_stationary_near_compact
    X f hX C hC hc (Brel ∩ W) S (hBrel.inter hW) hS
    (fun z hz => ⟨hSB hz,hDW (hSD hz)⟩) (fun z hz => (hSD hz).2) hvertical hfplane
    (fun s hs => (hdata s hs).2.2)
  obtain ⟨N1,hN1,hDN1,hN1e,hend⟩ := ContactTopology.ConvexDeformation.collar_endpoints_near_disk
    e he hD hfix X f hX C W hC hc hW hDW hAgree hfplane (fun s hs => (hdata s hs).2.2)
  have hSU : Icc (0:ℝ) 1 ×ˢ ContactTopology.ConvexDeformation.surfaceDisk ⊆
      (fun p : ℝ × (Fin 3 → ℝ) => f p.1 p.2) ⁻¹' U := by
    intro p hp
    change f p.1 p.2 ∈ U
    rw [hfplane p.1 p.2 hp.2.2]
    exact hDU hp.2
  obtain ⟨A2,B2,hA2,hB2,hIA2,hDB2,hAB2⟩ := generalized_tube_lemma isCompact_Icc
    ContactTopology.ConvexDeformation.surfaceDisk_compact (hU.preimage hf.continuous) hSU
  let N := (N0 ∩ N1) ∩ B2
  have hN : IsOpen N := (hN0.inter hN1).inter hB2
  have hDN : ContactTopology.ConvexDeformation.surfaceDisk ⊆ N :=
    fun y hy => ⟨⟨hDN0 hy,hDN1 hy⟩,hDB2 hy⟩
  let V0 := V2 ∩ N
  refine ⟨f,lam,N,E,V0,hf,hlam,hpos,hN,hDN,
    fun y hy => hN1e hy.1.2,hE,?_,hR,hfplane,fun y hy => hend y hy.1.2,
    hV2.inter hN,fun y hy => ⟨hSV2 hy,hDN (hSD hy)⟩,inter_subset_right,
    fun s hs y hy => hV2fix s hs y hy.1,?_⟩
  · intro p hp
    exact hEN0 ⟨hp.1,hp.2.1.1⟩
  · intro s hs
    refine ⟨fun y hy => hAB2 (show (s,y) ∈ A2 ×ˢ B2 from ⟨hIA2 hs,hy.2⟩),
      fun y hy => (hdata s hs).1 y hy.1.1,?_,?_⟩
    · intro y hy z hz heq
      have hxy : E (s,y)=E (s,z) := by
        rw [hE]
        exact Prod.ext rfl heq
      have hh := E.injOn (show (s,y) ∈ E.source from hEN0 ⟨hs,hy.1.1⟩)
        (show (s,z) ∈ E.source from hEN0 ⟨hs,hz.1.1⟩) hxy
      exact congrArg Prod.snd hh
    · intro y hy v
      have hh := (hdata s hs).2.1 y hy.1.1 v
      simpa only [ContactTopology.ConvexDeformation.covector_apply,ContactTopology.ConvexDeformation.dot,
        ContactTopology.ConvexDeformation.invariantCoefficients,ContactTopology.ConvexDeformation.xyMap_apply] using hh


open Set
open scoped ContDiff

theorem solution
    (u : (Fin 2 → ℝ) → ℝ) (β : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β)
    (hQ : ∀ x, β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
      u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0) ≠ 0)
    (e : OpenPartialHomeomorph (Fin 3 → ℝ) (Fin 3 → ℝ))
    (he : ContDiffOn ℝ ∞ (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) e.source)
    (hG : ContDiffOn ℝ ∞ (e.symm : (Fin 3 → ℝ) → (Fin 3 → ℝ)) e.target)
    (hD : {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ e.source)
    (hfix : ∀ y ∈ e.source, y 2=0 → e y=y)
    (L : (Fin 3 → ℝ) → ℝ) (hL : ContDiffOn ℝ ∞ L e.source)
    (hpositive : ∀ y ∈ e.source, 0 < L y)
    (S Brel : Set (Fin 3 → ℝ)) (hS : IsCompact S)
    (hSD : S ⊆ {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0})
    (hBrel : IsOpen Brel) (hSB : S ⊆ Brel) (hBe : Brel ⊆ e.source)
    (hBfix : ∀ y ∈ Brel, e y=y)
    (U : Set (Fin 3 → ℝ)) (hU : IsOpen U)
    (hDU : {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ U) :
    let A : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y => ![β ![y 0,y 1] 0,β ![y 0,y 1] 1,u ![y 0,y 1]]
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun a v => a 0*v 0+a 1*v 1+a 2*v 2
    (∀ y ∈ e.source, ∀ v, B (A (e y)) (fderiv ℝ (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) y v)=L y*B (A y) v) →
    ∃ ψ ρ : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ), ∃ Λ : ℝ → (Fin 3 → ℝ) → ℝ,
    ∃ M C V0 : Set (Fin 3 → ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => Λ p.1 p.2) ∧
      IsOpen M ∧ {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ M ∧ M ⊆ e.source ∧
      IsCompact C ∧ C ⊆ U ∧ IsOpen V0 ∧ S ⊆ V0 ∧ Disjoint C V0 ∧
      (∀ t y, y ∈ V0 → ψ t y=y ∧ ρ t y=y) ∧ (∀ y, ψ 0 y=y) ∧
      (∀ t y, ρ t (ψ t y)=y) ∧ (∀ t y, ψ t (ρ t y)=y) ∧
      (∀ t y, y ∉ C → ψ t y=y) ∧ (∀ t y, 0 < Λ t y) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y v, B (A (ψ t y)) (fderiv ℝ (ψ t) y v)=Λ t y*B (A y) v) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y v, B (A (ρ t y)) (fderiv ℝ (ρ t) y v)=
        (Λ t (ρ t y))⁻¹*B (A y) v) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y, y 0^2+y 1^2 ≤ 1 → y 2=0 → ψ t y=y) ∧
      ∀ y ∈ M, ψ 1 y=e y ∧ ρ 1 (e y)=y := by


  dsimp only
  intro hpb
  obtain ⟨f,lam,N,E,V0,hf,hlam,hpos,hN,hDN,hNe,hE,hEN,hR,hplane,hend,hV0,hSV0,hV0N,hV0fixed,hdata⟩ :=
    ContactTopology.relative_disk_contact_embedding_family_internal u β hu hβ hQ e he hG hD hfix L hL hpositive S Brel hS hSD hBrel hSB hBe hBfix U hU hDU hpb
  let θ : ℝ → ℝ := Real.smoothTransition
  have hθ : ContDiff ℝ ∞ θ := Real.smoothTransition.contDiff
  have hθ01 (s : ℝ) : θ s ∈ Icc (0:ℝ) 1 := ⟨Real.smoothTransition.nonneg s,Real.smoothTransition.le_one s⟩
  have hθ0 : θ 0=0 := Real.smoothTransition.zero
  have hθ1 : θ 1=1 := Real.smoothTransition.one
  let g : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun s => f (θ s)
  let ell : ℝ → (Fin 3 → ℝ) → ℝ := fun s => lam (θ s)
  have harg : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => (θ p.1,p.2)) :=
    (hθ.comp contDiff_fst).prodMk contDiff_snd
  have hg : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => g p.1 p.2) := hf.comp harg
  have hell : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => ell p.1 p.2) := hlam.comp harg
  let a := ContactTopology.ConvexDeformation.invariantCoefficients u β
  have ha := ContactTopology.ConvexDeformation.invariantCoefficients_contDiff u β hu hβ
  have haQ (y : Fin 3 → ℝ) : ContactTopology.ConvexDeformation.dot (a y)
      (ContactTopology.ConvexDeformation.curlLinear (fderiv ℝ a y)) ≠ 0 := by
    rw [ContactTopology.ConvexDeformation.invariant_volume_formula u β hu hβ]
    exact hQ _
  have hpb' : ∀ s x, x ∈ N → ∀ v,
      ContactTopology.ConvexDeformation.covector (a (g s x)) (fderiv ℝ (g s) x v)=
        ell s x*ContactTopology.ConvexDeformation.covector (a x) v := by
    intro s x hx v
    simpa only [a,g,ell,ContactTopology.ConvexDeformation.invariantCoefficients,
      ContactTopology.ConvexDeformation.xyMap_apply,ContactTopology.ConvexDeformation.covector_apply,
      ContactTopology.ConvexDeformation.dot] using (hdata (θ s) (hθ01 s)).2.2.2 x hx v
  have hi : ∀ s, InjOn (g s) N := by
    intro s x hx z hz heq
    exact (hdata (θ s) (hθ01 s)).2.2.1 x hx z hz heq
  have hder : ∀ s x, x ∈ N → Function.Injective (fderiv ℝ (g s) x) := by
    intro s x hx
    exact (hdata (θ s) (hθ01 s)).2.1 x hx
  have hg0 : ∀ x ∈ N, g 0 x=x := by
    intro x hx
    simpa only [g,hθ0] using (hend x hx).1
  obtain ⟨K,hK,hDK,hKN⟩ := exists_compact_between ContactTopology.ConvexDeformation.surfaceDisk_compact hN hDN
  have htU : ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ K, g s x ∈ U := by
    intro s hs x hx
    exact (hdata (θ s) (hθ01 s)).1 x (hKN hx)
  have hgV0 : ∀ s y, y ∈ V0 → g s y=y := fun s y hy => hV0fixed (θ s) (hθ01 s) y hy
  have hQraw (y : Fin 3 → ℝ) :
      a y 0*(fderiv ℝ a y (Pi.single 1 1) 2-fderiv ℝ a y (Pi.single 2 1) 1)+
      a y 1*(fderiv ℝ a y (Pi.single 2 1) 0-fderiv ℝ a y (Pi.single 0 1) 2)+
      a y 2*(fderiv ℝ a y (Pi.single 0 1) 1-fderiv ℝ a y (Pi.single 1 1) 0) ≠ 0 := haQ y
  have hrawpb : ∀ s x, x ∈ N → ∀ v,
      a (g s x) 0*fderiv ℝ (g s) x v 0+a (g s x) 1*fderiv ℝ (g s) x v 1+a (g s x) 2*fderiv ℝ (g s) x v 2=
        ell s x*(a x 0*v 0+a x 1*v 1+a x 2*v 2) := by
    simpa only [ContactTopology.ConvexDeformation.covector_apply,ContactTopology.ConvexDeformation.dot] using hpb'
  obtain ⟨ψ,ρ,Λ,C,hψ,hρ,hΛ,hC,hCU,hψ0,hρψ,hψρ,hout,hΛpos,hcontactRaw,hmatch,hVfix⟩ :=
    ContactTopology.relative_compact_contact_embedding_isotopy_extension a ha g hg ell hell N hN hi hder hg0
      V0 hV0N hgV0 K U hK hKN hU htU hQraw (fun s x _ => hpos _ _) hrawpb
  have hcontact : ∀ t ∈ Icc (0:ℝ) 1, ∀ y v,
      ContactTopology.ConvexDeformation.covector (a (ψ t y)) (fderiv ℝ (ψ t) y v)=
        Λ t y*ContactTopology.ConvexDeformation.covector (a y) v := by
    simpa only [ContactTopology.ConvexDeformation.covector_apply,ContactTopology.ConvexDeformation.dot] using hcontactRaw
  let C0 := C \ V0
  have hC0 : IsCompact C0 := hC.diff hV0
  have hC0U : C0 ⊆ U := diff_subset.trans hCU
  have hdis : Disjoint C0 V0 := disjoint_sdiff_left
  have hVboth : ∀ t y, y ∈ V0 → ψ t y=y ∧ ρ t y=y := by
    intro t y hy
    refine ⟨hVfix t y hy,?_⟩
    have hh := hρψ t y
    rwa [hVfix t y hy] at hh
  have hout0 : ∀ t y, y ∉ C0 → ψ t y=y := by
    intro t y hy
    by_cases hyC : y ∈ C
    · have hyV : y ∈ V0 := by
        by_contra hn
        exact hy ⟨hyC,hn⟩
      exact hVfix t y hyV
    · exact hout t y hyC
  refine ⟨ψ,ρ,Λ,interior K,C0,V0,hψ,hρ,hΛ,isOpen_interior,hDK,interior_subset.trans (hKN.trans hNe),
    hC0,hC0U,hV0,hSV0,hdis,hVboth,hψ0,hρψ,hψρ,hout0,hΛpos,?_,?_,?_,?_⟩
  · intro t ht y v
    simpa only [a,ContactTopology.ConvexDeformation.invariantCoefficients,
      ContactTopology.ConvexDeformation.xyMap_apply,ContactTopology.ConvexDeformation.covector_apply,
      ContactTopology.ConvexDeformation.dot] using hcontact t ht y v
  · intro t ht y v
    have hψt : ContDiff ℝ ∞ (ψ t) := hψ.comp (f := fun z : Fin 3 → ℝ => (t,z)) (contDiff_const.prodMk contDiff_id)
    have hρt : ContDiff ℝ ∞ (ρ t) := hρ.comp (f := fun z : Fin 3 → ℝ => (t,z)) (contDiff_const.prodMk contDiff_id)
    have hh := ContactTopology.ConvexDeformation.inverse_contact_pullback
      (fun z => ContactTopology.ConvexDeformation.covector (a z)) (ψ t) (ρ t) hψt hρt (hψρ t)
      (Λ t) (hΛpos t) (hcontact t ht) y v
    simpa only [a,ContactTopology.ConvexDeformation.invariantCoefficients,
      ContactTopology.ConvexDeformation.xyMap_apply,ContactTopology.ConvexDeformation.covector_apply,
      ContactTopology.ConvexDeformation.dot] using hh
  · intro t ht y hy hy0
    rw [hmatch t ht y (interior_subset (hDK ⟨hy,hy0⟩))]
    exact hplane (θ t) y hy0
  · intro y hy
    have hΨe : ψ 1 y=e y := by
      rw [hmatch 1 (by simp) y (interior_subset hy)]
      simpa only [g,hθ1] using (hend y (hKN (interior_subset hy))).2
    exact ⟨hΨe,by rw [← hΨe,hρψ]⟩
