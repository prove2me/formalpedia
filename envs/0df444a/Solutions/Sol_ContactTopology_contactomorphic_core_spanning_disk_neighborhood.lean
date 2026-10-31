-- Prove2me | solution 1 for ContactTopology.contactomorphic_core_spanning_disk_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T22:23:52.338501+00:00
-- url     : https://prove2.me/submissions/5f7cc7a6-ec0e-4cd5-96f4-2287f279c95c

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.Calculus.Deriv.Inv


import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Basic
import Theorems.Thm_FlowCalculus_regular_level_trajectory_invariant
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_GrayStability_Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_FlowCalculus_compact_supported_flow_preserves_regular_level
import Theorems.Thm_FlowCalculus_exists_unique_global_trajectory_of_compact_support
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


end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma smooth_injective_derivative_local_chart (F : V → V) (hF : ContDiff ℝ ∞ F)
    (p : V) (hinj : Injective (fderiv ℝ F p)) :
    ∃ e : OpenPartialHomeomorph V V, (e : V → V) = F ∧ p ∈ e.source := by
  let A : V ≃L[ℝ] V := (LinearEquiv.ofBijective (fderiv ℝ F p).toLinearMap
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt F (A : V →L[ℝ] V) p := (hF.differentiable (by simp) p).hasFDerivAt
  exact ⟨hF.contDiffAt.toOpenPartialHomeomorph F hd (by simp),
    hF.contDiffAt.toOpenPartialHomeomorph_coe hd (by simp),
    hF.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)⟩

/-- Local invertibility and injectivity on a compact set give one genuine smooth
chart around the entire compact set, inside any prescribed good open domain. -/
theorem compact_smooth_embedding_chart (F : V → V) (hF : ContDiff ℝ ∞ F)
    (S W : Set V) (hS : IsCompact S) (hW : IsOpen W) (hSW : S ⊆ W)
    (hinj : InjOn F S) (hder : ∀ p ∈ W, Injective (fderiv ℝ F p)) :
    ∃ e : OpenPartialHomeomorph V V, (e : V → V) = F ∧ S ⊆ e.source ∧
      e.source ⊆ W ∧ ∀ y ∈ e.target, ContDiffAt ℝ ∞ e.symm y := by
  have hloc : ∀ p ∈ S, ∃ O ∈ 𝓝 p, InjOn F O := by
    intro p hp
    obtain ⟨e,he,hp⟩ := smooth_injective_derivative_local_chart F hF p (hder p (hSW hp))
    exact ⟨e.source,e.open_source.mem_nhds hp,he ▸ e.injOn⟩
  obtain ⟨O,hO,hSO,hOi⟩ := hinj.exists_isOpen_superset hS (fun _ _ => hF.continuous.continuousAt) hloc
  let U := O ∩ W
  have hU : IsOpen U := hO.inter hW
  have hUi : InjOn F U := hOi.mono inter_subset_left
  have hopen : IsOpenMap (U.domRestrict F) := by
    apply IsOpenMap.of_nhds_le
    intro x
    obtain ⟨e,he,hx⟩ := smooth_injective_derivative_local_chart F hF x (hder x x.property.2)
    have hm : map F (𝓝 x.val) = 𝓝 (F x.val) := by
      simpa only [he] using e.map_nhds_eq hx
    have hs : map (fun x : U => (x : V)) (𝓝 x) = 𝓝 (x : V) :=
      hU.isOpenEmbedding_subtypeVal.map_nhds_eq x
    change 𝓝 (F x.val) ≤ map (fun z : U => F z.val) (𝓝 x)
    rw [show (fun z : U => F z.val) = F ∘ Subtype.val from rfl,← map_map,hs,hm]
  let e : OpenPartialHomeomorph V V := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hUi.toPartialEquiv F U) hF.continuous.continuousOn hopen hU
  have he : (e : V → V) = F := rfl
  refine ⟨e,he,fun x hx => ⟨hSO hx,hSW hx⟩,inter_subset_right,?_⟩
  intro y hy
  have hp : e.symm y ∈ W := (e.map_target hy).2
  let A : V ≃L[ℝ] V := (LinearEquiv.ofBijective (fderiv ℝ F (e.symm y)).toLinearMap
    ⟨hder _ hp,LinearMap.injective_iff_surjective.mp (hder _ hp)⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt e (A : V →L[ℝ] V) (e.symm y) := (hF.differentiable (by simp) _).hasFDerivAt
  exact e.contDiffAt_symm hy hd hF.contDiffAt

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.CoreDisk
open BirkhoffGlobalSection Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

def disk (u : Plane) : Phase :=
  ![2*u 0/(1+planeNormSq u),2*u 1/(1+planeNormSq u),
    (1-planeNormSq u)/(1+planeNormSq u),0]

lemma denominator_pos (u : Plane) : 0 < 1+planeNormSq u := by
  dsimp [planeNormSq]
  nlinarith [sq_nonneg (u 0),sq_nonneg (u 1)]

lemma disk_contDiff : ContDiff ℝ ∞ disk := by
  have hn : ContDiff ℝ ∞ planeNormSq := by unfold planeNormSq; fun_prop
  have hi : ContDiff ℝ ∞ (fun u : Plane => (1+planeNormSq u)⁻¹) :=
    (contDiff_const.add hn).inv (fun u => (denominator_pos u).ne')
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [disk] <;> (try simp only [div_eq_mul_inv]) <;> fun_prop

lemma disk_sphere (u : Plane) : disk u ∈ unitThreeSphere := by
  have hd := (denominator_pos u).ne'
  change (2*u 0/(1+planeNormSq u))^2+(2*u 1/(1+planeNormSq u))^2+
    (((1-planeNormSq u)/(1+planeNormSq u))^2+0^2)=1
  field_simp [hd]
  dsimp [planeNormSq]
  ring

lemma disk_boundary (u : Plane) (hu : u ∈ unitCircle) : disk u=![u 0,u 1,0,0] := by
  change planeNormSq u=1 at hu
  ext i
  fin_cases i <;> simp [disk,hu] <;> ring

lemma disk_upper (u : Plane) (hu : planeNormSq u ≤ 1) : 0 ≤ disk u 2 := by
  exact div_nonneg (sub_nonneg.mpr hu) (denominator_pos u).le

lemma disk_upper_strict (u : Plane) (hu : planeNormSq u < 1) : 0 < disk u 2 :=
  div_pos (sub_pos.mpr hu) (denominator_pos u)

lemma disk_recovery_denominator (u : Plane) : 1+disk u 2=2/(1+planeNormSq u) := by
  change 1+(1-planeNormSq u)/(1+planeNormSq u)=_
  field_simp [(denominator_pos u).ne']
  ring

lemma disk_recovery (u : Plane) :
    ![disk u 0/(1+disk u 2),disk u 1/(1+disk u 2)]=u := by
  rw [disk_recovery_denominator]
  ext i
  fin_cases i <;> dsimp [disk] <;> field_simp [(denominator_pos u).ne'] <;> ring

def inverse (y : Phase) : Plane := ![y 0/(1+y 2),y 1/(1+y 2)]

lemma inverse_contDiffAt (u : Plane) : ContDiffAt ℝ ∞ inverse (disk u) := by
  have hd : 0 < 1+disk u 2 := by rw [disk_recovery_denominator]; exact div_pos (by norm_num) (denominator_pos u)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [inverse] <;>
    exact ((contDiff_apply ℝ ℝ _).contDiffAt).div
      ((contDiffAt_const.add (contDiff_apply ℝ ℝ 2).contDiffAt)) hd.ne'

lemma disk_injective : Injective disk := by
  intro u v he
  have hh := congrArg inverse he
  simpa only [inverse,disk_recovery] using hh

lemma disk_derivative_injective (u : Plane) : Injective (fderiv ℝ disk u) := by
  have heq : inverse ∘ disk=id := funext disk_recovery
  have hd := congrArg (fun f : Plane → Plane => fderiv ℝ f u) heq
  rw [fderiv_comp u ((inverse_contDiffAt u).differentiableAt (by simp)) (disk_contDiff.differentiable (by simp) u)] at hd
  intro v w he
  have hh := congrArg (fderiv ℝ inverse (disk u)) he
  have he' := congrArg (fun L : Plane →L[ℝ] Plane => L v) hd
  have he'' := congrArg (fun L : Plane →L[ℝ] Plane => L w) hd
  simpa using he'.symm.trans (hh.trans he'')


end
end ContactTopology.CoreDisk


namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set
open scoped ContDiff
noncomputable section
lemma sphere_dot_self {y : Phase} (hy : y ∈ unitThreeSphere) : phaseDot y y = 1 := by
  change zNormSq y + wNormSq y = 1 at hy
  simp [zNormSq,wNormSq,phaseDot] at hy ⊢
  nlinarith

lemma dot_hasDerivAt {q g : ℝ → Phase} {v b : Phase} {t : ℝ}
    (hq : HasDerivAt q v t) (hg : HasDerivAt g b t) :
    HasDerivAt (fun s => phaseDot (q s) (g s)) (phaseDot v (g t) + phaseDot (q t) b) t := by
  have h := fun i => hasDerivAt_pi.mp hq i
  have k := fun i => hasDerivAt_pi.mp hg i
  have hd := ((((h 0).mul (k 0)).add ((h 1).mul (k 1))).add ((h 2).mul (k 2))).add ((h 3).mul (k 3))
  apply hd.congr_deriv
  simp only [phaseDot]
  ring

lemma dot_self_hasDerivAt {q : ℝ → Phase} {v : Phase} {t : ℝ} (hq : HasDerivAt q v t) :
    HasDerivAt (fun s => phaseDot (q s) (q s)) (2 * phaseDot (q t) v) t := by
  apply (dot_hasDerivAt hq hq).congr_deriv
  simp [phaseDot]
  ring


end
end BirkhoffGlobalSection.HopfTransport


namespace ContactTopology.Hemisphere
open ConvexDeformation BirkhoffGlobalSection Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
local notation "center" => ConvexDeformation.center

def raw (y : V) : V :=
  ![1+y 0^2-y 1^2-y 2^2, 2*y 0*y 1-2*y 2, 2*y 1+2*y 0*y 2]

def beta (x : P) : P := ![1+x 0^2-x 1^2, 2*x 0*x 1]
def normal (x : P) : ℝ := 2*x 1

lemma raw_contDiff : ContDiff ℝ ∞ raw := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [raw] <;> fun_prop

lemma beta_contDiff : ContDiff ℝ ∞ beta := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [beta] <;> fun_prop

lemma normal_contDiff : ContDiff ℝ ∞ normal := by unfold normal; fun_prop

lemma raw_fderiv (y v : V) : fderiv ℝ raw y v =
    ![2*y 0*v 0-2*y 1*v 1-2*y 2*v 2,
      2*v 0*y 1+2*y 0*v 1-2*v 2,
      2*v 1+2*v 0*y 2+2*y 0*v 2] := by
  let p (i : Fin 3) : V →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h0 := (((hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) y).add
    ((p 0).hasFDerivAt.pow 2)).sub ((p 1).hasFDerivAt.pow 2)).sub
      ((p 2).hasFDerivAt.pow 2)
  have h1 := (((((p 0).hasFDerivAt (x := y)).const_mul 2).mul
    ((p 1).hasFDerivAt (x := y))).sub
    (((p 2).hasFDerivAt (x := y)).const_mul 2))
  have h2 := (((p 1).hasFDerivAt (x := y)).const_mul 2).add
    ((((p 0).hasFDerivAt (x := y)).const_mul 2).mul ((p 2).hasFDerivAt (x := y)))
  change HasFDerivAt (fun z : V => 1+z 0^2-z 1^2-z 2^2) _ y at h0
  change HasFDerivAt (fun z : V => 2*z 0*z 1-2*z 2) _ y at h1
  change HasFDerivAt (fun z : V => 2*z 1+2*z 0*z 2) _ y at h2
  have hD : HasFDerivAt raw (ContinuousLinearMap.pi
      ![fderiv ℝ (fun z : V => 1+z 0^2-z 1^2-z 2^2) y,
        fderiv ℝ (fun z : V => 2*z 0*z 1-2*z 2) y,
        fderiv ℝ (fun z : V => 2*z 1+2*z 0*z 2) y]) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact h0.differentiableAt.hasFDerivAt
    · exact h1.differentiableAt.hasFDerivAt
    · exact h2.differentiableAt.hasFDerivAt
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp [h0.fderiv,h1.fderiv,h2.fderiv,p] <;> ring

lemma raw_curl (y : V) : curlLinear (fderiv ℝ raw y) = ![4,-4*y 2,4*y 1] := by
  simp only [curlLinear,raw_fderiv]
  ext i
  fin_cases i <;> simp <;> ring

lemma raw_volume (y : V) : dot (raw y) (curlLinear (fderiv ℝ raw y)) =
    4*(1+y 0^2+y 1^2+y 2^2) := by
  rw [raw_curl]
  simp [dot,raw]
  ring

lemma raw_positive (y : V) : 0 < dot (raw y) (curlLinear (fderiv ℝ raw y)) := by
  rw [raw_volume]
  positivity

lemma raw_central (y v : V) : covector (raw (center y)) (center v) =
    beta (xyMap y) 0*v 0+beta (xyMap y) 1*v 1 := by
  simp [covector_apply,dot,raw,ConvexDeformation.center,beta,xyMap]

lemma normal_fderiv (x v : P) : fderiv ℝ normal x v = 2*v 1 := by
  have hd := ((ContinuousLinearMap.proj 1 : P →L[ℝ] ℝ).hasFDerivAt (x := x)).const_mul 2
  change HasFDerivAt normal _ x at hd
  rw [hd.fderiv]
  simp

lemma beta_fderiv (x v : P) : fderiv ℝ beta x v =
    ![2*x 0*v 0-2*x 1*v 1,2*v 0*x 1+2*x 0*v 1] := by
  let p (i : Fin 2) : P →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h0 := ((hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) x).add
    ((p 0).hasFDerivAt.pow 2)).sub ((p 1).hasFDerivAt.pow 2)
  have h1 := (((p 0).hasFDerivAt (x := x)).const_mul 2).mul ((p 1).hasFDerivAt (x := x))
  change HasFDerivAt (fun z : P => 1+z 0^2-z 1^2) _ x at h0
  change HasFDerivAt (fun z : P => 2*z 0*z 1) _ x at h1
  have hD : HasFDerivAt beta (ContinuousLinearMap.pi
      ![fderiv ℝ (fun z : P => 1+z 0^2-z 1^2) x,
        fderiv ℝ (fun z : P => 2*z 0*z 1) x]) x := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact h0.differentiableAt.hasFDerivAt
    · exact h1.differentiableAt.hasFDerivAt
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp [h0.fderiv,h1.fderiv,p] <;> ring

lemma model_volume (x : P) : invariantVolume normal beta x=2*(1+x 0^2+3*x 1^2) := by
  simp [invariantVolume,normal_fderiv,beta_fderiv,beta,normal]
  ring

lemma model_positive (x : P) : 0 < invariantVolume normal beta x := by
  rw [model_volume]
  positivity

lemma model_signed_divergence (x : P) (hx : normal x ≠ 0) :
    0 < normal x*(fderiv ℝ beta x (Pi.single 0 1) 1-fderiv ℝ beta x (Pi.single 1 1) 0) := by
  have hb : x 1 ≠ 0 := by intro h; apply hx; simp [normal,h]
  simp [normal,beta_fderiv]
  nlinarith [sq_pos_of_ne_zero hb]

lemma model_crossing (x : P) (hx : normal x=0) : fderiv ℝ normal x ![beta x 1,-beta x 0] < 0 := by
  have hb : x 1=0 := by simpa [normal] using hx
  simp [normal_fderiv,beta,hb]
  nlinarith [sq_nonneg (x 0)]

lemma model_legendrian_boundary (x : P) (hx : diskSq x=1) :
    beta x 0*(-x 1)+beta x 1*x 0=0 := by
  dsimp [diskSq] at hx
  calc beta x 0*(-x 1)+beta x 1*x 0 = x 1*(x 0^2+x 1^2-1) := by simp [beta]; ring
    _ = 0 := by rw [hx]; ring

end
end ContactTopology.Hemisphere


namespace ContactTopology.Hemisphere
open ConvexDeformation BirkhoffGlobalSection Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
local notation "center" => ConvexDeformation.center

def radius (y : V) : ℝ := 1+y 0^2+y 1^2+y 2^2
def numerator (y : V) : Phase := ![2*y 0,2*y 1,1-y 0^2-y 1^2-y 2^2,-2*y 2]
def stereo (y : V) : Phase := (radius y)⁻¹ • numerator y
def inverse (p : Phase) : V := ![p 0/(1+p 2),p 1/(1+p 2),-p 3/(1+p 2)]

lemma radius_pos (y : V) : 0 < radius y := by unfold radius; positivity
lemma radius_contDiff : ContDiff ℝ ∞ radius := by unfold radius; fun_prop
lemma numerator_contDiff : ContDiff ℝ ∞ numerator := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [numerator] <;> fun_prop
lemma stereo_contDiff : ContDiff ℝ ∞ stereo :=
  (radius_contDiff.inv (fun y => (radius_pos y).ne')).smul numerator_contDiff

lemma stereo_sphere (y : V) : stereo y ∈ unitThreeSphere := by
  change ((radius y)⁻¹*(2*y 0))^2 +
    ((radius y)⁻¹*(2*y 1))^2 + (((radius y)⁻¹*(1-y 0^2-y 1^2-y 2^2))^2+
    ((radius y)⁻¹*(-2*y 2))^2) = 1
  field_simp [(radius_pos y).ne']
  unfold radius
  ring

lemma stereo_central (y : V) : stereo (center y) = CoreDisk.disk (xyMap y) := by
  ext i
  fin_cases i <;> simp [stereo,numerator,radius,CoreDisk.disk,planeNormSq,xyMap,div_eq_mul_inv] <;> ring

lemma stereo_denominator (y : V) : 1+stereo y 2=2/radius y := by
  change 1+(radius y)⁻¹*(1-y 0^2-y 1^2-y 2^2)=_
  field_simp [(radius_pos y).ne']
  unfold radius
  ring

lemma inverse_stereo (y : V) : inverse (stereo y)=y := by
  unfold inverse
  rw [stereo_denominator]
  ext i
  fin_cases i <;> simp [stereo,numerator] <;> field_simp [(radius_pos y).ne'] <;> ring

lemma stereo_inverse (p : Phase) (hp : p ∈ unitThreeSphere) (hden : 1+p 2 ≠ 0) :
    stereo (inverse p)=p := by
  have hs : p 0^2+p 1^2+(p 2^2+p 3^2)=1 := hp
  have hr : radius (inverse p)=2/(1+p 2) := by
    unfold radius inverse
    dsimp
    field_simp [hden]
    nlinarith [hs]
  unfold stereo
  rw [hr]
  ext i
  fin_cases i <;> simp [numerator,inverse] <;> field_simp [hden] <;>
    nlinarith [hs]

lemma inverse_contDiffAt (y : V) : ContDiffAt ℝ ∞ inverse (stereo y) := by
  have hden : 1+stereo y 2 ≠ 0 := by
    rw [stereo_denominator]
    exact (div_pos (by norm_num) (radius_pos y)).ne'
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [inverse] <;> fun_prop (disch := assumption)

lemma stereo_derivative_injective (y : V) : Injective (fderiv ℝ stereo y) := by
  have he : inverse ∘ stereo = id := funext inverse_stereo
  have hd := congrArg (fun f : V → V => fderiv ℝ f y) he
  rw [fderiv_comp y ((inverse_contDiffAt y).differentiableAt (by simp))
    (stereo_contDiff.differentiable (by simp) y)] at hd
  intro v w hvw
  have hh := congrArg (fderiv ℝ inverse (stereo y)) hvw
  have h1 := congrArg (fun L : V →L[ℝ] V => L v) hd
  have h2 := congrArg (fun L : V →L[ℝ] V => L w) hd
  simpa using h1.symm.trans (hh.trans h2)

lemma radius_fderiv (y v : V) : fderiv ℝ radius y v = 2*dot y v := by
  let p (i : Fin 3) : V →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hd := (((hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) y).add
    ((p 0).hasFDerivAt.pow 2)).add ((p 1).hasFDerivAt.pow 2)).add
      ((p 2).hasFDerivAt.pow 2)
  rw [show fderiv ℝ radius y = _ from hd.fderiv]
  simp [p,dot]
  ring

lemma numerator_fderiv (y v : V) : fderiv ℝ numerator y v =
    ![2*v 0,2*v 1,-2*dot y v,-2*v 2] := by
  let p (i : Fin 3) : V →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h2 := (((hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) y).sub
    ((p 0).hasFDerivAt.pow 2)).sub ((p 1).hasFDerivAt.pow 2)).sub
      ((p 2).hasFDerivAt.pow 2)
  have hD : HasFDerivAt numerator (ContinuousLinearMap.pi
      ![(2:ℝ) • p 0,(2:ℝ) • p 1,
        -(2*y 0) • p 0-(2*y 1) • p 1-(2*y 2) • p 2,(-2:ℝ) • p 2]) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (((p 0).hasFDerivAt (x := y)).const_mul 2)
    · exact (((p 1).hasFDerivAt (x := y)).const_mul 2)
    · convert! h2 using 1 <;> simp [p] <;> module
    · exact (((p 2).hasFDerivAt (x := y)).const_mul (-2))
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp [p,dot] <;> ring

lemma stereo_fderiv (y v : V) : fderiv ℝ stereo y v =
    (radius y)⁻¹ • (![2*v 0,2*v 1,-2*dot y v,-2*v 2] : Phase) -
    (2*dot y v/(radius y)^2) • numerator y := by
  have hi := (hasDerivAt_inv (radius_pos y).ne').comp_hasFDerivAt y
    (radius_contDiff.differentiable (by simp) y).hasFDerivAt
  have hd := hi.smul (numerator_contDiff.differentiable (by simp) y).hasFDerivAt
  rw [show fderiv ℝ stereo y = _ from hd.fderiv]
  ext i
  fin_cases i <;> simp [radius_fderiv,numerator_fderiv,numerator,div_eq_mul_inv,smul_smul] <;>
    try ring
  all_goals simp

lemma stereo_contact (y v : V) :
    phaseRadialContact (stereo y) (fderiv ℝ stereo y v) =
      (radius y)^(-2:ℤ)*covector (raw y) v := by
  rw [stereo_fderiv]
  simp [phaseRadialContact,phaseSymplecticForm,stereo,numerator,covector_apply,dot,raw]
  field_simp [(radius_pos y).ne']
  ring

end
end ContactTopology.Hemisphere


namespace ContactTopology.Hemisphere
open ConvexDeformation BirkhoffGlobalSection Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
local notation "center" => ConvexDeformation.center

def heightCutoff (z : ℝ) : ℝ :=
  Real.smoothTransition (4*(z+1))*Real.smoothTransition (4*(1-z))

lemma heightCutoff_contDiff : ContDiff ℝ ∞ heightCutoff := by unfold heightCutoff; fun_prop

lemma heightCutoff_one (z : ℝ) (hz : |z| < 2/3) : heightCutoff z = 1 := by
  have hb := abs_lt.mp hz
  simp [heightCutoff,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 4*(z+1)),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 4*(1-z))]

lemma heightCutoff_zero (z : ℝ) (hz : 1 < |z|) : heightCutoff z = 0 := by
  rcases lt_abs.mp hz with h|h
  · simp [heightCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : 4*(1-z) ≤ 0)]
  · simp [heightCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : 4*(z+1) ≤ 0)]

def hamiltonian (y : V) : ℝ := diskCutoff (xyMap y)*heightCutoff (y 2)*(2*y 1)

lemma hamiltonian_contDiff : ContDiff ℝ ∞ hamiltonian := by
  unfold hamiltonian
  exact ((diskCutoff_contDiff.comp xyMap.contDiff).mul
    (heightCutoff_contDiff.comp (contDiff_apply ℝ ℝ 2))).mul (by fun_prop)

lemma hamiltonian_compact : HasCompactSupport hamiltonian := by
  let join : P × ℝ → V := fun q => ![q.1 0,q.1 1,q.2]
  have hjoin : Continuous join := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [join] <;> fun_prop
  let C := join '' (tsupport diskCutoff ×ˢ Icc (-1:ℝ) 1)
  have hC : IsCompact C := (diskCutoff_compact.prod isCompact_Icc).image hjoin
  apply HasCompactSupport.intro' hC hC.isClosed
  intro y hy
  by_cases hx : xyMap y ∈ tsupport diskCutoff
  · have hz : 1 < |y 2| := by
      by_contra hn
      apply hy
      refine ⟨(xyMap y,y 2),⟨hx,abs_le.mp (not_lt.mp hn)⟩,?_⟩
      ext i
      fin_cases i <;> simp [join,xyMap]
    simp [hamiltonian,heightCutoff_zero (y 2) hz]
  · rw [hamiltonian,image_eq_zero_of_notMem_tsupport hx,zero_mul,zero_mul]

lemma hamiltonian_central_germ (y : V) (hy : diskSq (xyMap y) < 2) :
    hamiltonian =ᶠ[𝓝 (center y)] fun z : V => 2*z 1 := by
  have ho : IsOpen {z : V | diskSq (xyMap z) < 2 ∧ |z 2| < 2/3} :=
    (isOpen_lt (diskSq_contDiff.continuous.comp xyMap.continuous) continuous_const).inter
      (isOpen_lt ((continuous_apply 2).abs) continuous_const)
  have hc : center y ∈ {z : V | diskSq (xyMap z) < 2 ∧ |z 2| < 2/3} := by
    simpa using (show diskSq (xyMap y) < 2 ∧ (0:ℝ) < 2/3 from ⟨hy,by norm_num⟩)
  filter_upwards [ho.mem_nhds hc] with z hz
  rw [hamiltonian,diskCutoff_one _ hz.1,heightCutoff_one _ hz.2,one_mul,one_mul]

lemma hamiltonian_central (y : V) (hy : diskSq (xyMap y) < 2) :
    hamiltonian (center y) = normal (xyMap y) := by
  simpa [normal,xyMap] using (hamiltonian_central_germ y hy).eq_of_nhds

lemma hamiltonian_gradient_central (y : V) (hy : diskSq (xyMap y) < 2) :
    gradient3 hamiltonian (center y) = ![0,2,0] := by
  have he := hamiltonian_central_germ y hy
  have hd := ((ContinuousLinearMap.proj 1 : V →L[ℝ] ℝ).hasFDerivAt
    (x := center y)).const_mul 2
  change HasFDerivAt (fun z : V => 2*z 1) _ (center y) at hd
  unfold gradient3
  rw [he.fderiv_eq,hd.fderiv]
  simp

lemma transverse_hamiltonian (y : V) (hy : diskSq (xyMap y) < 2) :
    0 < hamiltonianField raw hamiltonian (center y) 2 := by
  change 0 < (dot (raw (center y)) (curlLinear (fderiv ℝ raw (center y))))⁻¹ *
    (hamiltonian (center y)*(curlLinear (fderiv ℝ raw (center y))) 2+
      cross (raw (center y)) (gradient3 hamiltonian (center y)) 2)
  apply mul_pos (inv_pos.mpr (raw_positive _))
  rw [hamiltonian_central y hy,hamiltonian_gradient_central y hy,raw_curl]
  simp [normal,xyMap,raw,cross,ConvexDeformation.center]
  nlinarith [sq_nonneg (y 0),sq_nonneg (y 1)]

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

lemma hemisphere_flowCollar_pullback
    (ψ : ℝ → V → V) (lam : ℝ → V → ℝ)
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (hamiltonianField raw hamiltonian (ψ t y)) t)
    (hpb : ∀ t y v, covector (raw (ψ t y)) (fderiv ℝ (ψ t) y v) =
      lam t y*covector (raw y) v)
    (hH : ∀ t y, hamiltonian (ψ t y) = lam t y*hamiltonian y)
    (y : V) (hy : diskSq (xyMap y) < 2) (v : V) :
    covector (raw (flowCollar ψ y)) (fderiv ℝ (flowCollar ψ) y v) =
      lam (y 2) (center y)*covector (invariantCoefficients normal beta y) v := by
  have hvalue (z : V) : covector (raw z) (hamiltonianField raw hamiltonian z) = hamiltonian z :=
    (hamiltonian_algebra (raw z) (curlLinear (fderiv ℝ raw z))
      (gradient3 hamiltonian z) 0 (hamiltonian z) (raw_positive z).ne').1
  rw [flowCollar_fderiv (hamiltonianField raw hamiltonian) ψ hψ hd,map_add,map_smul]
  change v 2*covector (raw (flowCollar ψ y)) (hamiltonianField raw hamiltonian (flowCollar ψ y))+
    covector (raw (ψ (y 2) (center y))) (fderiv ℝ (ψ (y 2)) (center y) (center v)) = _
  have hHflow : hamiltonian (flowCollar ψ y) = lam (y 2) (center y)*hamiltonian (center y) :=
    hH (y 2) (center y)
  rw [hvalue,hpb,hHflow,hamiltonian_central y hy,raw_central]
  simp [covector_apply,dot,invariantCoefficients]
  ring

def centralDisk : Set V := {y | diskSq (xyMap y) ≤ 1 ∧ y 2=0}

lemma centralDisk_compact : IsCompact centralDisk := by
  have hc : IsClosed centralDisk :=
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

/-- A genuine invertible contact-flow chart around the whole central disk. -/
theorem exists_hemisphere_flow_chart :
    ∃ e : OpenPartialHomeomorph V V, ∃ Λ : V → ℝ,
      ContDiff ℝ ∞ (e : V → V) ∧ ContDiff ℝ ∞ Λ ∧ (∀ y, 0 < Λ y) ∧
      centralDisk ⊆ e.source ∧ e.source ⊆ {y | diskSq (xyMap y) < 2} ∧
      (∀ y ∈ e.target, ContDiffAt ℝ ∞ e.symm y) ∧
      (∀ y, e (center y) = center y) ∧
      ∀ y ∈ e.source, ∀ v,
        covector (raw (e y)) (fderiv ℝ (e : V → V) y v) =
          Λ y*covector (invariantCoefficients normal beta y) v := by
  have hQ : ∀ y, dot (raw y) (curlLinear (fderiv ℝ raw y)) ≠ 0 := fun y => (raw_positive y).ne'
  obtain ⟨ψ,ρ,lam,hψ,hρ,hlam,h0,hbij,hρψ,hψρ,hd,hpositive,hpb,hHt⟩ :=
    integrate_hamiltonian_all_time raw hamiltonian raw_contDiff hamiltonian_contDiff hamiltonian_compact hQ
  let Λ : V → ℝ := fun y => lam (y 2) (center y)
  have hΛ : ContDiff ℝ ∞ Λ := hlam.comp ((contDiff_apply ℝ ℝ 2).prodMk center.contDiff)
  have hfix : ∀ y, flowCollar ψ (center y)=center y := by intro y; simp [flowCollar,h0]
  have hder : ∀ y, diskSq (xyMap y) < 2 → Injective (fderiv ℝ (flowCollar ψ) y) := by
    intro y hy
    exact transverse_flowCollar_derivative (hamiltonianField raw hamiltonian)
      (hamiltonianField_contDiff raw hamiltonian raw_contDiff hamiltonian_contDiff hQ)
      (hamiltonianField_compact raw hamiltonian hamiltonian_compact) ψ hψ h0 hd y
      (transverse_hamiltonian y hy).ne'
  have hfixed (y : V) (hy : y ∈ centralDisk) : flowCollar ψ y=y := by
    simp [flowCollar,hy.2,h0]
    ext i
    fin_cases i <;> simp [ConvexDeformation.center,hy.2]
  have hinj : InjOn (flowCollar ψ) centralDisk := by
    intro y hy z hz he
    simpa only [hfixed y hy,hfixed z hz] using he
  have hW : IsOpen {y : V | diskSq (xyMap y) < 2} :=
    isOpen_lt (diskSq_contDiff.continuous.comp xyMap.continuous) continuous_const
  obtain ⟨e,he,hS,hsource,hinv⟩ := compact_smooth_embedding_chart (flowCollar ψ)
    (flowCollar_contDiff ψ hψ) centralDisk {y | diskSq (xyMap y) < 2}
    centralDisk_compact hW (fun _ hy => lt_of_le_of_lt hy.1 (by norm_num)) hinj hder
  refine ⟨e,Λ,he ▸ flowCollar_contDiff ψ hψ,hΛ,fun y => hpositive _ _,hS,hsource,hinv,?_,?_⟩
  · intro y
    rw [he]
    exact hfix y
  · intro y hy v
    rw [he]
    exact hemisphere_flowCollar_pullback ψ lam hψ hd hpb hHt y (hsource hy) v

end
end ContactTopology.Hemisphere


namespace ContactTopology.Hemisphere
open ConvexDeformation BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
local notation "center" => ConvexDeformation.center

def reeb (p : Phase) : Phase := ![p 2,p 3,-p 0,-p 1]
def multiplier (F : EquivariantSphereContactomorphism) (p : Phase) : ℝ :=
  2*phaseRadialContact (F.toFun p) (fderiv ℝ F.toFun p (reeb p))

lemma reeb_contDiff : ContDiff ℝ ∞ reeb := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [reeb] <;> fun_prop

lemma multiplier_contDiffAt (F : EquivariantSphereContactomorphism) (p : Phase)
    (hp : p ∈ unitThreeSphere) : ContDiffAt ℝ ∞ (multiplier F) p := by
  have hF := F.smooth p hp
  have hV : ContDiffAt ℝ ∞ (fun q => fderiv ℝ F.toFun q (reeb q)) p :=
    (hF.fderiv_right (by simp)).clm_apply reeb_contDiff.contDiffAt
  unfold multiplier phaseRadialContact phaseSymplecticForm
  fun_prop

lemma multiplier_contact (F : EquivariantSphereContactomorphism) (p : Phase)
    (hp : p ∈ unitThreeSphere) :
    0 < multiplier F p ∧ ∀ v, phaseDot p v=0 →
      phaseRadialContact (F.toFun p) (fderiv ℝ F.toFun p v) =
        multiplier F p*phaseRadialContact p v := by
  obtain ⟨a,ha,hF⟩ := F.contact p hp
  have hT : phaseDot p (reeb p)=0 := by simp [reeb,phaseDot]; ring
  have hR : 2*phaseRadialContact p (reeb p)=1 := by
    have hs := sphere_dot_self hp
    dsimp [phaseRadialContact,phaseSymplecticForm,reeb,phaseDot] at hs ⊢
    linarith
  have he : multiplier F p=a := by
    unfold multiplier
    rw [hF _ hT]
    nlinarith [hR]
  rw [he]
  exact ⟨ha,hF⟩

lemma sphere_valued_derivative_tangent (C : V → Phase) (hC : ContDiff ℝ ∞ C)
    (hS : ∀ y, C y ∈ unitThreeSphere) (y v : V) : phaseDot (C y) (fderiv ℝ C y v)=0 := by
  let c : ℝ → V := fun s => y+s • v
  have hc : HasDerivAt c v 0 := by
    convert! (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const v) using 1 <;> simp [c]
  have hd := (hC.differentiable (by simp) (c 0)).hasFDerivAt.comp_hasDerivAt 0 hc
  have hsq := dot_self_hasDerivAt hd
  have heq : (fun s => phaseDot (C (c s)) (C (c s)))=fun _ => (1:ℝ) :=
    funext (fun s => sphere_dot_self (hS (c s)))
  change HasDerivAt (fun s => phaseDot (C (c s)) (C (c s))) _ 0 at hsq
  rw [heq] at hsq
  have hh := hsq.unique (hasDerivAt_const (0:ℝ) (1:ℝ))
  simp only [Function.comp_apply,c,zero_smul,add_zero] at hh
  linarith

def sphereChart (F : EquivariantSphereContactomorphism) (e : OpenPartialHomeomorph V V) : V → Phase :=
  F.toFun ∘ stereo ∘ e
def sphereInverse (F : EquivariantSphereContactomorphism) (e : OpenPartialHomeomorph V V) : Phase → V :=
  e.symm ∘ inverse ∘ F.invFun

lemma sphereChart_contDiff (F : EquivariantSphereContactomorphism) (e : OpenPartialHomeomorph V V)
    (he : ContDiff ℝ ∞ (e : V → V)) : ContDiff ℝ ∞ (sphereChart F e) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  exact (F.smooth _ (stereo_sphere (e y))).comp y (stereo_contDiff.comp he).contDiffAt

lemma sphereChart_mem (F : EquivariantSphereContactomorphism) (e : OpenPartialHomeomorph V V) (y : V) :
    sphereChart F e y ∈ unitThreeSphere := F.maps_sphere (stereo_sphere _)

lemma sphereInverse_chart (F : EquivariantSphereContactomorphism) (e : OpenPartialHomeomorph V V)
    (y : V) (hy : y ∈ e.source) : sphereInverse F e (sphereChart F e y)=y := by
  change e.symm (inverse (F.invFun (F.toFun (stereo (e y)))))=y
  rw [F.left_inv _ (stereo_sphere _),inverse_stereo,e.left_inv hy]

lemma sphereInverse_contDiffAt (F : EquivariantSphereContactomorphism) (e : OpenPartialHomeomorph V V)
    (hinv : ∀ y ∈ e.target, ContDiffAt ℝ ∞ e.symm y)
    (y : V) (hy : y ∈ e.source) : ContDiffAt ℝ ∞ (sphereInverse F e) (sphereChart F e y) := by
  have hF := F.inv_smooth _ (sphereChart_mem F e y)
  have hv : F.invFun (sphereChart F e y)=stereo (e y) := F.left_inv _ (stereo_sphere _)
  have hI : ContDiffAt ℝ ∞ (inverse ∘ F.invFun) (sphereChart F e y) := by
    exact (hv ▸ inverse_contDiffAt (e y)).comp _ hF
  have hv2 : (inverse ∘ F.invFun) (sphereChart F e y)=e y := by rw [Function.comp_apply,hv,inverse_stereo]
  exact (hv2 ▸ hinv (e y) (e.map_source hy)).comp _ hI

lemma sphereChart_derivative_injective (F : EquivariantSphereContactomorphism)
    (e : OpenPartialHomeomorph V V) (he : ContDiff ℝ ∞ (e : V → V))
    (hinv : ∀ y ∈ e.target, ContDiffAt ℝ ∞ e.symm y)
    (y : V) (hy : y ∈ e.source) : Injective (fderiv ℝ (sphereChart F e) y) := by
  have hC := sphereChart_contDiff F e he
  have hR := sphereInverse_contDiffAt F e hinv y hy
  have hident : sphereInverse F e ∘ sphereChart F e =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_source.mem_nhds hy] with z hz
    exact sphereInverse_chart F e z hz
  have hd : fderiv ℝ (sphereInverse F e ∘ sphereChart F e) y = fderiv ℝ id y := hident.fderiv_eq
  rw [fderiv_comp y (hR.differentiableAt (by simp)) (hC.differentiable (by simp) y)] at hd
  intro v w hvw
  have hh := congrArg (fderiv ℝ (sphereInverse F e) (sphereChart F e y)) hvw
  have h1 := congrArg (fun L : V →L[ℝ] V => L v) hd
  have h2 := congrArg (fun L : V →L[ℝ] V => L w) hd
  simpa using h1.symm.trans (hh.trans h2)

lemma embedding_of_smooth_inverse (C : V → Phase) (R : Phase → V) (N : Set V)
    (hC : Continuous C) (hR : ∀ y ∈ N, ContinuousAt R (C y))
    (hRC : ∀ y ∈ N, R (C y)=y) : IsEmbedding (fun y : N => C y) := by
  let f : N → Phase := fun y => C y
  let g : Set.range f → V := fun p => R p.val
  have hf : Continuous f := hC.comp continuous_subtype_val
  have hg : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    rintro ⟨p,y,hyp⟩
    have hr : ContinuousAt R (f y) := hR y.val y.property
    rw [hyp] at hr
    exact hr.comp continuous_subtype_val.continuousAt
  have hcomp : g ∘ Set.rangeFactorization f = (Subtype.val : N → V) := by
    funext y
    exact hRC y.val y.property
  have hfactor : Continuous (Set.rangeFactorization f) := hf.subtype_mk _
  have hE : IsEmbedding (Set.rangeFactorization f) :=
    IsEmbedding.of_comp hfactor hg (hcomp ▸ IsEmbedding.subtypeVal)
  exact IsEmbedding.subtypeVal.comp hE

lemma sphereChart_embedding (F : EquivariantSphereContactomorphism)
    (e : OpenPartialHomeomorph V V) (he : ContDiff ℝ ∞ (e : V → V))
    (hinv : ∀ y ∈ e.target, ContDiffAt ℝ ∞ e.symm y) :
    IsEmbedding (fun y : e.source => sphereChart F e y) :=
  embedding_of_smooth_inverse (sphereChart F e) (sphereInverse F e) e.source
    (sphereChart_contDiff F e he).continuous
    (fun y hy => (sphereInverse_contDiffAt F e hinv y hy).continuousAt)
    (sphereInverse_chart F e)

/-- The image is a genuine neighborhood in the sphere, with a two-sided
smooth inverse there, rather than just an immersed parametrization. -/
lemma sphereChart_local_right_inverse (F : EquivariantSphereContactomorphism)
    (e : OpenPartialHomeomorph V V) (y : V) (hy : y ∈ e.source) :
    ∃ O : Set Phase, IsOpen O ∧ sphereChart F e y ∈ O ∧
      ∀ p ∈ O, p ∈ unitThreeSphere →
        sphereInverse F e p ∈ e.source ∧ sphereChart F e (sphereInverse F e p)=p := by
  let q : Phase → V := inverse ∘ F.invFun
  let d : Phase → ℝ := fun p => 1+F.invFun p 2
  have hv : F.invFun (sphereChart F e y)=stereo (e y) := F.left_inv _ (stereo_sphere _)
  have hqval : q (sphereChart F e y)=e y := by
    change inverse (F.invFun (sphereChart F e y))=e y
    rw [hv,inverse_stereo]
  have hi := F.inv_smooth _ (sphereChart_mem F e y)
  have hq : ContinuousAt q (sphereChart F e y) := by
    have hst : ContDiffAt ℝ ∞ inverse (F.invFun (sphereChart F e y)) := by
      rw [hv]
      exact inverse_contDiffAt _
    exact (hst.comp _ hi).continuousAt
  have hd : ContinuousAt d (sphereChart F e y) :=
    continuousAt_const.add (((continuous_apply 2).continuousAt).comp hi.continuousAt)
  have hden : d (sphereChart F e y) ≠ 0 := by
    change 1+F.invFun (sphereChart F e y) 2 ≠ 0
    rw [hv,stereo_denominator]
    exact (div_pos (by norm_num) (radius_pos _)).ne'
  have hqmem : q ⁻¹' e.target ∈ 𝓝 (sphereChart F e y) :=
    hq.preimage_mem_nhds (e.open_target.mem_nhds (hqval ▸ e.map_source hy))
  have hdmem : d ⁻¹' {s : ℝ | s ≠ 0} ∈ 𝓝 (sphereChart F e y) :=
    hd.preimage_mem_nhds ((isOpen_ne : IsOpen {s : ℝ | s ≠ 0}).mem_nhds hden)
  obtain ⟨O,hO,hopen,hOy⟩ := mem_nhds_iff.mp (inter_mem hqmem hdmem)
  refine ⟨O,hopen,hOy,?_⟩
  intro p hp hSphere
  obtain ⟨hpt,hpd⟩ := hO hp
  change q p ∈ e.target at hpt
  change 1+F.invFun p 2 ≠ 0 at hpd
  refine ⟨e.map_target hpt,?_⟩
  change F.toFun (stereo (e (e.symm (q p))))=p
  rw [e.right_inv hpt]
  change F.toFun (stereo (inverse (F.invFun p)))=p
  rw [stereo_inverse _ (F.inv_maps_sphere hSphere) hpd,F.right_inv _ hSphere]

def chartFactor (F : EquivariantSphereContactomorphism) (e : OpenPartialHomeomorph V V)
    (Λ : V → ℝ) (y : V) : ℝ := multiplier F (stereo (e y))*(radius (e y))^(-2:ℤ)*Λ y

lemma chartFactor_contDiff (F : EquivariantSphereContactomorphism)
    (e : OpenPartialHomeomorph V V) (he : ContDiff ℝ ∞ (e : V → V))
    (Λ : V → ℝ) (hΛ : ContDiff ℝ ∞ Λ) : ContDiff ℝ ∞ (chartFactor F e Λ) := by
  have hm : ContDiff ℝ ∞ (fun y => multiplier F (stereo (e y))) := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    exact ContDiffAt.comp (g := multiplier F) (f := stereo ∘ (e : V → V)) y
      (multiplier_contDiffAt F (stereo (e y)) (stereo_sphere (e y)))
      (stereo_contDiff.comp he).contDiffAt
  unfold chartFactor
  have hi : ContDiff ℝ ∞ (fun y => (radius (e y))⁻¹) :=
    (radius_contDiff.comp he).inv (fun y => (radius_pos _).ne')
  convert! (hm.mul (hi.pow 2)).mul hΛ using 1
  funext y
  simp [zpow_neg,zpow_ofNat]

lemma chartFactor_positive (F : EquivariantSphereContactomorphism)
    (e : OpenPartialHomeomorph V V) (Λ : V → ℝ) (hΛ : ∀ y, 0 < Λ y) (y : V) :
    0 < chartFactor F e Λ y :=
  mul_pos (mul_pos (multiplier_contact F _ (stereo_sphere _)).1 (zpow_pos (radius_pos _) _)) (hΛ y)

lemma sphereChart_contact (F : EquivariantSphereContactomorphism)
    (e : OpenPartialHomeomorph V V) (he : ContDiff ℝ ∞ (e : V → V))
    (Λ : V → ℝ)
    (hpb : ∀ y ∈ e.source, ∀ v, covector (raw (e y)) (fderiv ℝ (e : V → V) y v) =
      Λ y*covector (invariantCoefficients normal beta y) v)
    (y : V) (hy : y ∈ e.source) (v : V) :
    phaseRadialContact (sphereChart F e y) (fderiv ℝ (sphereChart F e) y v) =
      chartFactor F e Λ y*covector (invariantCoefficients normal beta y) v := by
  have hse := stereo_contDiff.comp he
  have hD : fderiv ℝ (sphereChart F e) y v =
      fderiv ℝ F.toFun (stereo (e y)) (fderiv ℝ (stereo ∘ e) y v) := by
    change fderiv ℝ (F.toFun ∘ (stereo ∘ (e : V → V))) y v = _
    rw [fderiv_comp y ((F.smooth (stereo (e y)) (stereo_sphere (e y))).differentiableAt (by simp))
      (hse.differentiable (by simp) y)]
    rfl
  rw [hD]
  change phaseRadialContact (F.toFun (stereo (e y))) _ = _
  rw [(multiplier_contact F _ (stereo_sphere _)).2 _
    (sphere_valued_derivative_tangent (stereo ∘ e) hse (fun z => stereo_sphere _) y v),
    fderiv_comp y (stereo_contDiff.differentiable (by simp) _) (he.differentiable (by simp) y)]
  change multiplier F (stereo (e y))*phaseRadialContact (stereo (e y))
    (fderiv ℝ stereo (e y) (fderiv ℝ (e : V → V) y v)) = _
  rw [stereo_contact,hpb y hy v]
  unfold chartFactor
  ring

end
end ContactTopology.Hemisphere


open scoped ContDiff
theorem solution
    (F : BirkhoffGlobalSection.EquivariantSphereContactomorphism) :
    let d : (Fin 2 → ℝ) → (Fin 4 → ℝ) := fun x =>
      ![2*x 0/(1+x 0^2+x 1^2),2*x 1/(1+x 0^2+x 1^2),
        (1-x 0^2-x 1^2)/(1+x 0^2+x 1^2),0]
    let I : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun y v =>
      (1+y 0^2-y 1^2)*v 0+(2*y 0*y 1)*v 1+(2*y 1)*v 2
    ∃ C : (Fin 3 → ℝ) → (Fin 4 → ℝ), ∃ R : (Fin 4 → ℝ) → (Fin 3 → ℝ),
    ∃ r : (Fin 3 → ℝ) → ℝ, ∃ N : Set (Fin 3 → ℝ),
      ContDiff ℝ ∞ C ∧ ContDiff ℝ ∞ r ∧ (∀ y, 0 < r y) ∧ IsOpen N ∧
      (∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → (![x 0,x 1,0] : Fin 3 → ℝ) ∈ N) ∧
      (∀ y, C y ∈ BirkhoffGlobalSection.unitThreeSphere) ∧
      (∀ x : Fin 2 → ℝ, C ![x 0,x 1,0] = F.toFun (d x)) ∧
      Topology.IsEmbedding (fun y : N => C y) ∧
      (∀ y ∈ N, ContDiffAt ℝ ∞ R (C y) ∧ R (C y)=y ∧ Function.Injective (fderiv ℝ C y)) ∧
      (∀ y ∈ N, ∀ v,
        BirkhoffGlobalSection.phaseRadialContact (C y) (fderiv ℝ C y v) = r y*I y v) ∧
      (∀ y ∈ N, ∃ O : Set (Fin 4 → ℝ), IsOpen O ∧ C y ∈ O ∧
        ∀ p ∈ O, p ∈ BirkhoffGlobalSection.unitThreeSphere → R p ∈ N ∧ C (R p)=p) ∧
      (∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 →
        (BirkhoffGlobalSection.phaseRadialContact (C ![x 0,x 1,0])
          (fderiv ℝ C ![x 0,x 1,0] (Pi.single 2 1)) = 0 ↔ x 1=0)) ∧
      ∀ x : Fin 2 → ℝ, x 0^2+x 1^2=1 →
        BirkhoffGlobalSection.phaseRadialContact (C ![x 0,x 1,0])
          (fderiv ℝ C ![x 0,x 1,0] ![-x 1,x 0,0])=0
 := by
  dsimp only
  obtain ⟨e,Λ,he,hΛ,hpositive,hDisk,hsmall,hinv,hfix,hpb⟩ :=
    ContactTopology.Hemisphere.exists_hemisphere_flow_chart
  let C := ContactTopology.Hemisphere.sphereChart F e
  let R := ContactTopology.Hemisphere.sphereInverse F e
  let r := ContactTopology.Hemisphere.chartFactor F e Λ
  have hC : ContDiff ℝ ∞ C := ContactTopology.Hemisphere.sphereChart_contDiff F e he
  have hr : ContDiff ℝ ∞ r := ContactTopology.Hemisphere.chartFactor_contDiff F e he Λ hΛ
  have hpos : ∀ y, 0 < r y := ContactTopology.Hemisphere.chartFactor_positive F e Λ hpositive
  have hD (x : Fin 2 → ℝ) (hx : x 0^2+x 1^2 ≤ 1) : (![x 0,x 1,0] : Fin 3 → ℝ) ∈ e.source :=
    hDisk ⟨hx,rfl⟩
  have hcontact (y : Fin 3 → ℝ) (hy : y ∈ e.source) (v : Fin 3 → ℝ) :
      BirkhoffGlobalSection.phaseRadialContact (C y) (fderiv ℝ C y v) =
        r y*((1+y 0^2-y 1^2)*v 0+(2*y 0*y 1)*v 1+(2*y 1)*v 2) := by
    exact ContactTopology.Hemisphere.sphereChart_contact F e he Λ hpb y hy v
  refine ⟨C,R,r,e.source,hC,hr,hpos,e.open_source,hD,
    ContactTopology.Hemisphere.sphereChart_mem F e,?_,
    ContactTopology.Hemisphere.sphereChart_embedding F e he hinv,?_,hcontact,
    ContactTopology.Hemisphere.sphereChart_local_right_inverse F e,?_,?_⟩
  · intro x
    have hf := hfix (![x 0,x 1,0] : Fin 3 → ℝ)
    simp only [ContactTopology.ConvexDeformation.center_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two] at hf
    change F.toFun (ContactTopology.Hemisphere.stereo (e ![x 0,x 1,0])) = _
    rw [hf]
    have hs := ContactTopology.Hemisphere.stereo_central (![x 0,x 1,0] : Fin 3 → ℝ)
    simp only [ContactTopology.ConvexDeformation.center_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two] at hs
    rw [hs]
    congr 1
    ext i
    fin_cases i <;> simp [ContactTopology.CoreDisk.disk,BirkhoffGlobalSection.planeNormSq,
      ContactTopology.ConvexDeformation.xyMap] <;> ring
  · intro y hy
    exact ⟨ContactTopology.Hemisphere.sphereInverse_contDiffAt F e hinv y hy,
      ContactTopology.Hemisphere.sphereInverse_chart F e y hy,
      ContactTopology.Hemisphere.sphereChart_derivative_injective F e he hinv y hy⟩
  · intro x hx
    rw [hcontact _ (hD x hx)]
    simp [ne_of_gt (hpos ![x 0,x 1,0])]
  · intro x hx
    rw [hcontact _ (hD x hx.le)]
    have hb := ContactTopology.Hemisphere.model_legendrian_boundary x hx
    change (1+x 0^2-x 1^2)*(-x 1)+(2*x 0*x 1)*x 0=0 at hb
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,mul_zero,add_zero]
    rw [hb]
    simp
