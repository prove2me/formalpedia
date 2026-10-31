-- Prove2me | solution 1 for ContactTopology.dividing_fixed_invariant_disk_foliation_realization
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T20:44:39.965751+00:00
-- url     : https://prove2.me/submissions/48a8511e-5264-4cc3-aeb5-bf994056cf85

import Theorems.Thm_DifferentialTopology_positive_ratio_of_cooriented_regular_defining_functions
import Mathlib.Analysis.Normed.Operator.Banach
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
open Set Function Filter GrayStability
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def geometricField (u : P → ℝ) (β : P → P) (ε : ℝ) : V → V :=
  hamiltonianField (invariantCoefficients u β) (localizedHamiltonian u ε)

lemma geometricField_contDiff (u : P → ℝ) (β : P → P) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hpos : ∀ x, 0 < invariantVolume u β x) :
    ContDiff ℝ ∞ (geometricField u β ε) := by
  apply hamiltonianField_contDiff _ _ (invariantCoefficients_contDiff u β hu hβ)
    (localizedHamiltonian_contDiff u hu ε)
  intro y
  rw [invariant_volume_formula u β hu hβ]
  exact (hpos _).ne'

lemma geometricField_compact (u : P → ℝ) (β : P → P) (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (geometricField u β ε) :=
  hamiltonianField_compact _ _ (localizedHamiltonian_compact u ε hε)

lemma gradient3_mul (f g : V → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (y : V) :
    gradient3 (fun z => f z*g z) y = f y • gradient3 g y+g y • gradient3 f y := by
  have hd := (hf y).hasFDerivAt.mul (hg y).hasFDerivAt
  change HasFDerivAt (fun z => f z*g z) _ y at hd
  unfold gradient3
  rw [hd.fderiv]
  ext i
  fin_cases i <;> simp

lemma geometricField_normal_stationary (u : P → ℝ) (β : P → P) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hε : 0 < ε) (y : V) (hy : ε ≤ |y 2|) :
    geometricField u β ε y = 0 := by
  have hv : normalHamiltonian u (normalSpeed ε) y = 0 := by
    simp [normalHamiltonian,normalSpeed_zero ε (y 2) hε hy]
  have hg : gradient3 (normalHamiltonian u (normalSpeed ε)) y = 0 := by
    rw [normalHamiltonian_gradient u (normalSpeed ε) hu (normalSpeed_contDiff ε)]
    simp [normalSpeed_zero ε (y 2) hε hy,normalSpeed_deriv_zero ε (y 2) hε hy]
  have hH : ContDiff ℝ ∞ (normalHamiltonian u (normalSpeed ε)) :=
    ((normalSpeed_contDiff ε).comp (contDiff_apply ℝ ℝ 2)).mul (hu.comp xyMap.contDiff)
  have hgrad : gradient3 (localizedHamiltonian u ε) y = 0 := by
    change gradient3 (fun z => diskCutoff (xyMap z)*normalHamiltonian u (normalSpeed ε) z) y = 0
    have hcut : Differentiable ℝ (fun z : V => diskCutoff (xyMap z)) :=
      (diskCutoff_contDiff.comp xyMap.contDiff).differentiable (by simp)
    rw [gradient3_mul (fun z : V => diskCutoff (xyMap z)) (normalHamiltonian u (normalSpeed ε))
      hcut (hH.differentiable (by simp)) y,hg,hv]
    simp
  simp [geometricField,hamiltonianField,hamiltonianAlgebra,localizedHamiltonian,hv,hgrad,cross]

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

lemma regular_level_flow_all_time (F : V → ℝ) (hF : ContDiff ℝ ∞ F)
    (hreg : ∀ y, F y = 0 → Surjective (fderiv ℝ F y))
    (X : V → V) (hX : ContDiff ℝ ∞ X) (htan : ∀ y, F y = 0 → fderiv ℝ F y (X y) = 0)
    (ψ : ℝ → V → V) (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) :
    ∀ t y, F y = 0 → F (ψ t y) = 0 := by
  intro T y hy
  let γ : ℝ → V := fun s => ψ (s*T) y
  let Y : ℝ → V → V := fun _ z => T • X z
  have hY : ContDiff ℝ ∞ (fun p : ℝ × V => Y p.1 p.2) :=
    (hX.comp contDiff_snd).const_smul T
  have hγ : ∀ s, HasDerivAt γ (Y s (γ s)) s := by
    intro s
    have harg : HasDerivAt (fun v : ℝ => v*T) T s := by
      convert! (hasDerivAt_id (𝕜 := ℝ) s).mul_const T using 1 <;> simp
    convert! (hd (s*T) y).scomp s harg using 1
  have hcont : Continuous γ := continuous_iff_continuousAt.mpr fun s => (hγ s).continuousAt
  have hh := FlowCalculus.regular_level_trajectory_invariant F hF hreg Y hY 0 1 (by
      intro s hs z hz
      simp only [Y,map_smul,htan z hz,smul_zero])
    γ hcont.continuousOn (fun s _ => hγ s) (by simpa [γ,h0] using hy)
  simpa [γ] using hh 1 (by simp)

def boundaryFunction (y : V) : ℝ := diskSq (xyMap y)-1
def boundaryDerivative (y : V) : V →L[ℝ] ℝ :=
  (2*y 0) • ContinuousLinearMap.proj 0+(2*y 1) • ContinuousLinearMap.proj 1

lemma boundaryDerivative_apply (y v : V) : boundaryDerivative y v = 2*y 0*v 0+2*y 1*v 1 := by
  simp [boundaryDerivative]

lemma boundaryFunction_hasFDerivAt (y : V) : HasFDerivAt boundaryFunction (boundaryDerivative y) y := by
  have hd := (((hasFDerivAt_apply (𝕜 := ℝ) 0 y).pow 2).add
    ((hasFDerivAt_apply (𝕜 := ℝ) 1 y).pow 2)).sub_const 1
  change HasFDerivAt boundaryFunction _ y at hd
  convert! hd using 1
  ext v
  simp [boundaryDerivative]

lemma boundaryFunction_contDiff : ContDiff ℝ ∞ boundaryFunction := by
  unfold boundaryFunction
  exact (diskSq_contDiff.comp xyMap.contDiff).sub contDiff_const

lemma boundaryFunction_regular : ∀ y, boundaryFunction y = 0 → Surjective (fderiv ℝ boundaryFunction y) := by
  intro y hy w
  have hr : y 0^2+y 1^2 = 1 := by
    have hh : y 0^2+y 1^2-1 = 0 := by simpa [boundaryFunction,diskSq] using hy
    linarith
  refine ⟨(w/2) • (![y 0,y 1,0] : V),?_⟩
  rw [(boundaryFunction_hasFDerivAt y).fderiv,boundaryDerivative_apply]
  simp only [Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one]
  calc
    _ = w*(y 0^2+y 1^2) := by ring
    _ = w := by rw [hr,mul_one]

lemma geometricField_boundary_tangent (u : P → ℝ) (β : P → P) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hpos : ∀ x, 0 < invariantVolume u β x)
    (hLegendrian : ∀ x, diskSq x = 1 → β x 0*(-x 1)+β x 1*x 0 = 0) :
    ∀ y, boundaryFunction y = 0 → fderiv ℝ boundaryFunction y (geometricField u β ε y) = 0 := by
  intro y hy
  have hr : diskSq (xyMap y) = 1 := by unfold boundaryFunction at hy; linarith
  have ht := planarCharacteristic_boundary_tangent u β (xyMap y) (hLegendrian _ hr)
  rw [xyMap_apply] at ht
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at ht
  rw [(boundaryFunction_hasFDerivAt y).fderiv]
  rw [show geometricField u β ε y = compressionField u β (normalSpeed ε) y from
    localizedField_agrees u β ε hu hβ hpos y hr.le]
  simp only [boundaryDerivative_apply,compressionField,Matrix.cons_val_zero,Matrix.cons_val_one]
  calc
    _ = 2*deriv (normalSpeed ε) (y 2)*
      (y 0*planarCharacteristic u β (xyMap y) 0+y 1*planarCharacteristic u β (xyMap y) 1) := by ring
    _ = 0 := by rw [xyMap_apply,ht]; ring

theorem geometric_flow_preserves_disk (u : P → ℝ) (β : P → P) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hpos : ∀ x, 0 < invariantVolume u β x)
    (hε : 0 < ε)
    (hLegendrian : ∀ x, diskSq x = 1 → β x 0*(-x 1)+β x 1*x 0 = 0)
    (ψ : ℝ → V → V) (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (geometricField u β ε (ψ t y)) t) :
    ∀ t y, diskSq (xyMap y) ≤ 1 → diskSq (xyMap (ψ t y)) ≤ 1 := by
  have hX := geometricField_contDiff u β ε hu hβ hpos
  have hcX := geometricField_compact u β ε hε
  have hb := regular_level_flow_all_time boundaryFunction boundaryFunction_contDiff boundaryFunction_regular
    (geometricField u β ε) hX (geometricField_boundary_tangent u β ε hu hβ hpos hLegendrian) ψ h0 hd
  have hn := autonomous_flow_neg (geometricField u β ε) hX hcX ψ h0 hd
  intro T y hy
  by_contra hout
  have hgt : 1 < diskSq (xyMap (ψ T y)) := not_le.mp hout
  let f : ℝ → ℝ := fun s => diskSq (xyMap (ψ (s*T) y))
  have harg : Continuous (fun s : ℝ => (s*T,y)) :=
    (continuous_id.mul continuous_const).prodMk continuous_const
  have hf : Continuous f := diskSq_contDiff.continuous.comp
    (xyMap.continuous.comp (hψ.continuous.comp harg))
  obtain ⟨s,hs,hfs⟩ := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num) hf.continuousOn
    (show (1:ℝ) ∈ Icc (f 0) (f 1) by simpa [f,h0] using And.intro hy hgt.le)
  have hz : boundaryFunction (ψ (s*T) y) = 0 := by dsimp [boundaryFunction]; change f s-1=0; linarith
  have hback := hb (-(s*T)) (ψ (s*T) y) hz
  rw [hn] at hback
  have hinit : boundaryFunction y = 0 := hback
  have hB : boundaryFunction (ψ T y) = 0 := hb T y hinit
  unfold boundaryFunction at hB
  linarith

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma geometric_flow_preserves_strip (u : P → ℝ) (β : P → P) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hpos : ∀ x, 0 < invariantVolume u β x)
    (hε : 0 < ε) (ψ : ℝ → V → V) (h0 : ∀ y, ψ 0 y = y) (hbij : ∀ t, Bijective (ψ t))
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (geometricField u β ε (ψ t y)) t) :
    ∀ t y, |y 2| < ε → |ψ t y 2| < ε := by
  have hX := geometricField_contDiff u β ε hu hβ hpos
  have hcX := geometricField_compact u β ε hε
  have hX' : ContDiff ℝ ∞ (fun p : ℝ × V => geometricField u β ε p.2) := hX.comp contDiff_snd
  have hsupp : ∃ C : Set V, IsCompact C ∧ ∀ (t : ℝ) y, y ∉ C → geometricField u β ε y = 0 :=
    ⟨tsupport (geometricField u β ε),hcX,fun _ _ hy => image_eq_zero_of_notMem_tsupport hy⟩
  have hfix : ∀ t y, ε ≤ |y 2| → ψ t y = y := by
    intro t y hy
    exact ambient_flow_fixes (fun _ z => geometricField u β ε z) ψ hX' hsupp h0 hd y
      (fun _ => geometricField_normal_stationary u β ε hu hε y hy) t
  intro t y hy
  by_contra hout
  have ho : ε ≤ |ψ t y 2| := not_lt.mp hout
  have he : y = ψ t y := (hbij t).1 (by rw [hfix t (ψ t y) ho])
  rw [← he] at ho
  linarith

lemma geometric_flow_normal_derivative (u : P → ℝ) (β : P → P) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hpos : ∀ x, 0 < invariantVolume u β x)
    (hε : 0 < ε) (hLegendrian : ∀ x, diskSq x = 1 → β x 0*(-x 1)+β x 1*x 0 = 0)
    (ψ : ℝ → V → V) (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (geometricField u β ε (ψ t y)) t)
    (y : V) (hy : diskSq (xyMap y) ≤ 1) :
    ∀ t, HasDerivAt (fun s => ψ s y 2) (normalSpeed ε (ψ t y 2)) t := by
  intro t
  have hz := geometric_flow_preserves_disk u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hd t y hy
  have hh := (ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t (hd t y)
  change HasDerivAt (fun s => ψ s y 2) (geometricField u β ε (ψ t y) 2) t at hh
  rw [show geometricField u β ε (ψ t y) = compressionField u β (normalSpeed ε) (ψ t y) from
    localizedField_agrees u β ε hu hβ hpos _ hz] at hh
  simpa [compressionField,Matrix.vecHead,Matrix.vecTail] using hh

lemma normalSpeed_even (ε z : ℝ) : normalSpeed ε (-z) = normalSpeed ε z := by simp [normalSpeed]

lemma normal_trajectory_odd (ε : ℝ) (hε : 0 < ε) (τ : ℝ → ℝ) (h0 : τ 0 = 0)
    (hd : ∀ t, HasDerivAt τ (normalSpeed ε (τ t)) t) : ∀ t, τ (-t) = -τ t := by
  have hs : ∃ C : Set ℝ, IsCompact C ∧ ∀ (t : ℝ) z, z ∉ C → normalSpeed ε z = 0 :=
    ⟨tsupport (normalSpeed ε),normalSpeed_compact ε hε,fun _ _ hz => image_eq_zero_of_notMem_tsupport hz⟩
  have hf : (fun s => -τ (-s)) 0 = 0 ∧
      ∀ s, HasDerivAt (fun r => -τ (-r)) (normalSpeed ε (-τ (-s))) s := by
    refine ⟨by simp [h0],?_⟩
    intro s
    have hh := ((hd (-s)).comp s (hasDerivAt_neg s)).neg
    rw [normalSpeed_even]
    convert! hh using 1 <;> ring
  have he : (fun s => -τ (-s)) = τ :=
    (FlowCalculus.exists_unique_global_trajectory_of_compact_support (fun _ z => normalSpeed ε z)
      ((normalSpeed_contDiff ε).comp contDiff_snd) hs 0 0).unique hf ⟨h0,hd⟩
  intro t
  have hh := congrFun he t
  linarith

theorem normal_trajectory_covers_interval (ε : ℝ) (hε : 0 < ε) (τ : ℝ → ℝ)
    (h0 : τ 0 = 0) (hd : ∀ t, HasDerivAt τ (normalSpeed ε (τ t)) t)
    (hstrip : ∀ t, |τ t| < ε) :
    StrictMono τ ∧ ∀ z, |z| < ε → ∃ t, τ t = z := by
  have hdiff : Differentiable ℝ τ := fun t => (hd t).differentiableAt
  have hmono : StrictMono τ := strictMono_of_deriv_pos fun t => by
    rw [(hd t).deriv]
    exact normalSpeed_pos ε (τ t) hε (hstrip t)
  have hpositive : ∀ z, 0 < z → z < ε → ∃ t, τ t = z := by
    intro z hz hze
    by_contra hn
    have hneq : ∀ t, τ t ≠ z := by simpa only [not_exists] using hn
    have hbelow : ∀ t, 0 ≤ t → τ t < z := by
      intro t ht
      by_contra hout
      have hr : z ≤ τ t := not_lt.mp hout
      obtain ⟨s,hs,he⟩ := intermediate_value_Icc ht hdiff.continuous.continuousOn
        (show z ∈ Icc (τ 0) (τ t) by rw [h0]; exact ⟨hz.le,hr⟩)
      exact hneq s he
    obtain ⟨m,hm,hbound⟩ := isCompact_Icc.exists_forall_le'
      (normalSpeed_contDiff ε).continuous.continuousOn (fun x hx =>
        normalSpeed_pos ε x hε (by rw [abs_of_nonneg hx.1]; exact hx.2.trans_lt hze))
    let T : ℝ := (z+1)/m
    have hT : 0 < T := div_pos (by linarith) hm
    have hτbound : ∀ s, 0 ≤ s → m ≤ deriv τ s := by
      intro s hs
      rw [(hd s).deriv]
      apply hbound
      constructor
      · have hh := hmono.monotone hs
        rwa [h0] at hh
      · exact (hbelow s hs).le
    have hgrow := (convex_Icc (0:ℝ) T).mul_sub_le_image_sub_of_le_deriv
      hdiff.continuous.continuousOn hdiff.differentiableOn
      (fun s hs => hτbound s (interior_subset hs).1) 0 (by simp [hT.le]) T (by simp [hT.le]) hT.le
    have hmT : m*T = z+1 := by dsimp [T]; field_simp
    have htbelow := hbelow T hT.le
    rw [h0] at hgrow
    nlinarith
  refine ⟨hmono,?_⟩
  intro z hz
  rcases lt_trichotomy z 0 with hn | he | hp
  · obtain ⟨t,ht⟩ := hpositive (-z) (by linarith) (by simpa [abs_of_neg hn] using hz)
    refine ⟨-t,?_⟩
    rw [normal_trajectory_odd ε hε τ h0 hd,ht]
    ring
  · exact ⟨0,h0.trans he.symm⟩
  · exact hpositive z hp (by simpa [abs_of_pos hp] using hz)

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

lemma geometric_flow_clock (u : P → ℝ) (β : P → P) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hpos : ∀ x, 0 < invariantVolume u β x)
    (hε : 0 < ε) (hLegendrian : ∀ x, diskSq x = 1 → β x 0*(-x 1)+β x 1*x 0 = 0)
    (ψ : ℝ → V → V) (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (geometricField u β ε (ψ t y)) t) :
    ∀ y, diskSq (xyMap y) ≤ 1 → y 2 = 0 → ∀ t, ψ t y 2 = ψ t 0 2 := by
  intro y hy hy0
  have hzero : diskSq (xyMap (0:V)) ≤ 1 := by norm_num [diskSq]
  have hdy := geometric_flow_normal_derivative u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hd y hy
  have hd0 := geometric_flow_normal_derivative u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hd 0 hzero
  have hs : ∃ C : Set ℝ, IsCompact C ∧ ∀ (t : ℝ) z, z ∉ C → normalSpeed ε z = 0 :=
    ⟨tsupport (normalSpeed ε),normalSpeed_compact ε hε,fun _ _ hz => image_eq_zero_of_notMem_tsupport hz⟩
  have he : (fun t => ψ t y 2) = fun t => ψ t 0 2 :=
    (FlowCalculus.exists_unique_global_trajectory_of_compact_support (fun _ z => normalSpeed ε z)
      ((normalSpeed_contDiff ε).comp contDiff_snd) hs 0 0).unique
      ⟨by simp [h0,hy0],hdy⟩ ⟨by simp [h0],hd0⟩
  exact fun t => congrFun he t

lemma geometric_flow_clock_data (u : P → ℝ) (β : P → P) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hpos : ∀ x, 0 < invariantVolume u β x)
    (hε : 0 < ε) (hLegendrian : ∀ x, diskSq x = 1 → β x 0*(-x 1)+β x 1*x 0 = 0)
    (ψ : ℝ → V → V) (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y) (hbij : ∀ t, Bijective (ψ t))
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (geometricField u β ε (ψ t y)) t) :
    let τ : ℝ → ℝ := fun t => ψ t 0 2
    ContDiff ℝ ∞ τ ∧ τ 0 = 0 ∧ StrictMono τ ∧
      (∀ t, |τ t| < ε) ∧ (∀ z, |z| < ε → ∃ t, τ t = z) := by
  dsimp only
  have hz : diskSq (xyMap (0:V)) ≤ 1 := by norm_num [diskSq]
  have hτd := geometric_flow_normal_derivative u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hd 0 hz
  have hs : ∀ t, |ψ t 0 2| < ε := fun t => geometric_flow_preserves_strip u β ε hu hβ hpos hε
    ψ h0 hbij hd t 0 (by simpa using hε)
  have hτ0 : ψ 0 0 2 = 0 := by simp [h0]
  obtain ⟨hm,hr⟩ := normal_trajectory_covers_interval ε hε (fun t => ψ t 0 2) hτ0 hτd hs
  refine ⟨?_,hτ0,hm,hs,hr⟩
  exact (contDiff_apply ℝ ℝ 2).comp (hψ.comp (contDiff_id.prodMk contDiff_const))

theorem geometric_flowCollar_bijOn (u : P → ℝ) (β : P → P) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hpos : ∀ x, 0 < invariantVolume u β x)
    (hε : 0 < ε) (hLegendrian : ∀ x, diskSq x = 1 → β x 0*(-x 1)+β x 1*x 0 = 0)
    (ψ : ℝ → V → V) (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y) (hbij : ∀ t, Bijective (ψ t))
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (geometricField u β ε (ψ t y)) t) :
    BijOn (flowCollar ψ) {y | diskSq (xyMap y) ≤ 1}
      {y | diskSq (xyMap y) ≤ 1 ∧ |y 2| < ε} := by
  have hclock := geometric_flow_clock u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hd
  obtain ⟨hτ,hτ0,hmono,hstrip,hcover⟩ := geometric_flow_clock_data u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hbij hd
  have hn := autonomous_flow_neg (geometricField u β ε) (geometricField_contDiff u β ε hu hβ hpos)
    (geometricField_compact u β ε hε) ψ h0 hd
  have hnormal : ∀ y, diskSq (xyMap y) ≤ 1 → flowCollar ψ y 2 = ψ (y 2) 0 2 := by
    intro y hy
    exact hclock (center y) (by simpa only [xyMap_center] using hy) (center_two y) (y 2)
  refine ⟨?_,?_,?_⟩
  · intro y hy
    change diskSq (xyMap y) ≤ 1 at hy
    exact ⟨geometric_flow_preserves_disk u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hd (y 2) (center y)
      (by simpa only [xyMap_center] using hy),by rw [hnormal y hy]; exact hstrip (y 2)⟩
  · intro y hy z hz he
    have ht : y 2 = z 2 := hmono.injective (by
      have hh := congrFun he 2
      rw [hnormal y hy,hnormal z hz] at hh
      exact hh)
    have hc : center y = center z := (hbij (y 2)).1 (by simpa only [flowCollar,← ht] using he)
    ext i
    fin_cases i
    · exact congrFun hc 0
    · exact congrFun hc 1
    · exact ht
  · intro y hy
    obtain ⟨t,ht⟩ := hcover (y 2) hy.2
    let p := ψ (-t) y
    have hp : diskSq (xyMap p) ≤ 1 :=
      geometric_flow_preserves_disk u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hd (-t) y hy.1
    have hpt : ψ t p = y := by simpa [p] using hn (-t) y
    have hdP := geometric_flow_normal_derivative u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hd p hp
    have hz : diskSq (xyMap (0:V)) ≤ 1 := by norm_num [diskSq]
    have hd0 := geometric_flow_normal_derivative u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hd 0 hz
    have hsupp : ∃ C : Set ℝ, IsCompact C ∧ ∀ (s : ℝ) z, z ∉ C → normalSpeed ε z = 0 :=
      ⟨tsupport (normalSpeed ε),normalSpeed_compact ε hε,fun _ _ hz => image_eq_zero_of_notMem_tsupport hz⟩
    have hc : (fun s => ψ s p 2) = fun s => ψ s 0 2 :=
      (FlowCalculus.exists_unique_global_trajectory_of_compact_support (fun _ z => normalSpeed ε z)
        ((normalSpeed_contDiff ε).comp contDiff_snd) hsupp t (y 2)).unique
        ⟨by rw [hpt],hdP⟩ ⟨ht,hd0⟩
    have hp0 : p 2 = 0 := by
      have hh := congrFun hc 0
      simpa only [h0,Pi.zero_apply] using hh
    refine ⟨![p 0,p 1,t],?_,?_⟩
    · have hh : xyMap ![p 0,p 1,t] = xyMap p := by
        ext i
        fin_cases i <;> simp
      change diskSq (xyMap ![p 0,p 1,t]) ≤ 1
      rw [hh]
      exact hp
    · change ψ t (center ![p 0,p 1,t]) = y
      have hh : center ![p 0,p 1,t] = p := by ext i; fin_cases i <;> simp [hp0]
      rw [hh,hpt]

lemma geometric_flowCollar_derivative_injective (u : P → ℝ) (β : P → P) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hpos : ∀ x, 0 < invariantVolume u β x)
    (hε : 0 < ε) (ψ : ℝ → V → V) (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (geometricField u β ε (ψ t y)) t) :
    ∀ y, diskSq (xyMap y) ≤ 1 → Injective (fderiv ℝ (flowCollar ψ) y) := by
  intro y hy
  let X := geometricField u β ε
  have hX : ContDiff ℝ ∞ X := geometricField_contDiff u β ε hu hβ hpos
  have hcX : HasCompactSupport X := geometricField_compact u β ε hε
  have hinj := FlowCalculus.smooth_flow_spatial_derivative_injective (fun _ z => X z) ψ
    (hX.comp contDiff_snd) hψ h0 hd (y 2) (center y)
  have htrans := autonomous_flow_transports_field X hX hcX ψ hψ h0 hd (y 2) (center y)
  have hn : X (center y) 2 = 1 := by
    rw [show X (center y) = compressionField u β (normalSpeed ε) (center y) from
      localizedField_agrees u β ε hu hβ hpos _ (by simpa only [xyMap_center] using hy)]
    simp [compressionField,normalSpeed_at_zero ε hε,Matrix.vecHead,Matrix.vecTail]
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
    rw [center_two,hn] at hh
    simpa using hh
  simp only [hz,zero_smul,add_zero] at hk
  ext i
  fin_cases i
  · simpa using congrFun hk 0
  · simpa using congrFun hk 1
  · exact hz

lemma geometric_flowCollar_pullback (u : P → ℝ) (β : P → P) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hpos : ∀ x, 0 < invariantVolume u β x)
    (hε : 0 < ε) (ψ : ℝ → V → V) (lam : ℝ → V → ℝ)
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (geometricField u β ε (ψ t y)) t)
    (hpb : ∀ t y v, covector (invariantCoefficients u β (ψ t y)) (fderiv ℝ (ψ t) y v) =
      lam t y*covector (invariantCoefficients u β y) v)
    (hH : ∀ t y, localizedHamiltonian u ε (ψ t y) = lam t y*localizedHamiltonian u ε y) :
    ∀ y, diskSq (xyMap y) ≤ 1 → ∀ v,
      covector (invariantCoefficients u β (flowCollar ψ y)) (fderiv ℝ (flowCollar ψ) y v) =
        lam (y 2) (center y)*covector (invariantCoefficients u β y) v := by
  intro y hy v
  let a := invariantCoefficients u β
  let H := localizedHamiltonian u ε
  have hQ : ∀ z, dot (a z) (curlLinear (fderiv ℝ a z)) ≠ 0 := by
    intro z
    rw [invariant_volume_formula u β hu hβ]
    exact (hpos _).ne'
  have hvalue : ∀ z, covector (a z) (geometricField u β ε z) = H z := by
    intro z
    exact (hamiltonian_algebra (a z) (curlLinear (fderiv ℝ a z)) (gradient3 H z) 0 (H z) (hQ z)).1
  have hcenter : H (center y) = u (xyMap y) := by
    change diskCutoff (xyMap (center y))*(normalSpeed ε (center y 2)*u (xyMap (center y))) = _
    rw [xyMap_center,center_two,normalSpeed_at_zero ε hε,
      diskCutoff_one _ (by linarith : diskSq (xyMap y) < 2)]
    ring
  have hHflow : H (flowCollar ψ y) = lam (y 2) (center y)*H (center y) := hH (y 2) (center y)
  rw [flowCollar_fderiv (geometricField u β ε) ψ hψ hd,map_add,map_smul]
  change v 2*covector (a (flowCollar ψ y)) (geometricField u β ε (flowCollar ψ y))+
    covector (a (ψ (y 2) (center y))) (fderiv ℝ (ψ (y 2)) (center y) (center v)) = _
  rw [hvalue,hpb,hHflow,hcenter]
  simp [a,covector_apply,dot,invariantCoefficients]
  ring

theorem geometric_flowCollar_embedding (u : P → ℝ) (β : P → P) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hpos : ∀ x, 0 < invariantVolume u β x)
    (hε : 0 < ε) (hLegendrian : ∀ x, diskSq x = 1 → β x 0*(-x 1)+β x 1*x 0 = 0)
    (ψ : ℝ → V → V) (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y) (hbij : ∀ t, Bijective (ψ t))
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (geometricField u β ε (ψ t y)) t) :
    IsEmbedding (fun y : {y : V // diskSq (xyMap y) ≤ 1} => flowCollar ψ y) := by
  let S := {y : V // diskSq (xyMap y) ≤ 1}
  let T := {y : V // diskSq (xyMap y) ≤ 1 ∧ |y 2| < ε}
  let τ : ℝ → ℝ := fun t => ψ t 0 2
  obtain ⟨hτ,hτ0,hmono,hstrip,hcover⟩ := geometric_flow_clock_data u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hbij hd
  have hrange : range τ = Ioo (-ε) ε := by
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      exact abs_lt.mp (hstrip t)
    · intro hz
      exact hcover z (abs_lt.mpr hz)
  have hemb : IsEmbedding τ := hmono.isEmbedding_of_ordConnected (by rw [hrange]; exact ordConnected_Ioo)
  let clock : ℝ ≃ₜ range τ := hemb.toHomeomorph
  let back : T → ℝ := fun q => clock.symm ⟨q.val 2,by rw [hrange]; exact abs_lt.mp q.property.2⟩
  have hback : Continuous back := clock.symm.continuous.comp
    (((continuous_apply 2).comp continuous_subtype_val).subtype_mk _)
  have hBij := geometric_flowCollar_bijOn u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hbij hd
  let F : S → T := fun y => ⟨flowCollar ψ y,hBij.mapsTo y.property⟩
  have hF : Continuous F := ((flowCollar_contDiff ψ hψ).continuous.comp continuous_subtype_val).subtype_mk _
  have hnormal : ∀ y : S, flowCollar ψ y 2 = τ (y.val 2) := by
    intro y
    exact geometric_flow_clock u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hd (center y)
      (by simpa only [xyMap_center] using y.property) (center_two y) (y.val 2)
  have hbackF : ∀ y : S, back (F y) = y.val 2 := by
    intro y
    have he : (⟨(F y).val 2,by rw [hrange]; exact abs_lt.mp (F y).property.2⟩ : range τ) = clock (y.val 2) :=
      Subtype.ext (by simpa [F,clock] using hnormal y)
    change clock.symm _ = _
    rw [he,clock.symm_apply_apply]
  let rawInv : T → V := fun q => ![ψ (-back q) q.val 0,ψ (-back q) q.val 1,back q]
  have hraw : ∀ q : T, diskSq (xyMap (rawInv q)) ≤ 1 := by
    intro q
    have hp := geometric_flow_preserves_disk u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hd (-back q) q.val q.property.1
    have he : xyMap (rawInv q) = xyMap (ψ (-back q) q.val) := by ext i; fin_cases i <;> simp [rawInv]
    rw [he]
    exact hp
  have hrawCont : Continuous rawInv := by
    have hp : Continuous (fun q : T => ψ (-back q) q.val) :=
      hψ.continuous.comp (hback.neg.prodMk continuous_subtype_val)
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun q : T => ψ (-back q) q.val 0)
      exact (continuous_apply 0).comp hp
    · change Continuous (fun q : T => ψ (-back q) q.val 1)
      exact (continuous_apply 1).comp hp
    · change Continuous back
      exact hback
  let I : T → S := fun q => ⟨rawInv q,hraw q⟩
  have hI : Continuous I := hrawCont.subtype_mk _
  have hn := autonomous_flow_neg (geometricField u β ε) (geometricField_contDiff u β ε hu hβ hpos)
    (geometricField_compact u β ε hε) ψ h0 hd
  have hleft : LeftInverse I F := by
    intro y
    apply Subtype.ext
    have hp : ψ (-back (F y)) (F y).val = center y := by
      change ψ (-back (F y)) (flowCollar ψ y) = center y
      rw [hbackF]
      exact hn (y.val 2) (center y)
    ext i
    fin_cases i
    · simpa [I,rawInv] using congrFun hp 0
    · simpa [I,rawInv] using congrFun hp 1
    · exact hbackF y
  have hright : RightInverse I F := by
    intro q
    obtain ⟨y,hy,he⟩ := hBij.surjOn q.property
    have hf : F ⟨y,hy⟩ = q := Subtype.ext he
    rw [← hf,hleft]
  let E : S ≃ₜ T :=
    { toFun := F
      invFun := I
      left_inv := hleft
      right_inv := hright
      continuous_toFun := hF
      continuous_invFun := hI }
  exact IsEmbedding.subtypeVal.comp E.isEmbedding

theorem exists_geometric_disk_collar (u : P → ℝ) (β : P → P)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hpos : ∀ x, 0 < invariantVolume u β x)
    (hLegendrian : ∀ x, diskSq x = 1 → β x 0*(-x 1)+β x 1*x 0 = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Φ : V → V, ∃ Λ : V → ℝ,
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Λ ∧ (∀ y, 0 < Λ y) ∧
      (∀ y, Φ (center y) = center y) ∧
      BijOn Φ {y | diskSq (xyMap y) ≤ 1} {y | diskSq (xyMap y) ≤ 1 ∧ |y 2| < ε} ∧
      IsEmbedding (fun y : {y : V // diskSq (xyMap y) ≤ 1} => Φ y) ∧
      (∀ y, diskSq (xyMap y) ≤ 1 → Injective (fderiv ℝ Φ y)) ∧
      ∀ y, diskSq (xyMap y) ≤ 1 → ∀ v,
        covector (invariantCoefficients u β (Φ y)) (fderiv ℝ Φ y v) =
          Λ y*covector (invariantCoefficients u β y) v := by
  let a := invariantCoefficients u β
  let H := localizedHamiltonian u ε
  have ha : ContDiff ℝ ∞ a := invariantCoefficients_contDiff u β hu hβ
  have hH : ContDiff ℝ ∞ H := localizedHamiltonian_contDiff u hu ε
  have hcH : HasCompactSupport H := localizedHamiltonian_compact u ε hε
  have hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0 := by
    intro y
    rw [invariant_volume_formula u β hu hβ]
    exact (hpos _).ne'
  obtain ⟨ψ,ρ,lam,hψ,hρ,hlam,h0,hbij,hρψ,hψρ,hd,hpositive,hpb,hHt⟩ :=
    integrate_hamiltonian_all_time a H ha hH hcH hQ
  let Λ : V → ℝ := fun y => lam (y 2) (center y)
  have hΛ : ContDiff ℝ ∞ Λ := hlam.comp ((contDiff_apply ℝ ℝ 2).prodMk center.contDiff)
  refine ⟨flowCollar ψ,Λ,flowCollar_contDiff ψ hψ,hΛ,fun y => hpositive _ _,?_,?_,?_,?_,?_⟩
  · intro y
    simp [flowCollar,h0]
  · exact geometric_flowCollar_bijOn u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hbij hd
  · exact geometric_flowCollar_embedding u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hbij hd
  · exact geometric_flowCollar_derivative_injective u β ε hu hβ hpos hε ψ hψ h0 hd
  · exact geometric_flowCollar_pullback u β ε hu hβ hpos hε ψ lam hψ hd hpb hHt

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem relative_invariant_collar_realization (u : P → ℝ) (β₀ β₁ : P → P)
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
      (∀ t y, β₁ (xyMap y) = β₀ (xyMap y) → H t y = y) ∧
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
  have hfixeq : ∀ t y, β₁ (xyMap y) = β₀ (xyMap y) → ψ t y = y := by
    intro t y hy
    apply ambient_flow_fixes X ψ hX hsupp hψ0 hflow y _ t
    intro s
    have he : a₁ y = a₀ y := by
      rw [heqa]
      dsimp only
      have hh : horizontalTaper (fun x => β₁ x-β₀ x) χ y = 0 := by
        rw [xyMap_apply] at hy
        simp [horizontalTaper,hy]
      rw [hh,add_zero]
    have hv := blend_stationary a₀ a₁ ha₀ ha₁ y he s
    simp [X,moser,A,hv,cross]
  refine ⟨ρ,ψ,σ,C,hρ,hψ,hσ,hC,?_,hρψ,hψρ,?_,?_,?_,?_,?_⟩
  · intro y
    simpa only [hψ0] using hψρ 0 y
  · intro t y hy
    have hh := hρψ t y
    rw [hfix t y hy] at hh
    exact hh
  · intro t y
    exact inv_pos.mpr (hpos t (ρ t y))
  · intro t y hy
    have hh := hρψ t y
    rw [hfixeq t y hy] at hh
    exact hh
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
open Set Function Filter Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

@[simp] lemma plane_eta (x : P) : ![x 0,x 1] = x := by
  ext i
  fin_cases i <;> rfl

def planeIn : P →L[ℝ] V :=
  (ContinuousLinearMap.proj 0 : P →L[ℝ] ℝ).smulRight (![(1:ℝ),0,0] : V)+
  (ContinuousLinearMap.proj 1 : P →L[ℝ] ℝ).smulRight (![0,(1:ℝ),0] : V)

@[simp] lemma planeIn_apply (x : P) : planeIn x = ![x 0,x 1,0] := by
  ext i
  fin_cases i <;> simp [planeIn]
@[simp] lemma xyMap_planeIn (x : P) : xyMap (planeIn x) = x := by
  ext i
  fin_cases i <;> simp
@[simp] lemma center_planeIn (x : P) : center (planeIn x) = planeIn x := by simp
@[simp] lemma planeIn_two (x : P) : planeIn x 2 = 0 := by simp
lemma planeIn_injective : Injective planeIn := by
  intro x y h
  simpa only [xyMap_planeIn] using congrArg xyMap h

lemma inverse_spatial_derivative_injective (H G : ℝ → V → V)
    (hH : ContDiff ℝ ∞ (fun p : ℝ × V => H p.1 p.2))
    (hG : ContDiff ℝ ∞ (fun p : ℝ × V => G p.1 p.2))
    (hGH : ∀ t y, G t (H t y) = y) (t : ℝ) (y : V) :
    Injective (fderiv ℝ (H t) y) := by
  have hHs : ContDiff ℝ ∞ (H t) := hH.comp (contDiff_const.prodMk contDiff_id)
  have hGs : ContDiff ℝ ∞ (G t) := hG.comp (contDiff_const.prodMk contDiff_id)
  have hc := fderiv_comp y (hGs.differentiable (by simp) _) (hHs.differentiable (by simp) _)
  have he : G t ∘ H t = id := funext (hGH t)
  have hleft : LeftInverse (fderiv ℝ (G t) (H t y)) (fderiv ℝ (H t) y) := by
    intro v
    have hh := congrArg (fun L : V →L[ℝ] V => L v) hc
    simpa [he,id_eq] using hh.symm
  exact hleft.injective

lemma map_preserves_disk_of_fixed_exterior (H : V → V) (hH : Injective H)
    (K : Set P) (hK : K ⊆ {x | diskSq x < 1})
    (hfix : ∀ y, xyMap y ∉ K → H y = y) :
    MapsTo H {y | diskSq (xyMap y) ≤ 1} {y | diskSq (xyMap y) ≤ 1} := by
  intro y hy
  by_contra hn
  have hr : 1 < diskSq (xyMap (H y)) := not_le.mp hn
  have hout : xyMap (H y) ∉ K := fun hk => (hK hk).not_gt hr
  have he : H y = y := hH (hfix (H y) hout)
  rw [he] at hr
  exact (not_lt_of_ge hy) hr


theorem local_disk_foliation_realization (u : P → ℝ) (β₀ β₁ : P → P)
    (hu : ContDiff ℝ ∞ u) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁)
    (hpos₀ : ∀ x, 0 < invariantVolume u β₀ x) (hpos₁ : ∀ x, 0 < invariantVolume u β₁ x)
    (hLegendrian : ∀ x, diskSq x = 1 → β₀ x 0*(-x 1)+β₀ x 1*x 0 = 0)
    (K : Set P) (hK : IsCompact K) (hKD : K ⊆ {x | diskSq x < 1})
    (heq : ∀ x, x ∉ K → β₁ x = β₀ x) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℝ → P → V, ∃ r : P → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × P => k p.1 p.2) ∧ ContDiff ℝ ∞ r ∧
      (∀ x, 0 < r x) ∧ (∀ x, k 0 x = planeIn x) ∧
      (∀ t x, β₁ x = β₀ x → k t x = planeIn x) ∧
      (∀ t x, x ∉ K → k t x = planeIn x) ∧
      (∀ t x, diskSq x ≤ 1 → diskSq (xyMap (k t x)) ≤ 1 ∧ |k t x 2| < ε) ∧
      (∀ t, IsEmbedding (fun x : {x : P // diskSq x ≤ 1} => k t x)) ∧
      (∀ t x, diskSq x ≤ 1 → Injective (fderiv ℝ (k t) x)) ∧
      (∀ t x, diskSq x = 1 →
        covector (invariantCoefficients u β₀ (k t x))
          (fderiv ℝ (k t) x ![-x 1,x 0]) = 0) ∧
      (∀ x, diskSq x ≤ 1 → ∀ v,
        covector (invariantCoefficients u β₀ (k 1 x)) (fderiv ℝ (k 1) x v) =
          r x*(β₁ x 0*v 0+β₁ x 1*v 1)) := by
  obtain ⟨H,G,σ,C,hH,hG,hσ,hC,hinit,hHG,hGH,hfix,hpos,hstat,hdiv,hpb⟩ :=
    relative_invariant_collar_realization u β₀ β₁ hu h₀ h₁ hpos₀ hpos₁ K hK heq
  obtain ⟨Φ,Λ,hΦ,hΛ,hΛpos,hcenter,hbij,hemb,hdinj,hΦpb⟩ :=
    exists_geometric_disk_collar u β₀ hu h₀ hpos₀ hLegendrian ε hε
  have hHs : ∀ t, ContDiff ℝ ∞ (H t) := fun t => hH.comp (contDiff_const.prodMk contDiff_id)
  have hGs : ∀ t, ContDiff ℝ ∞ (G t) := fun t => hG.comp (contDiff_const.prodMk contDiff_id)
  have hHin : ∀ t, Injective (H t) := fun t => (show LeftInverse (G t) (H t) from hGH t).injective
  have hHdisk : ∀ t, MapsTo (H t) {y | diskSq (xyMap y) ≤ 1} {y | diskSq (xyMap y) ≤ 1} := by
    intro t
    exact map_preserves_disk_of_fixed_exterior (H t) (hHin t) K hKD
      (fun y hy => hstat t y (heq _ hy))
  let k : ℝ → P → V := fun t x => Φ (H t (planeIn x))
  let r : P → ℝ := fun x => Λ (H 1 (planeIn x))*σ 1 (planeIn x)
  have hk : ContDiff ℝ ∞ (fun p : ℝ × P => k p.1 p.2) :=
    hΦ.comp (hH.comp (contDiff_fst.prodMk (planeIn.contDiff.comp contDiff_snd)))
  have hr : ContDiff ℝ ∞ r :=
    (hΛ.comp ((hHs 1).comp planeIn.contDiff)).mul
      (hσ.comp (contDiff_const.prodMk planeIn.contDiff))
  have hkeq : ∀ t x, β₁ x = β₀ x → k t x = planeIn x := by
    intro t x hx
    have hh := hstat t (planeIn x) (by simpa only [xyMap_planeIn] using hx)
    dsimp only [k]
    rw [hh,← center_planeIn x,hcenter,center_planeIn]
  have hkfix : ∀ t x, x ∉ K → k t x = planeIn x :=
    fun t x hx => hkeq t x (heq x hx)
  have hkD : ∀ t x, diskSq x ≤ 1 → diskSq (xyMap (H t (planeIn x))) ≤ 1 := by
    intro t x hx
    exact hHdisk t (by
      change diskSq (xyMap (planeIn x)) ≤ 1
      simpa only [xyMap_planeIn] using hx)
  have hdk : ∀ t x, fderiv ℝ (k t) x =
      (fderiv ℝ Φ (H t (planeIn x))).comp ((fderiv ℝ (H t) (planeIn x)).comp planeIn) := by
    intro t x
    have hc := fderiv_comp x (hΦ.differentiable (by simp) _) (((hHs t).comp planeIn.contDiff).differentiable (by simp) x)
    rw [show k t = Φ ∘ (H t ∘ planeIn) from rfl,hc,
      fderiv_comp x ((hHs t).differentiable (by simp) _) (planeIn.differentiable x),planeIn.fderiv]
    rfl
  refine ⟨k,r,hk,hr,?_,?_,hkeq,hkfix,?_,?_,?_,?_,?_⟩
  · intro x
    exact mul_pos (hΛpos _) (hpos _ _)
  · intro x
    dsimp only [k]
    rw [hinit,← center_planeIn x,hcenter,center_planeIn]
  · intro t x hx
    exact hbij.mapsTo (hkD t x hx)
  · intro t
    let D := {x : P // diskSq x ≤ 1}
    let Z := {y : V // diskSq (xyMap y) ≤ 1}
    let F : D → Z := fun x => ⟨H t (planeIn x),hkD t x x.property⟩
    have hplane : IsEmbedding planeIn :=
      (show LeftInverse xyMap planeIn from xyMap_planeIn).isEmbedding xyMap.continuous planeIn.continuous
    have hHE : IsEmbedding (H t) :=
      (show LeftInverse (G t) (H t) from hGH t).isEmbedding (hGs t).continuous (hHs t).continuous
    have hF : IsEmbedding F := IsEmbedding.of_comp
      (((hHs t).continuous.comp (planeIn.continuous.comp continuous_subtype_val)).subtype_mk _)
      continuous_subtype_val (hHE.comp (hplane.comp IsEmbedding.subtypeVal))
    exact hemb.comp hF
  · intro t x hx
    rw [hdk]
    exact (hdinj _ (hkD t x hx)).comp
      ((inverse_spatial_derivative_injective H G hH hG hGH t (planeIn x)).comp planeIn_injective)
  · intro t x hx
    have hxK : x ∉ K := fun h => (hKD h).ne hx
    have hevent : k t =ᶠ[𝓝 x] planeIn := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      exact hkfix t y hy
    have hd : fderiv ℝ (k t) x = planeIn := by
      rw [hevent.fderiv_eq,planeIn.fderiv]
    rw [hkfix t x hxK,hd]
    simpa [covector_apply,dot,invariantCoefficients] using hLegendrian x hx
  · intro x hx v
    rw [hdk]
    change covector (invariantCoefficients u β₀ (Φ (H 1 (planeIn x))))
      (fderiv ℝ Φ (H 1 (planeIn x)) (fderiv ℝ (H 1) (planeIn x) (planeIn v))) = _
    rw [hΦpb _ (hkD 1 x hx)]
    have hp := hpb (planeIn x) (by simp) (planeIn v)
    change covector (invariantCoefficients u β₀ (H 1 (planeIn x)))
      (fderiv ℝ (H 1) (planeIn x) (planeIn v)) =
      σ 1 (planeIn x)*covector (invariantCoefficients u β₁ (planeIn x)) (planeIn v) at hp
    rw [hp]
    simp [r,covector_apply,dot,invariantCoefficients,mul_assoc]


lemma closed_disk_isCompact : IsCompact {x : P | diskSq x ≤ 1} := by
  apply (isCompact_Icc : IsCompact (Icc (![-1,-1] : P) ![1,1])).of_isClosed_subset
    (isClosed_le diskSq_contDiff.continuous continuous_const)
  intro x hx
  have h : x 0^2+x 1^2 ≤ 1 := hx
  have h₀ : -1 ≤ x 0 ∧ x 0 ≤ 1 := by constructor <;> nlinarith [sq_nonneg (x 1)]
  have h₁ : -1 ≤ x 1 ∧ x 1 ≤ 1 := by constructor <;> nlinarith [sq_nonneg (x 0)]
  constructor
  · intro i
    fin_cases i
    · exact h₀.1
    · exact h₁.1
  · intro i
    fin_cases i
    · exact h₀.2
    · exact h₁.2

lemma exists_disk_tube_in_open (U : Set V) (hU : IsOpen U)
    (hDU : ∀ x, diskSq x ≤ 1 → planeIn x ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y, diskSq (xyMap y) ≤ 1 → |y 2| < ε → y ∈ U := by
  let join : P × ℝ → V := fun p => ![p.1 0,p.1 1,p.2]
  have hjoin : Continuous join := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [join] <;> fun_prop
  have hs : {x : P | diskSq x ≤ 1} ×ˢ ({0} : Set ℝ) ⊆ join ⁻¹' U := by
    rintro ⟨x,z⟩ ⟨hx,hz⟩
    have hz0 : z = 0 := hz
    subst z
    simpa [join] using hDU x hx
  obtain ⟨A,B,hA,hB,hDA,h0B,hAB⟩ := generalized_tube_lemma closed_disk_isCompact
    isCompact_singleton (hU.preimage hjoin) hs
  have hzero : (0:ℝ) ∈ B := h0B (by simp)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds hzero)
  refine ⟨ε,hε,?_⟩
  intro y hy hz
  have hpair : (xyMap y,y 2) ∈ A ×ˢ B :=
    ⟨hDA hy,hball (by simpa [Metric.mem_ball,Real.dist_eq] using hz)⟩
  have hh := hAB hpair
  have he : join (xyMap y,y 2) = y := by
    ext i
    fin_cases i <;> simp [join]
  change join (xyMap y,y 2) ∈ U at hh
  simpa only [he] using hh

theorem neighborhood_disk_foliation_realization (u : P → ℝ) (β₀ β₁ : P → P)
    (hu : ContDiff ℝ ∞ u) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁)
    (hpos₀ : ∀ x, 0 < invariantVolume u β₀ x) (hpos₁ : ∀ x, 0 < invariantVolume u β₁ x)
    (hLegendrian : ∀ x, diskSq x = 1 → β₀ x 0*(-x 1)+β₀ x 1*x 0 = 0)
    (K : Set P) (hK : IsCompact K) (hKD : K ⊆ {x | diskSq x < 1})
    (heq : ∀ x, x ∉ K → β₁ x = β₀ x) (U : Set V) (hU : IsOpen U)
    (hDU : ∀ x, diskSq x ≤ 1 → planeIn x ∈ U) :
    ∃ k : ℝ → P → V, ∃ r : P → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × P => k p.1 p.2) ∧ ContDiff ℝ ∞ r ∧
      (∀ x, 0 < r x) ∧ (∀ x, k 0 x = planeIn x) ∧
      (∀ t x, β₁ x = β₀ x → k t x = planeIn x) ∧
      (∀ t x, x ∉ K → k t x = planeIn x) ∧
      (∀ t x, diskSq x ≤ 1 → diskSq (xyMap (k t x)) ≤ 1 ∧ k t x ∈ U) ∧
      (∀ t, IsEmbedding (fun x : {x : P // diskSq x ≤ 1} => k t x)) ∧
      (∀ t x, diskSq x ≤ 1 → Injective (fderiv ℝ (k t) x)) ∧
      (∀ t x, diskSq x = 1 →
        covector (invariantCoefficients u β₀ (k t x))
          (fderiv ℝ (k t) x ![-x 1,x 0]) = 0) ∧
      (∀ x, diskSq x ≤ 1 → ∀ v,
        covector (invariantCoefficients u β₀ (k 1 x)) (fderiv ℝ (k 1) x v) =
          r x*(β₁ x 0*v 0+β₁ x 1*v 1)) := by
  obtain ⟨ε,hε,hbound⟩ := exists_disk_tube_in_open U hU hDU
  obtain ⟨k,r,hk,hr,hpos,hinit,hstat,hfix,hthin,hemb,hinj,hLegend,hpb⟩ :=
    local_disk_foliation_realization u β₀ β₁ hu h₀ h₁ hpos₀ hpos₁ hLegendrian K hK hKD heq ε hε
  refine ⟨k,r,hk,hr,hpos,hinit,hstat,hfix,?_,hemb,hinj,hLegend,hpb⟩
  intro t x hx
  exact ⟨(hthin t x hx).1,hbound _ (hthin t x hx).1 (hthin t x hx).2⟩

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma geometric_flow_zero_horizontal (u : P → ℝ) (β : P → P) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hpos : ∀ x, 0 < invariantVolume u β x)
    (hε : 0 < ε) (ψ : ℝ → V → V) (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (geometricField u β ε (ψ t y)) t)
    (y : V) (hy : diskSq (xyMap y) ≤ 1) (hz : u (xyMap y) = 0) (t : ℝ) :
    xyMap (ψ t y) = xyMap y := by
  let X : ℝ → V → V := fun _ => geometricField u β ε
  have hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2) :=
    (geometricField_contDiff u β ε hu hβ hpos).comp contDiff_snd
  have hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0 :=
    ⟨tsupport (geometricField u β ε),geometricField_compact u β ε hε,
      fun _ _ hn => image_eq_zero_of_notMem_tsupport hn⟩
  have hver : ∀ s z, X s ![y 0,y 1,z] 0 = 0 ∧ X s ![y 0,y 1,z] 1 = 0 := by
    intro s z
    have he : xyMap (![y 0,y 1,z] : V) = xyMap y := by ext i; fin_cases i <;> simp
    have hh := localizedField_agrees u β ε hu hβ hpos ![y 0,y 1,z] (by simpa only [he] using hy)
    change geometricField u β ε ![y 0,y 1,z] = _ at hh
    dsimp only [X]
    rw [hh]
    have hz' : u ![y 0,y 1] = 0 := by simpa only [xyMap_apply] using hz
    constructor <;> simp [compressionField,planarCharacteristic,hz']
  have hh := flow_preserves_vertical_fibre X ψ hX hsupp h0 hd y hver t
  ext i
  fin_cases i
  · simpa using hh.1
  · simpa using hh.2

lemma geometric_flowCollar_zero_horizontal (u : P → ℝ) (β : P → P) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hpos : ∀ x, 0 < invariantVolume u β x)
    (hε : 0 < ε) (ψ : ℝ → V → V) (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (geometricField u β ε (ψ t y)) t)
    (y : V) (hy : diskSq (xyMap y) ≤ 1) (hz : u (xyMap y) = 0) :
    xyMap (flowCollar ψ y) = xyMap y := by
  change xyMap (ψ (y 2) (center y)) = xyMap y
  simpa only [xyMap_center] using geometric_flow_zero_horizontal u β ε hu hβ hpos hε ψ h0 hd
    (center y) (by simpa only [xyMap_center] using hy) (by simpa only [xyMap_center] using hz) (y 2)


theorem exists_geometric_disk_collar_tracked (u : P → ℝ) (β : P → P)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hpos : ∀ x, 0 < invariantVolume u β x)
    (hLegendrian : ∀ x, diskSq x = 1 → β x 0*(-x 1)+β x 1*x 0 = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Φ : V → V, ∃ Λ : V → ℝ,
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Λ ∧ (∀ y, 0 < Λ y) ∧
      (∀ y, Φ (center y) = center y) ∧
      BijOn Φ {y | diskSq (xyMap y) ≤ 1} {y | diskSq (xyMap y) ≤ 1 ∧ |y 2| < ε} ∧
      (∀ y, diskSq (xyMap y) ≤ 1 → u (xyMap y) = 0 → xyMap (Φ y) = xyMap y) ∧
      IsEmbedding (fun y : {y : V // diskSq (xyMap y) ≤ 1} => Φ y) ∧
      (∀ y, diskSq (xyMap y) ≤ 1 → Injective (fderiv ℝ Φ y)) ∧
      ∀ y, diskSq (xyMap y) ≤ 1 → ∀ v,
        covector (invariantCoefficients u β (Φ y)) (fderiv ℝ Φ y v) =
          Λ y*covector (invariantCoefficients u β y) v := by
  let a := invariantCoefficients u β
  let H := localizedHamiltonian u ε
  have ha : ContDiff ℝ ∞ a := invariantCoefficients_contDiff u β hu hβ
  have hH : ContDiff ℝ ∞ H := localizedHamiltonian_contDiff u hu ε
  have hcH : HasCompactSupport H := localizedHamiltonian_compact u ε hε
  have hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0 := by
    intro y
    rw [invariant_volume_formula u β hu hβ]
    exact (hpos _).ne'
  obtain ⟨ψ,ρ,lam,hψ,hρ,hlam,h0,hbij,hρψ,hψρ,hd,hpositive,hpb,hHt⟩ :=
    integrate_hamiltonian_all_time a H ha hH hcH hQ
  let Λ : V → ℝ := fun y => lam (y 2) (center y)
  have hΛ : ContDiff ℝ ∞ Λ := hlam.comp ((contDiff_apply ℝ ℝ 2).prodMk center.contDiff)
  refine ⟨flowCollar ψ,Λ,flowCollar_contDiff ψ hψ,hΛ,fun y => hpositive _ _,?_,?_,?_,?_,?_,?_⟩
  · intro y
    simp [flowCollar,h0]
  · exact geometric_flowCollar_bijOn u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hbij hd
  · exact geometric_flowCollar_zero_horizontal u β ε hu hβ hpos hε ψ h0 hd
  · exact geometric_flowCollar_embedding u β ε hu hβ hpos hε hLegendrian ψ hψ h0 hbij hd
  · exact geometric_flowCollar_derivative_injective u β ε hu hβ hpos hε ψ hψ h0 hd
  · exact geometric_flowCollar_pullback u β ε hu hβ hpos hε ψ lam hψ hd hpb hHt


end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem local_disk_foliation_realization_tracked (u : P → ℝ) (β₀ β₁ : P → P)
    (hu : ContDiff ℝ ∞ u) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁)
    (hpos₀ : ∀ x, 0 < invariantVolume u β₀ x) (hpos₁ : ∀ x, 0 < invariantVolume u β₁ x)
    (hLegendrian : ∀ x, diskSq x = 1 → β₀ x 0*(-x 1)+β₀ x 1*x 0 = 0)
    (K : Set P) (hK : IsCompact K) (hKD : K ⊆ {x | diskSq x < 1})
    (heq : ∀ x, x ∉ K → β₁ x = β₀ x) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℝ → P → V, ∃ r : P → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × P => k p.1 p.2) ∧ ContDiff ℝ ∞ r ∧
      (∀ x, 0 < r x) ∧ (∀ x, k 0 x = planeIn x) ∧
      (∀ t x, β₁ x = β₀ x → k t x = planeIn x) ∧
      (∀ t x, x ∉ K → k t x = planeIn x) ∧
      (∀ t x, diskSq x ≤ 1 → diskSq (xyMap (k t x)) ≤ 1 ∧ |k t x 2| < ε) ∧
      (∀ t x, diskSq x ≤ 1 → u x = 0 → xyMap (k t x) = x) ∧
      (∀ t, IsEmbedding (fun x : {x : P // diskSq x ≤ 1} => k t x)) ∧
      (∀ t x, diskSq x ≤ 1 → Injective (fderiv ℝ (k t) x)) ∧
      (∀ t x, diskSq x = 1 →
        covector (invariantCoefficients u β₀ (k t x))
          (fderiv ℝ (k t) x ![-x 1,x 0]) = 0) ∧
      (∀ x, diskSq x ≤ 1 → ∀ v,
        covector (invariantCoefficients u β₀ (k 1 x)) (fderiv ℝ (k 1) x v) =
          r x*(β₁ x 0*v 0+β₁ x 1*v 1)) := by
  obtain ⟨H,G,σ,C,hH,hG,hσ,hC,hinit,hHG,hGH,hfix,hpos,hstat,hdiv,hpb⟩ :=
    relative_invariant_collar_realization u β₀ β₁ hu h₀ h₁ hpos₀ hpos₁ K hK heq
  obtain ⟨Φ,Λ,hΦ,hΛ,hΛpos,hcenter,hbij,hΦzero,hemb,hdinj,hΦpb⟩ :=
    exists_geometric_disk_collar_tracked u β₀ hu h₀ hpos₀ hLegendrian ε hε
  have hHs : ∀ t, ContDiff ℝ ∞ (H t) := fun t => hH.comp (contDiff_const.prodMk contDiff_id)
  have hGs : ∀ t, ContDiff ℝ ∞ (G t) := fun t => hG.comp (contDiff_const.prodMk contDiff_id)
  have hHin : ∀ t, Injective (H t) := fun t => (show LeftInverse (G t) (H t) from hGH t).injective
  have hHdisk : ∀ t, MapsTo (H t) {y | diskSq (xyMap y) ≤ 1} {y | diskSq (xyMap y) ≤ 1} := by
    intro t
    exact map_preserves_disk_of_fixed_exterior (H t) (hHin t) K hKD
      (fun y hy => hstat t y (heq _ hy))
  let k : ℝ → P → V := fun t x => Φ (H t (planeIn x))
  let r : P → ℝ := fun x => Λ (H 1 (planeIn x))*σ 1 (planeIn x)
  have hk : ContDiff ℝ ∞ (fun p : ℝ × P => k p.1 p.2) :=
    hΦ.comp (hH.comp (contDiff_fst.prodMk (planeIn.contDiff.comp contDiff_snd)))
  have hr : ContDiff ℝ ∞ r :=
    (hΛ.comp ((hHs 1).comp planeIn.contDiff)).mul
      (hσ.comp (contDiff_const.prodMk planeIn.contDiff))
  have hkeq : ∀ t x, β₁ x = β₀ x → k t x = planeIn x := by
    intro t x hx
    have hh := hstat t (planeIn x) (by simpa only [xyMap_planeIn] using hx)
    dsimp only [k]
    rw [hh,← center_planeIn x,hcenter,center_planeIn]
  have hkfix : ∀ t x, x ∉ K → k t x = planeIn x :=
    fun t x hx => hkeq t x (heq x hx)
  have hkD : ∀ t x, diskSq x ≤ 1 → diskSq (xyMap (H t (planeIn x))) ≤ 1 := by
    intro t x hx
    exact hHdisk t (by
      change diskSq (xyMap (planeIn x)) ≤ 1
      simpa only [xyMap_planeIn] using hx)
  have hdk : ∀ t x, fderiv ℝ (k t) x =
      (fderiv ℝ Φ (H t (planeIn x))).comp ((fderiv ℝ (H t) (planeIn x)).comp planeIn) := by
    intro t x
    have hc := fderiv_comp x (hΦ.differentiable (by simp) _) (((hHs t).comp planeIn.contDiff).differentiable (by simp) x)
    rw [show k t = Φ ∘ (H t ∘ planeIn) from rfl,hc,
      fderiv_comp x ((hHs t).differentiable (by simp) _) (planeIn.differentiable x),planeIn.fderiv]
    rfl
  refine ⟨k,r,hk,hr,?_,?_,hkeq,hkfix,?_,?_,?_,?_,?_,?_⟩
  · intro x
    exact mul_pos (hΛpos _) (hpos _ _)
  · intro x
    dsimp only [k]
    rw [hinit,← center_planeIn x,hcenter,center_planeIn]
  · intro t x hx
    exact hbij.mapsTo (hkD t x hx)
  · intro t x hx hz
    have hh := (hdiv t (planeIn x) (by simpa only [xyMap_planeIn] using hz)).1
    have hxy : xyMap (H t (planeIn x)) = x := by
      ext i
      fin_cases i
      · simpa using hh.1
      · simpa using hh.2
    dsimp only [k]
    rw [hΦzero _ (hkD t x hx) (by simpa only [hxy] using hz),hxy]
  · intro t
    let D := {x : P // diskSq x ≤ 1}
    let Z := {y : V // diskSq (xyMap y) ≤ 1}
    let F : D → Z := fun x => ⟨H t (planeIn x),hkD t x x.property⟩
    have hplane : IsEmbedding planeIn :=
      (show LeftInverse xyMap planeIn from xyMap_planeIn).isEmbedding xyMap.continuous planeIn.continuous
    have hHE : IsEmbedding (H t) :=
      (show LeftInverse (G t) (H t) from hGH t).isEmbedding (hGs t).continuous (hHs t).continuous
    have hF : IsEmbedding F := IsEmbedding.of_comp
      (((hHs t).continuous.comp (planeIn.continuous.comp continuous_subtype_val)).subtype_mk _)
      continuous_subtype_val (hHE.comp (hplane.comp IsEmbedding.subtypeVal))
    exact hemb.comp hF
  · intro t x hx
    rw [hdk]
    exact (hdinj _ (hkD t x hx)).comp
      ((inverse_spatial_derivative_injective H G hH hG hGH t (planeIn x)).comp planeIn_injective)
  · intro t x hx
    have hxK : x ∉ K := fun h => (hKD h).ne hx
    have hevent : k t =ᶠ[𝓝 x] planeIn := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      exact hkfix t y hy
    have hd : fderiv ℝ (k t) x = planeIn := by
      rw [hevent.fderiv_eq,planeIn.fderiv]
    rw [hkfix t x hxK,hd]
    simpa [covector_apply,dot,invariantCoefficients] using hLegendrian x hx
  · intro x hx v
    rw [hdk]
    change covector (invariantCoefficients u β₀ (Φ (H 1 (planeIn x))))
      (fderiv ℝ Φ (H 1 (planeIn x)) (fderiv ℝ (H 1) (planeIn x) (planeIn v))) = _
    rw [hΦpb _ (hkD 1 x hx)]
    have hp := hpb (planeIn x) (by simp) (planeIn v)
    change covector (invariantCoefficients u β₀ (H 1 (planeIn x)))
      (fderiv ℝ (H 1) (planeIn x) (planeIn v)) =
      σ 1 (planeIn x)*covector (invariantCoefficients u β₁ (planeIn x)) (planeIn v) at hp
    rw [hp]
    simp [r,covector_apply,dot,invariantCoefficients,mul_assoc]


end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem integrate_time_contact_field (a : V → V) (X : ℝ → V → V) (μ : ℝ → V → ℝ)
    (ha : ContDiff ℝ ∞ a)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hμ : ContDiff ℝ ∞ (fun p : ℝ × V => μ p.1 p.2))
    (hsupp : ∃ C : Set V, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0)
    (hLie : ∀ t y v, lieDerivOneForm (X t) (fun y => covector (a y)) y v =
      μ t y*covector (a y) v) :
    ∃ ψ ρ : ℝ → V → V, ∃ lam : ℝ → V → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧ (∀ t, Bijective (ψ t)) ∧
      (∀ t y, ρ t (ψ t y) = y) ∧ (∀ t y, ψ t (ρ t y) = y) ∧
      (∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t) ∧
      (∀ t y, 0 < lam t y) ∧
      ∀ t y v, covector (a (ψ t y)) (fderiv ℝ (ψ t) y v) = lam t y*covector (a y) v := by
  obtain ⟨ψ,hψ,h0,hbij,hflow⟩ := exists_ambient_flow X hX hsupp
  obtain ⟨ρ,hρ,hρψ,hψρ⟩ := smooth_joint_flow_inverse X ψ hX hψ h0 hbij hflow
  let α : OneForm 3 := fun y => covector (a y)
  let q : ℝ → (ℝ × V) → ℝ := fun s p => p.1*μ (s*p.1) (ψ (s*p.1) p.2)
  have harg : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => (p.1*p.2.1,p.2.2)) := by fun_prop
  have hq : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => q p.1 p.2) :=
    (contDiff_fst.comp contDiff_snd).mul (hμ.comp
      ((contDiff_fst.comp harg).prodMk (hψ.comp harg)))
  obtain ⟨Λ,hΛ,hΛ0,hpos,htransport⟩ := ParameterizedCalculus.smooth_scalar_linear_transport q hq
  let lam : ℝ → V → ℝ := fun t y => Λ 1 (t,y)
  have hlam : ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) :=
    hΛ.comp (contDiff_const.prodMk contDiff_id)
  have hα : ContDiff ℝ ∞ α := covector.contDiff.comp ha
  have hη : IsSmoothFamily (fun _ => α) := hα.comp contDiff_snd
  have hdiff : ∀ t y v, HasDerivAt (fun s => pullback (ψ s) α y v)
      (μ t (ψ t y)*pullback (ψ t) α y v) t := by
    intro t y v
    have hd := GrayStability.pullback_family_hasDerivAt (fun _ => α) hη X hX ψ hψ h0 hbij hflow t y v
    simp only [formTimeDeriv,deriv_const,zero_add] at hd
    have hl := hLie t (ψ t y) (fderiv ℝ (ψ t) y v)
    change lieDerivOneForm (X t) α (ψ t y) (fderiv ℝ (ψ t) y v) = _ at hl
    rw [hl] at hd
    exact hd
  refine ⟨ψ,ρ,lam,hψ,hρ,hlam,h0,hbij,hρψ,hψρ,hflow,fun t y => hpos 1 (t,y),?_⟩
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

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def timeGradient (H : ℝ × V → ℝ) (p : ℝ × V) : V :=
  ![fderiv ℝ H p (0,Pi.single 0 1),fderiv ℝ H p (0,Pi.single 1 1),
    fderiv ℝ H p (0,Pi.single 2 1)]

lemma timeGradient_slice (H : ℝ × V → ℝ) (hH : ContDiff ℝ ∞ H) (t : ℝ) (y : V) :
    gradient3 (fun z => H (t,z)) y = timeGradient H (t,y) := by
  have hd := (hH.differentiable (by simp) (t,y)).hasFDerivAt.comp y
    ((hasFDerivAt_const (𝕜 := ℝ) t y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y))
  change HasFDerivAt (fun z => H (t,z)) _ y at hd
  unfold gradient3 timeGradient
  rw [hd.fderiv]
  ext i
  fin_cases i <;> rfl

lemma time_hamiltonian_smooth (a : V → V) (H : ℝ × V → ℝ)
    (ha : ContDiff ℝ ∞ a) (hH : ContDiff ℝ ∞ H)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0) :
    ContDiff ℝ ∞ (fun p : ℝ × V => hamiltonianField a (fun y => H (p.1,y)) p.2) ∧
    ContDiff ℝ ∞ (fun p : ℝ × V => hamiltonianRate a (fun y => H (p.1,y)) p.2) := by
  have hda : ContDiff ℝ ∞ (fderiv ℝ a) := ha.fderiv_right (by simp)
  have hdH : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (by simp)
  have hg : ContDiff ℝ ∞ (timeGradient H) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [timeGradient] <;> fun_prop
  have hc : ContDiff ℝ ∞ (fun p : ℝ × V => curlLinear (fderiv ℝ a p.2)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [curlLinear] <;> fun_prop
  have hq : ContDiff ℝ ∞ (fun p : ℝ × V => dot (a p.2) (curlLinear (fderiv ℝ a p.2))) := by
    unfold dot
    fun_prop
  have hcross : ContDiff ℝ ∞ (fun p : ℝ × V => cross (a p.2) (timeGradient H p)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [cross] <;> fun_prop
  have hdot : ContDiff ℝ ∞ (fun p : ℝ × V => dot (curlLinear (fderiv ℝ a p.2)) (timeGradient H p)) := by
    unfold dot
    fun_prop
  constructor
  · have hh := (hq.inv (fun p => hQ p.2)).smul ((hH.smul hc).add hcross)
    convert! hh using 1
    funext p
    simp [hamiltonianField,hamiltonianAlgebra,timeGradient_slice H hH]
  · have hh := hdot.div hq (fun p => hQ p.2)
    convert! hh using 1
    funext p
    simp [hamiltonianRate,timeGradient_slice H hH]

theorem integrate_time_hamiltonian (a : V → V) (H : ℝ × V → ℝ)
    (ha : ContDiff ℝ ∞ a) (hH : ContDiff ℝ ∞ H)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0)
    (C : Set V) (hC : IsCompact C) (hout : ∀ t y, y ∉ C → H (t,y) = 0) :
    ∃ ψ ρ : ℝ → V → V, ∃ lam : ℝ → V → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧ (∀ t, Bijective (ψ t)) ∧
      (∀ t y, ρ t (ψ t y) = y) ∧ (∀ t y, ψ t (ρ t y) = y) ∧
      (∀ t y, HasDerivAt (fun s => ψ s y) (hamiltonianField a (fun z => H (t,z)) (ψ t y)) t) ∧
      (∀ t y, 0 < lam t y) ∧
      ∀ t y v, covector (a (ψ t y)) (fderiv ℝ (ψ t) y v) = lam t y*covector (a y) v := by
  let X : ℝ → V → V := fun t => hamiltonianField a (fun y => H (t,y))
  let μ : ℝ → V → ℝ := fun t => hamiltonianRate a (fun y => H (t,y))
  obtain ⟨hX,hμ⟩ := time_hamiltonian_smooth a H ha hH hQ
  have hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0 := by
    refine ⟨C,hC,?_⟩
    intro t y hy
    have he : (fun z => H (t,z)) =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hy] with z hz
      exact hout t z hz
    have hg : gradient3 (fun z => H (t,z)) y = 0 := by
      unfold gradient3
      rw [he.fderiv_eq]
      simp
    simp [X,hamiltonianField,hamiltonianAlgebra,he.eq_of_nhds,hg,cross]
  apply integrate_time_contact_field a X μ ha hX hμ hsupp
  intro t y v
  have hs : ContDiff ℝ ∞ (fun z => H (t,z)) := hH.comp (contDiff_const.prodMk contDiff_id)
  exact hamiltonianField_lie a (fun z => H (t,z)) ha hs hQ y v

lemma hamiltonian_multiple_normal_zero (u : P → ℝ) (β : P → P) (f : V → ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hf : ContDiff ℝ ∞ f)
    (hpos : ∀ x, 0 < invariantVolume u β x) (y : V) (hy : u (xyMap y) = 0) :
    hamiltonianField (invariantCoefficients u β) (fun z => f z*u (xyMap z)) y = ![0,0,f y] := by
  let U : V → ℝ := fun z => u (xyMap z)
  have hU : ContDiff ℝ ∞ U := hu.comp xyMap.contDiff
  have hg : gradient3 (fun z => f z*U z) y = f y • gradient3 U y := by
    rw [gradient3_mul f U (hf.differentiable (by simp)) (hU.differentiable (by simp))]
    simp only [show U y = 0 from hy,zero_smul,add_zero]
  have hbase : hamiltonianField (invariantCoefficients u β) U y = ![0,0,1] := by
    have he : U = normalHamiltonian u (fun _ => 1) := by funext z; simp [U,normalHamiltonian]
    rw [he]
    unfold hamiltonianField
    rw [invariant_curl_formula u β hu hβ,normalHamiltonian_gradient u (fun _ => 1) hu contDiff_const]
    simpa [compressionField,normalHamiltonian,deriv_const] using
      invariant_compression_field_formula u β (fun _ => 1) y (hpos _).ne'
  have hscale : hamiltonianField (invariantCoefficients u β) (fun z => f z*U z) y =
      f y • hamiltonianField (invariantCoefficients u β) U y := by
    unfold hamiltonianField
    rw [hg]
    have hz : U y = 0 := hy
    ext i
    fin_cases i <;> simp [hamiltonianAlgebra,hz,cross] <;> ring
  change hamiltonianField _ (fun z => f z*U z) y = _
  rw [hscale,hbase]
  ext i
  fin_cases i <;> simp

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def correctionCutoff (ε z : ℝ) : ℝ :=
  Real.smoothTransition (4*(z+ε)/ε)*Real.smoothTransition (4*(ε-z)/ε)

lemma correctionCutoff_contDiff (ε : ℝ) : ContDiff ℝ ∞ (correctionCutoff ε) := by
  unfold correctionCutoff
  fun_prop

lemma correctionCutoff_one (ε : ℝ) (hε : 0 < ε) (z : ℝ) (hz : |z| ≤ 2*ε/3) :
    correctionCutoff ε z = 1 := by
  have hb := abs_le.mp hz
  have h₁ : 1 ≤ 4*(z+ε)/ε := (le_div_iff₀ hε).mpr (by linarith)
  have h₂ : 1 ≤ 4*(ε-z)/ε := (le_div_iff₀ hε).mpr (by linarith)
  simp [correctionCutoff,Real.smoothTransition.one_of_one_le h₁,Real.smoothTransition.one_of_one_le h₂]

lemma correctionCutoff_zero (ε : ℝ) (hε : 0 < ε) (z : ℝ) (hz : ε < |z|) :
    correctionCutoff ε z = 0 := by
  rcases lt_abs.mp hz with h|h
  · have hh : 4*(ε-z)/ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
    simp [correctionCutoff,Real.smoothTransition.zero_of_nonpos hh]
  · have hh : 4*(z+ε)/ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
    simp [correctionCutoff,Real.smoothTransition.zero_of_nonpos hh]

def heightVelocity (k : ℝ → P → V) (p : ℝ × P) : ℝ :=
  fderiv ℝ (fun q : ℝ × P => k q.1 q.2) p (1,0) 2

lemma heightVelocity_contDiff (k : ℝ → P → V)
    (hk : ContDiff ℝ ∞ (fun p : ℝ × P => k p.1 p.2)) : ContDiff ℝ ∞ (heightVelocity k) := by
  have hd := hk.fderiv_right (m := ∞) (by simp)
  unfold heightVelocity
  fun_prop

lemma heightVelocity_hasDerivAt (k : ℝ → P → V)
    (hk : ContDiff ℝ ∞ (fun p : ℝ × P => k p.1 p.2)) (t : ℝ) (x : P) :
    HasDerivAt (fun s => k s x 2) (heightVelocity k (t,x)) t := by
  have hd := (hk.differentiable (by simp) (t,x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id (𝕜 := ℝ) t).prodMk (hasDerivAt_const t x))
  exact (ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hd

lemma heightVelocity_zero (k : ℝ → P → V)
    (hk : ContDiff ℝ ∞ (fun p : ℝ × P => k p.1 p.2))
    (x : P) (hfix : ∀ t, k t x = planeIn x) (t : ℝ) : heightVelocity k (t,x) = 0 := by
  have hh := heightVelocity_hasDerivAt k hk t x
  have he : (fun s => k s x 2) = fun _ => 0 := by funext s; rw [hfix]; simp
  rw [he] at hh
  exact hh.unique (hasDerivAt_const t (0:ℝ))

def correctionHamiltonian (u : P → ℝ) (k : ℝ → P → V) (ε : ℝ) (p : ℝ × V) : ℝ :=
  (-heightVelocity k (p.1,xyMap p.2)*correctionCutoff ε (p.2 2))*u (xyMap p.2)

lemma correctionHamiltonian_contDiff (u : P → ℝ) (k : ℝ → P → V) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hk : ContDiff ℝ ∞ (fun p : ℝ × P => k p.1 p.2)) :
    ContDiff ℝ ∞ (correctionHamiltonian u k ε) := by
  have hvel := heightVelocity_contDiff k hk
  have hxy : ContDiff ℝ ∞ (fun p : ℝ × V => (p.1,xyMap p.2)) :=
    contDiff_fst.prodMk (xyMap.contDiff.comp contDiff_snd)
  exact ((hvel.comp hxy).neg.mul ((correctionCutoff_contDiff ε).comp
    ((contDiff_apply ℝ ℝ 2).comp contDiff_snd))).mul (hu.comp (xyMap.contDiff.comp contDiff_snd))

def correctionSupport (K : Set P) (ε : ℝ) : Set V :=
  {y | xyMap y ∈ K ∧ |y 2| ≤ ε}

lemma correctionSupport_compact (K : Set P) (hK : IsCompact K) (ε : ℝ) :
    IsCompact (correctionSupport K ε) := by
  let join : P × ℝ → V := fun p => ![p.1 0,p.1 1,p.2]
  have hc : Continuous join := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [join] <;> fun_prop
  have he : correctionSupport K ε = join '' (K ×ˢ Icc (-ε) ε) := by
    ext y
    constructor
    · intro hy
      refine ⟨(xyMap y,y 2),⟨hy.1,abs_le.mp hy.2⟩,?_⟩
      ext i
      fin_cases i <;> simp [join]
    · rintro ⟨⟨x,z⟩,⟨hx,hz⟩,rfl⟩
      constructor
      · have hxy : xyMap (join (x,z)) = x := by ext i; fin_cases i <;> simp [join]
        simpa only [hxy] using hx
      · exact abs_le.mpr hz
  rw [he]
  exact (hK.prod isCompact_Icc).image hc

lemma correctionHamiltonian_outside (u : P → ℝ) (k : ℝ → P → V) (ε : ℝ)
    (hk : ContDiff ℝ ∞ (fun p : ℝ × P => k p.1 p.2)) (hε : 0 < ε)
    (K : Set P) (hfix : ∀ t x, x ∉ K → k t x = planeIn x) :
    ∀ t y, y ∉ correctionSupport K ε → correctionHamiltonian u k ε (t,y) = 0 := by
  intro t y hy
  by_cases hx : xyMap y ∈ K
  · have hz : ε < |y 2| := by
      by_contra hn
      exact hy ⟨hx,not_lt.mp hn⟩
    simp [correctionHamiltonian,correctionCutoff_zero ε hε (y 2) hz]
  · have hv := heightVelocity_zero k hk (xyMap y) (fun s => hfix s _ hx) t
    unfold correctionHamiltonian
    rw [hv]
    simp

lemma correctionField_zero_fibre (u : P → ℝ) (β : P → P) (k : ℝ → P → V) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β)
    (hk : ContDiff ℝ ∞ (fun p : ℝ × P => k p.1 p.2))
    (hpos : ∀ x, 0 < invariantVolume u β x) (t : ℝ) (y : V) (hy : u (xyMap y) = 0) :
    hamiltonianField (invariantCoefficients u β) (fun z => correctionHamiltonian u k ε (t,z)) y =
      ![0,0,-heightVelocity k (t,xyMap y)*correctionCutoff ε (y 2)] := by
  let f : V → ℝ := fun z => -heightVelocity k (t,xyMap z)*correctionCutoff ε (z 2)
  have hf : ContDiff ℝ ∞ f :=
    (((heightVelocity_contDiff k hk).comp (contDiff_const.prodMk xyMap.contDiff)).neg).mul
      ((correctionCutoff_contDiff ε).comp (contDiff_apply ℝ ℝ 2))
  exact hamiltonian_multiple_normal_zero u β f hu hβ hf hpos y hy

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem contact_corrects_dividing_height (u : P → ℝ) (β : P → P)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hpos : ∀ x, 0 < invariantVolume u β x)
    (K : Set P) (hK : IsCompact K) (hKD : K ⊆ {x | diskSq x < 1})
    (k : ℝ → P → V) (hk : ContDiff ℝ ∞ (fun p : ℝ × P => k p.1 p.2))
    (hinit : ∀ x, k 0 x = planeIn x) (hfix : ∀ t x, x ∉ K → k t x = planeIn x)
    (ε : ℝ) (hε : 0 < ε) (hheight : ∀ t x, diskSq x ≤ 1 → |k t x 2| < ε/3)
    (htrack : ∀ t x, diskSq x ≤ 1 → u x = 0 → xyMap (k t x) = x) :
    ∃ ψ ρ : ℝ → V → V, ∃ lam : ℝ → V → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧
      (∀ t y, ρ t (ψ t y) = y) ∧ (∀ t y, ψ t (ρ t y) = y) ∧
      (∀ t y, 0 < lam t y) ∧
      (∀ t y v, covector (invariantCoefficients u β (ψ t y)) (fderiv ℝ (ψ t) y v) =
        lam t y*covector (invariantCoefficients u β y) v) ∧
      (∀ t y, xyMap y ∉ K → ψ t y = y) ∧
      (∀ t y, diskSq (xyMap y) ≤ 1 → diskSq (xyMap (ψ t y)) ≤ 1) ∧
      (∀ t y, |y 2| ≤ ε → |ψ t y 2| ≤ ε) ∧
      (∀ t x, diskSq x ≤ 1 → u x = 0 → ψ t (k t x) = planeIn x) := by
  let a := invariantCoefficients u β
  let H := correctionHamiltonian u k ε
  let C := correctionSupport K ε
  let X : ℝ → V → V := fun t => hamiltonianField a (fun y => H (t,y))
  have ha : ContDiff ℝ ∞ a := invariantCoefficients_contDiff u β hu hβ
  have hH : ContDiff ℝ ∞ H := correctionHamiltonian_contDiff u k ε hu hk
  have hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0 := by
    intro y
    rw [invariant_volume_formula u β hu hβ]
    exact (hpos _).ne'
  have hC : IsCompact C := correctionSupport_compact K hK ε
  have hHout : ∀ t y, y ∉ C → H (t,y) = 0 := correctionHamiltonian_outside u k ε hk hε K hfix
  have hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2) :=
    (time_hamiltonian_smooth a H ha hH hQ).1
  have hXout : ∀ t y, y ∉ C → X t y = 0 := by
    intro t y hy
    have he : (fun z => H (t,z)) =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hy] with z hz
      exact hHout t z hz
    have hg : gradient3 (fun z => H (t,z)) y = 0 := by
      unfold gradient3
      rw [he.fderiv_eq]
      simp
    simp [X,hamiltonianField,hamiltonianAlgebra,he.eq_of_nhds,hg,cross]
  have hsupp : ∃ D : Set V, IsCompact D ∧ ∀ t y, y ∉ D → X t y = 0 := ⟨C,hC,hXout⟩
  obtain ⟨ψ,ρ,lam,hψ,hρ,hlam,h0,hbij,hρψ,hψρ,hd,hpositive,hpb⟩ :=
    integrate_time_hamiltonian a H ha hH hQ C hC hHout
  have hfixC : ∀ t y, y ∉ C → ψ t y = y := by
    intro t y hy
    exact ambient_flow_fixes X ψ hX hsupp h0 hd y (fun s => hXout s y hy) t
  have hfixxy : ∀ t y, xyMap y ∉ K → ψ t y = y := by
    intro t y hy
    exact hfixC t y (fun hc => hy hc.1)
  have hfixz : ∀ t y, ε < |y 2| → ψ t y = y := by
    intro t y hy
    exact hfixC t y (fun hc => (not_lt_of_ge hc.2) hy)
  have hDisk : ∀ t y, diskSq (xyMap y) ≤ 1 → diskSq (xyMap (ψ t y)) ≤ 1 := by
    intro t
    exact map_preserves_disk_of_fixed_exterior (ψ t) (hbij t).1 K hKD (hfixxy t)
  have hSlab : ∀ t y, |y 2| ≤ ε → |ψ t y 2| ≤ ε := by
    intro t y hy
    by_contra hn
    have hr : ε < |ψ t y 2| := not_le.mp hn
    have he : ψ t y = y := (hbij t).1 (hfixz t (ψ t y) hr)
    rw [he] at hr
    exact (not_lt_of_ge hy) hr
  refine ⟨ψ,ρ,lam,hψ,hρ,hlam,h0,hρψ,hψρ,hpositive,hpb,hfixxy,hDisk,hSlab,?_⟩
  intro t x hx hz
  let c : ℝ → V := fun s => ![x 0,x 1,k t x 2-k s x 2]
  have hc0 : c 0 = k t x := by
    have hh := htrack t x hx hz
    ext i
    fin_cases i
    · simpa [c] using (congrFun hh 0).symm
    · simpa [c] using (congrFun hh 1).symm
    · simp [c,hinit]
  have hc : ∀ s, HasDerivAt c (X s (c s)) s := by
    intro s
    have hxy : xyMap (c s) = x := by simp [c]
    have hbound : |c s 2| ≤ 2*ε/3 := by
      change |k t x 2-k s x 2| ≤ 2*ε/3
      have hb := abs_sub (k t x 2) (k s x 2)
      linarith [hheight t x hx,hheight s x hx]
    have hfield : X s (c s) = ![0,0,-heightVelocity k (s,x)] := by
      have hh := correctionField_zero_fibre u β k ε hu hβ hk hpos s (c s) (by simpa only [hxy] using hz)
      change X s (c s) = _ at hh
      rw [hxy,correctionCutoff_one ε hε _ hbound,mul_one] at hh
      exact hh
    rw [hfield]
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [c] using hasDerivAt_const s (x 0)
    · simpa [c] using hasDerivAt_const s (x 1)
    · convert! (hasDerivAt_const s (k t x 2)).sub (heightVelocity_hasDerivAt k hk s x) using 1 <;> simp [c]
  have he : (fun s => ψ s (k t x)) = c :=
    (FlowCalculus.exists_unique_global_trajectory_of_compact_support X hX hsupp 0 (k t x)).unique
      ⟨h0 _,fun s => hd s _⟩ ⟨hc0,hc⟩
  simpa [c] using congrFun he t

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem dividing_fixed_disk_realization (u : P → ℝ) (β₀ β₁ : P → P)
    (hu : ContDiff ℝ ∞ u) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁)
    (hpos₀ : ∀ x, 0 < invariantVolume u β₀ x) (hpos₁ : ∀ x, 0 < invariantVolume u β₁ x)
    (hLegendrian : ∀ x, diskSq x = 1 → β₀ x 0*(-x 1)+β₀ x 1*x 0 = 0)
    (K : Set P) (hK : IsCompact K) (hKD : K ⊆ {x | diskSq x < 1})
    (heq : ∀ x, x ∉ K → β₁ x = β₀ x) (U : Set V) (hU : IsOpen U)
    (hDU : ∀ x, diskSq x ≤ 1 → planeIn x ∈ U) :
    ∃ k : ℝ → P → V, ∃ r : P → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × P => k p.1 p.2) ∧ ContDiff ℝ ∞ r ∧
      (∀ x, 0 < r x) ∧ (∀ x, k 0 x = planeIn x) ∧
      (∀ t x, x ∉ K → k t x = planeIn x) ∧
      (∀ t x, diskSq x ≤ 1 → u x = 0 → k t x = planeIn x) ∧
      (∀ t x, diskSq x ≤ 1 → diskSq (xyMap (k t x)) ≤ 1 ∧ k t x ∈ U) ∧
      (∀ t, IsEmbedding (fun x : {x : P // diskSq x ≤ 1} => k t x)) ∧
      (∀ t x, diskSq x ≤ 1 → Injective (fderiv ℝ (k t) x)) ∧
      (∀ t x, diskSq x = 1 →
        covector (invariantCoefficients u β₀ (k t x)) (fderiv ℝ (k t) x ![-x 1,x 0]) = 0) ∧
      ∀ x, diskSq x ≤ 1 → ∀ v,
        covector (invariantCoefficients u β₀ (k 1 x)) (fderiv ℝ (k 1) x v) =
          r x*(β₁ x 0*v 0+β₁ x 1*v 1) := by
  obtain ⟨δ,hδ,hUbound⟩ := exists_disk_tube_in_open U hU hDU
  let ε := δ/2
  have hε : 0 < ε := half_pos hδ
  obtain ⟨k,r,hk,hr,hrpos,hinit,hstat,hfix,hthin,htrack,hemb,hinj,hLegend,hpb⟩ :=
    local_disk_foliation_realization_tracked u β₀ β₁ hu h₀ h₁ hpos₀ hpos₁ hLegendrian K hK hKD heq
      (ε/3) (by positivity)
  obtain ⟨ψ,ρ,lam,hψ,hρ,hlam,hψ0,hρψ,hψρ,hpositive,hψpb,hψfix,hψDisk,hψSlab,hψzero⟩ :=
    contact_corrects_dividing_height u β₀ hu h₀ hpos₀ K hK hKD k hk hinit hfix ε hε
      (fun t x hx => (hthin t x hx).2) htrack
  let k' : ℝ → P → V := fun t x => ψ t (k t x)
  let r' : P → ℝ := fun x => lam 1 (k 1 x)*r x
  have hks : ∀ t, ContDiff ℝ ∞ (k t) := fun t => hk.comp (contDiff_const.prodMk contDiff_id)
  have hψs : ∀ t, ContDiff ℝ ∞ (ψ t) := fun t => hψ.comp (contDiff_const.prodMk contDiff_id)
  have hk' : ContDiff ℝ ∞ (fun p : ℝ × P => k' p.1 p.2) := hψ.comp (contDiff_fst.prodMk hk)
  have hr' : ContDiff ℝ ∞ r' := (hlam.comp (contDiff_const.prodMk (hks 1))).mul hr
  have hfix' : ∀ t x, x ∉ K → k' t x = planeIn x := by
    intro t x hx
    dsimp only [k']
    rw [hfix t x hx]
    exact hψfix t (planeIn x) (by simpa only [xyMap_planeIn] using hx)
  have hdk : ∀ t x, fderiv ℝ (k' t) x =
      (fderiv ℝ (ψ t) (k t x)).comp (fderiv ℝ (k t) x) := by
    intro t x
    exact fderiv_comp x ((hψs t).differentiable (by simp) _) ((hks t).differentiable (by simp) _)
  refine ⟨k',r',hk',hr',?_,?_,hfix',hψzero,?_,?_,?_,?_,?_⟩
  · intro x
    exact mul_pos (hpositive _ _) (hrpos _)
  · intro x
    dsimp only [k']
    rw [hψ0,hinit]
  · intro t x hx
    have hd := hψDisk t (k t x) (hthin t x hx).1
    have hz : |k' t x 2| ≤ ε := hψSlab t (k t x) (by linarith [(hthin t x hx).2])
    exact ⟨hd,hUbound _ hd (lt_of_le_of_lt hz (by dsimp [ε]; linarith))⟩
  · intro t
    have he : IsEmbedding (ψ t) :=
      (show LeftInverse (ρ t) (ψ t) from hρψ t).isEmbedding
        (hρ.comp (contDiff_const.prodMk contDiff_id)).continuous (hψs t).continuous
    exact he.comp (hemb t)
  · intro t x hx
    rw [hdk]
    exact (inverse_spatial_derivative_injective ψ ρ hψ hρ hρψ t (k t x)).comp (hinj t x hx)
  · intro t x hx
    have hxK : x ∉ K := fun h => (hKD h).ne hx
    have hevent : k' t =ᶠ[𝓝 x] planeIn := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      exact hfix' t y hy
    have hd : fderiv ℝ (k' t) x = planeIn := by rw [hevent.fderiv_eq,planeIn.fderiv]
    rw [hfix' t x hxK,hd]
    simpa [covector_apply,dot,invariantCoefficients] using hLegendrian x hx
  · intro x hx v
    rw [hdk]
    change covector (invariantCoefficients u β₀ (ψ 1 (k 1 x)))
      (fderiv ℝ (ψ 1) (k 1 x) (fderiv ℝ (k 1) x v)) = _
    rw [hψpb,hpb x hx]
    dsimp only [r']
    ring

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.Normalization
open Set Filter Function Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev P := Fin 2 → ℝ
abbrev V := Fin 3 → ℝ

def volume (u : P → ℝ) (β : P → P) (x : P) : ℝ :=
  β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
    u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)

lemma precomp_equiv_derivative_ne_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (u : F → ℝ) (hu : ContDiff ℝ ∞ u) (p : E)
    (hD : fderiv ℝ u (e p) ≠ 0) : fderiv ℝ (fun x => u (e x)) p ≠ 0 := by
  have hd := (hu.differentiable (by simp) (e p)).hasFDerivAt.comp p e.hasFDerivAt
  change HasFDerivAt (fun x => u (e x)) _ p at hd
  intro hz
  apply hD
  apply ContinuousLinearMap.ext
  intro w
  obtain ⟨z,rfl⟩ := e.surjective w
  have he := congrArg (fun D : E →L[ℝ] ℝ => D z) (hd.fderiv.symm.trans hz)
  simpa using he

lemma positive_ratio_finTwo (u v : P → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hregu : ∀ x, u x = 0 → fderiv ℝ u x ≠ 0)
    (hregv : ∀ x, v x = 0 → fderiv ℝ v x ≠ 0)
    (hzero : ∀ x, u x = 0 ↔ v x = 0) (hsign : ∀ x, v x ≠ 0 → 0 < u x*v x) :
    ∃ a : P → ℝ, ContDiff ℝ ∞ a ∧ (∀ x, 0 < a x) ∧ ∀ x, u x = a x*v x := by
  let e : P ≃L[ℝ] (ℝ × ℝ) := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let U : (ℝ × ℝ) → ℝ := fun x => u (e.symm x)
  let W : (ℝ × ℝ) → ℝ := fun x => v (e.symm x)
  have hU : ContDiff ℝ ∞ U := hu.comp e.symm.contDiff
  have hW : ContDiff ℝ ∞ W := hv.comp e.symm.contDiff
  obtain ⟨a,ha,hunique⟩ := DifferentialTopology.positive_ratio_of_cooriented_regular_defining_functions U W hU hW
    (fun x hx => precomp_equiv_derivative_ne_zero e.symm u hu x (hregu _ hx))
    (fun x hx => precomp_equiv_derivative_ne_zero e.symm v hv x (hregv _ hx))
    (fun x => hzero (e.symm x)) (fun x hx => hsign (e.symm x) hx)
  refine ⟨fun x => a (e x),ha.1.comp e.contDiff,fun x => ha.2.1 _,?_⟩
  intro x
  simpa only [U,W,e.symm_apply_apply] using ha.2.2 (e x)

lemma volume_regular_zero (u : P → ℝ) (β : P → P) (hpos : ∀ x, 0 < volume u β x) :
    ∀ x, u x = 0 → fderiv ℝ u x ≠ 0 := by
  intro x hx hd
  have hp := hpos x
  simp [volume,hx,hd] at hp

lemma volume_scale (u : P → ℝ) (β : P → P) (a : P → ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (ha : ContDiff ℝ ∞ a) (x : P) :
    volume (fun y => a y*u y) (fun y => a y • β y) x = a x^2*volume u β x := by
  have hdu := ((ha.differentiable (by simp) x).hasFDerivAt.mul
    (hu.differentiable (by simp) x).hasFDerivAt).fderiv
  have hdβ := ((ha.differentiable (by simp) x).hasFDerivAt.smul
    (hβ.differentiable (by simp) x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => a y*u y) x = _ at hdu
  change fderiv ℝ (fun y => a y • β y) x = _ at hdβ
  simp [volume,hdu,hdβ]
  ring

lemma factor_eq_one_on_open (u v a : P → ℝ) (hv : ContDiff ℝ ∞ v) (ha : ContDiff ℝ ∞ a)
    (hreg : ∀ x, v x = 0 → fderiv ℝ v x ≠ 0) (hfactor : ∀ x, u x = a x*v x)
    (U : Set P) (hU : IsOpen U) (heq : EqOn u v U) : ∀ x ∈ U, a x = 1 := by
  intro x hx
  by_cases hz : v x = 0
  · have hnear : u =ᶠ[𝓝 x] v := Filter.mem_of_superset (hU.mem_nhds hx) heq
    have hprod : u = (fun x => a x*v x) := funext hfactor
    have hd : a x • fderiv ℝ v x = fderiv ℝ v x := by
      calc
        a x • fderiv ℝ v x = fderiv ℝ (fun y => a y*v y) x := by
          rw [fderiv_fun_mul (ha.differentiable (by simp) x) (hv.differentiable (by simp) x)]
          simp [hz]
        _ = fderiv ℝ u x := by rw [← hprod]
        _ = fderiv ℝ v x := hnear.fderiv_eq
    have hw : ∃ w, fderiv ℝ v x w ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hreg x hz (ContinuousLinearMap.ext hn)
    obtain ⟨w,hw⟩ := hw
    apply mul_right_cancel₀ hw
    simpa using congrArg (fun D : P →L[ℝ] ℝ => D w) hd
  · apply mul_right_cancel₀ hz
    rw [← hfactor x,heq hx,one_mul]

lemma normalize_invariant_forms (u₀ u₁ : P → ℝ) (β₀ β₁ : P → P)
    (hu₀ : ContDiff ℝ ∞ u₀) (hu₁ : ContDiff ℝ ∞ u₁)
    (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁)
    (hpos₀ : ∀ x, 0 < volume u₀ β₀ x) (hpos₁ : ∀ x, 0 < volume u₁ β₁ x)
    (hzero : ∀ x, u₀ x = 0 ↔ u₁ x = 0)
    (hsign : ∀ x, u₁ x ≠ 0 → 0 < u₀ x*u₁ x)
    (K : Set P) (hK : IsCompact K)
    (heq : ∀ x, x ∉ K → u₀ x = u₁ x ∧ β₁ x = β₀ x) :
    ∃ a : P → ℝ, ContDiff ℝ ∞ a ∧ (∀ x, 0 < a x) ∧ (∀ x, u₀ x = a x*u₁ x) ∧
      ContDiff ℝ ∞ (fun x => a x • β₁ x) ∧
      (∀ x, 0 < volume u₀ (fun x => a x • β₁ x) x) ∧
      (∀ x, x ∉ K → a x = 1 ∧ a x • β₁ x = β₀ x) := by
  have hreg₀ := volume_regular_zero u₀ β₀ hpos₀
  have hreg₁ := volume_regular_zero u₁ β₁ hpos₁
  obtain ⟨a,ha,hapos,hfactor⟩ := positive_ratio_finTwo u₀ u₁ hu₀ hu₁ hreg₀ hreg₁ hzero hsign
  have hone : ∀ x, x ∉ K → a x = 1 :=
    factor_eq_one_on_open u₀ u₁ a hu₁ ha hreg₁ hfactor Kᶜ hK.isClosed.isOpen_compl
      (fun x hx => (heq x hx).1)
  refine ⟨a,ha,hapos,hfactor,ha.smul hβ₁,?_,?_⟩
  · intro x
    have huEq : u₀ = (fun x => a x*u₁ x) := funext hfactor
    rw [huEq,volume_scale u₁ β₁ a hu₁ hβ₁ ha]
    exact mul_pos (sq_pos_of_pos (hapos x)) (hpos₁ x)
  · intro x hx
    exact ⟨hone x hx,by rw [hone x hx,one_smul,(heq x hx).2]⟩

end
end ContactTopology.Normalization


namespace ContactTopology.Normalization
open Set Function Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem cooriented_dividing_fixed_disk_realization (u₀ u₁ : P → ℝ) (β₀ β₁ : P → P)
    (hu₀ : ContDiff ℝ ∞ u₀) (hu₁ : ContDiff ℝ ∞ u₁)
    (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁)
    (hpos₀ : ∀ x, 0 < volume u₀ β₀ x) (hpos₁ : ∀ x, 0 < volume u₁ β₁ x)
    (hzero : ∀ x, u₀ x = 0 ↔ u₁ x = 0)
    (hsign : ∀ x, u₁ x ≠ 0 → 0 < u₀ x*u₁ x)
    (hLegendrian : ∀ x, x 0^2+x 1^2 = 1 → β₀ x 0*(-x 1)+β₀ x 1*x 0 = 0)
    (K : Set P) (hK : IsCompact K) (hKD : K ⊆ {x | x 0^2+x 1^2 < 1})
    (heq : ∀ x, x ∉ K → u₀ x = u₁ x ∧ β₁ x = β₀ x)
    (U : Set V) (hU : IsOpen U)
    (hDU : ∀ x : P, x 0^2+x 1^2 ≤ 1 → (![x 0,x 1,0] : V) ∈ U) :
    let I : V → V := fun y => ![β₀ ![y 0,y 1] 0,β₀ ![y 0,y 1] 1,u₀ ![y 0,y 1]]
    let B : V → V → ℝ := fun a v => a 0*v 0+a 1*v 1+a 2*v 2
    ∃ k : ℝ → P → V, ∃ R : P → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × P => k p.1 p.2) ∧ ContDiff ℝ ∞ R ∧
      (∀ x, 0 < R x) ∧ (∀ x, k 0 x = ![x 0,x 1,0]) ∧
      (∀ t x, x ∉ K → k t x = ![x 0,x 1,0]) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → u₀ x = 0 → k t x = ![x 0,x 1,0]) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → (k t x 0)^2+(k t x 1)^2 ≤ 1 ∧ k t x ∈ U) ∧
      (∀ t, IsEmbedding (fun x : {x : P // x 0^2+x 1^2 ≤ 1} => k t x)) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → Injective (fderiv ℝ (k t) x)) ∧
      (∀ t x, x 0^2+x 1^2 = 1 → B (I (k t x)) (fderiv ℝ (k t) x ![-x 1,x 0]) = 0) ∧
      ∀ x, x 0^2+x 1^2 ≤ 1 → ∀ v,
        B (I (k 1 x)) (fderiv ℝ (k 1) x v) = R x*(β₁ x 0*v 0+β₁ x 1*v 1) := by
  dsimp only
  obtain ⟨a,ha,hapos,hfactor,hhat,hvolhat,heqa⟩ :=
    normalize_invariant_forms u₀ u₁ β₀ β₁ hu₀ hu₁ hβ₀ hβ₁ hpos₀ hpos₁ hzero hsign K hK heq
  obtain ⟨k,r,hk,hr,hrpos,hinit,hfix,hΓ,hneigh,hemb,hinj,hLegend,hpb⟩ :=
    ContactTopology.ConvexDeformation.dividing_fixed_disk_realization u₀ β₀ (fun x => a x • β₁ x)
      hu₀ hβ₀ hhat hpos₀ hvolhat hLegendrian K hK hKD (fun x hx => (heqa x hx).2) U hU
      (by simpa only [ContactTopology.ConvexDeformation.planeIn_apply,ContactTopology.ConvexDeformation.diskSq] using hDU)
  refine ⟨k,fun x => r x*a x,hk,hr.mul ha,fun x => mul_pos (hrpos x) (hapos x),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [ContactTopology.ConvexDeformation.planeIn_apply] using hinit
  · simpa only [ContactTopology.ConvexDeformation.planeIn_apply] using hfix
  · simpa only [ContactTopology.ConvexDeformation.planeIn_apply,ContactTopology.ConvexDeformation.diskSq] using hΓ
  · simpa only [ContactTopology.ConvexDeformation.diskSq,ContactTopology.ConvexDeformation.xyMap_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one] using hneigh
  · exact hemb
  · exact hinj
  · simpa [ContactTopology.ConvexDeformation.covector_apply,ContactTopology.ConvexDeformation.dot,
      ContactTopology.ConvexDeformation.invariantCoefficients,ContactTopology.ConvexDeformation.diskSq] using hLegend
  · intro x hx v
    have hp := hpb x hx v
    have hp' :
        (fun a v : V => a 0*v 0+a 1*v 1+a 2*v 2)
          (![β₀ ![k 1 x 0,k 1 x 1] 0,β₀ ![k 1 x 0,k 1 x 1] 1,u₀ ![k 1 x 0,k 1 x 1]])
          (fderiv ℝ (k 1) x v) = r x*((a x • β₁ x) 0*v 0+(a x • β₁ x) 1*v 1) := by
      simpa [ContactTopology.ConvexDeformation.covector_apply,ContactTopology.ConvexDeformation.dot,
        ContactTopology.ConvexDeformation.invariantCoefficients] using hp
    dsimp only at hp'
    rw [hp']
    simp only [Pi.smul_apply,smul_eq_mul]
    ring

end
end ContactTopology.Normalization


open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem solution (u₀ u₁ : (Fin 2 → ℝ) → ℝ) (β₀ β₁ : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hu₀ : ContDiff ℝ ∞ u₀) (hu₁ : ContDiff ℝ ∞ u₁)
    (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁)
    (hzero : ∀ x, u₀ x = 0 ↔ u₁ x = 0)
    (hsign : ∀ x, u₁ x ≠ 0 → 0 < u₀ x*u₁ x)
    (hLegendrian : ∀ x, x 0^2+x 1^2 = 1 → β₀ x 0*(-x 1)+β₀ x 1*x 0 = 0)
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) (hKD : K ⊆ {x | x 0^2+x 1^2 < 1})
    (heq : ∀ x, x ∉ K → u₀ x = u₁ x ∧ β₁ x = β₀ x)
    (U : Set (Fin 3 → ℝ)) (hU : IsOpen U)
    (hDU : ∀ x : (Fin 2 → ℝ), x 0^2+x 1^2 ≤ 1 → (![x 0,x 1,0] : (Fin 3 → ℝ)) ∈ U) :
    let Q : ((Fin 2 → ℝ) → ℝ) → ((Fin 2 → ℝ) → (Fin 2 → ℝ)) → (Fin 2 → ℝ) → ℝ := fun u β x =>
      β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
        u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)
    (∀ x, 0 < Q u₀ β₀ x) → (∀ x, 0 < Q u₁ β₁ x) →
    let I : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y => ![β₀ ![y 0,y 1] 0,β₀ ![y 0,y 1] 1,u₀ ![y 0,y 1]]
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun a v => a 0*v 0+a 1*v 1+a 2*v 2
    ∃ k : ℝ → (Fin 2 → ℝ) → (Fin 3 → ℝ), ∃ R : (Fin 2 → ℝ) → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 2 → ℝ) => k p.1 p.2) ∧ ContDiff ℝ ∞ R ∧
      (∀ x, 0 < R x) ∧ (∀ x, k 0 x = ![x 0,x 1,0]) ∧
      (∀ t x, x ∉ K → k t x = ![x 0,x 1,0]) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → u₀ x = 0 → k t x = ![x 0,x 1,0]) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → (k t x 0)^2+(k t x 1)^2 ≤ 1 ∧ k t x ∈ U) ∧
      (∀ t, Topology.IsEmbedding (fun x : {x : (Fin 2 → ℝ) // x 0^2+x 1^2 ≤ 1} => k t x)) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → Function.Injective (fderiv ℝ (k t) x)) ∧
      (∀ t x, x 0^2+x 1^2 = 1 → B (I (k t x)) (fderiv ℝ (k t) x ![-x 1,x 0]) = 0) ∧
      ∀ x, x 0^2+x 1^2 ≤ 1 → ∀ v,
        B (I (k 1 x)) (fderiv ℝ (k 1) x v) = R x*(β₁ x 0*v 0+β₁ x 1*v 1) := by
  dsimp only
  intro hpos₀ hpos₁
  exact ContactTopology.Normalization.cooriented_dividing_fixed_disk_realization
    u₀ u₁ β₀ β₁ hu₀ hu₁ hβ₀ hβ₁ hpos₀ hpos₁ hzero hsign hLegendrian K hK hKD heq U hU hDU
