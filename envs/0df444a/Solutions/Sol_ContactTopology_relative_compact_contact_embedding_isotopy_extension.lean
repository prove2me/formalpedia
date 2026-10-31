-- Prove2me | solution 1 for ContactTopology.relative_compact_contact_embedding_isotopy_extension
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T23:54:23.10041+00:00
-- url     : https://prove2.me/submissions/3adae69d-7a2c-4d7e-a81d-beb3884760a2

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
import Mathlib.Geometry.Manifold.PartitionOfUnity
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
import Theorems.Thm_ContactCalculus_exterior_pairing_pullback
import Theorems.Thm_FlowCalculus_compact_supported_flow_preserves_regular_level
import Theorems.Thm_FlowCalculus_exists_unique_global_trajectory_of_compact_support
import Theorems.Thm_FlowCalculus_regular_level_trajectory_invariant
import Theorems.Thm_FlowCalculus_smooth_flow_spatial_derivative_injective
import Theorems.Thm_GrayStability_pullback_family_hasDerivAt
import Theorems.Thm_ParameterizedCalculus_smooth_scalar_linear_transport
import Theorems.Thm_SmoothJetExtension_compact_first_jet_extension


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


end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma embedding_velocity_cartan (α : V → V →L[ℝ] ℝ) (hα : ContDiff ℝ ∞ α)
    (g : ℝ → V → V) (hg : ContDiff ℝ ∞ (fun p : ℝ × V => g p.1 p.2))
    (lam : ℝ → V → ℝ) (hlam : ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2))
    (N : Set V) (hN : IsOpen N)
    (hpb : ∀ s x, x ∈ N → ∀ v, α (g s x) (fderiv ℝ (g s) x v)=lam s x*α x v)
    (s : ℝ) (x : V) (hx : x ∈ N) (v : V) :
    let G : (ℝ × V) → V := fun p => g p.1 p.2
    let H : (ℝ × V) → ℝ := fun p => α (G p) (fderiv ℝ G p (1,0))
    fderiv ℝ H (s,x) (0,v)+
      (fderiv ℝ α (g s x) (fderiv ℝ G (s,x) (1,0)) (fderiv ℝ (g s) x v)-
       fderiv ℝ α (g s x) (fderiv ℝ (g s) x v) (fderiv ℝ G (s,x) (1,0)))=
      fderiv ℝ (fun p : ℝ × V => lam p.1 p.2) (s,x) (1,0)*α x v := by
  let G : (ℝ × V) → V := fun p => g p.1 p.2
  let P : (ℝ × V) → ((ℝ × V) →L[ℝ] ℝ) := fun p => (α (G p)).comp (fderiv ℝ G p)
  have hDG : ContDiff ℝ ∞ (fderiv ℝ G) := hg.fderiv_right (by simp)
  have hP : ContDiff ℝ ∞ P := ((hα.comp hg).clm_comp hDG)
  have hspace (p : ℝ × V) : fderiv ℝ G p (0,v)=fderiv ℝ (g p.1) p.2 v := by
    have hd := (hg.differentiable (by simp) p).hasFDerivAt.comp p.2
      ((hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2))
    have hh := congrArg (fun D : V →L[ℝ] V => D v) hd.fderiv
    exact hh.symm
  have hpbgerm : (fun p => P p (0,v)) =ᶠ[𝓝 (s,x)] (fun p => lam p.1 p.2*α p.2 v) := by
    have hO : IsOpen ((Set.univ : Set ℝ) ×ˢ N) := isOpen_univ.prod hN
    filter_upwards [hO.mem_nhds (show (s,x) ∈ (Set.univ : Set ℝ) ×ˢ N from ⟨mem_univ _,hx⟩)] with p hp
    change α (g p.1 p.2) (fderiv ℝ G p (0,v))=_
    rw [hspace,hpb p.1 p.2 hp.2]
  have hDapply (w z : ℝ × V) : fderiv ℝ (fun p => P p z) (s,x) w=fderiv ℝ P (s,x) w z := by
    have hh := (hP.differentiable (by simp) (s,x)).hasFDerivAt.clm_apply (hasFDerivAt_const z (s,x))
    change HasFDerivAt (fun p => P p z) _ (s,x) at hh
    rw [hh.fderiv]
    simp
  have hright := (hlam.differentiable (by simp) (s,x)).hasFDerivAt.mul
    (((hα.comp contDiff_snd).differentiable (by simp) (s,x)).hasFDerivAt.clm_apply (hasFDerivAt_const v (s,x)))
  have hscalar := congrArg (fun D : (ℝ × V) →L[ℝ] ℝ => D (1,0)) hright.fderiv
  change fderiv ℝ (fun p : ℝ × V => lam p.1 p.2*α p.2 v) (s,x) (1,0)=_ at hscalar
  have hαzero : fderiv ℝ (α ∘ (Prod.snd : (ℝ × V) → V)) (s,x) (1,0)=0 := by
    rw [fderiv_comp (s,x) (hα.differentiable (by simp) x) differentiableAt_snd,fderiv_snd]
    change fderiv ℝ α x (0:V)=0
    exact map_zero _
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.zero_apply,smul_eq_mul,hαzero,mul_zero,add_zero,Function.comp_apply,
    map_zero] at hscalar
  have hscalar' : fderiv ℝ (fun p : ℝ × V => lam p.1 p.2*α p.2 v) (s,x) (1,0)=
      fderiv ℝ (fun p : ℝ × V => lam p.1 p.2) (s,x) (1,0)*α x v := by
    simpa only [zero_add,mul_comm] using hscalar
  have htime : fderiv ℝ P (s,x) (1,0) (0,v)=
      fderiv ℝ (fun p : ℝ × V => lam p.1 p.2) (s,x) (1,0)*α x v := by
    rw [← hDapply,hpbgerm.fderiv_eq]
    exact hscalar'
  have hext := ContactCalculus.exterior_pairing_pullback α G (s,x) (1,0) (0,v)
    (hα.differentiable (by simp) _) (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  change fderiv ℝ P (s,x) (1,0) (0,v)-fderiv ℝ P (s,x) (0,v) (1,0)=_ at hext
  rw [htime,hspace] at hext
  dsimp only
  change fderiv ℝ (fun p => P p (1,0)) (s,x) (0,v)+_=_
  rw [hDapply]
  linarith

end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma hamiltonian_algebra_unique (a c g Y : V) (H μ : ℝ) (hQ : dot a c ≠ 0)
    (hval : dot a Y=H)
    (hLie : ∀ v : V, dot g v+dot c (cross Y v)=μ*dot a v) :
    Y=hamiltonianAlgebra a c H g := by
  have h0 := hLie (Pi.single 0 1)
  have h1 := hLie (Pi.single 1 1)
  have h2 := hLie (Pi.single 2 1)
  simp [dot,cross] at h0 h1 h2
  have he (i : Fin 3) : dot a c*Y i=H*c i+cross a g i := by
    fin_cases i
    · change dot a c*Y 0=H*c 0+(a 1*g 2-a 2*g 1)
      simp only [dot] at hval ⊢
      linear_combination (c 0)*hval-(a 1)*h2+(a 2)*h1
    · change dot a c*Y 1=H*c 1+(a 2*g 0-a 0*g 2)
      simp only [dot] at hval ⊢
      linear_combination (c 1)*hval-(a 2)*h0+(a 0)*h2
    · change dot a c*Y 2=H*c 2+(a 0*g 1-a 1*g 0)
      simp only [dot] at hval ⊢
      linear_combination (c 2)*hval-(a 0)*h1+(a 1)*h0
  ext i
  change Y i=(dot a c)⁻¹*(H*c i+cross a g i)
  rw [← he i]
  field_simp [hQ]

lemma contact_field_is_hamiltonian (a Y : V → V) (H μ : V → ℝ)
    (ha : ContDiff ℝ ∞ a) (hY : ContDiff ℝ ∞ Y)
    (hval : ∀ y, covector (a y) (Y y)=H y)
    (hLie : ∀ y v, lieDerivOneForm Y (fun z => covector (a z)) y v=μ y*covector (a y) v)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0) :
    ∀ y, Y y=hamiltonianField a H y := by
  intro y
  have hp : (fun z => covector (a z) (Y z))=H := funext hval
  have hD (w v : V) : fderiv ℝ (fun z => covector (a z)) y w v=dot (fderiv ℝ a y w) v := by
    have hd := covector.hasFDerivAt.comp y (ha.differentiable (by simp) y).hasFDerivAt
    change HasFDerivAt (fun z => covector (a z)) _ y at hd
    rw [hd.fderiv]
    exact covector_apply _ _
  have hDer (v : V) : fderiv ℝ H y v=
      dot (fderiv ℝ a y v) (Y y)+dot (a y) (fderiv ℝ Y y v) := by
    have hd := ((covector.contDiff.comp ha).differentiable (by simp) y).hasFDerivAt.clm_apply
      (hY.differentiable (by simp) y).hasFDerivAt
    have hh := congrArg (fun D : V →L[ℝ] ℝ => D v) hd.fderiv
    change fderiv ℝ (fun z => covector (a z) (Y z)) y v=_ at hh
    rw [hp] at hh
    change fderiv ℝ H y v=covector (a y) (fderiv ℝ Y y v)+
      fderiv ℝ (fun z => covector (a z)) y v (Y y) at hh
    rw [hD,covector_apply] at hh
    linarith
  apply hamiltonian_algebra_unique (a y) (curlLinear (fderiv ℝ a y)) (gradient3 H y)
    (Y y) (H y) (μ y) (hQ y) (hval y)
  intro v
  rw [gradient3_pair,← exterior_cross,hDer]
  have hh := hLie y v
  change fderiv ℝ (fun z => covector (a z)) y (Y y) v+covector (a y) (fderiv ℝ Y y v)=_ at hh
  rw [hD,covector_apply,covector_apply] at hh
  linarith

end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma hamiltonianField_germ (a : V → V) (H K : V → ℝ) (y : V) (he : H =ᶠ[𝓝 y] K) :
    hamiltonianField a H y=hamiltonianField a K y := by
  unfold hamiltonianField gradient3
  rw [he.eq_of_nhds,he.fderiv_eq]

lemma hamiltonianField_mix (a : V → V) (H K : V → ℝ)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (s : ℝ) (y : V) :
    hamiltonianField a (fun z => (1-s)*H z+s*K z) y=
      (1-s) • hamiltonianField a H y+s • hamiltonianField a K y := by
  have hd := ((hH.differentiable (by simp) y).hasFDerivAt.const_mul (1-s)).add
    ((hK.differentiable (by simp) y).hasFDerivAt.const_mul s)
  change HasFDerivAt (fun z => (1-s)*H z+s*K z) _ y at hd
  have hg : gradient3 (fun z => (1-s)*H z+s*K z) y=
      (1-s) • gradient3 H y+s • gradient3 K y := by
    unfold gradient3
    rw [hd.fderiv]
    ext i
    fin_cases i <;> simp <;> ring
  unfold hamiltonianField
  rw [hg]
  ext i
  fin_cases i <;> simp [hamiltonianAlgebra,cross,Matrix.vecHead,Matrix.vecTail] <;> ring

lemma hamiltonian_family_contDiff (a : V → V) (H : ℝ → V → ℝ)
    (ha : ContDiff ℝ ∞ a) (hH : ContDiff ℝ ∞ (fun p : ℝ × V => H p.1 p.2))
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0) :
    ContDiff ℝ ∞ (fun p : ℝ × V => hamiltonianField a (H p.1) p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => hamiltonianRate a (H p.1) p.2) := by
  have hd (s : ℝ) (y v : V) : fderiv ℝ (H s) y v=
      fderiv ℝ (fun p : ℝ × V => H p.1 p.2) (s,y) (0,v) := by
    have hh := (hH.differentiable (by simp) (s,y)).hasFDerivAt.comp y
      ((hasFDerivAt_const (𝕜 := ℝ) s y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y))
    exact congrArg (fun D : V →L[ℝ] ℝ => D v) hh.fderiv
  have hg : ContDiff ℝ ∞ (fun p : ℝ × V => gradient3 (H p.1) p.2) := by
    have hgi (i : Fin 3) : ContDiff ℝ ∞ (fun p : ℝ × V =>
        fderiv ℝ (H p.1) p.2 (Pi.single i 1)) := by
      have he : (fun p : ℝ × V => fderiv ℝ (H p.1) p.2 (Pi.single i 1))=
          (fun p : ℝ × V => fderiv ℝ (fun q : ℝ × V => H q.1 q.2) p (0,Pi.single i 1)) :=
        funext (fun p => hd p.1 p.2 (Pi.single i 1))
      rw [he]
      exact (hH.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact hgi 0
    · exact hgi 1
    · exact hgi 2
  have hc : ContDiff ℝ ∞ (fun y => curlLinear (fderiv ℝ a y)) := by
    have hda : ContDiff ℝ ∞ (fderiv ℝ a) := ha.fderiv_right (by simp)
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [curlLinear] <;> fun_prop
  have hvolume : ContDiff ℝ ∞ (fun y => dot (a y) (curlLinear (fderiv ℝ a y))) := by
    unfold dot
    fun_prop
  have hInv : ContDiff ℝ ∞ (fun p : ℝ × V => (dot (a p.2) (curlLinear (fderiv ℝ a p.2)))⁻¹) :=
    (hvolume.inv hQ).comp contDiff_snd
  have hcP := hc.comp (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × V → V))
  have hcross : ContDiff ℝ ∞ (fun p : ℝ × V => cross (a p.2) (gradient3 (H p.1) p.2)) := by
    have haP := ha.comp (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × V → V))
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [cross] <;> fun_prop
  constructor
  · exact hInv.smul ((hH.smul hcP).add hcross)
  · unfold hamiltonianRate
    have hn : ContDiff ℝ ∞ (fun p : ℝ × V => dot (curlLinear (fderiv ℝ a p.2)) (gradient3 (H p.1) p.2)) := by
      unfold dot
      fun_prop
    exact hn.div (hvolume.comp contDiff_snd) (fun p => hQ p.2)


end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def embeddingVelocity (g : ℝ → V → V) (p : ℝ × V) : V :=
  fderiv ℝ (fun q : ℝ × V => g q.1 q.2) p (1,0)

lemma embeddingVelocity_smooth (g : ℝ → V → V)
    (hg : ContDiff ℝ ∞ (fun p : ℝ × V => g p.1 p.2)) :
    ContDiff ℝ ∞ (embeddingVelocity g) :=
  (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

def eulerianVelocity (g : ℝ → V → V) (E : OpenPartialHomeomorph (ℝ × V) (ℝ × V))
    (p : ℝ × V) : V := embeddingVelocity g (E.symm p)

def eulerianHamiltonian (a : V → V) (g : ℝ → V → V)
    (E : OpenPartialHomeomorph (ℝ × V) (ℝ × V)) (p : ℝ × V) : ℝ :=
  covector (a p.2) (eulerianVelocity g E p)

lemma eulerianHamiltonian_smooth_on (a : V → V) (ha : ContDiff ℝ ∞ a)
    (g : ℝ → V → V) (hg : ContDiff ℝ ∞ (fun p : ℝ × V => g p.1 p.2))
    (E : OpenPartialHomeomorph (ℝ × V) (ℝ × V))
    (hR : ∀ p ∈ E.target, ContDiffAt ℝ ∞ E.symm p) :
    ContDiffOn ℝ ∞ (eulerianHamiltonian a g E) E.target := by
  intro p hp
  exact (((covector.contDiff.comp (ha.comp contDiff_snd)).contDiffAt).clm_apply
    ((embeddingVelocity_smooth g hg).contDiffAt.comp p (hR p hp))).contDiffWithinAt

lemma eulerian_hamiltonian_field (a : V → V) (ha : ContDiff ℝ ∞ a)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0)
    (g : ℝ → V → V) (hg : ContDiff ℝ ∞ (fun p : ℝ × V => g p.1 p.2))
    (lam : ℝ → V → ℝ) (hlam : ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2))
    (N : Set V) (hN : IsOpen N) (hpos : ∀ s x, x ∈ N → 0 < lam s x)
    (hpb : ∀ s x, x ∈ N → ∀ v,
      covector (a (g s x)) (fderiv ℝ (g s) x v)=lam s x*covector (a x) v)
    (hder : ∀ s x, x ∈ N → Injective (fderiv ℝ (g s) x))
    (E : OpenPartialHomeomorph (ℝ × V) (ℝ × V))
    (hE : (E : (ℝ × V) → (ℝ × V))=fun p => (p.1,g p.1 p.2))
    (hsource : E.source=(Set.univ : Set ℝ) ×ˢ N)
    (hR : ∀ p ∈ E.target, ContDiffAt ℝ ∞ E.symm p) :
    ∀ s x, x ∈ N →
      hamiltonianField a (fun y => eulerianHamiltonian a g E (s,y)) (g s x)=embeddingVelocity g (s,x) := by
  let α : V → V →L[ℝ] ℝ := fun y => covector (a y)
  have hα : ContDiff ℝ ∞ α := covector.contDiff.comp ha
  let H := eulerianHamiltonian a g E
  have hH : ContDiffOn ℝ ∞ H E.target := eulerianHamiltonian_smooth_on a ha g hg E hR
  have hsrc (s : ℝ) (x : V) (hx : x ∈ N) : (s,x) ∈ E.source := by rw [hsource]; exact ⟨mem_univ _,hx⟩
  have hinv (s : ℝ) (x : V) (hx : x ∈ N) : E.symm (s,g s x)=(s,x) := by
    have hh := E.left_inv (hsrc s x hx)
    simpa only [hE] using hh
  have htarg (s : ℝ) (x : V) (hx : x ∈ N) : (s,g s x) ∈ E.target := by
    simpa only [hE] using E.map_source (hsrc s x hx)
  let Hsrc : (ℝ × V) → ℝ := fun p => α (g p.1 p.2) (embeddingVelocity g p)
  have hHsrc : ContDiff ℝ ∞ Hsrc := (hα.comp hg).clm_apply (embeddingVelocity_smooth g hg)
  intro s x hx
  have hgs : ContDiff ℝ ∞ (g s) := hg.comp (f := fun y : V => (s,y)) (contDiff_const.prodMk contDiff_id)
  have hHs : ContDiffAt ℝ ∞ (fun y => H (s,y)) (g s x) :=
    (hH.contDiffAt (E.open_target.mem_nhds (htarg s x hx))).comp (g s x)
      (contDiff_const.prodMk contDiff_id).contDiffAt
  have hscalar : (fun z => H (s,g s z)) =ᶠ[𝓝 x] (fun z => Hsrc (s,z)) := by
    filter_upwards [hN.mem_nhds hx] with z hz
    simp only [H,eulerianHamiltonian,eulerianVelocity,hinv s z hz,Hsrc,α]
  have hD (v : V) : fderiv ℝ (fun y => H (s,y)) (g s x) (fderiv ℝ (g s) x v)=
      fderiv ℝ Hsrc (s,x) (0,v) := by
    have hleft := (hHs.differentiableAt (by simp)).hasFDerivAt.comp x (hgs.differentiable (by simp) x).hasFDerivAt
    have hright := (hHsrc.differentiable (by simp) (s,x)).hasFDerivAt.comp x
      ((hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
    have hh := congrArg (fun D : V →L[ℝ] ℝ => D v)
      (hleft.fderiv.symm.trans (hscalar.fderiv_eq.trans hright.fderiv))
    exact hh
  have hCovD (y w v : V) : fderiv ℝ α y w v=dot (fderiv ℝ a y w) v := by
    have hd := covector.hasFDerivAt.comp y (ha.differentiable (by simp) y).hasFDerivAt
    change HasFDerivAt α _ y at hd
    rw [hd.fderiv]
    exact covector_apply _ _
  let Y := embeddingVelocity g (s,x)
  let Ls := fderiv ℝ (fun p : ℝ × V => lam p.1 p.2) (s,x) (1,0)
  have hval : dot (a (g s x)) Y=H (s,g s x) := by
    simp only [H,eulerianHamiltonian,eulerianVelocity,hinv s x hx,covector_apply,Y]
  symm
  apply hamiltonian_algebra_unique (a (g s x)) (curlLinear (fderiv ℝ a (g s x)))
    (gradient3 (fun y => H (s,y)) (g s x)) Y (H (s,g s x)) (Ls/lam s x) (hQ _) hval
  intro v
  obtain ⟨w,hw⟩ := LinearMap.injective_iff_surjective.mp (hder s x hx) v
  change fderiv ℝ (g s) x w=v at hw
  have hc := embedding_velocity_cartan α hα g hg lam hlam N hN hpb s x hx w
  change fderiv ℝ Hsrc (s,x) (0,w)+
    (fderiv ℝ α (g s x) Y (fderiv ℝ (g s) x w)-
      fderiv ℝ α (g s x) (fderiv ℝ (g s) x w) Y)=Ls*α x w at hc
  rw [hw,← hD w,hw,hCovD,hCovD] at hc
  rw [gradient3_pair,← exterior_cross]
  have hp := hpb s x hx w
  rw [hw,covector_apply,covector_apply] at hp
  have heq : (Ls/lam s x)*dot (a (g s x)) v=Ls*dot (a x) w := by
    rw [hp]
    field_simp [(hpos s x hx).ne']
  rw [heq]
  exact hc

end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

lemma open_smooth_embedding_chart (F : E → E) (hF : ContDiff ℝ ∞ F)
    (U : Set E) (hU : IsOpen U) (hinj : InjOn F U)
    (hder : ∀ p ∈ U, Injective (fderiv ℝ F p)) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E)=F ∧ e.source=U ∧
      ∀ y ∈ e.target, ContDiffAt ℝ ∞ e.symm y := by
  have hopen : IsOpenMap (U.domRestrict F) := by
    apply IsOpenMap.of_nhds_le
    intro x
    obtain ⟨e,he,hx⟩ := smooth_injective_derivative_local_chart_general F hF x (hder x x.property)
    have hm : map F (𝓝 x.val) = 𝓝 (F x.val) := by
      simpa only [he] using e.map_nhds_eq hx
    have hs : map (fun x : U => (x : E)) (𝓝 x) = 𝓝 (x : E) :=
      hU.isOpenEmbedding_subtypeVal.map_nhds_eq x
    change 𝓝 (F x.val) ≤ map (fun z : U => F z.val) (𝓝 x)
    rw [show (fun z : U => F z.val) = F ∘ Subtype.val from rfl,← map_map,hs,hm]
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hinj.toPartialEquiv F U) hF.continuous.continuousOn hopen hU
  have he : (e : E → E) = F := rfl
  refine ⟨e,he,rfl,?_⟩
  intro y hy
  have hp : e.symm y ∈ U := e.map_target hy
  let A : E ≃L[ℝ] E := (LinearEquiv.ofBijective (fderiv ℝ F (e.symm y)).toLinearMap
    ⟨hder _ hp,LinearMap.injective_iff_surjective.mp (hder _ hp)⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt e (A : E →L[ℝ] E) (e.symm y) := (hF.differentiable (by simp) _).hasFDerivAt
  exact e.contDiffAt_symm hy hd hF.contDiffAt

end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology Manifold
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma localized_scalar_extension (h : E → ℝ) (O C : Set E)
    (hO : IsOpen O) (hC : IsCompact C) (hCO : C ⊆ O) (hh : ContDiffOn ℝ ∞ h O) :
    ∃ H χ : E → ℝ, ∃ W : Set E,
      ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ O ∧ IsOpen W ∧ C ⊆ W ∧ W ⊆ O ∧
      (∀ p ∈ W, H =ᶠ[𝓝 p] h) ∧ (∀ p ∈ O, H =ᶠ[𝓝 p] (fun q => χ q*h q)) ∧
      ∀ p, p ∉ tsupport χ → H =ᶠ[𝓝 p] (fun _ => (0:ℝ)) := by
  obtain ⟨K,hK,hCK,hKO⟩ := exists_compact_between hC hO hCO
  obtain ⟨χ,hχC,hχout,-⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,E)) hC.isClosed hCK (n := (⊤:ℕ∞))
  have hχ : ContDiff ℝ ∞ (χ : E → ℝ) := contMDiff_iff_contDiff.mp χ.contMDiff
  have hχsupp : tsupport (χ : E → ℝ) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro p hp
    by_contra hn
    exact hp (hχout p hn)
  have hcχ : HasCompactSupport (χ : E → ℝ) := hK.of_isClosed_subset isClosed_closure hχsupp
  obtain ⟨A,hA,hcA,hjet⟩ := SmoothJetExtension.compact_first_jet_extension K hK h (fderiv ℝ h) (by
    intro p hp
    exact ⟨O,hO,hKO hp,h,hh,fun q _ => ⟨rfl,rfl⟩⟩)
  let H : E → ℝ := fun p => χ p*A p
  have hHO (p : E) (hp : p ∈ O) : H p=χ p*h p := by
    by_cases hpk : p ∈ K
    · simp only [H,(hjet p hpk).1]
    · simp only [H,hχout p hpk,mul_zero,zero_mul]
  have hnear : ∀ p ∈ C, H =ᶠ[𝓝 p] h := by
    intro p hp
    filter_upwards [hχC.filter_mono (nhds_le_nhdsSet hp),hO.mem_nhds (hCO hp)] with q hq hqO
    rw [hHO q hqO,hq,one_mul]
  obtain ⟨W0,hW0,hWC,hWval⟩ := eventually_nhdsSet_iff_exists.mp
    (show H =ᶠ[𝓝ˢ C] h from by
      change ∀ᶠ q in 𝓝ˢ C, H q=h q
      exact eventually_nhdsSet_iff_forall.mpr hnear)
  let W := W0 ∩ O
  refine ⟨H,χ,W,hχ.mul hA,hcχ.mul_right,hχ,hcχ,hχsupp.trans hKO,hW0.inter hO,
    fun p hp => ⟨hWC hp,hCO hp⟩,inter_subset_right,?_,?_,?_⟩
  · intro p hp
    filter_upwards [(hW0.inter hO).mem_nhds hp] with q hq
    exact hWval q hq.1
  · intro p hp
    filter_upwards [hO.mem_nhds hp] with q hq
    exact hHO q hq
  · intro p hp
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
    simp only [H,hq,Pi.zero_apply,zero_mul]

end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem compact_generator_of_contact_embeddings (a : V → V) (ha : ContDiff ℝ ∞ a)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0)
    (g : ℝ → V → V) (hg : ContDiff ℝ ∞ (fun p : ℝ × V => g p.1 p.2))
    (lam : ℝ → V → ℝ) (hlam : ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2))
    (N : Set V) (hN : IsOpen N) (hpos : ∀ s x, x ∈ N → 0 < lam s x)
    (hpb : ∀ s x, x ∈ N → ∀ v,
      covector (a (g s x)) (fderiv ℝ (g s) x v)=lam s x*covector (a x) v)
    (hinj : ∀ s, InjOn (g s) N) (hder : ∀ s x, x ∈ N → Injective (fderiv ℝ (g s) x))
    (K U : Set V) (hK : IsCompact K) (hKN : K ⊆ N) (hU : IsOpen U)
    (htrack : ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ K, g s x ∈ U) :
    ∃ H : ℝ → V → ℝ, ∃ C : Set V,
      ContDiff ℝ ∞ (fun p : ℝ × V => H p.1 p.2) ∧ IsCompact C ∧ C ⊆ U ∧
      (∀ s y, y ∉ C → hamiltonianField a (H s) y=0) ∧
      ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ K,
        hamiltonianField a (H s) (g s x)=embeddingVelocity g (s,x) := by
  let F : (ℝ × V) → (ℝ × V) := fun p => (p.1,g p.1 p.2)
  have hF : ContDiff ℝ ∞ F := contDiff_fst.prodMk hg
  have hFI : InjOn F ((Set.univ : Set ℝ) ×ˢ N) := by
    intro p hp q hq heq
    have hs : p.1=q.1 := by simpa only [F] using congrArg Prod.fst heq
    have hsp : g p.1 p.2=g p.1 q.2 := by
      simpa only [F,← hs] using congrArg Prod.snd heq
    exact Prod.ext hs (hinj p.1 hp.2 hq.2 hsp)
  obtain ⟨E,hE,hsource,hR⟩ := open_smooth_embedding_chart F hF ((Set.univ : Set ℝ) ×ˢ N)
    (isOpen_univ.prod hN) hFI (fun p hp => parameter_lift_derivative_injective g hg p.1 p.2 (hder p.1 p.2 hp.2))
  let O := E.target ∩ ((Set.univ : Set ℝ) ×ˢ U)
  have hO : IsOpen O := E.open_target.inter (isOpen_univ.prod hU)
  let T : Set (ℝ × V) := F '' (Icc (0:ℝ) 1 ×ˢ K)
  have hT : IsCompact T := (isCompact_Icc.prod hK).image hF.continuous
  have hTO : T ⊆ O := by
    rintro p ⟨q,hq,rfl⟩
    refine ⟨?_,mem_univ _,htrack q.1 hq.1 q.2 hq.2⟩
    have hs : q ∈ E.source := by rw [hsource]; exact ⟨mem_univ _,hKN hq.2⟩
    simpa only [hE] using E.map_source hs
  let h := eulerianHamiltonian a g E
  have hh : ContDiffOn ℝ ∞ h O := (eulerianHamiltonian_smooth_on a ha g hg E hR).mono inter_subset_left
  obtain ⟨A,χ,W,hA,hcA,hχ,hcχ,hχO,hW,hTW,hWO,hAgerm,hAprod,hAzero⟩ :=
    localized_scalar_extension h O T hO hT hTO hh
  let H : ℝ → V → ℝ := fun s y => A (s,y)
  let C := Prod.snd '' tsupport χ
  have hC : IsCompact C := hcχ.image continuous_snd
  have hCU : C ⊆ U := by
    rintro y ⟨p,hp,rfl⟩
    exact (hχO hp).2.2
  refine ⟨H,C,hA,hC,hCU,?_,?_⟩
  · intro s y hy
    have hp : (s,y) ∉ tsupport χ := fun hh => hy ⟨(s,y),hh,rfl⟩
    have hs : (H s) =ᶠ[𝓝 y] (fun _ => (0:ℝ)) :=
      (hAzero (s,y) hp).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
    rw [hamiltonianField_germ a (H s) (fun _ => 0) y hs]
    simp [hamiltonianField,hamiltonianAlgebra,gradient3,cross]
  · intro s hs x hx
    have hp : (s,g s x) ∈ T := ⟨(s,x),⟨hs,hx⟩,rfl⟩
    have hgerm : H s =ᶠ[𝓝 (g s x)] (fun y => h (s,y)) :=
      (hAgerm (s,g s x) (hTW hp)).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
    rw [hamiltonianField_germ a (H s) (fun y => h (s,y)) (g s x) hgerm]
    exact eulerian_hamiltonian_field a ha hQ g hg lam hlam N hN hpos hpb hder E hE hsource hR s x (hKN hx)

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

theorem integrate_time_contact_field (α : V → V →L[ℝ] ℝ) (hα : ContDiff ℝ ∞ α)
    (X : ℝ → V → V) (μ : ℝ → V → ℝ)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hμ : ContDiff ℝ ∞ (fun p : ℝ × V => μ p.1 p.2))
    (C : Set V) (hC : IsCompact C) (hc : ∀ t y, y ∉ C → X t y=0)
    (hLie : ∀ t y v, lieDerivOneForm (X t) α y v=μ t y*α y v) :
    ∃ ψ ρ : ℝ → V → V, ∃ lam : ℝ → V → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) ∧
      (∀ y, ψ 0 y=y) ∧ (∀ t, Bijective (ψ t)) ∧
      (∀ t y, ρ t (ψ t y)=y) ∧ (∀ t y, ψ t (ρ t y)=y) ∧
      (∀ t y, HasDerivAt (fun r => ψ r y) (X t (ψ t y)) t) ∧
      (∀ t y, y ∉ C → ψ t y=y) ∧ (∀ t y, 0 < lam t y) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ y v, α (ψ t y) (fderiv ℝ (ψ t) y v)=lam t y*α y v := by
  obtain ⟨ψ,hψ,h0,hbij,hd⟩ := exists_ambient_flow X hX ⟨C,hC,hc⟩
  obtain ⟨ρ,hρ,hρψ,hψρ⟩ := smooth_joint_flow_inverse X ψ hX hψ h0 hbij hd
  let q : ℝ → V → ℝ := fun t y => μ t (ψ t y)
  have hq : ContDiff ℝ ∞ (fun p : ℝ × V => q p.1 p.2) := hμ.comp (contDiff_fst.prodMk hψ)
  obtain ⟨lam,hlam,hlam0,hpos,htransport⟩ := ParameterizedCalculus.smooth_scalar_linear_transport q hq
  refine ⟨ψ,ρ,lam,hψ,hρ,hlam,h0,hbij,hρψ,hψρ,hd,?_,hpos,?_⟩
  · intro t y hy
    exact ambient_flow_fixes X ψ hX ⟨C,hC,hc⟩ h0 hd y (fun r => hc r y hy) t
  · intro t ht y v
    have hf : ∀ s ∈ Icc (0:ℝ) 1,
        HasDerivAt (fun r => pullback (ψ r) α y v) (q s y*pullback (ψ s) α y v) s := by
      intro s hs
      have hh := GrayStability.pullback_family_hasDerivAt (fun _ => α) (hα.comp contDiff_snd) X hX ψ hψ h0 hbij hd s y v
      simp only [formTimeDeriv,deriv_const,zero_add] at hh
      rw [hLie] at hh
      exact hh
    have hh := htransport y (fun r => pullback (ψ r) α y v) hf t ht
    have hid : ψ 0=id := funext h0
    simpa [pullback,hid] using hh

theorem extend_contact_embedding_family (a : V → V) (ha : ContDiff ℝ ∞ a)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0)
    (g : ℝ → V → V) (hg : ContDiff ℝ ∞ (fun p : ℝ × V => g p.1 p.2))
    (lam : ℝ → V → ℝ) (hlam : ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2))
    (N : Set V) (hN : IsOpen N) (hpos : ∀ s x, x ∈ N → 0 < lam s x)
    (hpb : ∀ s x, x ∈ N → ∀ v,
      covector (a (g s x)) (fderiv ℝ (g s) x v)=lam s x*covector (a x) v)
    (hinj : ∀ s, InjOn (g s) N) (hder : ∀ s x, x ∈ N → Injective (fderiv ℝ (g s) x))
    (h0 : ∀ x ∈ N, g 0 x=x)
    (K U : Set V) (hK : IsCompact K) (hKN : K ⊆ N) (hU : IsOpen U)
    (htrack : ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ K, g s x ∈ U) :
    ∃ ψ ρ : ℝ → V → V, ∃ Λ : ℝ → V → ℝ, ∃ C : Set V,
      ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => Λ p.1 p.2) ∧
      IsCompact C ∧ C ⊆ U ∧ (∀ y, ψ 0 y=y) ∧
      (∀ t y, ρ t (ψ t y)=y) ∧ (∀ t y, ψ t (ρ t y)=y) ∧
      (∀ t y, y ∉ C → ψ t y=y) ∧ (∀ t y, 0 < Λ t y) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y v,
        covector (a (ψ t y)) (fderiv ℝ (ψ t) y v)=Λ t y*covector (a y) v) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ K, ψ t x=g t x := by
  obtain ⟨H,C,hH,hC,hCU,hc,hmatch⟩ := compact_generator_of_contact_embeddings a ha hQ g hg lam hlam
    N hN hpos hpb hinj hder K U hK hKN hU htrack
  let X : ℝ → V → V := fun t => hamiltonianField a (H t)
  let μ : ℝ → V → ℝ := fun t => hamiltonianRate a (H t)
  obtain ⟨hX,hμ⟩ := hamiltonian_family_contDiff a H ha hH hQ
  have hLie (t : ℝ) (y v : V) : lieDerivOneForm (X t) (fun z => covector (a z)) y v=μ t y*covector (a y) v := by
    have hHt : ContDiff ℝ ∞ (H t) := hH.comp (f := fun z : V => (t,z)) (contDiff_const.prodMk contDiff_id)
    exact hamiltonianField_lie a (H t) ha hHt hQ y v
  obtain ⟨ψ,ρ,Λ,hψ,hρ,hΛ,hψ0,hbij,hρψ,hψρ,hd,hfix,hposΛ,hpbΛ⟩ :=
    integrate_time_contact_field (fun z => covector (a z)) (covector.contDiff.comp ha) X μ hX hμ C hC hc hLie
  refine ⟨ψ,ρ,Λ,C,hψ,hρ,hΛ,hC,hCU,hψ0,hρψ,hψρ,hfix,hposΛ,hpbΛ,?_⟩
  obtain ⟨L,hL⟩ := FlowCalculus.uniform_spatial_lipschitz_of_compact_support X hX ⟨C,hC,hc⟩ 0 1
  intro t ht x hx
  have hgcurve (r : ℝ) : HasDerivAt (fun s => g s x) (embeddingVelocity g (r,x)) r := by
    have hh := (hg.differentiable (by simp) (r,x)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (hasDerivAt_const r x))
    exact hh
  have hψc : Continuous (fun s => ψ s x) := hψ.continuous.comp (continuous_id.prodMk continuous_const)
  have hgc : Continuous (fun s => g s x) := hg.continuous.comp (continuous_id.prodMk continuous_const)
  have heq : EqOn (fun s => ψ s x) (fun s => g s x) (Icc (0:ℝ) 1) := by
    apply ODE_solution_unique_of_mem_Icc_right (v := X) (s := fun _ => Set.univ)
      (fun r hr => (hL r (Ico_subset_Icc_self hr)).lipschitzOnWith) hψc.continuousOn
      (fun r hr => (hd r x).hasDerivWithinAt) (fun _ _ => mem_univ _) hgc.continuousOn
    · intro r hr
      change HasDerivWithinAt (fun s => g s x) (hamiltonianField a (H r) (g r x)) (Ici r) r
      rw [hmatch r (Ico_subset_Icc_self hr) x hx]
      exact (hgcurve r).hasDerivWithinAt
    · exact fun _ _ => mem_univ _
    · rw [hψ0,h0 x (hKN hx)]
  exact heq ht

end
end ContactTopology.ConvexDeformation



namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma hamiltonianField_product_at (a : V → V) (χ H : V → ℝ) (y : V)
    (hχ : DifferentiableAt ℝ χ y) (hH : DifferentiableAt ℝ H y) :
    hamiltonianField a (fun z => χ z*H z) y=
      χ y • hamiltonianField a H y+
        ((dot (a y) (curlLinear (fderiv ℝ a y)))⁻¹*H y) • cross (a y) (gradient3 χ y) := by
  have hd := hχ.hasFDerivAt.mul hH.hasFDerivAt
  change HasFDerivAt (fun z => χ z*H z) _ y at hd
  have hg : gradient3 (fun z => χ z*H z) y=χ y • gradient3 H y+H y • gradient3 χ y := by
    unfold gradient3
    rw [hd.fderiv]
    ext i
    fin_cases i <;> simp <;> ring
  unfold hamiltonianField
  rw [hg]
  ext i
  fin_cases i <;> simp [hamiltonianAlgebra,cross,Matrix.vecHead,Matrix.vecTail] <;> ring

lemma hamiltonian_cutoff_preserves_zero_at (a : V → V) (χ H : V → ℝ) (y : V)
    (hχ : DifferentiableAt ℝ χ y) (hH : DifferentiableAt ℝ H y)
    (hval : H y=0) (hfield : hamiltonianField a H y=0) :
    hamiltonianField a (fun z => χ z*H z) y=0 := by
  rw [hamiltonianField_product_at a χ H y hχ hH,hfield,hval]
  simp

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma embeddingVelocity_zero_of_fixed (g : ℝ → V → V)
    (hg : ContDiff ℝ ∞ (fun p : ℝ × V => g p.1 p.2))
    (S : Set V) (hfix : ∀ s y, y ∈ S → g s y=y) (s : ℝ) (y : V) (hy : y ∈ S) :
    embeddingVelocity g (s,y)=0 := by
  have hd := (hg.differentiable (by simp) (s,y)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))
  change HasDerivAt (fun r => g r y) (embeddingVelocity g (s,y)) s at hd
  have heq : (fun r => g r y)=(fun _ => y) := funext (fun r => hfix r y hy)
  rw [heq] at hd
  exact hd.unique (hasDerivAt_const s y)

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem relative_compact_generator_of_contact_embeddings (a : V → V) (ha : ContDiff ℝ ∞ a)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0)
    (g : ℝ → V → V) (hg : ContDiff ℝ ∞ (fun p : ℝ × V => g p.1 p.2))
    (lam : ℝ → V → ℝ) (hlam : ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2))
    (N : Set V) (hN : IsOpen N) (hpos : ∀ s x, x ∈ N → 0 < lam s x)
    (hpb : ∀ s x, x ∈ N → ∀ v,
      covector (a (g s x)) (fderiv ℝ (g s) x v)=lam s x*covector (a x) v)
    (hinj : ∀ s, InjOn (g s) N) (hder : ∀ s x, x ∈ N → Injective (fderiv ℝ (g s) x))
    (S : Set V) (hSN : S ⊆ N) (hfix : ∀ s y, y ∈ S → g s y=y)
    (K U : Set V) (hK : IsCompact K) (hKN : K ⊆ N) (hU : IsOpen U)
    (htrack : ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ K, g s x ∈ U) :
    ∃ H : ℝ → V → ℝ, ∃ C : Set V,
      ContDiff ℝ ∞ (fun p : ℝ × V => H p.1 p.2) ∧ IsCompact C ∧ C ⊆ U ∧
      (∀ s y, y ∉ C → hamiltonianField a (H s) y=0) ∧
      (∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ K,
        hamiltonianField a (H s) (g s x)=embeddingVelocity g (s,x)) ∧
      ∀ s y, y ∈ S → hamiltonianField a (H s) y=0 := by
  let F : (ℝ × V) → (ℝ × V) := fun p => (p.1,g p.1 p.2)
  have hF : ContDiff ℝ ∞ F := contDiff_fst.prodMk hg
  have hFI : InjOn F ((Set.univ : Set ℝ) ×ˢ N) := by
    intro p hp q hq heq
    have hs : p.1=q.1 := by simpa only [F] using congrArg Prod.fst heq
    have hsp : g p.1 p.2=g p.1 q.2 := by
      simpa only [F,← hs] using congrArg Prod.snd heq
    exact Prod.ext hs (hinj p.1 hp.2 hq.2 hsp)
  obtain ⟨E,hE,hsource,hR⟩ := open_smooth_embedding_chart F hF ((Set.univ : Set ℝ) ×ˢ N)
    (isOpen_univ.prod hN) hFI (fun p hp => parameter_lift_derivative_injective g hg p.1 p.2 (hder p.1 p.2 hp.2))
  let O := E.target ∩ ((Set.univ : Set ℝ) ×ˢ U)
  have hO : IsOpen O := E.open_target.inter (isOpen_univ.prod hU)
  let T : Set (ℝ × V) := F '' (Icc (0:ℝ) 1 ×ˢ K)
  have hT : IsCompact T := (isCompact_Icc.prod hK).image hF.continuous
  have hTO : T ⊆ O := by
    rintro p ⟨q,hq,rfl⟩
    refine ⟨?_,mem_univ _,htrack q.1 hq.1 q.2 hq.2⟩
    have hs : q ∈ E.source := by rw [hsource]; exact ⟨mem_univ _,hKN hq.2⟩
    simpa only [hE] using E.map_source hs
  let h := eulerianHamiltonian a g E
  have hh : ContDiffOn ℝ ∞ h O := (eulerianHamiltonian_smooth_on a ha g hg E hR).mono inter_subset_left
  obtain ⟨A,χ,W,hA,hcA,hχ,hcχ,hχO,hW,hTW,hWO,hAgerm,hAprod,hAzero⟩ :=
    localized_scalar_extension h O T hO hT hTO hh
  let H : ℝ → V → ℝ := fun s y => A (s,y)
  let C := Prod.snd '' tsupport χ
  have hC : IsCompact C := hcχ.image continuous_snd
  have hCU : C ⊆ U := by
    rintro y ⟨p,hp,rfl⟩
    exact (hχO hp).2.2
  refine ⟨H,C,hA,hC,hCU,?_,?_,?_⟩
  · intro s y hy
    have hp : (s,y) ∉ tsupport χ := fun hh => hy ⟨(s,y),hh,rfl⟩
    have hs : (H s) =ᶠ[𝓝 y] (fun _ => (0:ℝ)) :=
      (hAzero (s,y) hp).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
    rw [hamiltonianField_germ a (H s) (fun _ => 0) y hs]
    simp [hamiltonianField,hamiltonianAlgebra,gradient3,cross]
  · intro s hs x hx
    have hp : (s,g s x) ∈ T := ⟨(s,x),⟨hs,hx⟩,rfl⟩
    have hgerm : H s =ᶠ[𝓝 (g s x)] (fun y => h (s,y)) :=
      (hAgerm (s,g s x) (hTW hp)).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
    rw [hamiltonianField_germ a (H s) (fun y => h (s,y)) (g s x) hgerm]
    exact eulerian_hamiltonian_field a ha hQ g hg lam hlam N hN hpos hpb hder E hE hsource hR s x (hKN hx)
  · intro s y hy
    by_cases hp : (s,y) ∈ tsupport χ
    · have hpO := hχO hp
      have hsy : g s y=y := hfix s y hy
      have hvel := embeddingVelocity_zero_of_fixed g hg S hfix s y hy
      have hs : (s,y) ∈ E.source := by rw [hsource]; exact ⟨mem_univ _,hSN hy⟩
      have hinverse : E.symm (s,y)=(s,y) := by
        have hi := E.left_inv hs
        simpa only [hE,F,hsy] using hi
      have hval : h (s,y)=0 := by
        simp only [h,eulerianHamiltonian,eulerianVelocity,hinverse,hvel,map_zero]
      have hfield : hamiltonianField a (fun z => h (s,z)) y=0 := by
        have hi := eulerian_hamiltonian_field a ha hQ g hg lam hlam N hN hpos hpb hder E hE hsource hR s y (hSN hy)
        simpa only [hsy,hvel] using hi
      have hgerm : H s =ᶠ[𝓝 y] (fun z => χ (s,z)*h (s,z)) :=
        (hAprod (s,y) hpO).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
      rw [hamiltonianField_germ a (H s) (fun z => χ (s,z)*h (s,z)) y hgerm]
      have hdχ : DifferentiableAt ℝ (fun z => χ (s,z)) y :=
        (hχ.comp (f := fun z : V => (s,z)) (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y
      have hdh : DifferentiableAt ℝ (fun z => h (s,z)) y :=
        ((hh.contDiffAt (hO.mem_nhds hpO)).comp y (contDiff_const.prodMk contDiff_id).contDiffAt).differentiableAt (by simp)
      exact hamiltonian_cutoff_preserves_zero_at a (fun z => χ (s,z)) (fun z => h (s,z)) y hdχ hdh hval hfield
    · have hgerm : H s =ᶠ[𝓝 y] (fun _ => (0:ℝ)) :=
        (hAzero (s,y) hp).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
      rw [hamiltonianField_germ a (H s) (fun _ => 0) y hgerm]
      simp [hamiltonianField,hamiltonianAlgebra,gradient3,cross]

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem relative_extend_contact_embedding_family (a : V → V) (ha : ContDiff ℝ ∞ a)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0)
    (g : ℝ → V → V) (hg : ContDiff ℝ ∞ (fun p : ℝ × V => g p.1 p.2))
    (lam : ℝ → V → ℝ) (hlam : ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2))
    (N : Set V) (hN : IsOpen N) (hpos : ∀ s x, x ∈ N → 0 < lam s x)
    (hpb : ∀ s x, x ∈ N → ∀ v,
      covector (a (g s x)) (fderiv ℝ (g s) x v)=lam s x*covector (a x) v)
    (hinj : ∀ s, InjOn (g s) N) (hder : ∀ s x, x ∈ N → Injective (fderiv ℝ (g s) x))
    (h0 : ∀ x ∈ N, g 0 x=x)
    (S : Set V) (hSN : S ⊆ N) (hstationary : ∀ s y, y ∈ S → g s y=y)
    (K U : Set V) (hK : IsCompact K) (hKN : K ⊆ N) (hU : IsOpen U)
    (htrack : ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ K, g s x ∈ U) :
    ∃ ψ ρ : ℝ → V → V, ∃ Λ : ℝ → V → ℝ, ∃ C : Set V,
      ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => Λ p.1 p.2) ∧
      IsCompact C ∧ C ⊆ U ∧ (∀ y, ψ 0 y=y) ∧
      (∀ t y, ρ t (ψ t y)=y) ∧ (∀ t y, ψ t (ρ t y)=y) ∧
      (∀ t y, y ∉ C → ψ t y=y) ∧ (∀ t y, 0 < Λ t y) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y v,
        covector (a (ψ t y)) (fderiv ℝ (ψ t) y v)=Λ t y*covector (a y) v) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ K, ψ t x=g t x) ∧
      ∀ t y, y ∈ S → ψ t y=y := by
  obtain ⟨H,C,hH,hC,hCU,hc,hmatch,hSzero⟩ := relative_compact_generator_of_contact_embeddings a ha hQ g hg lam hlam
    N hN hpos hpb hinj hder S hSN hstationary K U hK hKN hU htrack
  let X : ℝ → V → V := fun t => hamiltonianField a (H t)
  let μ : ℝ → V → ℝ := fun t => hamiltonianRate a (H t)
  obtain ⟨hX,hμ⟩ := hamiltonian_family_contDiff a H ha hH hQ
  have hLie (t : ℝ) (y v : V) : lieDerivOneForm (X t) (fun z => covector (a z)) y v=μ t y*covector (a y) v := by
    have hHt : ContDiff ℝ ∞ (H t) := hH.comp (f := fun z : V => (t,z)) (contDiff_const.prodMk contDiff_id)
    exact hamiltonianField_lie a (H t) ha hHt hQ y v
  obtain ⟨ψ,ρ,Λ,hψ,hρ,hΛ,hψ0,hbij,hρψ,hψρ,hd,hfix,hposΛ,hpbΛ⟩ :=
    integrate_time_contact_field (fun z => covector (a z)) (covector.contDiff.comp ha) X μ hX hμ C hC hc hLie
  have hSfix : ∀ t y, y ∈ S → ψ t y=y := by
    intro t y hy
    exact ambient_flow_fixes X ψ hX ⟨C,hC,hc⟩ hψ0 hd y (fun r => hSzero r y hy) t
  refine ⟨ψ,ρ,Λ,C,hψ,hρ,hΛ,hC,hCU,hψ0,hρψ,hψρ,hfix,hposΛ,hpbΛ,?_,hSfix⟩
  obtain ⟨L,hL⟩ := FlowCalculus.uniform_spatial_lipschitz_of_compact_support X hX ⟨C,hC,hc⟩ 0 1
  intro t ht x hx
  have hgcurve (r : ℝ) : HasDerivAt (fun s => g s x) (embeddingVelocity g (r,x)) r := by
    have hh := (hg.differentiable (by simp) (r,x)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (hasDerivAt_const r x))
    exact hh
  have hψc : Continuous (fun s => ψ s x) := hψ.continuous.comp (continuous_id.prodMk continuous_const)
  have hgc : Continuous (fun s => g s x) := hg.continuous.comp (continuous_id.prodMk continuous_const)
  have heq : EqOn (fun s => ψ s x) (fun s => g s x) (Icc (0:ℝ) 1) := by
    apply ODE_solution_unique_of_mem_Icc_right (v := X) (s := fun _ => Set.univ)
      (fun r hr => (hL r (Ico_subset_Icc_self hr)).lipschitzOnWith) hψc.continuousOn
      (fun r hr => (hd r x).hasDerivWithinAt) (fun _ _ => mem_univ _) hgc.continuousOn
    · intro r hr
      change HasDerivWithinAt (fun s => g s x) (hamiltonianField a (H r) (g r x)) (Ici r) r
      rw [hmatch r (Ico_subset_Icc_self hr) x hx]
      exact (hgcurve r).hasDerivWithinAt
    · exact fun _ _ => mem_univ _
    · rw [hψ0,h0 x (hKN hx)]
  exact heq ht

end
end ContactTopology.ConvexDeformation


open Set
open scoped ContDiff

theorem solution
    (a : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (ha : ContDiff ℝ ∞ a)
    (g : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hg : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => g p.1 p.2))
    (lam : ℝ → (Fin 3 → ℝ) → ℝ)
    (hlam : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => lam p.1 p.2))
    (N : Set (Fin 3 → ℝ)) (hN : IsOpen N)
    (hinj : ∀ s, InjOn (g s) N)
    (hder : ∀ s x, x ∈ N → Function.Injective (fderiv ℝ (g s) x))
    (h0 : ∀ x ∈ N, g 0 x=x)
    (S : Set (Fin 3 → ℝ)) (hSN : S ⊆ N) (hstationary : ∀ s y, y ∈ S → g s y=y)
    (K U : Set (Fin 3 → ℝ)) (hK : IsCompact K) (hKN : K ⊆ N) (hU : IsOpen U)
    (htrack : ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ K, g s x ∈ U) :
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun p v => p 0*v 0+p 1*v 1+p 2*v 2
    let c : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y =>
      ![fderiv ℝ a y (Pi.single 1 1) 2-fderiv ℝ a y (Pi.single 2 1) 1,
        fderiv ℝ a y (Pi.single 2 1) 0-fderiv ℝ a y (Pi.single 0 1) 2,
        fderiv ℝ a y (Pi.single 0 1) 1-fderiv ℝ a y (Pi.single 1 1) 0]
    (∀ y, B (a y) (c y) ≠ 0) → (∀ s x, x ∈ N → 0 < lam s x) →
    (∀ s x, x ∈ N → ∀ v, B (a (g s x)) (fderiv ℝ (g s) x v)=lam s x*B (a x) v) →
    ∃ ψ ρ : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ), ∃ Λ : ℝ → (Fin 3 → ℝ) → ℝ,
    ∃ C : Set (Fin 3 → ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => Λ p.1 p.2) ∧
      IsCompact C ∧ C ⊆ U ∧ (∀ y, ψ 0 y=y) ∧
      (∀ t y, ρ t (ψ t y)=y) ∧ (∀ t y, ψ t (ρ t y)=y) ∧
      (∀ t y, y ∉ C → ψ t y=y) ∧ (∀ t y, 0 < Λ t y) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y v, B (a (ψ t y)) (fderiv ℝ (ψ t) y v)=Λ t y*B (a y) v) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ K, ψ t x=g t x) ∧
      ∀ t y, y ∈ S → ψ t y=y := by


  dsimp only
  intro hQ hpos hpb
  have hp : ∀ s x, x ∈ N → ∀ v,
      ContactTopology.ConvexDeformation.covector (a (g s x)) (fderiv ℝ (g s) x v)=
        lam s x*ContactTopology.ConvexDeformation.covector (a x) v := by
    simpa only [ContactTopology.ConvexDeformation.covector_apply,ContactTopology.ConvexDeformation.dot] using hpb
  obtain ⟨ψ,ρ,Λ,C,hψ,hρ,hΛ,hC,hCU,hψ0,hρψ,hψρ,hout,hΛpos,hcontact,hmatch,hSfix⟩ :=
    ContactTopology.ConvexDeformation.relative_extend_contact_embedding_family a ha hQ g hg lam hlam N hN hpos hp
      hinj hder h0 S hSN hstationary K U hK hKN hU htrack
  refine ⟨ψ,ρ,Λ,C,hψ,hρ,hΛ,hC,hCU,hψ0,hρψ,hψρ,hout,hΛpos,?_,hmatch,hSfix⟩
  intro t ht y v
  simpa only [ContactTopology.ConvexDeformation.covector_apply,ContactTopology.ConvexDeformation.dot] using hcontact t ht y v
