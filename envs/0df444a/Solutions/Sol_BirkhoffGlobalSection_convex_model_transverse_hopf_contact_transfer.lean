-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_transverse_hopf_contact_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T22:10:06.018399+00:00
-- url     : https://prove2.me/submissions/ff7be9aa-14f4-45ea-bc98-3cec94318606

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Definitions.Def_GrayStability_Basic
import Mathlib.Algebra.Field.Periodic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.TietzeExtension
import Theorems.Thm_BirkhoffGlobalSection_compact_unique_ray_radial_graph
import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Theorems.Thm_BirkhoffGlobalSection_convex_model_smooth_radial_chart
import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_contact_pairing
import Theorems.Thm_BirkhoffGlobalSection_left_component_radial_norm_positive
import Theorems.Thm_BirkhoffGlobalSection_left_component_ray_exists
import Theorems.Thm_BirkhoffGlobalSection_left_component_ray_unique_scale
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_geometry
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_radial_bijection
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_radial_derivative_pos
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_smooth_radial_chart
import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
import Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
import Theorems.Thm_ContactCalculus_extDeriv_naturality_of_tangent_pullback_on_regular_level
import Theorems.Thm_ContactCalculus_exterior_pairing_pullback
import Theorems.Thm_FlowCalculus_compact_supported_flow_preserves_regular_level
import Theorems.Thm_FlowCalculus_exists_unique_global_trajectory_of_compact_support
import Theorems.Thm_FlowCalculus_smooth_flow_spatial_derivative_injective
import Theorems.Thm_GrayStability_pullback_family_hasDerivAt
import Theorems.Thm_GrayStability_smooth_moser_lie_generator
import Theorems.Thm_ParameterizedCalculus_smooth_scalar_linear_transport

















set_option backward.isDefEq.respectTransparency false

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set Filter
open scoped ContDiff Topology
noncomputable section

lemma radiusSq_pos (y : Phase) (hy : y ≠ 0) : 0 < zNormSq y + wNormSq y := by
  by_contra hn
  have hle := le_of_not_gt hn
  unfold zNormSq wNormSq at hle
  apply hy
  ext i
  fin_cases i <;> dsimp <;>
    nlinarith [sq_nonneg (y 0),sq_nonneg (y 1),sq_nonneg (y 2),sq_nonneg (y 3)]

lemma sphere_ne_zero {u : Phase} (hu : u ∈ unitThreeSphere) : u ≠ 0 := by
  intro he
  simpa [he,unitThreeSphere,zNormSq,wNormSq] using hu

lemma normalize_unit {u : Phase} (hu : u ∈ unitThreeSphere) : radialNormalize u = u := by
  change zNormSq u + wNormSq u = 1 at hu
  simp [radialNormalize,hu]

lemma normalize_positive_smul {u : Phase} (hu : u ∈ unitThreeSphere) {r : ℝ} (hr : 0 < r) :
    radialNormalize (r • u) = u := by
  have he : zNormSq (r • u) + wNormSq (r • u) = r^2 := by
    change zNormSq u + wNormSq u = 1 at hu
    simp [zNormSq,wNormSq] at hu ⊢
    nlinarith [sq_nonneg (u 0),sq_nonneg (u 1),sq_nonneg (u 2),sq_nonneg (u 3)]
  simp [radialNormalize,he,Real.sqrt_sq hr.le,smul_smul,inv_mul_cancel₀ hr.ne']

-- This implicit-function step follows the accepted smooth radial gauge chart proof
-- (submission 0a6b8288-05d8-46ac-bf13-6e10d532f4ed), with an arbitrary continuous radius.
lemma smooth_continuous_implicit_radius (f : Phase × ℝ → ℝ) (r : Phase → ℝ) (u : Phase)
    (hf : ContDiffAt ℝ ∞ f (u,r u)) (hr : ContinuousAt r u)
    (hi : ((fderiv ℝ f (u,r u)).comp (ContinuousLinearMap.inr ℝ Phase ℝ)).IsInvertible)
    (heq : ∀ᶠ x in 𝓝 u, f (x,r x) = f (u,r u)) : ContDiffAt ℝ ∞ r u := by
  let ψ := hf.implicitFunction (by simp) hi
  have hψ : ContDiffAt ℝ ∞ ψ u := hf.contDiffAt_implicitFunction (by simp) hi
  have hlocal := hf.eventually_apply_eq_iff_implicitFunction (by simp) hi
  have ht : Tendsto (fun x => (x,r x)) (𝓝 u) (𝓝 (u,r u)) := continuousAt_id.prodMk hr
  have hevent : r =ᶠ[𝓝 u] ψ := by
    filter_upwards [ht.eventually hlocal,heq] with x hx hroot
    exact (hx.mp hroot).symm
  exact hψ.congr_of_eventuallyEq hevent

lemma left_component_smooth_radial_chart (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ G : Phase → Phase,
      (∀ u ∈ unitThreeSphere, ContDiffAt ℝ ∞ G u ∧ G u ∈ leftEnergyComponent μ c ∧
        radialNormalize (G u) = u ∧ G (-u) = -G u ∧ ∃ r : ℝ, 0 < r ∧ G u = r • u) ∧
      (∀ y ∈ leftEnergyComponent μ c, G (radialNormalize y) = y) := by
  have hgeom := left_energy_component_geometry μ c hμ0 hμ1 hc
  have hnorm := left_component_radial_norm_positive μ c hμ0 hμ1 hc
  have h0 : (0 : Phase) ∉ leftEnergyComponent μ c := by
    intro hm
    have hp := hnorm 0 hm
    simpa [zNormSq,wNormSq] using hp
  have huniq : ∀ x : {x : Phase // x ∈ unitThreeSphere}, ∃! r : ℝ,
      0 < r ∧ (fun i : Fin 4 => r * (x : Phase) i) ∈ leftEnergyComponent μ c := by
    intro x
    obtain ⟨r,hr,hm⟩ := left_component_ray_exists μ c hμ0 hμ1 hc x x.property
    refine ⟨r,⟨hr,hm⟩,?_⟩
    intro s hs
    exact left_component_ray_unique_scale μ c hμ0 hμ1 hc x x.property s r hs.1 hr hs.2 hm
  obtain ⟨ρ,hρc,hρpos,hρrange⟩ := compact_unique_ray_radial_graph (leftEnergyComponent μ c) hgeom.1 h0 huniq
  have hclosed : IsClosed unitThreeSphere := by
    have hp : Continuous (fun u : Phase => zNormSq u + wNormSq u) := by
      unfold zNormSq wNormSq
      fun_prop
    exact isClosed_eq hp continuous_const
  obtain ⟨ρA,hρA⟩ := ContinuousMap.exists_restrict_eq hclosed (⟨ρ,hρc⟩ : C(unitThreeSphere,ℝ))
  have hρAe : ∀ u : {u : Phase // u ∈ unitThreeSphere}, ρA u = ρ u := by
    intro u
    exact congrArg (fun f : C(unitThreeSphere,ℝ) => f u) hρA
  let r : Phase → ℝ := fun x => ρA (radialNormalize x)
  let G : Phase → Phase := fun x => r x • radialNormalize x
  have hrdata : ∀ x : Phase, x ≠ 0 → 0 < r x ∧ G x ∈ leftEnergyComponent μ c := by
    intro x hx
    have hN := (radial_normalization_contact_identity x (radiusSq_pos x hx)).2.1
    have he : r x = ρ ⟨radialNormalize x,hN⟩ := hρAe ⟨radialNormalize x,hN⟩
    refine ⟨he ▸ hρpos _,?_⟩
    rw [hρrange]
    refine ⟨⟨radialNormalize x,hN⟩,?_⟩
    change (fun i => ρ ⟨radialNormalize x,hN⟩ * radialNormalize x i) = r x • radialNormalize x
    rw [he]
    rfl
  have hNinj : InjOn radialNormalize (leftEnergyComponent μ c) := by
    obtain ⟨f,hfc,hfb,hfe⟩ := left_energy_component_radial_bijection μ c hμ0 hμ1 hc
    intro x hx y hy he
    have hf : f ⟨x,hx⟩ = f ⟨y,hy⟩ := by
      apply Subtype.ext
      rw [hfe,hfe]
      ext i
      simpa [radialNormalize,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm] using congrFun he i
    exact congrArg Subtype.val (hfb.1 hf)
  have hGnorm : ∀ u ∈ unitThreeSphere, radialNormalize (G u) = u := by
    intro u hu
    change radialNormalize (r u • radialNormalize u) = u
    rw [normalize_unit hu]
    exact normalize_positive_smul hu (hrdata u (sphere_ne_zero hu)).1
  have hGsmooth : ∀ u ∈ unitThreeSphere, ContDiffAt ℝ ∞ G u := by
    intro u hu
    have hNu : ContDiffAt ℝ ∞ radialNormalize u :=
      (radial_normalization_contact_identity u (radiusSq_pos u (sphere_ne_zero hu))).1
    have hru : ContinuousAt r u := ρA.continuous.continuousAt.comp hNu.continuousAt
    have hGu := (hrdata u (sphere_ne_zero hu)).2
    have hHG : ContDiffAt ℝ ∞ (leviCivitaHamiltonian μ c) (r u • radialNormalize u) :=
      (hgeom.2.1 (G u) hGu).1
    let f : Phase × ℝ → ℝ := fun p => leviCivitaHamiltonian μ c (p.2 • radialNormalize p.1)
    have hs : ContDiffAt ℝ ∞ (fun p : Phase × ℝ => p.2 • radialNormalize p.1) (u,r u) :=
      contDiffAt_snd.smul (hNu.comp (u,r u) contDiffAt_fst)
    have hf : ContDiffAt ℝ ∞ f (u,r u) := by
      convert! hHG.comp (u,r u) hs using 1
    have hnonzero : fderiv ℝ (leviCivitaHamiltonian μ c) (G u) (radialNormalize u) ≠ 0 := by
      intro hz
      have hp := left_energy_component_radial_derivative_pos μ c hμ0 hμ1 hc (G u) hGu
      have he : fderiv ℝ (leviCivitaHamiltonian μ c) (G u) (G u) = 0 := by
        change fderiv ℝ (leviCivitaHamiltonian μ c) (G u) (r u • radialNormalize u) = 0
        rw [map_smul,hz,smul_zero]
      exact hp.ne' he
    have hdN := (hNu.differentiableAt (by simp)).hasFDerivAt.comp (u,r u)
      (hasFDerivAt_fst (𝕜 := ℝ) (p := (u,r u)))
    have hds := (hasFDerivAt_snd (𝕜 := ℝ) (p := (u,r u))).smul hdN
    have hdf := (hHG.differentiableAt (by simp)).hasFDerivAt.comp (u,r u) hds
    change HasFDerivAt f _ (u,r u) at hdf
    have hrestrict : (fderiv ℝ f (u,r u)).comp (ContinuousLinearMap.inr ℝ Phase ℝ) =
        (fderiv ℝ (leviCivitaHamiltonian μ c) (G u) (radialNormalize u)) • ContinuousLinearMap.id ℝ ℝ := by
      rw [hdf.fderiv]
      ext a
      simp [mul_comm,G]
    have hi : ((fderiv ℝ f (u,r u)).comp (ContinuousLinearMap.inr ℝ Phase ℝ)).IsInvertible := by
      rw [hrestrict]
      apply ContinuousLinearMap.IsInvertible.of_inverse
        (g := (fderiv ℝ (leviCivitaHamiltonian μ c) (G u) (radialNormalize u))⁻¹ • ContinuousLinearMap.id ℝ ℝ)
      · ext a; simp [hnonzero]
      · ext a; simp [hnonzero]
    have hzero : ∀ x : Phase, x ≠ 0 → leviCivitaHamiltonian μ c (G x) = 0 := by
      intro x hx
      exact (connectedComponentIn_subset (regularEnergyLocus μ c) (leftCollisionPoint μ) (hrdata x hx).2).1
    have heq : ∀ᶠ x in 𝓝 u, f (x,r x) = f (u,r u) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds (sphere_ne_zero hu)] with x hx
      exact (hzero x hx).trans (hzero u (sphere_ne_zero hu)).symm
    exact (smooth_continuous_implicit_radius f r u hf hru hi heq).smul hNu
  refine ⟨G,?_,?_⟩
  · intro u hu
    refine ⟨hGsmooth u hu,(hrdata u (sphere_ne_zero hu)).2,hGnorm u hu,?_,r u,(hrdata u (sphere_ne_zero hu)).1,?_⟩
    · have hnu : -u ∈ unitThreeSphere := by simpa [unitThreeSphere,zNormSq,wNormSq] using hu
      have hGune := ne_of_mem_of_not_mem (hrdata u (sphere_ne_zero hu)).2 h0
      apply hNinj (hrdata (-u) (sphere_ne_zero hnu)).2
        ((hgeom.2.2.1 (G u)).mp (hrdata u (sphere_ne_zero hu)).2)
      rw [hGnorm (-u) hnu,(radial_normalization_contact_identity (G u) (radiusSq_pos (G u) hGune)).2.2.1,hGnorm u hu]
    · dsimp [G]
      rw [normalize_unit hu]
  · intro y hy
    have hNy := (radial_normalization_contact_identity y (hnorm y hy)).2.1
    exact hNinj (hrdata _ (sphere_ne_zero hNy)).2 hy (hGnorm _ hNy)

end
end BirkhoffGlobalSection.HopfTransport

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

lemma sphere_line_norm_positive (y v : Phase) (hy : y ∈ unitThreeSphere)
    (hv : phaseDot y v = 0) (s : ℝ) :
    0 < zNormSq (y+s•v) + wNormSq (y+s•v) := by
  have hy' := sphere_dot_self hy
  have hvv : 0 ≤ phaseDot v v := by
    simp only [phaseDot]
    nlinarith [sq_nonneg (v 0),sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]
  have he : zNormSq (y+s•v) + wNormSq (y+s•v) = 1 + s^2 * phaseDot v v := by
    simp [zNormSq,wNormSq,phaseDot] at hy' hv ⊢
    linear_combination hy' + (2*s)*hv
  rw [he]
  nlinarith [sq_nonneg s,mul_nonneg (sq_nonneg s) hvv]

lemma sphere_curve_hasDerivAt (y v : Phase) (hy : y ∈ unitThreeSphere)
    (hv : phaseDot y v = 0) :
    HasDerivAt (fun s : ℝ => radialNormalize (y+s•v)) v 0 := by
  have hc : HasDerivAt (fun s : ℝ => y+s•v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1 <;> simp
  have hq : HasDerivAt (fun s : ℝ => zNormSq (y+s•v)+wNormSq (y+s•v)) 0 0 := by
    convert! dot_self_hasDerivAt hc using 1
    · ext s
      simp [zNormSq,wNormSq,phaseDot,pow_two,add_assoc]
    · simp [hv]
  have hQ : zNormSq y + wNormSq y = 1 := hy
  have hs := hq.sqrt (by simp [hQ])
  have hi := hs.inv (by simp [hQ])
  have hd := hi.smul hc
  convert! hd using 1 <;> simp [radialNormalize,hQ]

lemma sphere_tangent_fderiv_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f g : Phase → E) (y v : Phase)
    (hy : y ∈ unitThreeSphere) (hv : phaseDot y v = 0)
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y)
    (heq : EqOn f g unitThreeSphere) : fderiv ℝ f y v = fderiv ℝ g y v := by
  have hc := sphere_curve_hasDerivAt y v hy hv
  have hfy : DifferentiableAt ℝ f (radialNormalize (y+(0:ℝ)•v)) := by simpa [normalize_unit hy] using hf
  have hgy : DifferentiableAt ℝ g (radialNormalize (y+(0:ℝ)•v)) := by simpa [normalize_unit hy] using hg
  have hdf := hfy.hasFDerivAt.comp_hasDerivAt 0 hc
  have hdg := hgy.hasFDerivAt.comp_hasDerivAt 0 hc
  have hfun : f ∘ (fun s : ℝ => radialNormalize (y+s•v)) = g ∘ (fun s : ℝ => radialNormalize (y+s•v)) := by
    funext s
    exact heq (x := radialNormalize (y+s•v))
      (radial_normalization_contact_identity _ (sphere_line_norm_positive y v hy hv s)).2.1
  rw [hfun] at hdf
  have he := hdf.unique hdg
  simpa [normalize_unit hy] using he

lemma sphere_map_fderiv_tangent (f : Phase → Phase) (y v : Phase)
    (hy : y ∈ unitThreeSphere) (hv : phaseDot y v = 0)
    (hf : DifferentiableAt ℝ f y) (hmap : MapsTo f unitThreeSphere unitThreeSphere) :
    phaseDot (f y) (fderiv ℝ f y v) = 0 := by
  have hc := sphere_curve_hasDerivAt y v hy hv
  have hfy : DifferentiableAt ℝ f (radialNormalize (y+(0:ℝ)•v)) := by simpa [normalize_unit hy] using hf
  have hd := dot_self_hasDerivAt (hfy.hasFDerivAt.comp_hasDerivAt 0 hc)
  have heq : (fun s : ℝ => phaseDot (f (radialNormalize (y+s•v))) (f (radialNormalize (y+s•v)))) = fun _ => (1:ℝ) := by
    funext s
    exact sphere_dot_self (hmap (radial_normalization_contact_identity _
      (sphere_line_norm_positive y v hy hv s)).2.1)
  change HasDerivAt (fun s : ℝ => phaseDot (f (radialNormalize (y+s•v))) (f (radialNormalize (y+s•v)))) _ 0 at hd
  rw [heq] at hd
  have he := hd.unique (hasDerivAt_const (0:ℝ) (1:ℝ))
  simp [normalize_unit hy] at he
  linarith

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set
open scoped ContDiff
noncomputable section

lemma convex_frontier_ne_zero {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    {y : Phase} (hy : y ∈ frontier M.body) : y ≠ 0 := by
  intro he
  have hn : y ∉ interior M.body := hy.2
  apply hn
  simpa [he] using M.origin_interior

lemma normalized_model_sphere_equivalence (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (M : ConvexRegularizationModel μ c) :
    ∃ T U : Phase → Phase,
      (∀ u ∈ unitThreeSphere, ContDiffAt ℝ ∞ T u ∧ ContDiffAt ℝ ∞ U u ∧
        T u ∈ unitThreeSphere ∧ U u ∈ unitThreeSphere) ∧
      (∀ u ∈ unitThreeSphere, U (T u) = u ∧ T (U u) = u) ∧
      (∀ u ∈ unitThreeSphere, T (-u) = -T u ∧ U (-u) = -U u) ∧
      ∀ y ∈ leftEnergyComponent μ c,
        T (radialNormalize y) = radialNormalize (M.toModel y) := by
  obtain ⟨G,hG,hGinv⟩ := BirkhoffGlobalSection.left_energy_component_smooth_radial_chart μ c hμ0 hμ1 hc
  let A : Phase → Phase := fun u => (gauge M.body u)⁻¹ • u
  have hA := convex_model_smooth_radial_chart M
  change (∀ y ∈ frontier M.body, ContDiffAt ℝ ∞ radialNormalize y ∧ radialNormalize y ∈ unitThreeSphere ∧ A (radialNormalize y) = y) ∧
    (∀ u ∈ unitThreeSphere, ContDiffAt ℝ ∞ A u ∧ A u ∈ frontier M.body ∧ radialNormalize (A u) = u) at hA
  have hmfront : ∀ y ∈ leftEnergyComponent μ c, M.toModel y ∈ frontier M.body := by
    intro y hy
    rw [← M.image_frontier]
    exact ⟨y,hy,rfl⟩
  have hback : ∀ y ∈ frontier M.body, M.fromModel y ∈ leftEnergyComponent μ c := by
    intro y hy
    rw [← M.image_frontier] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    simpa only [M.left_inverse x (M.contains_component hx)] using hx
  have hftarget : ∀ y ∈ frontier M.body, y ∈ M.target := by
    intro y hy
    rw [← M.image_frontier] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    exact M.toModel_mapsTo (M.contains_component hx)
  have hsN : ∀ y ∈ leftEnergyComponent μ c, ContDiffAt ℝ ∞ radialNormalize y ∧ radialNormalize y ∈ unitThreeSphere := by
    intro y hy
    have hn := radial_normalization_contact_identity y
      (left_component_radial_norm_positive μ c hμ0 hμ1 hc y hy)
    exact ⟨hn.1,hn.2.1⟩
  let T : Phase → Phase := fun u => radialNormalize (M.toModel (G u))
  let U : Phase → Phase := fun u => radialNormalize (M.fromModel (A u))
  have hT : ∀ u ∈ unitThreeSphere, ContDiffAt ℝ ∞ T u ∧ T u ∈ unitThreeSphere := by
    intro u hu
    have hGu := (hG u hu).2.1
    have hFu := hmfront _ hGu
    have hNu := hA.1 _ hFu
    have hF := M.toModel_smooth.contDiffAt (M.source_open.mem_nhds (M.contains_component hGu))
    refine ⟨?_,hNu.2.1⟩
    exact hNu.1.comp u (hF.comp u (hG u hu).1)
  have hU : ∀ u ∈ unitThreeSphere, ContDiffAt ℝ ∞ U u ∧ U u ∈ unitThreeSphere := by
    intro u hu
    have hAu := (hA.2 u hu).2.1
    have hFu := hback _ hAu
    have hNu := hsN _ hFu
    have hF := M.fromModel_smooth.contDiffAt (M.target_open.mem_nhds (hftarget _ hAu))
    refine ⟨?_,hNu.2⟩
    exact hNu.1.comp u (hF.comp u (hA.2 u hu).1)
  have hUT : ∀ u ∈ unitThreeSphere, U (T u) = u := by
    intro u hu
    have hGu := (hG u hu).2.1
    change radialNormalize (M.fromModel (A (radialNormalize (M.toModel (G u))))) = u
    rw [(hA.1 _ (hmfront _ hGu)).2.2,M.left_inverse _ (M.contains_component hGu)]
    exact (hG u hu).2.2.1
  have hTU : ∀ u ∈ unitThreeSphere, T (U u) = u := by
    intro u hu
    have hAu := (hA.2 u hu).2.1
    change radialNormalize (M.toModel (G (radialNormalize (M.fromModel (A u))))) = u
    rw [hGinv _ (hback _ hAu),M.right_inverse _ (hftarget _ hAu)]
    exact (hA.2 u hu).2.2
  have hTinj : InjOn T unitThreeSphere := by
    intro u hu v hv he
    have hi := congrArg U he
    simpa only [hUT u hu,hUT v hv] using hi
  have hTneg : ∀ u ∈ unitThreeSphere, T (-u) = -T u := by
    intro u hu
    change radialNormalize (M.toModel (G (-u))) = -radialNormalize (M.toModel (G u))
    rw [(hG u hu).2.2.2.1,M.antipodal _ (hG u hu).2.1]
    exact (radial_normalization_contact_identity _ (radiusSq_pos _
      (convex_frontier_ne_zero M (hmfront _ (hG u hu).2.1)))).2.2.1
  refine ⟨T,U,?_,?_,?_,?_⟩
  · intro u hu
    exact ⟨(hT u hu).1,(hU u hu).1,(hT u hu).2,(hU u hu).2⟩
  · intro u hu
    exact ⟨hUT u hu,hTU u hu⟩
  · intro u hu
    refine ⟨hTneg u hu,?_⟩
    have hnu : -u ∈ unitThreeSphere := by simpa [unitThreeSphere,zNormSq,wNormSq] using hu
    have hUnu := (hU (-u) hnu).2
    have hUu := (hU u hu).2
    have hnUu : -U u ∈ unitThreeSphere := by simpa [unitThreeSphere,zNormSq,wNormSq] using hUu
    apply hTinj hUnu hnUu
    rw [hTU (-u) hnu,hTneg _ hUu,hTU u hu]
  · intro y hy
    change radialNormalize (M.toModel (G (radialNormalize y))) = _
    rw [hGinv y hy]

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set
open scoped ContDiff
noncomputable section

lemma sphere_neg_mem {y : Phase} (hy : y ∈ unitThreeSphere) : -y ∈ unitThreeSphere := by
  simpa [unitThreeSphere,zNormSq,wNormSq] using hy

lemma sphere_odd_tangent_derivative (f : Phase → Phase)
    (hs : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ f y)
    (hodd : ∀ y ∈ unitThreeSphere, f (-y) = -f y)
    (y v : Phase) (hy : y ∈ unitThreeSphere) (hv : phaseDot y v = 0) :
    fderiv ℝ f (-y) v = fderiv ℝ f y v := by
  let g : Phase → Phase := fun z => -f (-z)
  have hn : HasFDerivAt (fun z : Phase => -z) (-ContinuousLinearMap.id ℝ Phase) y :=
    (hasFDerivAt_id y).neg
  have hg := (((hs (-y) (sphere_neg_mem hy)).differentiableAt (by simp)).hasFDerivAt.comp y hn).neg
  have heq : EqOn f g unitThreeSphere := by
    intro z hz
    dsimp [g]
    rw [hodd z hz,neg_neg]
  have he := sphere_tangent_fderiv_eq f g y v hy hv
    ((hs y hy).differentiableAt (by simp)) hg.differentiableAt heq
  change HasFDerivAt g _ y at hg
  rw [hg.fderiv] at he
  simpa [ContinuousLinearMap.comp_apply] using he.symm

lemma sphere_diffeo_tangent_leftInverse (T U : Phase → Phase)
    (hT : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ T y ∧ T y ∈ unitThreeSphere)
    (hU : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ U y)
    (hUT : ∀ y ∈ unitThreeSphere, U (T y) = y)
    (y v : Phase) (hy : y ∈ unitThreeSphere) (hv : phaseDot y v = 0) :
    fderiv ℝ U (T y) (fderiv ℝ T y v) = v := by
  have hTd := ((hT y hy).1).differentiableAt (by simp)
  have hUd := (hU (T y) (hT y hy).2).differentiableAt (by simp)
  have he := sphere_tangent_fderiv_eq (U ∘ T) id y v hy hv
    (hUd.comp y hTd) differentiableAt_id hUT
  rw [fderiv_comp y hUd hTd] at he
  simpa using he

lemma sphere_diffeo_tangent_injective (T U : Phase → Phase)
    (hT : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ T y ∧ T y ∈ unitThreeSphere)
    (hU : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ U y)
    (hUT : ∀ y ∈ unitThreeSphere, U (T y) = y)
    (y : Phase) (hy : y ∈ unitThreeSphere) :
    InjOn (fderiv ℝ T y) {v : Phase | phaseDot y v = 0} := by
  intro v hv w hw he
  have hi := congrArg (fderiv ℝ U (T y)) he
  simpa only [sphere_diffeo_tangent_leftInverse T U hT hU hUT y v hy hv,
    sphere_diffeo_tangent_leftInverse T U hT hU hUT y w hy hw] using hi

lemma sphere_diffeo_tangent_surjective (T U : Phase → Phase)
    (hT : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ T y ∧ T y ∈ unitThreeSphere)
    (hU : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ U y ∧ U y ∈ unitThreeSphere)
    (hUT : ∀ y ∈ unitThreeSphere, U (T y) = y)
    (hTU : ∀ y ∈ unitThreeSphere, T (U y) = y)
    (y : Phase) (hy : y ∈ unitThreeSphere) (w : Phase) (hw : phaseDot (T y) w = 0) :
    ∃ v : Phase, phaseDot y v = 0 ∧ fderiv ℝ T y v = w := by
  refine ⟨fderiv ℝ U (T y) w,?_,?_⟩
  · have ht := sphere_map_fderiv_tangent U (T y) w (hT y hy).2 hw
      ((hU (T y) (hT y hy).2).1.differentiableAt (by simp)) (fun z hz => (hU z hz).2)
    simpa only [hUT y hy] using ht
  · have hi := sphere_diffeo_tangent_leftInverse U T hU (fun z hz => (hT z hz).1) hTU
      (T y) w (hT y hy).2 hw
    simpa only [hUT y hy] using hi

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set Filter
open scoped ContDiff Topology
noncomputable section

lemma sphere_smooth_extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Phase → E) (hf : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ f y) :
    ∃ g : Phase → E, ContDiff ℝ ∞ g ∧ EqOn g f unitThreeSphere ∧
      ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 → fderiv ℝ g y v = fderiv ℝ f y v := by
  let χ : Phase → ℝ := fun y => Real.smoothTransition (4*(zNormSq y+wNormSq y)-1)
  have hQ : ContDiff ℝ ∞ (fun y : Phase => zNormSq y+wNormSq y) := by
    unfold zNormSq wNormSq
    fun_prop
  have hχ : ContDiff ℝ ∞ χ := by
    have hθ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))
    exact hθ.comp ((contDiff_const.mul hQ).sub contDiff_const)
  let g : Phase → E := fun y => χ y • f (radialNormalize y)
  have hg : ContDiff ℝ ∞ g := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y = 0
    · have hnear : ∀ᶠ z : Phase in 𝓝 y, zNormSq z+wNormSq z < 1/4 := by
        apply (isOpen_lt hQ.continuous continuous_const).mem_nhds
        simp [hy,zNormSq,wNormSq]
      have he : g =ᶠ[𝓝 y] (fun _ => (0:E)) := by
        filter_upwards [hnear] with z hz
        change χ z • f (radialNormalize z) = 0
        have hχz : χ z = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
        rw [hχz,zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq he
    · have hn := radial_normalization_contact_identity y (radiusSq_pos y hy)
      exact hχ.contDiffAt.smul ((hf _ hn.2.1).comp y hn.1)
  have heq : EqOn g f unitThreeSphere := by
    intro y hy
    have hqy : zNormSq y+wNormSq y = 1 := hy
    have hχy : χ y = 1 := by
      change Real.smoothTransition (4*(zNormSq y+wNormSq y)-1) = 1
      rw [hqy,Real.smoothTransition.one_of_one_le (by norm_num)]
    dsimp [g]
    rw [hχy,one_smul,normalize_unit hy]
  refine ⟨g,hg,heq,?_⟩
  intro y hy v hv
  exact sphere_tangent_fderiv_eq g f y v hy hv
    (hg.differentiable (by simp) y) ((hf y hy).differentiableAt (by simp)) heq

lemma normalize_tangent_derivative (y v : Phase) (hy : y ∈ unitThreeSphere)
    (hv : phaseDot y v = 0) : fderiv ℝ radialNormalize y v = v := by
  have hd := sphere_tangent_fderiv_eq radialNormalize id y v hy hv
    ((radial_normalization_contact_identity y (radiusSq_pos y (sphere_ne_zero hy))).1.differentiableAt (by simp))
    differentiableAt_id (fun z hz => normalize_unit hz)
  simpa using hd

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set Filter
open scoped ContDiff Topology
noncomputable section

lemma radiusSq_smul (s : ℝ) (x : Phase) :
    zNormSq (s•x)+wNormSq (s•x) = s^2*(zNormSq x+wNormSq x) := by
  simp [zNormSq,wNormSq]
  ring

lemma left_component_radial_lift (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ a : Phase → ℝ,
      (∀ x : Phase, x ≠ 0 → ContDiffAt ℝ ∞ a x ∧ 0 < a x ∧
        a x • x ∈ leftEnergyComponent μ c) ∧
      (∀ u ∈ unitThreeSphere, radialNormalize (a u • u) = u ∧ a (-u) = a u) ∧
      (∀ y ∈ leftEnergyComponent μ c, a (radialNormalize y) • radialNormalize y = y) := by
  obtain ⟨G,hG,hGinv⟩ := BirkhoffGlobalSection.left_energy_component_smooth_radial_chart μ c hμ0 hμ1 hc
  let g : Phase → Phase := fun x => G (radialNormalize x)
  let Q : Phase → ℝ := fun x => zNormSq x+wNormSq x
  have hQ : ContDiff ℝ ∞ Q := by unfold Q zNormSq wNormSq; fun_prop
  have hg : ∀ x : Phase, x ≠ 0 → ContDiffAt ℝ ∞ g x ∧ g x ∈ leftEnergyComponent μ c := by
    intro x hx
    have hNx := radial_normalization_contact_identity x (radiusSq_pos x hx)
    exact ⟨((hG _ hNx.2.1).1).comp x hNx.1,(hG _ hNx.2.1).2.1⟩
  let a : Phase → ℝ := fun x => Real.sqrt (Q (g x)) / Real.sqrt (Q x)
  have hapos : ∀ x : Phase, x ≠ 0 → 0 < a x := by
    intro x hx
    exact div_pos (Real.sqrt_pos.mpr (left_component_radial_norm_positive μ c hμ0 hμ1 hc _ (hg x hx).2))
      (Real.sqrt_pos.mpr (radiusSq_pos x hx))
  have hrepr : ∀ x : Phase, x ≠ 0 → a x • x = g x := by
    intro x hx
    have hNx := (radial_normalization_contact_identity x (radiusSq_pos x hx)).2.1
    obtain ⟨s,hs,hsg⟩ := (hG _ hNx).2.2.2.2
    have he : Q (g x) = s^2 := by
      change Q (G (radialNormalize x)) = s^2
      rw [hsg]
      change zNormSq (s•radialNormalize x)+wNormSq (s•radialNormalize x) = s^2
      rw [radiusSq_smul]
      change zNormSq (radialNormalize x)+wNormSq (radialNormalize x) = 1 at hNx
      rw [hNx,mul_one]
    change (Real.sqrt (Q (g x)) / Real.sqrt (Q x)) • x = G (radialNormalize x)
    rw [he,Real.sqrt_sq hs.le,hsg]
    simp [radialNormalize,div_eq_mul_inv,smul_smul,Q]
  have hasmooth : ∀ x : Phase, x ≠ 0 → ContDiffAt ℝ ∞ a x := by
    intro x hx
    exact (((hQ.contDiffAt.comp x (hg x hx).1).sqrt
      (left_component_radial_norm_positive μ c hμ0 hμ1 hc _ (hg x hx).2).ne').div
      (hQ.contDiffAt.sqrt (radiusSq_pos x hx).ne')
      (Real.sqrt_pos.mpr (radiusSq_pos x hx)).ne')
  refine ⟨a,?_,?_,?_⟩
  · intro x hx
    exact ⟨hasmooth x hx,hapos x hx,hrepr x hx ▸ (hg x hx).2⟩
  · intro u hu
    have hune := sphere_ne_zero hu
    have hnune := sphere_ne_zero (sphere_neg_mem hu)
    have hgunit : g u = G u := by dsimp [g]; rw [normalize_unit hu]
    have hgnunit : g (-u) = -G u := by
      dsimp [g]
      rw [normalize_unit (sphere_neg_mem hu),(hG u hu).2.2.2.1]
    constructor
    · rw [hrepr u hune,hgunit]
      exact (hG u hu).2.2.1
    · dsimp [a]
      rw [hgnunit,hgunit]
      simp [Q,zNormSq,wNormSq]
  · intro y hy
    have hNy := (radial_normalization_contact_identity y
      (left_component_radial_norm_positive μ c hμ0 hμ1 hc y hy)).2.1
    rw [hrepr _ (sphere_ne_zero hNy)]
    dsimp [g]
    rw [normalize_unit hNy,hGinv y hy]

lemma left_component_radial_lift_tangent (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (a : Phase → ℝ)
    (ha : ∀ x : Phase, x ≠ 0 → ContDiffAt ℝ ∞ a x ∧ 0 < a x ∧ a x • x ∈ leftEnergyComponent μ c)
    (u : Phase) (hu : u ∈ unitThreeSphere) :
    (∀ v : Phase, fderiv ℝ (leviCivitaHamiltonian μ c) (a u•u)
      (fderiv ℝ (fun x => a x•x) u v) = 0) ∧
    (∀ w : Phase, fderiv ℝ (leviCivitaHamiltonian μ c) (a u•u) w = 0 →
      ∃ v : Phase, phaseDot u v = 0 ∧ fderiv ℝ (fun x => a x•x) u v = w) := by
  have hau := ha u (sphere_ne_zero hu)
  have hH := (left_energy_component_geometry μ c hμ0 hμ1 hc).2.1 _ hau.2.2 |>.1
  have hzero : (fun x : Phase => leviCivitaHamiltonian μ c (a x•x)) =ᶠ[𝓝 u] (fun _ => (0:ℝ)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (sphere_ne_zero hu)] with x hx
    exact (connectedComponentIn_subset (regularEnergyLocus μ c) (leftCollisionPoint μ) (ha x hx).2.2).1
  have hrad : fderiv ℝ (leviCivitaHamiltonian μ c) (a u•u) u ≠ 0 := by
    intro hz
    have hp := left_energy_component_radial_derivative_pos μ c hμ0 hμ1 hc _ hau.2.2
    rw [map_smul,hz,smul_zero] at hp
    exact lt_irrefl 0 hp
  have hsurj := radial_characteristic_bundle.{0,0,0}.2.2.1 a (leviCivitaHamiltonian μ c) u 0 hu
    (hau.1.differentiableAt (by simp)) hau.2.1 (hH.differentiableAt (by simp)) hzero hrad (by simp)
  refine ⟨hsurj.2.2,?_⟩
  intro w hw
  have hs := radial_characteristic_bundle.{0,0,0}.2.2.1 a (leviCivitaHamiltonian μ c) u w hu
    (hau.1.differentiableAt (by simp)) hau.2.1 (hH.differentiableAt (by simp)) hzero hrad hw
  exact ⟨_,hs.1,hs.2.1⟩

end
end BirkhoffGlobalSection.HopfTransport




namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection GrayStability
noncomputable section

lemma omega_self (v : Phase) : phaseSymplecticForm v v = 0 := by
  simp [phaseSymplecticForm]; ring

lemma omega_swap (u v : Phase) : phaseSymplecticForm u v = -phaseSymplecticForm v u := by
  simp [phaseSymplecticForm]; ring

lemma omega_smul_left (a : ℝ) (u v : Phase) :
    phaseSymplecticForm (a • u) v = a * phaseSymplecticForm u v := by
  simp [phaseSymplecticForm]; ring

lemma omega_sub_smul_right (u v w : Phase) (a : ℝ) :
    phaseSymplecticForm u (v - a • w) = phaseSymplecticForm u v - a * phaseSymplecticForm u w := by
  simp [phaseSymplecticForm]; ring

lemma omega_ext {u v : Phase} (h : ∀ w, phaseSymplecticForm u w = phaseSymplecticForm v w) : u = v := by
  have h0 := h (Pi.single 0 1)
  have h1 := h (Pi.single 1 1)
  have h2 := h (Pi.single 2 1)
  have h3 := h (Pi.single 3 1)
  simp [phaseSymplecticForm] at h0 h1 h2 h3
  ext i
  fin_cases i
  · exact h2
  · exact h3
  · exact h0
  · exact h1

lemma hyperplane_radical (D : Phase →L[ℝ] ℝ) (hD : D ≠ 0)
    (R u : Phase) (hR : ∀ v, phaseSymplecticForm R v = D v)
    (hu : ∀ v, D v = 0 → phaseSymplecticForm u v = 0) :
    ∃ a : ℝ, u = a • R := by
  obtain ⟨q,hq⟩ : ∃ q : Phase, D q ≠ 0 := by
    by_contra! hh
    apply hD
    ext v
    simpa using hh v
  let a := phaseSymplecticForm u q / D q
  refine ⟨a, omega_ext (fun v => ?_)⟩
  have hp : D (v - (D v / D q) • q) = 0 := by
    simp only [map_sub,map_smul,smul_eq_mul]
    field_simp
    ring
  have he := hu _ hp
  rw [omega_sub_smul_right] at he
  rw [omega_smul_left,hR]
  calc
    phaseSymplecticForm u v = (D v / D q) * phaseSymplecticForm u q := sub_eq_zero.mp he
    _ = a * D v := by dsimp [a]; ring

lemma hyperplane_contact_nondegenerate (D A : Phase →L[ℝ] ℝ) (hD : D ≠ 0)
    (R : Phase) (hR : ∀ v, phaseSymplecticForm R v = D v) (hAR : A R ≠ 0) :
    (∃ v : Phase, D v = 0 ∧ A v ≠ 0) ∧
      ∀ u : Phase, D u = 0 → A u = 0 → u ≠ 0 →
        ∃ v : Phase, D v = 0 ∧ A v = 0 ∧ phaseSymplecticForm u v ≠ 0 := by
  have hDR : D R = 0 := by rw [← hR,omega_self]
  refine ⟨⟨R,hDR,hAR⟩,?_⟩
  intro u hDu hAu hune
  by_contra! hv
  have hvan : ∀ w : Phase, D w = 0 → phaseSymplecticForm u w = 0 := by
    intro w hw
    have hpD : D (w - (A w / A R) • R) = 0 := by simp [hw,hDR]
    have hpA : A (w - (A w / A R) • R) = 0 := by
      simp only [map_sub,map_smul,smul_eq_mul]
      field_simp
      ring
    have he := hv _ hpD hpA
    rw [omega_sub_smul_right,omega_swap u R,hR,hDu] at he
    simpa using he
  obtain ⟨a,ha⟩ := hyperplane_radical D hD R u hR hvan
  have haz : a = 0 := by
    have he := congrArg A ha
    rw [hAu,map_smul,smul_eq_mul] at he
    exact (mul_eq_zero.mp he.symm).resolve_right hAR
  apply hune
  rw [ha,haz,zero_smul]

lemma contact_interpolation_at_hyperplane (D A₀ A₁ : Phase →L[ℝ] ℝ) (hD : D ≠ 0)
    (R : Phase) (hR : ∀ v, phaseSymplecticForm R v = D v)
    (hA₀ : 0 < A₀ R) (hA₁ : 0 < A₁ R) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let A := (1-t) • A₀ + t • A₁
    0 < A R ∧ (∃ v : Phase, D v = 0 ∧ A v ≠ 0) ∧
      ∀ u : Phase, D u = 0 → A u = 0 → u ≠ 0 →
        ∃ v : Phase, D v = 0 ∧ A v = 0 ∧ phaseSymplecticForm u v ≠ 0 := by
  dsimp only
  have hp : 0 < ((1-t) • A₀ + t • A₁) R := by
    simp only [add_apply,smul_apply,smul_eq_mul]
    have h0 : 0 ≤ (1-t) * A₀ R := mul_nonneg (sub_nonneg.mpr ht.2) hA₀.le
    have h1 : 0 ≤ t * A₁ R := mul_nonneg ht.1 hA₁.le
    by_cases hz : t = 0
    · simpa [hz] using hA₀
    · exact add_pos_of_nonneg_of_pos h0 (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm hz)) hA₁)
  exact ⟨hp,hyperplane_contact_nondegenerate D _ hD R hR hp.ne'⟩

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection GrayStability
open scoped ContDiff
noncomputable section

def radialForm (y : Phase) : Phase →L[ℝ] ℝ :=
  (y 2 / 2) • ContinuousLinearMap.proj 0 + (y 3 / 2) • ContinuousLinearMap.proj 1 -
    (y 0 / 2) • ContinuousLinearMap.proj 2 - (y 1 / 2) • ContinuousLinearMap.proj 3

lemma radialForm_apply (y v : Phase) : radialForm y v = phaseRadialContact y v := by
  simp [radialForm,phaseRadialContact,phaseSymplecticForm]
  ring

def radialFormLinear : Phase →L[ℝ] (Phase →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := radialForm
      map_add' := by intro u v; ext w; simp [radialForm_apply,phaseRadialContact,phaseSymplecticForm]; ring
      map_smul' := by intro a v; ext w; simp [radialForm_apply,phaseRadialContact,phaseSymplecticForm]; ring }

lemma radialForm_contDiff : ContDiff ℝ ∞ radialForm := radialFormLinear.contDiff

lemma radialForm_fderiv (y v : Phase) : fderiv ℝ radialForm y v = radialForm v := by
  exact congrArg (fun L : Phase →L[ℝ] (Phase →L[ℝ] ℝ) => L v) (radialFormLinear.hasFDerivAt.fderiv)

lemma radialForm_extDeriv (y v w : Phase) :
    extDerivOneForm radialForm y v w = -phaseSymplecticForm v w := by
  simp only [extDerivOneForm,radialForm_fderiv,radialForm_apply]
  simp [phaseRadialContact,phaseSymplecticForm]
  ring

def pullbackRadialForm (f : Phase → Phase) (y : Phase) : Phase →L[ℝ] ℝ :=
  (radialForm (f y)).comp (fderiv ℝ f y)

lemma pullbackRadialForm_contDiffAt (f : Phase → Phase) (y : Phase)
    (hf : ContDiffAt ℝ ∞ f y) : ContDiffAt ℝ ∞ (pullbackRadialForm f) y := by
  exact (radialForm_contDiff.contDiffAt.comp y hf).clm_comp (hf.fderiv_right (by simp))

lemma pullbackRadialForm_extDeriv (f : Phase → Phase) (y v w : Phase)
    (hf : ContDiffAt ℝ ∞ f y) :
    extDerivOneForm (pullbackRadialForm f) y v w =
      -phaseSymplecticForm (fderiv ℝ f y v) (fderiv ℝ f y w) := by
  have hp := ContactCalculus.exterior_pairing_pullback radialForm f y v w
    (radialForm_contDiff.differentiable (by simp) (f y)) (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  change _ = extDerivOneForm radialForm (f y) (fderiv ℝ f y v) (fderiv ℝ f y w) at hp
  rw [← radialForm_extDeriv (f y)]
  exact hp

def primitiveBlend (κ : ℝ) (f : Phase → Phase) (t : ℝ) : OneForm 4 :=
  fun y => (1-t) • (κ • radialForm y) + t • pullbackRadialForm f y

lemma primitiveBlend_extDeriv (κ : ℝ) (f : Phase → Phase) (t : ℝ) (y v w : Phase)
    (hf : ContDiffAt ℝ ∞ f y)
    (hsymp : ∀ v w, phaseSymplecticForm (fderiv ℝ f y v) (fderiv ℝ f y w) = κ * phaseSymplecticForm v w) :
    extDerivOneForm (primitiveBlend κ f t) y v w = -κ * phaseSymplecticForm v w := by
  have h0 := ((radialForm_contDiff.differentiable (by simp) y).hasFDerivAt.const_smul κ).const_smul (1-t)
  have h1 := ((pullbackRadialForm_contDiffAt f y hf).differentiableAt (by simp)).hasFDerivAt.const_smul t
  have he := (h0.add h1).fderiv
  change fderiv ℝ (primitiveBlend κ f t) y = _ at he
  simp only [extDerivOneForm,he,add_apply,smul_apply,smul_eq_mul]
  have hd0 := radialForm_extDeriv y v w
  have hd1 := pullbackRadialForm_extDeriv f y v w hf
  dsimp [extDerivOneForm] at hd0 hd1
  rw [hsymp] at hd1
  linear_combination (1-t)*κ*hd0 + t*hd1

lemma omega_hamiltonian_pairing (H : Phase → ℝ) (y v : Phase) :
    phaseSymplecticForm (hamiltonianVectorField H y) v = fderiv ℝ H y v := by
  have hbasis : ∀ i : Fin 4, coordinateVector i = Pi.single i 1 := by
    intro i; ext j; simp [coordinateVector,Pi.single_apply,eq_comm]
  have he : v = ∑ i : Fin 4, v i • Pi.single i (1 : ℝ) := by
    ext j; fin_cases j <;> simp [Fin.sum_univ_four]
  conv_rhs => rw [he,map_sum]
  simp only [map_smul,smul_eq_mul]
  simp [hamiltonianVectorField,partialDerivative,hbasis,phaseSymplecticForm,Fin.sum_univ_four]
  ring

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection GrayStability
open scoped ContDiff
noncomputable section

lemma convex_model_primitive_blend_contact (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (M : ConvexRegularizationModel μ c)
    (y : Phase) (hy : y ∈ leftEnergyComponent μ c) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let A := primitiveBlend M.symplecticScale M.toModel t
    0 < A y (hamiltonianVectorField (leviCivitaHamiltonian μ c) y) ∧
      (∃ v : Phase, fderiv ℝ (leviCivitaHamiltonian μ c) y v = 0 ∧ A y v ≠ 0) ∧
      (∀ u : Phase, fderiv ℝ (leviCivitaHamiltonian μ c) y u = 0 → A y u = 0 → u ≠ 0 →
        ∃ v : Phase, fderiv ℝ (leviCivitaHamiltonian μ c) y v = 0 ∧ A y v = 0 ∧
          extDerivOneForm A y u v ≠ 0) ∧
      (∀ u v : Phase, extDerivOneForm A y u v = -M.symplecticScale * phaseSymplecticForm u v) := by
  let R := hamiltonianVectorField (leviCivitaHamiltonian μ c) y
  have hD : fderiv ℝ (leviCivitaHamiltonian μ c) y ≠ 0 :=
    (left_energy_component_geometry μ c hμ0 hμ1 hc).2.1 y hy |>.2
  have hf : ContDiffAt ℝ ∞ M.toModel y :=
    M.toModel_smooth.contDiffAt (M.source_open.mem_nhds (M.contains_component hy))
  have h0 : 0 < (M.symplecticScale • radialForm y) R := by
    simp only [smul_apply,smul_eq_mul,radialForm_apply]
    apply mul_pos M.symplecticScale_pos
    rw [hamiltonian_radial_contact_pairing]
    exact div_pos (left_energy_component_radial_derivative_pos μ c hμ0 hμ1 hc y hy) (by norm_num)
  have hmy : M.toModel y ∈ frontier M.body := by
    rw [← M.image_frontier]
    exact ⟨y,hy,rfl⟩
  have h1 : 0 < pullbackRadialForm M.toModel y R := by
    change 0 < radialForm (M.toModel y) (fderiv ℝ M.toModel y R)
    rw [M.vectorField y hy]
    rw [map_smul,smul_eq_mul,radialForm_apply]
    exact mul_pos (M.timeScale_pos y hy) (convex_model_boundary_contact_positive M (M.toModel y) hmy)
  have hC := contact_interpolation_at_hyperplane (fderiv ℝ (leviCivitaHamiltonian μ c) y)
    (M.symplecticScale • radialForm y) (pullbackRadialForm M.toModel y) hD R
    (omega_hamiltonian_pairing (leviCivitaHamiltonian μ c) y) h0 h1 t ht
  have he : ∀ u v : Phase,
      extDerivOneForm (primitiveBlend M.symplecticScale M.toModel t) y u v =
        -M.symplecticScale * phaseSymplecticForm u v := by
    intro u v
    exact primitiveBlend_extDeriv _ _ _ _ _ _ hf (M.symplectic y (M.contains_component hy))
  refine ⟨hC.1,hC.2.1,?_,he⟩
  intro u hDu hAu hune
  obtain ⟨v,hDv,hAv,hω⟩ := hC.2.2 u hDu hAu hune
  refine ⟨v,hDv,hAv,?_⟩
  rw [he]
  exact mul_ne_zero (neg_ne_zero.mpr M.symplecticScale_pos.ne') hω

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection GrayStability Set
open scoped ContDiff Topology
noncomputable section

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


end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection GrayStability Set
open scoped ContDiff
noncomputable section

lemma primitiveBlend_contDiffAt (κ : ℝ) (f : Phase → Phase) (t : ℝ) (y : Phase)
    (hf : ContDiffAt ℝ ∞ f y) : ContDiffAt ℝ ∞ (primitiveBlend κ f t) y := by
  exact ((radialForm_contDiff.contDiffAt.const_smul κ).const_smul (1-t)).add
    ((pullbackRadialForm_contDiffAt f y hf).const_smul t)

def sourceLiftForm (κ : ℝ) (f : Phase → Phase) (a : Phase → ℝ) (t : ℝ) : OneForm 4 :=
  fun u => (primitiveBlend κ f t (a u•u)).comp (fderiv ℝ (fun x => a x•x) u)

lemma sourceLiftForm_contDiffAt (κ : ℝ) (f : Phase → Phase) (a : Phase → ℝ) (t : ℝ) (u : Phase)
    (ha : ContDiffAt ℝ ∞ a u) (hf : ContDiffAt ℝ ∞ f (a u•u)) :
    ContDiffAt ℝ ∞ (sourceLiftForm κ f a t) u := by
  have hG : ContDiffAt ℝ ∞ (fun x => a x•x) u := ha.smul contDiffAt_id
  exact ((primitiveBlend_contDiffAt κ f t _ hf).comp (f := fun x => a x•x) u hG).clm_comp (hG.fderiv_right (by simp))

lemma sourceLiftForm_extDeriv (κ : ℝ) (f : Phase → Phase) (a : Phase → ℝ) (t : ℝ) (u v w : Phase)
    (ha : ContDiffAt ℝ ∞ a u) (hf : ContDiffAt ℝ ∞ f (a u•u))
    (hsymp : ∀ v w, phaseSymplecticForm (fderiv ℝ f (a u•u) v) (fderiv ℝ f (a u•u) w) = κ * phaseSymplecticForm v w) :
    extDerivOneForm (sourceLiftForm κ f a t) u v w =
      -κ * phaseSymplecticForm (fderiv ℝ (fun x => a x•x) u v) (fderiv ℝ (fun x => a x•x) u w) := by
  have hG : ContDiffAt ℝ ∞ (fun x => a x•x) u := ha.smul contDiffAt_id
  have hp := ContactCalculus.exterior_pairing_pullback (primitiveBlend κ f t) (fun x => a x•x) u v w
    ((primitiveBlend_contDiffAt κ f t _ hf).differentiableAt (by simp))
    (hG.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  change extDerivOneForm (sourceLiftForm κ f a t) u v w =
    extDerivOneForm (primitiveBlend κ f t) (a u•u)
      (fderiv ℝ (fun x => a x•x) u v) (fderiv ℝ (fun x => a x•x) u w) at hp
  rw [hp,primitiveBlend_extDeriv κ f t (a u•u) _ _ hf hsymp]

lemma radial_lift_tangent_leftInverse (a : Phase → ℝ)
    (ha : ∀ u ∈ unitThreeSphere, ContDiffAt ℝ ∞ a u ∧ 0 < a u)
    (u v : Phase) (hu : u ∈ unitThreeSphere) (hv : phaseDot u v = 0) :
    fderiv ℝ radialNormalize (a u•u) (fderiv ℝ (fun x => a x•x) u v) = v := by
  have hG : ContDiffAt ℝ ∞ (fun x => a x•x) u := (ha u hu).1.smul contDiffAt_id
  have hN : ContDiffAt ℝ ∞ radialNormalize (a u•u) :=
    (radial_normalization_contact_identity _ (by rw [radiusSq_smul]; change zNormSq u+wNormSq u=1 at hu; rw [hu,mul_one]; exact sq_pos_of_pos (ha u hu).2)).1
  have heq : EqOn (radialNormalize ∘ fun x => a x•x) id unitThreeSphere := by
    intro z hz
    exact normalize_positive_smul hz (ha z hz).2
  have he := sphere_tangent_fderiv_eq (radialNormalize ∘ fun x => a x•x) id u v hu hv
    ((hN.differentiableAt (by simp)).comp (f := fun x => a x•x) u (hG.differentiableAt (by simp))) differentiableAt_id heq
  rw [fderiv_comp (g := radialNormalize) (f := fun x => a x•x) u (hN.differentiableAt (by simp)) (hG.differentiableAt (by simp))] at he
  simpa using he

lemma sourceLiftForm_isContact (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (M : ConvexRegularizationModel μ c) (a : Phase → ℝ)
    (ha : ∀ x : Phase, x ≠ 0 → ContDiffAt ℝ ∞ a x ∧ 0 < a x ∧ a x•x ∈ leftEnergyComponent μ c)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (u : Phase) (hu : u ∈ unitThreeSphere) :
    IsContactFormAt sphereEq (sourceLiftForm M.symplecticScale M.toModel a t) u := by
  have hau := ha u (sphere_ne_zero hu)
  have hf : ContDiffAt ℝ ∞ M.toModel (a u•u) :=
    M.toModel_smooth.contDiffAt (M.source_open.mem_nhds (M.contains_component hau.2.2))
  have hsrc := convex_model_primitive_blend_contact μ c hμ0 hμ1 hc M (a u•u) hau.2.2 t ht
  have htan := left_component_radial_lift_tangent μ c hμ0 hμ1 hc a ha u hu
  have hInv := radial_lift_tangent_leftInverse a (fun z hz => ⟨(ha z (sphere_ne_zero hz)).1,(ha z (sphere_ne_zero hz)).2.1⟩) u
  constructor
  · obtain ⟨w,hwD,hwA⟩ := hsrc.2.1
    obtain ⟨v,hv,hPv⟩ := htan.2 w hwD
    refine ⟨v,mem_tangentSpace_sphereEq.mpr hv,?_⟩
    change (primitiveBlend M.symplecticScale M.toModel t (a u•u))
      (fderiv ℝ (fun x => a x•x) u v) ≠ 0
    rw [hPv]
    exact hwA
  · intro v hv hvne
    have hvt : phaseDot u v = 0 := mem_tangentSpace_sphereEq.mp hv.1
    have hPvne : fderiv ℝ (fun x => a x•x) u v ≠ 0 := by
      intro hz
      have hi := hInv v hu hvt
      rw [hz,map_zero] at hi
      exact hvne hi.symm
    have hPvA : (primitiveBlend M.symplecticScale M.toModel t (a u•u))
        (fderiv ℝ (fun x => a x•x) u v) = 0 := hv.2
    obtain ⟨w,hwD,hwA,hwω⟩ := hsrc.2.2.1 _ (htan.1 v) hPvA hPvne
    obtain ⟨z,hzt,hPz⟩ := htan.2 w hwD
    refine ⟨z,⟨mem_tangentSpace_sphereEq.mpr hzt,?_⟩,?_⟩
    · change (primitiveBlend M.symplecticScale M.toModel t (a u•u))
        (fderiv ℝ (fun x => a x•x) u z) = 0
      rw [hPz]
      exact hwA
    · rw [sourceLiftForm_extDeriv M.symplecticScale M.toModel a t u v z hau.1 hf
        (M.symplectic _ (M.contains_component hau.2.2)),hPz]
      have hx := hsrc.2.2.2 (fderiv ℝ (fun x => a x•x) u v) w
      rw [hx] at hwω
      exact hwω

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection GrayStability Set
open scoped ContDiff
noncomputable section

def oddForm (α : OneForm 4) : OneForm 4 := fun y => (1/2:ℝ) • (α y-α (-y))

lemma oddForm_odd (α : OneForm 4) (y : Phase) : oddForm α (-y) = -oddForm α y := by
  ext v
  simp [oddForm]
  ring

lemma oddForm_contDiff {α : OneForm 4} (hα : ContDiff ℝ ∞ α) : ContDiff ℝ ∞ (oddForm α) := by
  exact (hα.sub (hα.comp contDiff_id.neg)).const_smul (1/2:ℝ)

lemma smooth_odd_sphere_form_extension (α : OneForm 4)
    (hα : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ α y)
    (hodd : ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 → α (-y) v = -α y v) :
    ∃ β : OneForm 4, ContDiff ℝ ∞ β ∧ (∀ y, β (-y) = -β y) ∧
      (∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 → β y v = α y v) ∧
      (∀ y ∈ unitThreeSphere, ∀ v w : Phase, phaseDot y v = 0 → phaseDot y w = 0 →
        extDerivOneForm β y v w = extDerivOneForm α y v w) := by
  obtain ⟨A,hA,hAeq,hAfd⟩ := sphere_smooth_extension α hα
  let β := oddForm A
  have hβ := oddForm_contDiff hA
  have hβeq : ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 → β y v = α y v := by
    intro y hy v hv
    change ((1/2:ℝ) • (A y-A (-y))) v = α y v
    rw [hAeq hy,hAeq (sphere_neg_mem hy)]
    simp only [smul_apply,sub_apply,smul_eq_mul,hodd y hy v hv]
    ring
  refine ⟨β,hβ,oddForm_odd A,hβeq,?_⟩
  intro y hy v w hv hw
  have hreg := sphereEq_regular
  have hpull : ∀ z ∈ levelSet sphereEq, ∀ v ∈ tangentSpace sphereEq z,
      β (id z) (fderiv ℝ id z v) = A z v := by
    intro z hz v hv
    simp only [id_eq,fderiv_id,ContinuousLinearMap.id_apply]
    rw [hβeq z (mem_levelSet_sphereEq.mp hz) v (mem_tangentSpace_sphereEq.mp hv),hAeq (mem_levelSet_sphereEq.mp hz)]
  have he := ContactCalculus.extDeriv_naturality_of_tangent_pullback_on_regular_level
    sphereEq hreg.1 hreg.2.2 β A hβ hA id contDiff_id hpull y (mem_levelSet_sphereEq.mpr hy)
    v w (mem_tangentSpace_sphereEq.mpr hv) (mem_tangentSpace_sphereEq.mpr hw)
  simp only [id_eq,fderiv_id,ContinuousLinearMap.id_apply] at he
  rw [he]
  dsimp [extDerivOneForm]
  rw [hAfd y hy v hv,hAfd y hy w hw]

lemma pullbackRadialForm_odd_tangent (f : Phase → Phase)
    (hf : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ f y)
    (hodd : ∀ y ∈ unitThreeSphere, f (-y) = -f y)
    (y v : Phase) (hy : y ∈ unitThreeSphere) (hv : phaseDot y v = 0) :
    pullbackRadialForm f (-y) v = -pullbackRadialForm f y v := by
  change radialForm (f (-y)) (fderiv ℝ f (-y) v) = -radialForm (f y) (fderiv ℝ f y v)
  rw [hodd y hy,sphere_odd_tangent_derivative f hf hodd y v hy hv]
  simp [radialForm_apply,phaseRadialContact,phaseSymplecticForm]
  ring

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection GrayStability Set
open scoped ContDiff
noncomputable section

def formBlend (α₀ α₁ : OneForm 4) (t : ℝ) : OneForm 4 := fun y => (1-t)•α₀ y+t•α₁ y

lemma formBlend_extDeriv (α₀ α₁ : OneForm 4) (t : ℝ) (y v w : Phase)
    (h₀ : DifferentiableAt ℝ α₀ y) (h₁ : DifferentiableAt ℝ α₁ y) :
    extDerivOneForm (formBlend α₀ α₁ t) y v w =
      (1-t)*extDerivOneForm α₀ y v w+t*extDerivOneForm α₁ y v w := by
  have hd := ((h₀.hasFDerivAt.const_smul (1-t)).add (h₁.hasFDerivAt.const_smul t)).fderiv
  change fderiv ℝ (formBlend α₀ α₁ t) y = _ at hd
  simp only [extDerivOneForm,hd,add_apply,smul_apply,smul_eq_mul]
  ring

lemma contact_tangent_congr (α β : OneForm 4) (y : Phase)
    (heq : ∀ v : Phase, phaseDot y v = 0 → β y v = α y v)
    (hext : ∀ v w : Phase, phaseDot y v = 0 → phaseDot y w = 0 →
      extDerivOneForm β y v w = extDerivOneForm α y v w)
    (hc : IsContactFormAt sphereEq α y) : IsContactFormAt sphereEq β y := by
  constructor
  · obtain ⟨v,hvt,hva⟩ := hc.1
    exact ⟨v,hvt,by rw [heq v (mem_tangentSpace_sphereEq.mp hvt)]; exact hva⟩
  · intro u hu hune
    have hut := mem_tangentSpace_sphereEq.mp hu.1
    have hua : α y u = 0 := by rw [← heq u hut]; exact hu.2
    obtain ⟨v,hv,hva⟩ := hc.2 u ⟨hu.1,hua⟩ hune
    refine ⟨v,⟨hv.1,?_⟩,?_⟩
    · rw [heq v (mem_tangentSpace_sphereEq.mp hv.1)]
      exact hv.2
    · rw [hext u v hut (mem_tangentSpace_sphereEq.mp hv.1)]
      exact hva

lemma global_odd_contact_interpolation (δ₀ δ₁ : OneForm 4)
    (h₀ : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ δ₀ y)
    (h₁ : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ δ₁ y)
    (ho₀ : ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 → δ₀ (-y) v = -δ₀ y v)
    (ho₁ : ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 → δ₁ (-y) v = -δ₁ y v)
    (hc : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, IsContactFormAt sphereEq (formBlend δ₀ δ₁ t) y) :
    ∃ α : ℝ → OneForm 4, IsContactFamilyOn sphereEq α ∧
      (∀ t y, α t (-y) = -α t y) ∧
      ∀ t y, y ∈ unitThreeSphere → ∀ v : Phase, phaseDot y v = 0 → α t y v = formBlend δ₀ δ₁ t y v := by
  obtain ⟨β₀,hβ₀,hoβ₀,hval₀,hext₀⟩ := smooth_odd_sphere_form_extension δ₀ h₀ ho₀
  obtain ⟨β₁,hβ₁,hoβ₁,hval₁,hext₁⟩ := smooth_odd_sphere_form_extension δ₁ h₁ ho₁
  let α : ℝ → OneForm 4 := formBlend β₀ β₁
  have hα : ContDiff ℝ ∞ (fun p : ℝ × Phase => α p.1 p.2) :=
    (((contDiff_const.sub contDiff_fst).smul (hβ₀.comp contDiff_snd)).add
      (contDiff_fst.smul (hβ₁.comp contDiff_snd)))
  have hval : ∀ t y, y ∈ unitThreeSphere → ∀ v : Phase, phaseDot y v = 0 → α t y v = formBlend δ₀ δ₁ t y v := by
    intro t y hy v hv
    simp only [α,formBlend,add_apply,smul_apply,smul_eq_mul,hval₀ y hy v hv,hval₁ y hy v hv]
  refine ⟨α,⟨hα,?_⟩,?_,hval⟩
  · intro t ht y hy
    have hyS := mem_levelSet_sphereEq.mp hy
    apply contact_tangent_congr (formBlend δ₀ δ₁ t) (α t) y (hval t y hyS)
    · intro v w hv hw
      rw [formBlend_extDeriv β₀ β₁ t y v w (hβ₀.differentiable (by simp) y) (hβ₁.differentiable (by simp) y),
        formBlend_extDeriv δ₀ δ₁ t y v w ((h₀ y hyS).differentiableAt (by simp)) ((h₁ y hyS).differentiableAt (by simp)),
        hext₀ y hyS v w hv hw,hext₁ y hyS v w hv hw]
    · exact hc t ht y hyS
  · intro t y
    ext v
    simp [α,formBlend,hoβ₀ y,hoβ₁ y]
    ring

lemma sourceLiftForm_blend (κ : ℝ) (f : Phase → Phase) (a : Phase → ℝ) (t : ℝ) :
    sourceLiftForm κ f a t = formBlend (sourceLiftForm κ f a 0) (sourceLiftForm κ f a 1) t := by
  ext y v
  simp [sourceLiftForm,formBlend,primitiveBlend]

lemma sourceLiftForm_zero (κ : ℝ) (f : Phase → Phase) (a : Phase → ℝ) :
    sourceLiftForm κ f a 0 = fun y => κ • pullbackRadialForm (fun x => a x•x) y := by
  ext y v
  simp [sourceLiftForm,primitiveBlend,pullbackRadialForm]

lemma sourceLiftForm_one_apply (κ : ℝ) (f : Phase → Phase) (a : Phase → ℝ) (u v : Phase)
    (ha : ContDiffAt ℝ ∞ a u) (hf : ContDiffAt ℝ ∞ f (a u•u)) :
    sourceLiftForm κ f a 1 u v = pullbackRadialForm (f ∘ fun x => a x•x) u v := by
  have hG : ContDiffAt ℝ ∞ (fun x => a x•x) u := ha.smul contDiffAt_id
  simp only [sourceLiftForm,primitiveBlend,sub_self,zero_smul,one_smul,zero_add,pullbackRadialForm,
    ContinuousLinearMap.comp_apply]
  rw [fderiv_comp (g := f) (f := fun x => a x•x) u (hf.differentiableAt (by simp)) (hG.differentiableAt (by simp))]
  rfl

lemma convex_model_global_contact_family (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (M : ConvexRegularizationModel μ c) (a : Phase → ℝ)
    (ha : ∀ x : Phase, x ≠ 0 → ContDiffAt ℝ ∞ a x ∧ 0 < a x ∧ a x•x ∈ leftEnergyComponent μ c)
    (haeven : ∀ u ∈ unitThreeSphere, a (-u) = a u) :
    ∃ α : ℝ → OneForm 4, IsContactFamilyOn sphereEq α ∧ (∀ t y, α t (-y) = -α t y) ∧
      ∀ t y, y ∈ unitThreeSphere → ∀ v : Phase, phaseDot y v = 0 →
        α t y v = sourceLiftForm M.symplecticScale M.toModel a t y v := by
  let G : Phase → Phase := fun x => a x•x
  have hG : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ G y := fun y hy => (ha y (sphere_ne_zero hy)).1.smul contDiffAt_id
  have hGo : ∀ y ∈ unitThreeSphere, G (-y) = -G y := by
    intro y hy
    dsimp [G]
    rw [haeven y hy,smul_neg]
  have hF : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ M.toModel (G y) := by
    intro y hy
    exact M.toModel_smooth.contDiffAt (M.source_open.mem_nhds (M.contains_component (ha y (sphere_ne_zero hy)).2.2))
  have hFG : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ (M.toModel ∘ G) y := by
    intro y hy
    exact (hF y hy).comp (f := G) y (hG y hy)
  have hFGo : ∀ y ∈ unitThreeSphere, (M.toModel ∘ G) (-y) = -(M.toModel ∘ G) y := by
    intro y hy
    change M.toModel (G (-y)) = -M.toModel (G y)
    rw [hGo y hy]
    exact M.antipodal _ (ha y (sphere_ne_zero hy)).2.2
  have hδ : ∀ t y, y ∈ unitThreeSphere → ContDiffAt ℝ ∞ (sourceLiftForm M.symplecticScale M.toModel a t) y := by
    intro t y hy
    exact sourceLiftForm_contDiffAt _ _ _ _ _ (ha y (sphere_ne_zero hy)).1 (hF y hy)
  have ho₀ : ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      sourceLiftForm M.symplecticScale M.toModel a 0 (-y) v = -sourceLiftForm M.symplecticScale M.toModel a 0 y v := by
    intro y hy v hv
    rw [sourceLiftForm_zero]
    simp only [smul_apply,smul_eq_mul]
    rw [pullbackRadialForm_odd_tangent G hG hGo y v hy hv]
    ring
  have ho₁ : ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      sourceLiftForm M.symplecticScale M.toModel a 1 (-y) v = -sourceLiftForm M.symplecticScale M.toModel a 1 y v := by
    intro y hy v hv
    rw [sourceLiftForm_one_apply _ _ _ _ _ (ha (-y) (sphere_ne_zero (sphere_neg_mem hy))).1 (hF (-y) (sphere_neg_mem hy)),
      sourceLiftForm_one_apply _ _ _ _ _ (ha y (sphere_ne_zero hy)).1 (hF y hy)]
    exact pullbackRadialForm_odd_tangent (M.toModel ∘ G) hFG hFGo y v hy hv
  obtain ⟨α,hα,hoα,hval⟩ := global_odd_contact_interpolation
    (sourceLiftForm M.symplecticScale M.toModel a 0) (sourceLiftForm M.symplecticScale M.toModel a 1)
    (hδ 0) (hδ 1) ho₀ ho₁ (by
      intro t ht y hy
      rw [← sourceLiftForm_blend]
      exact sourceLiftForm_isContact μ c hμ0 hμ1 hc M a ha t ht y hy)
  refine ⟨α,hα,hoα,?_⟩
  intro t y hy v hv
  rw [hval t y hy v hv,← sourceLiftForm_blend]

end
end BirkhoffGlobalSection.HopfTransport



open Set Function
open scoped ContDiff
namespace SmoothJetExtension
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A smooth finite-dimensional immersion has a smooth local left inverse.
The inverse-function theorem is applied after a fixed linear left inverse of
its derivative; no global tubular-neighborhood theorem is assumed. -/
lemma exists_smooth_local_leftInverse (f : E → F) (hf : ContDiff ℝ ∞ f)
    (a : E) (hinj : Injective (fderiv ℝ f a))
    (W : Set E) (hW : IsOpen W) (haW : a ∈ W) :
    ∃ (r : F → E) (U : Set E) (V : Set F),
      IsOpen U ∧ a ∈ U ∧ U ⊆ W ∧ IsOpen V ∧ f a ∈ V ∧ ContDiffOn ℝ ∞ r V ∧
      MapsTo r V U ∧
      ∀ x ∈ U, f x ∈ V ∧ r (f x) = x := by
  classical
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj
  let g : E → E := L ∘ f
  have hg : ContDiff ℝ ∞ g := L.contDiff.comp hf
  have hD : fderiv ℝ g a = ContinuousLinearMap.id ℝ E := by
    have hd := L.hasFDerivAt.comp a (hf.differentiable (by simp) a).hasFDerivAt
    rw [hd.fderiv]
    ext v
    exact hL v
  have hd0 : HasFDerivAt g ((ContinuousLinearEquiv.refl ℝ E) : E →L[ℝ] E) a := by
    simpa only [ContinuousLinearEquiv.coe_refl, hD] using (hg.differentiable (by simp) a).hasFDerivAt
  let e₀ := hg.contDiffAt.toOpenPartialHomeomorph g hd0 (by simp)
  have he₀ : (e₀ : E → E) = g := hg.contDiffAt.toOpenPartialHomeomorph_coe hd0 (by simp)
  let N : Set E := {x | IsUnit (fderiv ℝ g x)} ∩ W
  have hDc : Continuous (fderiv ℝ g) := (hg.fderiv_right (m := ∞) (by simp)).continuous
  have hNo : IsOpen N := (Units.isOpen.preimage hDc).inter hW
  have haN : a ∈ N := by
    refine ⟨?_, haW⟩
    change IsUnit (fderiv ℝ g a)
    rw [hD]
    exact isUnit_one
  let e := e₀.restrOpen N hNo
  have he : (e : E → E) = g := by simpa only [e, OpenPartialHomeomorph.coe_restrOpen] using he₀
  have hae : a ∈ e.source := ⟨hg.contDiffAt.mem_toOpenPartialHomeomorph_source hd0 (by simp), haN⟩
  let V : Set F := L ⁻¹' e.target
  let r : F → E := e.symm ∘ L
  refine ⟨r, e.source, V, e.open_source, hae, (fun x hx => hx.2.2),
    e.open_target.preimage L.continuous, ?_, ?_, (fun q hq => e.map_target hq), ?_⟩
  · change L (f a) ∈ e.target
    change g a ∈ e.target
    rw [← he]
    exact e.map_source hae
  · intro q hq
    have hxe : e.symm (L q) ∈ e.source := e.map_target hq
    have hxN : e.symm (L q) ∈ N := hxe.2
    have hj : Bijective (fderiv ℝ g (e.symm (L q))) :=
      ContinuousLinearMap.isUnit_iff_bijective.mp hxN.1
    let A : E ≃L[ℝ] E :=
      (LinearEquiv.ofBijective (fderiv ℝ g (e.symm (L q))).toLinearMap hj).toContinuousLinearEquiv
    have hA : (A : E →L[ℝ] E) = fderiv ℝ g (e.symm (L q)) := by ext v; rfl
    have hgd : HasFDerivAt (e : E → E) (A : E →L[ℝ] E) (e.symm (L q)) := by
      rw [he, hA]
      exact (hg.differentiable (by simp) _).hasFDerivAt
    have hgc : ContDiffAt ℝ ∞ (e : E → E) (e.symm (L q)) := by rw [he]; exact hg.contDiffAt
    exact ((e.contDiffAt_symm hq hgd hgc).comp q L.contDiff.contDiffAt).contDiffWithinAt
  · intro x hx
    have hfx : L (f x) ∈ e.target := by
      change g x ∈ e.target
      rw [← he]
      exact e.map_source hx
    refine ⟨hfx, ?_⟩
    change e.symm (g x) = x
    rw [← he]
    exact e.left_inv hx

end SmoothJetExtension

namespace BirkhoffGlobalSection.HopfTransport
open Set Function Filter
open scoped ContDiff Topology
noncomputable section

/-- A periodic immersion with the translation symmetry of a flow has a local
smooth time coordinate on its trace, even if the supplied period is not prime. -/
lemma periodic_trace_local_inverse {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (q : ℝ → E) (hq : ContDiff ℝ ∞ q) (P : ℝ) (hP : 0 < P)
    (hperiod : Periodic q P)
    (hshift : ∀ a b, q a = q b → ∀ s, q (a+s) = q (b+s))
    (a : ℝ) (hinj : Injective (fderiv ℝ q a)) :
    ∃ r : E → ℝ, ContDiffAt ℝ ∞ r (q a) ∧ r (q a) = a ∧
      ∀ᶠ z in 𝓝 (q a), z ∈ range q → q (r z) = z := by
  obtain ⟨r,U,V,hU,haU,_,hV,haV,hr,_,hleft⟩ :=
    SmoothJetExtension.exists_smooth_local_leftInverse q hq a hinj univ isOpen_univ (mem_univ a)
  let O : Set ℝ := ⋃ b : {b : ℝ // q b = q a}, (fun s : ℝ => s-b.1+a) ⁻¹' U
  have hO : IsOpen O := isOpen_iUnion fun b => hU.preimage (by fun_prop)
  have hret : ∀ b, q b = q a → b ∈ O := by
    intro b hb
    exact mem_iUnion.mpr ⟨⟨b,hb⟩,by simpa using haU⟩
  have hpatch : ∀ s ∈ O, ∃ t ∈ U, q t = q s := by
    intro s hs
    obtain ⟨b,hb⟩ := mem_iUnion.mp hs
    refine ⟨s-b.1+a,hb,?_⟩
    have he := hshift a b.1 b.2.symm (s-b.1)
    convert he using 1 <;> congr 1 <;> ring
  let C : Set ℝ := Icc 0 P \ O
  have hC : IsCompact C := isCompact_Icc.diff hO
  have hqC : IsCompact (q '' C) := hC.image hq.continuous
  have hnot : q a ∉ q '' C := by
    rintro ⟨b,hb,he⟩
    exact hb.2 (hret b he)
  refine ⟨r,hr.contDiffAt (hV.mem_nhds haV),(hleft a haU).2,?_⟩
  filter_upwards [hV.mem_nhds haV,hqC.isClosed.isOpen_compl.mem_nhds hnot] with z hzV hzC
  rintro ⟨s,rfl⟩
  obtain ⟨b,hb,he⟩ := hperiod.exists_mem_Ico₀ hP s
  have hbO : b ∈ O := by
    by_contra hn
    apply hzC
    exact ⟨b,⟨⟨hb.1,hb.2.le⟩,hn⟩,he.symm⟩
  obtain ⟨t,ht,hqt⟩ := hpatch b hbO
  rw [he,← hqt,(hleft t ht).2]

lemma tangent_of_periodic_trace {E D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (q : ℝ → E) (hq : ContDiff ℝ ∞ q) (P : ℝ) (hP : 0 < P)
    (hperiod : Periodic q P)
    (hshift : ∀ a b, q a = q b → ∀ s, q (a+s) = q (b+s))
    (a : ℝ) (hinj : Injective (fderiv ℝ q a))
    (c : D → E) (x v : D) (hc : DifferentiableAt ℝ c x)
    (hca : c x = q a) (him : ∀ᶠ z in 𝓝 x, c z ∈ range q) :
    ∃ b : ℝ, fderiv ℝ c x v = b • deriv q a := by
  obtain ⟨r,hr,hra,hlocal⟩ := periodic_trace_local_inverse q hq P hP hperiod hshift a hinj
  have hr' : DifferentiableAt ℝ r (c x) := by
    rw [hca]
    exact hr.differentiableAt (by simp)
  have hrc : r (c x) = a := by rw [hca,hra]
  have hq' : HasFDerivAt q (fderiv ℝ q a) (r (c x)) := by
    rw [hrc]
    exact (hq.differentiable (by simp) a).hasFDerivAt
  have hd' := hq'.comp x (hr'.hasFDerivAt.comp x hc.hasFDerivAt)
  have he : (fun z => q (r (c z))) =ᶠ[𝓝 x] c := by
    have hct : Tendsto c (𝓝 x) (𝓝 (q a)) := hca ▸ hc.continuousAt
    filter_upwards [hct.eventually hlocal,him] with z hz himz
    exact hz himz
  have hder := (hd'.congr_of_eventuallyEq he.symm).fderiv
  refine ⟨fderiv ℝ r (c x) (fderiv ℝ c x v),?_⟩
  calc
    fderiv ℝ c x v = fderiv ℝ q a (fderiv ℝ r (c x) (fderiv ℝ c x v)) :=
      congrArg (fun L : D →L[ℝ] E => L v) hder
    _ = _ := by
      rw [(hq.differentiable (by simp) a).hasDerivAt.hasFDerivAt.fderiv]
      rfl

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma smooth_of_ode_along_smooth_field {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℝ → E) (X : E → E) (hder : ∀ t, HasDerivAt q (X (q t)) t)
    (hX : ∀ t, ContDiffAt ℝ ∞ X (q t)) : ContDiff ℝ ∞ q := by
  rw [contDiff_infty]
  intro n
  induction n with
  | zero => exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (hder t).continuousAt)
  | succ n ih =>
    have hd : deriv q = X ∘ q := funext fun t => (hder t).deriv
    have hh := contDiff_succ_iff_deriv (𝕜 := ℝ) (f := q) (n := (n : ℕ∞ω))
    push_cast
    apply hh.mpr
    refine ⟨fun t => (hder t).differentiableAt,by simp,?_⟩
    rw [hd]
    apply contDiff_iff_contDiffAt.mpr
    intro t
    exact ((hX t).of_le (by exact_mod_cast le_top)).comp t ih.contDiffAt

lemma hamiltonian_field_contDiffAt (H : Phase → ℝ) (y : Phase)
    (hH : ContDiffAt ℝ ∞ H y) : ContDiffAt ℝ ∞ (hamiltonianVectorField H) y := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ H) y := hH.fderiv_right (by simp)
  have hp : ∀ i, ContDiffAt ℝ ∞ (fun z => partialDerivative H z i) y :=
    fun i => hd.clm_apply contDiffAt_const
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hp 2
  · exact hp 3
  · exact (hp 0).neg
  · exact (hp 1).neg

lemma lc_flow_hasDerivAt (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (p : LeftEnergyState μ c) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ((φ s p : LeftEnergyState μ c) : Phase))
      (hamiltonianVectorField (leviCivitaHamiltonian μ c) (φ t p : Phase)) t := by
  have hh : HasDerivAt (fun s : ℝ => ((φ s (φ t p) : LeftEnergyState μ c) : Phase))
      (hamiltonianVectorField (leviCivitaHamiltonian μ c) (φ t p : Phase)) (t-t) := by
    simpa using hφ (φ t p)
  convert! hh.scomp (h := fun s : ℝ => s-t) t ((hasDerivAt_id t).sub_const t) using 1
  · funext s
    simp [Function.comp_def,← φ.map_add]
  · simp

lemma lc_flow_contDiff (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (p : LeftEnergyState μ c) :
    ContDiff ℝ ∞ (fun s : ℝ => ((φ s p : LeftEnergyState μ c) : Phase)) := by
  apply smooth_of_ode_along_smooth_field _ _ (lc_flow_hasDerivAt μ c φ hφ p)
  intro t
  exact hamiltonian_field_contDiffAt _ _ ((left_energy_component_geometry μ c hμ0 hμ1 hc).2.1 _ (φ t p).property).1

lemma lc_orbit_periodic {μ c : ℝ} {φ : Flow ℝ (LeftEnergyState μ c)} (γ : PeriodicOrbit φ) :
    Periodic (fun t : ℝ => ((φ t γ.point : LeftEnergyState μ c) : Phase)) γ.period := by
  intro t
  simp only [φ.map_add,γ.closed]

lemma lc_orbit_shift {μ c : ℝ} {φ : Flow ℝ (LeftEnergyState μ c)} (γ : PeriodicOrbit φ)
    (a b : ℝ) (hab : (φ a γ.point : Phase) = (φ b γ.point : Phase)) (s : ℝ) :
    (φ (a+s) γ.point : Phase) = (φ (b+s) γ.point : Phase) := by
  have hh : φ a γ.point = φ b γ.point := Subtype.ext hab
  rw [add_comm a s,add_comm b s,φ.map_add,φ.map_add,hh]

/-- Any differentiable local parametrization contained in this periodic trace
has a tangent parallel to the Hamiltonian field. Positivity selects its sign. -/
lemma orbit_tangent_positive_primitive_blend {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (γ : PeriodicOrbit φ) (k : D → Phase) (x v : D) (hk : DifferentiableAt ℝ k x)
    (hkx : k x ∈ orbitSet γ) (him : ∀ᶠ z in 𝓝 x, k z ∈ orbitSet γ)
    (hpos : 0 < phaseRadialContact (k x) (fderiv ℝ k x v)) :
    ∀ t ∈ Icc (0:ℝ) 1, 0 < primitiveBlend M.symplecticScale M.toModel t (k x) (fderiv ℝ k x v) := by
  obtain ⟨a,ha⟩ := hkx
  let q : ℝ → Phase := fun t => (φ t γ.point : Phase)
  let R := hamiltonianVectorField (leviCivitaHamiltonian μ c) (k x)
  have hy : k x ∈ leftEnergyComponent μ c := by rw [← ha]; exact (φ a γ.point).property
  have hRpos : 0 < phaseRadialContact (k x) R := by
    rw [hamiltonian_radial_contact_pairing]
    exact div_pos (left_energy_component_radial_derivative_pos μ c hμ0 hμ1 hc _ hy) (by norm_num)
  have hRne : R ≠ 0 := by
    intro he
    have hh : phaseRadialContact (k x) R = 0 := by simp [he,phaseRadialContact,phaseSymplecticForm]
    linarith
  have hq := lc_flow_contDiff μ c hμ0 hμ1 hc φ hφ γ.point
  have hqa : HasDerivAt q R a := by
    simpa only [q,ha,R] using lc_flow_hasDerivAt μ c φ hφ γ.point a
  have hinj : Injective (fderiv ℝ q a) := by
    rw [hqa.hasFDerivAt.fderiv]
    exact smul_left_injective ℝ hRne
  obtain ⟨b,hb⟩ := tangent_of_periodic_trace q hq γ.period γ.period_pos (lc_orbit_periodic γ)
    (lc_orbit_shift γ) a hinj k x v hk ha.symm him
  rw [hqa.deriv] at hb
  have hbpos : 0 < b := by
    rw [hb] at hpos
    have he : phaseRadialContact (k x) (b • R) = b * phaseRadialContact (k x) R := by
      simpa only [radialForm_apply,smul_eq_mul] using (radialForm (k x)).map_smul b R
    rw [he] at hpos
    exact (mul_pos_iff_of_pos_right hRpos).mp hpos
  intro t ht
  rw [hb,map_smul,smul_eq_mul]
  exact mul_pos hbpos (convex_model_primitive_blend_contact μ c hμ0 hμ1 hc M (k x) hy t ht).1

end
end BirkhoffGlobalSection.HopfTransport



set_option backward.isDefEq.respectTransparency false

namespace BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection Set
open scoped ContDiff
noncomputable section

lemma deriv_eq_of_eqOn_Icc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℝ → F} {a b : F} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hf : HasDerivAt f a t) (hg : HasDerivAt g b t) (heq : EqOn f g (Icc 0 1)) : a = b := by
  apply (uniqueDiffOn_Icc_zero_one t ht).eq_deriv (Icc (0 : ℝ) 1)
    (hf.hasDerivWithinAt.congr heq.symm (heq ht).symm) hg.hasDerivWithinAt

noncomputable def circleCurve (u : Plane) (s : ℝ) : Plane :=
  Real.cos s • u + Real.sin s • circleTangent u

lemma circleCurve_zero (u : Plane) : circleCurve u 0 = u := by simp [circleCurve]

lemma circleCurve_mem (u : Plane) (hu : u ∈ unitCircle) (s : ℝ) : circleCurve u s ∈ unitCircle := by
  have he : planeNormSq (circleCurve u s) =
      (Real.cos s ^ 2 + Real.sin s ^ 2) * planeNormSq u := by
    simp only [circleCurve, circleTangent, planeNormSq, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  change planeNormSq (circleCurve u s) = 1
  rw [he, Real.cos_sq_add_sin_sq, one_mul]
  exact hu

lemma circleCurve_hasDerivAt (u : Plane) : HasDerivAt (circleCurve u) (circleTangent u) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  have h := ((Real.hasDerivAt_cos 0).mul_const (u i)).add
    ((Real.hasDerivAt_sin 0).mul_const (circleTangent u i))
  change HasDerivAt (fun s => Real.cos s * u i + Real.sin s * circleTangent u i)
    (circleTangent u i) 0
  convert! h using 1 <;>
    simp only [Real.sin_zero, Real.cos_zero, neg_zero, zero_mul, one_mul, zero_add]


lemma circleCurve_hasDerivAt_all (u : Plane) (s : ℝ) :
    HasDerivAt (circleCurve u) (circleTangent (circleCurve u s)) s := by
  apply hasDerivAt_pi.mpr
  intro i
  have h := ((Real.hasDerivAt_cos s).mul_const (u i)).add
    ((Real.hasDerivAt_sin s).mul_const (circleTangent u i))
  change HasDerivAt (fun r => Real.cos r * u i + Real.sin r * circleTangent u i)
    (circleTangent (circleCurve u s) i) s
  convert! h using 1
  fin_cases i <;> simp [circleTangent, circleCurve] <;> ring


end
end BirkhoffGlobalSection.ContactGenerator

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma radial_lift_contact (a : Phase → ℝ) (y v : Phase)
    (ha : DifferentiableAt ℝ a y) :
    phaseRadialContact (a y • y) (fderiv ℝ (fun x : Phase => a x • x) y v) =
      a y ^ 2 * phaseRadialContact y v := by
  have hd := ha.hasFDerivAt.smul (hasFDerivAt_id y)
  change HasFDerivAt (fun x : Phase => a x • x) _ y at hd
  rw [hd.fderiv]
  simp [phaseRadialContact,phaseSymplecticForm]
  ring

lemma orbit_knot_positive_primitive_blend (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (γ : PeriodicOrbit φ) (k : Plane → Phase)
    (hk : ∀ u ∈ unitCircle, ContDiffAt ℝ ∞ k u)
    (him : MapsTo k unitCircle (orbitSet γ))
    (hpos : ∀ u ∈ unitCircle, 0 < phaseRadialContact (k u) (fderiv ℝ k u (circleTangent u))) :
    ∀ t ∈ Icc (0:ℝ) 1, ∀ u ∈ unitCircle,
      0 < primitiveBlend M.symplecticScale M.toModel t (k u) (fderiv ℝ k u (circleTangent u)) := by
  intro t ht u hu
  let C : ℝ → Phase := fun s => k (ContactGenerator.circleCurve u s)
  have hku : DifferentiableAt ℝ k (ContactGenerator.circleCurve u 0) := by
    rw [ContactGenerator.circleCurve_zero]
    exact (hk u hu).differentiableAt (by simp)
  have hC : HasDerivAt C (fderiv ℝ k u (circleTangent u)) 0 := by
    convert! hku.hasFDerivAt.comp_hasDerivAt 0 (ContactGenerator.circleCurve_hasDerivAt u) using 1
    simp only [ContactGenerator.circleCurve_zero]
  have hD : fderiv ℝ C 0 (1:ℝ) = fderiv ℝ k u (circleTangent u) := by
    rw [hC.hasFDerivAt.fderiv]
    simp
  have hC0 : C 0 = k u := by simp [C,ContactGenerator.circleCurve_zero]
  have hposC : 0 < phaseRadialContact (C 0) (fderiv ℝ C 0 (1:ℝ)) := by
    rw [hC0,hD]
    exact hpos u hu
  have hh := orbit_tangent_positive_primitive_blend μ c hμ0 hμ1 hc M φ hφ γ C 0 1 hC.differentiableAt
    (hC0.symm ▸ him hu) (Filter.Eventually.of_forall fun s => him (ContactGenerator.circleCurve_mem u hu s)) hposC t ht
  rwa [hC0,hD] at hh

/-- The fixed normalized orbit stays positive for the entire pulled-back
contact family. This uses the actual orbit and its supplied transverse knot. -/
lemma normalized_orbit_positive_sourceLiftForm (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (γ : PeriodicOrbit φ) (a : Phase → ℝ)
    (ha : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ a y ∧ 0 < a y)
    (hainv : ∀ y ∈ leftEnergyComponent μ c, a (radialNormalize y) • radialNormalize y = y)
    (k : Plane → Phase) (hk : ∀ u ∈ unitCircle, ContDiffAt ℝ ∞ k u)
    (hsphere : MapsTo k unitCircle unitThreeSphere)
    (himage : MapsTo k unitCircle (radialNormalize '' orbitSet γ))
    (hpos : ∀ u ∈ unitCircle, 0 < phaseRadialContact (k u) (fderiv ℝ k u (circleTangent u))) :
    ∀ t ∈ Icc (0:ℝ) 1, ∀ u ∈ unitCircle,
      0 < sourceLiftForm M.symplecticScale M.toModel a t (k u) (fderiv ℝ k u (circleTangent u)) := by
  let G : Phase → Phase := fun y => a y • y
  let K : Plane → Phase := G ∘ k
  have hG : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ G y :=
    fun y hy => (ha y hy).1.smul contDiffAt_id
  have hK : ∀ u ∈ unitCircle, ContDiffAt ℝ ∞ K u := by
    intro u hu
    exact (hG (k u) (hsphere hu)).comp (f := k) u (hk u hu)
  have hKim : MapsTo K unitCircle (orbitSet γ) := by
    intro u hu
    obtain ⟨y,hy,he⟩ := himage hu
    have hycomp : y ∈ leftEnergyComponent μ c := by
      obtain ⟨s,rfl⟩ := hy
      exact (φ s γ.point).property
    have hKeq : K u = y := by
      change a (k u) • k u = y
      rw [← he,hainv y hycomp]
    rwa [hKeq]
  have hKD : ∀ u ∈ unitCircle, ∀ v : Plane,
      fderiv ℝ K u v = fderiv ℝ G (k u) (fderiv ℝ k u v) := by
    intro u hu v
    rw [fderiv_comp u ((hG (k u) (hsphere hu)).differentiableAt (by simp)) ((hk u hu).differentiableAt (by simp))]
    rfl
  have hKpos : ∀ u ∈ unitCircle, 0 < phaseRadialContact (K u) (fderiv ℝ K u (circleTangent u)) := by
    intro u hu
    rw [hKD u hu]
    change 0 < phaseRadialContact (a (k u) • k u) (fderiv ℝ G (k u) (fderiv ℝ k u (circleTangent u)))
    rw [radial_lift_contact a (k u) _ ((ha (k u) (hsphere hu)).1.differentiableAt (by simp))]
    exact mul_pos (sq_pos_of_pos (ha (k u) (hsphere hu)).2) (hpos u hu)
  intro t ht u hu
  have hh := orbit_knot_positive_primitive_blend μ c hμ0 hμ1 hc M φ hφ γ K hK hKim hKpos t ht u hu
  rw [hKD u hu] at hh
  exact hh

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection GrayStability Set Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma circle_sphere_map_fderiv_tangent (k : Plane → Phase)
    (hk : ∀ u ∈ unitCircle, DifferentiableAt ℝ k u)
    (hsphere : MapsTo k unitCircle unitThreeSphere) (u : Plane) (hu : u ∈ unitCircle) :
    phaseDot (k u) (fderiv ℝ k u (circleTangent u)) = 0 := by
  have hku : DifferentiableAt ℝ k (ContactGenerator.circleCurve u 0) := by
    rw [ContactGenerator.circleCurve_zero]
    exact hk u hu
  have hc : HasDerivAt (fun s => k (ContactGenerator.circleCurve u s))
      (fderiv ℝ k u (circleTangent u)) 0 := by
    convert! hku.hasFDerivAt.comp_hasDerivAt 0 (ContactGenerator.circleCurve_hasDerivAt u) using 1
    simp only [ContactGenerator.circleCurve_zero]
  have hd := dot_self_hasDerivAt hc
  have heq : (fun s => phaseDot (k (ContactGenerator.circleCurve u s)) (k (ContactGenerator.circleCurve u s))) =
      fun _ => (1:ℝ) := by
    funext s
    exact sphere_dot_self (hsphere (ContactGenerator.circleCurve_mem u hu s))
  rw [heq] at hd
  have he := hd.unique (hasDerivAt_const (0:ℝ) (1:ℝ))
  simp only [ContactGenerator.circleCurve_zero] at he
  linarith

lemma sourceLiftForm_zero_apply (κ : ℝ) (f : Phase → Phase) (a : Phase → ℝ) (y v : Phase)
    (ha : DifferentiableAt ℝ a y) :
    sourceLiftForm κ f a 0 y v = κ * a y ^ 2 * phaseRadialContact y v := by
  rw [sourceLiftForm_zero]
  simp only [smul_apply,smul_eq_mul,pullbackRadialForm,ContinuousLinearMap.comp_apply,radialForm_apply]
  rw [radial_lift_contact a y v ha]
  ring

lemma convex_model_contact_family_positive_on_hopf_orbit
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (γ : PeriodicOrbit φ)
    (I : EquivariantTransverseHopfIsotopy (radialNormalize '' orbitSet γ)) :
    ∃ a : Phase → ℝ, ∃ α : ℝ → OneForm 4,
      (∀ x : Phase, x ≠ 0 → ContDiffAt ℝ ∞ a x ∧ 0 < a x ∧ a x • x ∈ leftEnergyComponent μ c) ∧
      (∀ y ∈ leftEnergyComponent μ c, a (radialNormalize y) • radialNormalize y = y) ∧
      IsContactFamilyOn sphereEq α ∧ (∀ t y, α t (-y) = -α t y) ∧
      (∀ t y, y ∈ unitThreeSphere → ∀ v : Phase, phaseDot y v = 0 →
        α t y v = sourceLiftForm M.symplecticScale M.toModel a t y v) ∧
      (∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
        α 0 y v = M.symplecticScale * a y ^ 2 * phaseRadialContact y v) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ u ∈ unitCircle,
        0 < α t (I.isotopy (1,u)) (fderiv ℝ (fun w => I.isotopy (1,w)) u (circleTangent u))) := by
  obtain ⟨a,ha,hasphere,hainv⟩ := left_component_radial_lift μ c hμ0 hμ1 hc
  obtain ⟨α,hα,ho,hval⟩ := convex_model_global_contact_family μ c hμ0 hμ1 hc M a ha
    (fun u hu => (hasphere u hu).2)
  have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by norm_num,le_rfl⟩
  let k : Plane → Phase := fun u => I.isotopy (1,u)
  have hk : ∀ u ∈ unitCircle, ContDiffAt ℝ ∞ k u := by
    intro u hu
    exact (I.smooth 1 h1 u hu).comp u (contDiffAt_const.prodMk contDiffAt_id)
  have hsphere : MapsTo k unitCircle unitThreeSphere := fun u hu => I.sphere 1 h1 u hu
  have himage : MapsTo k unitCircle (radialNormalize '' orbitSet γ) := by
    intro u hu
    rw [← I.finish]
    exact ⟨u,hu,rfl⟩
  have hpos := normalized_orbit_positive_sourceLiftForm μ c hμ0 hμ1 hc M φ hφ γ a
    (fun y hy => ⟨(ha y (sphere_ne_zero hy)).1,(ha y (sphere_ne_zero hy)).2.1⟩) hainv k hk hsphere himage
    (fun u hu => I.positive 1 h1 u hu)
  refine ⟨a,α,ha,hainv,hα,ho,hval,?_,?_⟩
  · intro y hy v hv
    rw [hval 0 y hy v hv,sourceLiftForm_zero_apply _ _ _ _ _ ((ha y (sphere_ne_zero hy)).1.differentiableAt (by simp))]
  · intro t ht u hu
    rw [hval t (k u) (hsphere hu) (fderiv ℝ k u (circleTangent u))
      (circle_sphere_map_fderiv_tangent k (fun u hu => (hk u hu).differentiableAt (by simp)) hsphere u hu)]
    exact hpos t ht u hu

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection GrayStability Set
open scoped ContDiff
noncomputable section

def oddAverage (X : ℝ → Phase → Phase) (t : ℝ) (y : Phase) : Phase :=
  (1 / 2 : ℝ) • (X t y - X t (-y))

lemma oddAverage_odd (X : ℝ → Phase → Phase) (t : ℝ) (y : Phase) :
    oddAverage X t (-y) = -oddAverage X t y := by
  ext i
  simp [oddAverage]
  ring

lemma oddAverage_contDiff {X : ℝ → Phase → Phase}
    (hX : ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : ℝ × Phase => oddAverage X p.1 p.2) := by
  exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × Phase => (1/2 : ℝ))).smul (hX.sub (hX.comp (contDiff_fst.prodMk contDiff_snd.neg)))

lemma oddAverage_fderiv_apply {X : ℝ → Phase → Phase}
    (hX : ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2)) (t : ℝ) (y v : Phase) :
    fderiv ℝ (oddAverage X t) y v =
      (1 / 2 : ℝ) • (fderiv ℝ (X t) y v + fderiv ℝ (X t) (-y) v) := by
  have hd : Differentiable ℝ (X t) :=
    (hX.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hn : HasFDerivAt (fun z : Phase => -z) (-ContinuousLinearMap.id ℝ Phase) y :=
    (hasFDerivAt_id y).neg
  have hf := (((hd y).hasFDerivAt).sub (((hd (-y)).hasFDerivAt).comp y hn)).const_smul (1/2 : ℝ)
  change fderiv ℝ ((1/2 : ℝ) • (X t - X t ∘ Neg.neg)) y v = _
  rw [hf.fderiv]
  simp [ContinuousLinearMap.comp_apply]

lemma oddAverage_compact_support {X : ℝ → Phase → Phase}
    (hX : ∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0) :
    ∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → oddAverage X t y = 0 := by
  obtain ⟨C,hC,hs⟩ := hX
  refine ⟨C ∪ Neg.neg '' C, hC.union (hC.image continuous_neg), ?_⟩
  intro t y hy
  have hyC : y ∉ C := fun h => hy (Or.inl h)
  have hnyC : -y ∉ C := fun h => hy (Or.inr ⟨-y,h,neg_neg y⟩)
  simp [oddAverage, hs t y hyC, hs t (-y) hnyC]

lemma sphere_neg {y : Phase} (hy : y ∈ unitThreeSphere) : -y ∈ unitThreeSphere := by
  simpa [unitThreeSphere,zNormSq,wNormSq] using hy

lemma oddAverage_tangent {X : ℝ → Phase → Phase}
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (X t y) = 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (oddAverage X t y) = 0 := by
  intro t ht y hy
  have h1 := hX t ht y hy
  have h2 := hX t ht (-y) (sphere_neg hy)
  simp [phaseDot] at h1 h2
  simp [oddAverage, phaseDot]
  linear_combination (1/2 : ℝ) * h1 + (1/2 : ℝ) * h2

lemma odd_map_fderiv_even {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Phase → E) (hf : Differentiable ℝ f) (ho : ∀ y, f (-y) = -f y) (y v : Phase) :
    fderiv ℝ f (-y) v = fderiv ℝ f y v := by
  have hn : HasFDerivAt (fun z : Phase => -z) (-ContinuousLinearMap.id ℝ Phase) y := (hasFDerivAt_id y).neg
  have h₁ := (hf (-y)).hasFDerivAt.comp y hn
  have h₂ := (hf y).hasFDerivAt.neg
  have heq : (f ∘ fun z : Phase => -z) = -f := funext ho
  rw [heq] at h₁
  have he := congrArg (fun L : Phase →L[ℝ] E => L v) (h₁.unique h₂)
  simpa using he

lemma formTimeDeriv_odd (α : ℝ → OneForm 4) (ho : ∀ t y, α t (-y) = -α t y)
    (t : ℝ) (y v : Phase) : formTimeDeriv α t (-y) v = -formTimeDeriv α t y v := by
  have heq : (fun s => α s (-y) v) = -(fun s => α s y v) := by
    funext s
    rw [ho s y]
    rfl
  dsimp [formTimeDeriv]
  rw [heq,deriv.neg]

lemma odd_moser_equation (α : ℝ → OneForm 4) (hα : IsContactFamilyOn sphereEq α)
    (ho : ∀ t y, α t (-y) = -α t y)
    (X : ℝ → Phase → Phase) (μ : ℝ → Phase → ℝ)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2))
    (heq : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      formTimeDeriv α t y v+lieDerivOneForm (X t) (α t) y v = μ t y*α t y v) :
    ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      formTimeDeriv α t y v+lieDerivOneForm (oddAverage X t) (α t) y v =
        ((μ t y+μ t (-y))/2)*α t y v := by
  intro t ht y hy v hv
  have hnv : phaseDot (-y) v = 0 := by simp [phaseDot] at hv ⊢; linarith
  have h₁ := heq t ht y hy v hv
  have h₂ := heq t ht (-y) (sphere_neg_mem hy) v hnv
  have hαdiff : Differentiable ℝ (α t) :=
    (hα.1.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hda := odd_map_fderiv_even (α t) hαdiff (ho t) y (X t (-y))
  rw [formTimeDeriv_odd α ho,ho t y] at h₂
  dsimp [lieDerivOneForm] at h₁ h₂ ⊢
  rw [ho t y] at h₂
  rw [hda] at h₂
  rw [oddAverage_fderiv_apply hX]
  simp only [oddAverage,map_smul,map_sub,map_add,smul_apply,sub_apply,add_apply,neg_apply,smul_eq_mul] at h₂ ⊢
  linear_combination (1/2:ℝ)*h₁-(1/2:ℝ)*h₂

lemma equivariant_moser_generator (α : ℝ → OneForm 4) (hα : IsContactFamilyOn sphereEq α)
    (ho : ∀ t y, α t (-y) = -α t y) :
    ∃ X : ℝ → Phase → Phase, ∃ μ : ℝ → Phase → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Phase => μ p.1 p.2) ∧
      (∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0) ∧
      (∀ t y, X t (-y) = -X t y) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ levelSet sphereEq, X t y ∈ contactPlane sphereEq (α t) y) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ levelSet sphereEq, ∀ v ∈ tangentSpace sphereEq y,
        formTimeDeriv α t y v+lieDerivOneForm (X t) (α t) y v = μ t y*α t y v) := by
  obtain ⟨X,μ,hX,hμ,hsupp,hplane,heq⟩ := GrayStability.smooth_moser_lie_generator sphereEq sphereEq_regular α hα
  have htan : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (X t y) = 0 := by
    intro t ht y hy
    exact mem_tangentSpace_sphereEq.mp (hplane t ht y (mem_levelSet_sphereEq.mpr hy)).1
  refine ⟨oddAverage X,(fun t y => (μ t y+μ t (-y))/2),oddAverage_contDiff hX,?_,
    oddAverage_compact_support hsupp,oddAverage_odd X,?_,?_⟩
  · exact (hμ.add (hμ.comp (contDiff_fst.prodMk contDiff_snd.neg))).div_const 2
  · intro t ht y hy
    have hyS := mem_levelSet_sphereEq.mp hy
    refine ⟨mem_tangentSpace_sphereEq.mpr (oddAverage_tangent htan t ht y hyS),?_⟩
    have h₁ := (hplane t ht y hy).2
    have h₂ := (hplane t ht (-y) (mem_levelSet_sphereEq.mpr (sphere_neg_mem hyS))).2
    rw [ho t y] at h₂
    simp only [neg_apply] at h₂
    simp only [oddAverage,map_smul,map_sub,smul_eq_mul,h₁]
    linarith
  · intro t ht y hy v hv
    apply odd_moser_equation α hα ho X μ hX ?_ t ht y (mem_levelSet_sphereEq.mp hy) v (mem_tangentSpace_sphereEq.mp hv)
    intro s hs z hz w hw
    exact heq s hs z (mem_levelSet_sphereEq.mpr hz) w (mem_tangentSpace_sphereEq.mpr hw)

end
end BirkhoffGlobalSection.HopfTransport


open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

namespace BirkhoffGlobalSection.HopfTransport
noncomputable section

lemma smooth_inverse_of_bijective_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → E) (hf : ContDiff ℝ ∞ f) (hb : Function.Bijective f)
    (hi : ∀ x, Function.Injective (fderiv ℝ f x)) :
    ∃ g : E → E, ContDiff ℝ ∞ g ∧ (∀ x, g (f x) = x) ∧ (∀ x, f (g x) = x) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
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
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
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
      change fderiv ℝ (ψ p.1) p.2 (v.2-w.2) = 0
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

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection GrayStability Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma equivariant_gray_sphere (α : ℝ → OneForm 4) (hα : IsContactFamilyOn sphereEq α)
    (ho : ∀ t y, α t (-y) = -α t y) :
    ∃ ψ ρ : ℝ → Phase → Phase, ∃ lam : ℝ → Phase → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × Phase => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Phase => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Phase => lam p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧
      (∀ t y, ρ t (ψ t y) = y) ∧ (∀ t y, ψ t (ρ t y) = y) ∧
      (∀ t y, ψ t (-y) = -ψ t y) ∧ (∀ t y, ρ t (-y) = -ρ t y) ∧
      IsIsotopyOf sphereEq ψ ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ρ t y ∈ unitThreeSphere) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, 0 < lam t y) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
        pullback (ψ t) (α t) y v = lam t y * α 0 y v) := by
  obtain ⟨X,μ,hX,hμ,hsupp,hodd,hplane,heq⟩ := equivariant_moser_generator α hα ho
  have htan : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ levelSet sphereEq, X t y ∈ tangentSpace sphereEq y := by
    intro t ht y hy
    exact (hplane t ht y hy).1
  obtain ⟨ψ,hψ,h0,hbij,hflow,hiso,hDψ⟩ := FlowCalculus.compact_supported_flow_preserves_regular_level
    sphereEq sphereEq_regular X hX hsupp htan
  obtain ⟨ρ,hρ,hρψ,hψρ⟩ := smooth_joint_flow_inverse X ψ hX hψ h0 hbij hflow
  have hψodd : ∀ t y, ψ t (-y) = -ψ t y := by
    intro t y
    have hp : (fun s => ψ s (-y)) 0 = -y ∧
        ∀ s, HasDerivAt (fun r => ψ r (-y)) (X s (ψ s (-y))) s := ⟨h0 (-y),fun s => hflow s (-y)⟩
    have hn : (fun s => -ψ s y) 0 = -y ∧
        ∀ s, HasDerivAt (fun r => -ψ r y) (X s (-ψ s y)) s := by
      constructor
      · change -ψ 0 y = -y
        rw [h0]
      · intro s
        rw [hodd]
        convert! (hflow s y).neg using 1
    have hh : (fun s => ψ s (-y)) = (fun s => -ψ s y) := by
      apply (FlowCalculus.exists_unique_global_trajectory_of_compact_support X hX hsupp 0 (-y)).unique
      · convert! hp using 1
      · convert! hn using 1
    exact congrFun hh t
  have hρodd : ∀ t y, ρ t (-y) = -ρ t y := by
    intro t y
    apply (hbij t).1
    rw [hψρ,hψodd,hψρ]
  have hρsphere : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ρ t y ∈ unitThreeSphere := by
    intro t ht y hy
    obtain ⟨z,hz,hzmap⟩ := (hiso.2.2 t ht).1.surjOn (mem_levelSet_sphereEq.mpr hy)
    rw [← hzmap,hρψ]
    exact mem_levelSet_sphereEq.mp hz
  let q : ℝ → Phase → ℝ := fun t y => μ t (ψ t y)
  have hq : ContDiff ℝ ∞ (fun p : ℝ × Phase => q p.1 p.2) := hμ.comp (contDiff_fst.prodMk hψ)
  obtain ⟨lam,hlam,_,hpos,htransport⟩ := ParameterizedCalculus.smooth_scalar_linear_transport q hq
  refine ⟨ψ,ρ,lam,hψ,hρ,hlam,h0,hρψ,hψρ,hψodd,hρodd,hiso,hρsphere,?_,?_⟩
  · intro t ht y hy
    exact hpos t y
  · intro t ht y hyS v hvS
    have hy := mem_levelSet_sphereEq.mpr hyS
    have hv := mem_tangentSpace_sphereEq.mpr hvS
    have hf : ∀ s ∈ Icc (0:ℝ) 1,
        HasDerivAt (fun r => pullback (ψ r) (α r) y v) (q s y*pullback (ψ s) (α s) y v) s := by
      intro s hs
      have hmap : ψ s y ∈ levelSet sphereEq := (hiso.2.2 s hs).1.mapsTo hy
      have hw := hDψ s hs y hy v hv
      have hd := GrayStability.pullback_family_hasDerivAt α hα.1 X hX ψ hψ h0 hbij hflow s y v
      rw [heq s hs (ψ s y) hmap (fderiv ℝ (ψ s) y v) hw] at hd
      exact hd
    have hinit : pullback (ψ 0) (α 0) y v = α 0 y v := by
      have hid : ψ 0 = id := funext h0
      simp [pullback,hid]
    simpa only [hinit] using htransport y (fun s => pullback (ψ s) (α s) y v) hf t ht

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection GrayStability Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Pulling a fixed transverse knot backwards through Gray's family gives
a knot transverse to the initial form. All derivative identities are tangent
identities on the sphere, rather than assumed ambient contact identities. -/
lemma inverse_gray_knot_positive
    (α : ℝ → OneForm 4) (ψ ρ : ℝ → Phase → Phase) (lam : ℝ → Phase → ℝ)
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × Phase => ψ p.1 p.2))
    (hρ : ContDiff ℝ ∞ (fun p : ℝ × Phase => ρ p.1 p.2))
    (hψρ : ∀ t y, ψ t (ρ t y) = y)
    (hρsphere : ∀ t ∈ Icc (0:ℝ) 1, MapsTo (ρ t) unitThreeSphere unitThreeSphere)
    (hlam : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, 0 < lam t y)
    (hpullback : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      pullback (ψ t) (α t) y v = lam t y * α 0 y v)
    (hstandard : ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      0 < α 0 y v → 0 < phaseRadialContact y v)
    (k : Plane → Phase) (hk : ∀ u ∈ unitCircle, ContDiffAt ℝ ∞ k u)
    (hsphere : MapsTo k unitCircle unitThreeSphere)
    (hpos : ∀ t ∈ Icc (0:ℝ) 1, ∀ u ∈ unitCircle,
      0 < α t (k u) (fderiv ℝ k u (circleTangent u))) :
    ∀ t ∈ Icc (0:ℝ) 1, ∀ u ∈ unitCircle,
      0 < phaseRadialContact (ρ t (k u))
        (fderiv ℝ (fun w => ρ t (k w)) u (circleTangent u)) := by
  intro t ht u hu
  have hψt : ContDiff ℝ ∞ (ψ t) := hψ.comp (contDiff_const.prodMk contDiff_id)
  have hρt : ContDiff ℝ ∞ (ρ t) := hρ.comp (contDiff_const.prodMk contDiff_id)
  have hv := circle_sphere_map_fderiv_tangent k (fun u hu => (hk u hu).differentiableAt (by simp)) hsphere u hu
  let z := ρ t (k u)
  let w := fderiv ℝ (ρ t) (k u) (fderiv ℝ k u (circleTangent u))
  have hz : z ∈ unitThreeSphere := hρsphere t ht (hsphere hu)
  have hw : phaseDot z w = 0 := sphere_map_fderiv_tangent (ρ t) (k u) _ (hsphere hu) hv
    (hρt.differentiable (by simp) _) (hρsphere t ht)
  have hD : fderiv ℝ (ψ t) z w = fderiv ℝ k u (circleTangent u) :=
    sphere_diffeo_tangent_leftInverse (ρ t) (ψ t)
      (fun y hy => ⟨hρt.contDiffAt,hρsphere t ht hy⟩) (fun y hy => hψt.contDiffAt)
      (fun y hy => hψρ t y) (k u) _ (hsphere hu) hv
  have he := hpullback t ht z hz w hw
  change α t (ψ t z) (fderiv ℝ (ψ t) z w) = lam t z * α 0 z w at he
  rw [hD,hψρ] at he
  have hinit : 0 < α 0 z w := (mul_pos_iff_of_pos_left (hlam t ht z hz)).mp (he ▸ hpos t ht u hu)
  have hh := hstandard z hz w hw hinit
  have hder : fderiv ℝ (fun v => ρ t (k v)) u = (fderiv ℝ (ρ t) (k u)).comp (fderiv ℝ k u) := by
    exact fderiv_comp u (hρt.differentiable (by simp) _) ((hk u hu).differentiableAt (by simp))
  rw [hder]
  exact hh

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Append a transverse deformation of the endpoint knot while keeping the
fixed standard Hopf starting parametrization. The two smooth clocks have
disjoint transition intervals, so no piecewise smooth gluing is needed. -/
lemma hopf_isotopy_append_deformation {K : Set Phase}
    (I : EquivariantTransverseHopfIsotopy K) (ρ : ℝ → Phase → Phase)
    (hρ : ContDiff ℝ ∞ (fun p : ℝ × Phase => ρ p.1 p.2))
    (hρ0 : ∀ y, ρ 0 y = y)
    (hρsphere : ∀ t ∈ Icc (0:ℝ) 1, MapsTo (ρ t) unitThreeSphere unitThreeSphere)
    (hρinj : ∀ t ∈ Icc (0:ℝ) 1, InjOn (ρ t) unitThreeSphere)
    (hρodd : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ρ t (-y) = -ρ t y)
    (hpos : ∀ t ∈ Icc (0:ℝ) 1, ∀ u ∈ unitCircle,
      0 < phaseRadialContact (ρ t (I.isotopy (1,u)))
        (fderiv ℝ (fun w => ρ t (I.isotopy (1,w))) u (circleTangent u))) :
    Nonempty (EquivariantTransverseHopfIsotopy (ρ 1 '' K)) := by
  let σ : ℝ → ℝ := fun t => Real.smoothTransition (4*t)
  let θ : ℝ → ℝ := fun t => Real.smoothTransition (4*t-2)
  have hσ : ContDiff ℝ ∞ σ := (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp (contDiff_const.mul contDiff_id)
  have hθ : ContDiff ℝ ∞ θ := (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hσmem : ∀ t, σ t ∈ Icc (0:ℝ) 1 := fun t => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
  have hθmem : ∀ t, θ t ∈ Icc (0:ℝ) 1 := fun t => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
  have hσ0 : σ 0 = 0 := by simp [σ,Real.smoothTransition.zero]
  have hθ0 : θ 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have hσ1 : σ 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
  have hθ1 : θ 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
  let J : ℝ × Plane → Phase := fun p => ρ (θ p.1) (I.isotopy (σ p.1,p.2))
  refine ⟨{
    isotopy := J
    smooth := ?_
    sphere := ?_
    injective := ?_
    antipodal := ?_
    positive := ?_
    start := ?_
    finish := ?_ }⟩
  · intro t ht u hu
    have hI := (I.smooth (σ t) (hσmem t) u hu).comp (t,u)
      ((hσ.contDiffAt.comp (t,u) contDiffAt_fst).prodMk contDiffAt_snd)
    exact hρ.contDiffAt.comp (t,u) ((hθ.contDiffAt.comp (t,u) contDiffAt_fst).prodMk hI)
  · intro t ht u hu
    exact hρsphere (θ t) (hθmem t) (I.sphere (σ t) (hσmem t) u hu)
  · intro t ht u hu v hv he
    apply I.injective (σ t) (hσmem t) hu hv
    exact hρinj (θ t) (hθmem t) (I.sphere (σ t) (hσmem t) u hu)
      (I.sphere (σ t) (hσmem t) v hv) he
  · intro t ht u hu
    change ρ (θ t) (I.isotopy (σ t,-u)) = -ρ (θ t) (I.isotopy (σ t,u))
    rw [I.antipodal (σ t) (hσmem t) u hu]
    exact hρodd (θ t) (hθmem t) _ (I.sphere (σ t) (hσmem t) u hu)
  · intro t ht u hu
    change 0 < phaseRadialContact ((fun w => J (t,w)) u) (fderiv ℝ (fun w => J (t,w)) u (circleTangent u))
    by_cases htlow : t ≤ 1/2
    · have hz : θ t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
      have heq : (fun w => J (t,w)) = (fun w => I.isotopy (σ t,w)) := by
        funext w
        simp only [J,hz,hρ0]
      rw [heq]
      exact I.positive (σ t) (hσmem t) u hu
    · have hz : σ t = 1 := Real.smoothTransition.one_of_one_le (by linarith)
      have heq : (fun w => J (t,w)) = (fun w => ρ (θ t) (I.isotopy (1,w))) := by
        funext w
        simp only [J,hz]
      rw [heq]
      exact hpos (θ t) (hθmem t) u hu
  · intro u hu
    change ρ (θ 0) (I.isotopy (σ 0,u)) = standardHopfCircle u
    rw [hθ0,hσ0,hρ0,I.start u hu]
  · change (fun u => ρ (θ 1) (I.isotopy (σ 1,u))) '' unitCircle = _
    rw [hθ1,hσ1]
    change (ρ 1 ∘ fun u => I.isotopy (1,u)) '' unitCircle = _
    rw [Set.image_comp,I.finish]

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection GrayStability Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma normalized_model_contact_endpoint (μ c : ℝ) (M : ConvexRegularizationModel μ c)
    (a : Phase → ℝ)
    (ha : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ a y ∧ 0 < a y ∧ a y • y ∈ leftEnergyComponent μ c)
    (T : Phase → Phase) (hT : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ T y)
    (hTnorm : ∀ y ∈ leftEnergyComponent μ c, T (radialNormalize y) = radialNormalize (M.toModel y)) :
    ∀ y ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ ∀ v : Phase, phaseDot y v = 0 →
      sourceLiftForm M.symplecticScale M.toModel a 1 y v =
        r * phaseRadialContact (T y) (fderiv ℝ T y v) := by
  let G : Phase → Phase := fun y => a y • y
  let P : Phase → Phase := M.toModel ∘ G
  have hG : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ G y := fun y hy => (ha y hy).1.smul contDiffAt_id
  have hM : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ M.toModel (G y) := fun y hy =>
    M.toModel_smooth.contDiffAt (M.source_open.mem_nhds (M.contains_component (ha y hy).2.2))
  have hP : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ P y := fun y hy =>
    (hM y hy).comp (f := G) y (hG y hy)
  have hfront : ∀ y ∈ unitThreeSphere, P y ∈ frontier M.body := by
    intro y hy
    rw [← M.image_frontier]
    exact ⟨G y,(ha y hy).2.2,rfl⟩
  have hQ : ∀ y ∈ unitThreeSphere, 0 < zNormSq (P y)+wNormSq (P y) := fun y hy =>
    radiusSq_pos _ (convex_frontier_ne_zero M (hfront y hy))
  have hN : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ radialNormalize (P y) := fun y hy =>
    (radial_normalization_contact_identity _ (hQ y hy)).1
  have heq : EqOn T (radialNormalize ∘ P) unitThreeSphere := by
    intro y hy
    have hh := hTnorm (G y) (ha y hy).2.2
    change T (radialNormalize (a y • y)) = radialNormalize (P y) at hh
    rwa [normalize_positive_smul hy (ha y hy).2.1] at hh
  intro y hy
  refine ⟨zNormSq (P y)+wNormSq (P y),hQ y hy,?_⟩
  intro v hv
  have hd := sphere_tangent_fderiv_eq T (radialNormalize ∘ P) y v hy hv
    ((hT y hy).differentiableAt (by simp))
    (((hN y hy).comp (f := P) y (hP y hy)).differentiableAt (by simp)) heq
  have hn := (radial_normalization_contact_identity (P y) (hQ y hy)).2.2.2 (fderiv ℝ P y v)
  have he : phaseRadialContact (T y) (fderiv ℝ T y v) =
      pullbackRadialForm P y v / (zNormSq (P y)+wNormSq (P y)) := by
    rw [heq hy,hd,fderiv_comp y ((hN y hy).differentiableAt (by simp)) ((hP y hy).differentiableAt (by simp))]
    simpa only [Function.comp_apply,pullbackRadialForm,ContinuousLinearMap.comp_apply,radialForm_apply] using hn
  rw [sourceLiftForm_one_apply _ _ _ _ _ (ha y hy).1 (hM y hy)]
  change pullbackRadialForm P y v = _
  rw [he]
  field_simp [(hQ y hy).ne']

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection GrayStability Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma gray_corrected_contactomorphism (T U ψ ρ : Phase → Phase)
    (hT : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ T y ∧ T y ∈ unitThreeSphere)
    (hU : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ U y ∧ U y ∈ unitThreeSphere)
    (hUT : ∀ y ∈ unitThreeSphere, U (T y) = y)
    (hTU : ∀ y ∈ unitThreeSphere, T (U y) = y)
    (hTneg : ∀ y ∈ unitThreeSphere, T (-y) = -T y)
    (hψ : ContDiff ℝ ∞ ψ) (hρ : ContDiff ℝ ∞ ρ)
    (hψsphere : MapsTo ψ unitThreeSphere unitThreeSphere)
    (hρsphere : MapsTo ρ unitThreeSphere unitThreeSphere)
    (hρψ : ∀ y, ρ (ψ y) = y) (hψρ : ∀ y, ψ (ρ y) = y)
    (hψneg : ∀ y, ψ (-y) = -ψ y)
    (A B : OneForm 4) (lam : Phase → ℝ)
    (hlam : ∀ y ∈ unitThreeSphere, 0 < lam y)
    (hpull : ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      B (ψ y) (fderiv ℝ ψ y v) = lam y * A y v)
    (hA : ∀ y ∈ unitThreeSphere, ∃ p : ℝ, 0 < p ∧ ∀ v : Phase, phaseDot y v = 0 →
      A y v = p * phaseRadialContact y v)
    (hB : ∀ y ∈ unitThreeSphere, ∃ q : ℝ, 0 < q ∧ ∀ v : Phase, phaseDot y v = 0 →
      B y v = q * phaseRadialContact (T y) (fderiv ℝ T y v)) :
    ∃ F : EquivariantSphereContactomorphism,
      (∀ y, F.toFun y = T (ψ y)) ∧ (∀ y, F.invFun y = ρ (U y)) := by
  refine ⟨{
    toFun := T ∘ ψ
    invFun := ρ ∘ U
    smooth := ?_
    inv_smooth := ?_
    maps_sphere := ?_
    inv_maps_sphere := ?_
    left_inv := ?_
    right_inv := ?_
    antipodal := ?_
    contact := ?_ },(fun _ => rfl),(fun _ => rfl)⟩
  · intro y hy
    exact ((hT (ψ y) (hψsphere hy)).1).comp y hψ.contDiffAt
  · intro y hy
    exact hρ.contDiffAt.comp y (hU y hy).1
  · intro y hy
    exact (hT (ψ y) (hψsphere hy)).2
  · intro y hy
    exact hρsphere (hU y hy).2
  · intro y hy
    change ρ (U (T (ψ y))) = y
    rw [hUT (ψ y) (hψsphere hy),hρψ]
  · intro y hy
    change T (ψ (ρ (U y))) = y
    rw [hψρ,hTU y hy]
  · intro y hy
    change T (ψ (-y)) = -T (ψ y)
    rw [hψneg,hTneg (ψ y) (hψsphere hy)]
  · intro y hy
    obtain ⟨p,hp,hpval⟩ := hA y hy
    obtain ⟨q,hq,hqval⟩ := hB (ψ y) (hψsphere hy)
    refine ⟨lam y*p/q,div_pos (mul_pos (hlam y hy) hp) hq,?_⟩
    intro v hv
    have hψv := sphere_map_fderiv_tangent ψ y v hy hv (hψ.differentiable (by simp) y) hψsphere
    have he := hpull y hy v hv
    rw [hqval _ hψv,hpval v hv] at he
    rw [fderiv_comp y ((hT (ψ y) (hψsphere hy)).1.differentiableAt (by simp)) (hψ.differentiable (by simp) y)]
    change phaseRadialContact (T (ψ y)) (fderiv ℝ T (ψ y) (fderiv ℝ ψ y v)) =
      (lam y*p/q)*phaseRadialContact y v
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hq.ne').mpr
    nlinarith [he]

end
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection GrayStability Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- The full analytic transport for the actual regularization model. The
remaining distinction from the target is precisely invariance of the fixed
standard Hopf class under equivariant sphere contactomorphisms. -/
lemma convex_model_transverse_hopf_contact_transfer
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (γ : PeriodicOrbit φ)
    (hI : Nonempty (EquivariantTransverseHopfIsotopy (radialNormalize '' orbitSet γ))) :
    ∃ K : Set Phase, ∃ F : EquivariantSphereContactomorphism,
      Nonempty (EquivariantTransverseHopfIsotopy K) ∧
      F.toFun '' K = radialNormalize '' (M.toModel '' orbitSet γ) := by
  obtain ⟨I⟩ := hI
  obtain ⟨a,α,ha,hainv,hα,ho,hval,hα0,hαpos⟩ :=
    convex_model_contact_family_positive_on_hopf_orbit μ c hμ0 hμ1 hc M φ hφ γ I
  obtain ⟨ψ,ρ,lam,hψ,hρ,_,hψ0,hρψ,hψρ,hψodd,hρodd,hiso,hρsphere,hlam,hpb⟩ :=
    equivariant_gray_sphere α hα ho
  have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by norm_num,le_rfl⟩
  have hψsphere : ∀ t ∈ Icc (0:ℝ) 1, MapsTo (ψ t) unitThreeSphere unitThreeSphere := by
    intro t ht y hy
    exact mem_levelSet_sphereEq.mp ((hiso.2.2 t ht).1.mapsTo (mem_levelSet_sphereEq.mpr hy))
  have hρ0 : ∀ y, ρ 0 y = y := by
    intro y
    have hh := hρψ 0 y
    rwa [hψ0] at hh
  have hρinj : ∀ t ∈ Icc (0:ℝ) 1, InjOn (ρ t) unitThreeSphere := by
    intro t ht y hy z hz he
    have hh := congrArg (ψ t) he
    simpa only [hψρ] using hh
  have hstandard : ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      0 < α 0 y v → 0 < phaseRadialContact y v := by
    intro y hy v hv hh
    rw [hα0 y hy v hv] at hh
    exact (mul_pos_iff_of_pos_left (mul_pos M.symplecticScale_pos (sq_pos_of_pos (ha y (sphere_ne_zero hy)).2.1))).mp hh
  let k : Plane → Phase := fun u => I.isotopy (1,u)
  have hk : ∀ u ∈ unitCircle, ContDiffAt ℝ ∞ k u := by
    intro u hu
    exact (I.smooth 1 h1 u hu).comp u (contDiffAt_const.prodMk contDiffAt_id)
  have hinversepos := inverse_gray_knot_positive α ψ ρ lam hψ hρ hψρ hρsphere hlam hpb hstandard k hk
    (fun u hu => I.sphere 1 h1 u hu) hαpos
  have hJ := hopf_isotopy_append_deformation I ρ hρ hρ0 hρsphere hρinj
    (fun t ht y hy => hρodd t y) hinversepos
  obtain ⟨T,U,hTU,hInv,hodd,hTnorm⟩ := normalized_model_sphere_equivalence μ c hμ0 hμ1 hc M
  have hT : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ T y ∧ T y ∈ unitThreeSphere :=
    fun y hy => ⟨(hTU y hy).1,(hTU y hy).2.2.1⟩
  have hU : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ U y ∧ U y ∈ unitThreeSphere :=
    fun y hy => ⟨(hTU y hy).2.1,(hTU y hy).2.2.2⟩
  have hA : ∀ y ∈ unitThreeSphere, ∃ p : ℝ, 0 < p ∧ ∀ v : Phase, phaseDot y v = 0 →
      α 0 y v = p * phaseRadialContact y v := by
    intro y hy
    exact ⟨M.symplecticScale*a y^2,mul_pos M.symplecticScale_pos (sq_pos_of_pos (ha y (sphere_ne_zero hy)).2.1),hα0 y hy⟩
  have hB : ∀ y ∈ unitThreeSphere, ∃ q : ℝ, 0 < q ∧ ∀ v : Phase, phaseDot y v = 0 →
      α 1 y v = q * phaseRadialContact (T y) (fderiv ℝ T y v) := by
    intro y hy
    obtain ⟨q,hq,hqval⟩ := normalized_model_contact_endpoint μ c M a
      (fun y hy => ha y (sphere_ne_zero hy)) T (fun y hy => (hT y hy).1) hTnorm y hy
    refine ⟨q,hq,?_⟩
    intro v hv
    rw [hval 1 y hy v hv]
    exact hqval v hv
  have hψ1 : ContDiff ℝ ∞ (ψ 1) := hψ.comp (contDiff_const.prodMk contDiff_id)
  have hρ1 : ContDiff ℝ ∞ (ρ 1) := hρ.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨F,hF,_⟩ := gray_corrected_contactomorphism T U (ψ 1) (ρ 1) hT hU
    (fun y hy => (hInv y hy).1) (fun y hy => (hInv y hy).2) (fun y hy => (hodd y hy).1)
    hψ1 hρ1 (hψsphere 1 h1) (hρsphere 1 h1) (hρψ 1) (hψρ 1) (hψodd 1)
    (α 0) (α 1) (lam 1) (hlam 1 h1) (hpb 1 h1) hA hB
  refine ⟨ρ 1 '' (radialNormalize '' orbitSet γ),F,hJ,?_⟩
  calc
    F.toFun '' (ρ 1 '' (radialNormalize '' orbitSet γ)) = T '' (radialNormalize '' orbitSet γ) := by
      rw [Set.image_image]
      apply Set.image_congr
      intro y hy
      rw [hF,hψρ]
    _ = radialNormalize '' (M.toModel '' orbitSet γ) := by
      rw [Set.image_image,Set.image_image]
      apply Set.image_congr
      intro y hy
      have hycomp : y ∈ leftEnergyComponent μ c := by
        obtain ⟨s,rfl⟩ := hy
        exact (φ s γ.point).property
      exact hTnorm y hycomp

end
end BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection

theorem solution
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (γ : PeriodicOrbit φ)
    (hI : Nonempty (EquivariantTransverseHopfIsotopy (radialNormalize '' orbitSet γ))) :
    ∃ K : Set Phase, ∃ F : EquivariantSphereContactomorphism,
      Nonempty (EquivariantTransverseHopfIsotopy K) ∧
      F.toFun '' K = radialNormalize '' (M.toModel '' orbitSet γ)  := by
  exact BirkhoffGlobalSection.HopfTransport.convex_model_transverse_hopf_contact_transfer
    μ c hμ0 hμ1 hc M φ hφ γ hI
