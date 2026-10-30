-- Prove2me | solution 1 for BirkhoffGlobalSection.left_energy_component_smooth_radial_chart
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T21:27:27.84617+00:00
-- url     : https://prove2.me/submissions/a97860d1-b720-4790-92ae-267db224327c

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_geometry
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_radial_derivative_pos
import Theorems.Thm_BirkhoffGlobalSection_left_component_radial_norm_positive
import Theorems.Thm_BirkhoffGlobalSection_left_component_ray_exists
import Theorems.Thm_BirkhoffGlobalSection_left_component_ray_unique_scale
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_radial_bijection
import Theorems.Thm_BirkhoffGlobalSection_compact_unique_ray_radial_graph
import Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.TietzeExtension
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

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

open BirkhoffGlobalSection
open scoped ContDiff
theorem solution
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c) :
    ∃ G : Phase → Phase,
      (∀ u ∈ unitThreeSphere, ContDiffAt ℝ ∞ G u ∧ G u ∈ leftEnergyComponent μ c ∧
        radialNormalize (G u) = u ∧ G (-u) = -G u ∧ ∃ r : ℝ, 0 < r ∧ G u = r • u) ∧
      (∀ y ∈ leftEnergyComponent μ c, G (radialNormalize y) = y) := by
  exact BirkhoffGlobalSection.HopfTransport.left_component_smooth_radial_chart μ c hμ0 hμ1 hc
