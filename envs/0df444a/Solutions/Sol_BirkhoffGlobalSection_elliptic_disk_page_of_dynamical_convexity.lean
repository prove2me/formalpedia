-- Prove2me | solution 1 for BirkhoffGlobalSection.elliptic_disk_page_of_dynamical_convexity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-07T03:42:09.88223+00:00
-- url     : https://prove2.me/submissions/65808e79-250f-4b7f-9604-fe1cbef0eff4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_reeb_elliptic_disk_page_of_dynamical_convexity
import Theorems.Thm_BirkhoffGlobalSection_convex_model_complete_normalized_flow_of_model_fields
import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue

/-!
# Elliptic disk pages in model Hamiltonian time

The child `reeb_elliptic_disk_page_of_dynamical_convexity` is the Hryniewicz--Salomão rational
open book theorem, lifted to the sphere, for the Reeb flow of the radial contact form `λ` on the
boundary of a centrally symmetric strictly convex body. That flow has velocity
`X_H / λ(X_H)` and commutes with the antipodal map even when `H` is not even. A complete flow
of this form exists for every convex model (`convex_model_complete_normalized_flow_of_model_fields`).

This file proves the change of time back to the model Hamiltonian flow `D.flow`:

* For every boundary point `y` the clock `τ(s) = ∫₀ˢ λ(X_H(Φ_r y)) dr` is an increasing
  bijection of `ℝ` (the integrand is bounded below by its positive minimum on the compact
  boundary). The curve `s ↦ Φ_{τ⁻¹ s} y` solves the Reeb equation, so by uniqueness for the
  locally Lipschitz field `X_H / λ(X_H)` it is the Reeb trajectory: `ψ_{τ(s)} y = Φ_s y`.
* The model orbit `Γ` becomes a simple Reeb orbit with the same trace and period `τ(T)`.
* Returns of the Reeb flow at unbounded times are returns of `D.flow` at unbounded times, and
  transversality to `X_H / λ(X_H)` is transversality to `X_H`.
-/

open BirkhoffGlobalSection
open scoped ContDiff Topology

set_option autoImplicit false

namespace BirkhoffGlobalSection.EllipticPage

/-- The Hamiltonian vector field of a `C²` function is `C¹`. -/
lemma hvf_contDiffAt {F : Phase → ℝ} {s : Phase} (hF : ContDiffAt ℝ 2 F s) :
    ContDiffAt ℝ 1 (hamiltonianVectorField F) s := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ F) s := hF.fderiv_right (by norm_num)
  have hp : ∀ i : Fin 4, ContDiffAt ℝ 1 (fun s => partialDerivative F s i) s :=
    fun i => hd.clm_apply contDiffAt_const
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · simpa [hamiltonianVectorField] using hp 2
  · simpa [hamiltonianVectorField] using hp 3
  · simpa [hamiltonianVectorField] using (hp 0).neg
  · simpa [hamiltonianVectorField] using (hp 1).neg

/-- The contact rate `λ_y(X_F y)` of a `C²` function is `C¹`. -/
lemma rate_contDiffAt {F : Phase → ℝ} {s : Phase} (hF : ContDiffAt ℝ 2 F s) :
    ContDiffAt ℝ 1 (fun y => phaseRadialContact y (hamiltonianVectorField F y)) s := by
  have h := contDiffAt_pi.1 (hvf_contDiffAt hF)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  unfold phaseRadialContact phaseSymplecticForm
  fun_prop

/-- Two solutions of an autonomous equation with locally Lipschitz field agree everywhere
once they agree at time `0`. -/
lemma eq_of_ode {v : Phase → Phase} {f g : ℝ → Phase}
    (hv : ∀ t, ∃ K, ∃ s ∈ 𝓝 (f t), LipschitzOnWith K v s)
    (hf : ∀ t, HasDerivAt f (v (f t)) t) (hg : ∀ t, HasDerivAt g (v (g t)) t)
    (h0 : f 0 = g 0) : ∀ t, f t = g t := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  set A : Set ℝ := {t | f t = g t} with hA
  have hclosed : IsClosed A := isClosed_eq hfc hgc
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t₀ ht₀
    have ht₀' : f t₀ = g t₀ := ht₀
    obtain ⟨K, s, hs, hL⟩ := hv t₀
    have hs' : s ∈ 𝓝 (g t₀) := by rw [← ht₀']; exact hs
    have hf' : ∀ᶠ t in 𝓝 t₀, HasDerivAt f (v (f t)) t ∧ f t ∈ s := by
      filter_upwards [hfc.continuousAt.preimage_mem_nhds hs] with t ht
      exact ⟨hf t, ht⟩
    have hg' : ∀ᶠ t in 𝓝 t₀, HasDerivAt g (v (g t)) t ∧ g t ∈ s := by
      filter_upwards [hgc.continuousAt.preimage_mem_nhds hs'] with t ht
      exact ⟨hg t, ht⟩
    have heq := ODE_solution_unique_of_eventually (v := fun _ => v) (s := fun _ => s) (K := K)
      (Filter.Eventually.of_forall fun _ => hL) hf' hg' ht₀'
    filter_upwards [heq] with t ht
    exact ht
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, h0⟩
  intro t
  have ht : t ∈ A := by rw [huniv]; trivial
  exact ht

/-- The model boundary lies in the domain of the model coordinates. -/
lemma frontier_subset_target {μ c : ℝ} (M : ConvexRegularizationModel μ c) :
    frontier M.body ⊆ M.target := by
  intro z hz
  rw [← M.image_frontier] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  exact M.toModel_mapsTo (M.contains_component hs)

lemma model_contDiffAt {μ c : ℝ} (M : ConvexRegularizationModel μ c) {z : Phase}
    (hz : z ∈ frontier M.body) : ContDiffAt ℝ ∞ M.modelHamiltonian z :=
  M.model_smooth.contDiffAt (M.target_open.mem_nhds (frontier_subset_target M hz))

/-- **Change of time.** Each Reeb trajectory is the model Hamiltonian trajectory through the
same point, run with an increasing clock `e` fixing `0`. -/
lemma reeb_reparam {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    {φ : Flow ℝ (LeftEnergyState μ c)} (D : ConvexModelDynamics M φ)
    (ψ : Flow ℝ (ConvexModelState M))
    (hψ : ∀ s t, HasDerivAt (fun v => (ψ v s : Phase))
      ((phaseRadialContact (ψ t s) (hamiltonianVectorField M.modelHamiltonian (ψ t s)))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian (ψ t s)) t)
    (y : ConvexModelState M) :
    ∃ e : ℝ ≃o ℝ, e 0 = 0 ∧ ∀ s, ψ (e s) y = D.flow s y := by
  set H := M.modelHamiltonian with hHdef
  set G : Phase → ℝ := fun z => phaseRadialContact z (hamiltonianVectorField H z) with hG
  have hH2 : ∀ z ∈ frontier M.body, ContDiffAt ℝ 2 H z := fun z hz =>
    (model_contDiffAt M hz).of_le (WithTop.coe_le_coe.2 le_top)
  have hGc : ∀ z ∈ frontier M.body, ContinuousAt G z := fun z hz =>
    (rate_contDiffAt (hH2 z hz)).continuousAt
  have hGpos : ∀ z ∈ frontier M.body, 0 < G z := convex_model_boundary_contact_positive M
  -- the model trajectory and its velocity at every time
  set x : ℝ → Phase := fun s => (D.flow s y : Phase) with hxdef
  have hx : ∀ s, HasDerivAt x (hamiltonianVectorField H (x s)) s := by
    intro s
    have h0 := D.hamiltonian (D.flow s y)
    have h1 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h0)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    show (D.flow r y : Phase) = (D.flow (r - s) (D.flow s y) : Phase)
    rw [← Flow.map_add, sub_add_cancel]
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hxm : ∀ s, x s ∈ frontier M.body := fun s => (D.flow s y).property
  -- the clock rate and its positive lower bound
  set g : ℝ → ℝ := fun s => G (x s) with hgdef
  have hgc : Continuous g :=
    continuous_iff_continuousAt.2 fun s => (hGc _ (hxm s)).comp hxc.continuousAt
  have hgpos : ∀ s, 0 < g s := fun s => hGpos _ (hxm s)
  have hcpt : IsCompact (frontier M.body) :=
    M.body_compact.of_isClosed_subset isClosed_frontier M.body_compact.isClosed.frontier_subset
  obtain ⟨m, hm, hmle⟩ : ∃ m, 0 < m ∧ ∀ s, m ≤ g s := by
    obtain ⟨z₀, hz₀, hmin⟩ := hcpt.exists_isMinOn ⟨_, y.property⟩
      (fun z hz => (hGc z hz).continuousWithinAt)
    exact ⟨G z₀, hGpos z₀ hz₀, fun s => hmin (hxm s)⟩
  -- the clock
  set σ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, g s with hσ
  have hσd : ∀ t, HasDerivAt σ (g t) t := fun t => (hgc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hσ0 : σ 0 = 0 := by simp [hσ]
  have hσc : Continuous σ := continuous_iff_continuousAt.2 fun t => (hσd t).continuousAt
  have hσmono : StrictMono σ :=
    strictMono_of_deriv_pos fun t => by rw [(hσd t).deriv]; exact hgpos t
  have hgd : ∀ t, HasDerivAt (fun t => σ t - m * t) (g t - m) t := fun t => by
    have h := (hσd t).sub ((hasDerivAt_id' t).const_mul m)
    rw [mul_one] at h
    exact h
  have hgmono : Monotone fun t => σ t - m * t := by
    apply monotone_of_deriv_nonneg
    · intro t; exact (hgd t).differentiableAt
    · intro t; rw [(hgd t).deriv]; linarith [hmle t]
  have hsurj : Function.Surjective σ := by
    intro v
    rcases le_or_gt 0 v with hv | hv
    · have hvm : (0 : ℝ) ≤ v / m := div_nonneg hv hm.le
      have hup : v ≤ σ (v / m) := by
        have := hgmono hvm
        simp only at this
        rw [mul_div_cancel₀ v hm.ne', hσ0, mul_zero, sub_zero] at this
        linarith
      obtain ⟨t, -, ht⟩ := intermediate_value_Icc hvm hσc.continuousOn
        ⟨by rw [hσ0]; exact hv, hup⟩
      exact ⟨t, ht⟩
    · have hvm : v / m ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv.le hm.le
      have hlo : σ (v / m) ≤ v := by
        have := hgmono hvm
        simp only at this
        rw [mul_div_cancel₀ v hm.ne', hσ0, mul_zero, sub_zero] at this
        linarith
      obtain ⟨t, -, ht⟩ := intermediate_value_Icc hvm hσc.continuousOn
        ⟨hlo, by rw [hσ0]; exact hv.le⟩
      exact ⟨t, ht⟩
  set e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective σ hσmono hsurj with he
  have heσ : ∀ t, e.symm (σ t) = t := fun t =>
    StrictMono.orderIsoOfSurjective_symm_apply_self σ hσmono hsurj t
  have hσe : ∀ τ, σ (e.symm τ) = τ := fun τ =>
    StrictMono.orderIsoOfSurjective_self_symm_apply σ hσmono hsurj τ
  have he0 : e.symm 0 = 0 := by simpa [hσ0] using heσ 0
  -- the reparametrized model trajectory solves the Reeb equation
  set V : Phase → Phase := fun z => (G z)⁻¹ • hamiltonianVectorField H z with hVdef
  have hcurve : ∀ τ, HasDerivAt (fun τ => x (e.symm τ)) (V (x (e.symm τ))) τ := by
    intro τ
    have hinv : HasDerivAt e.symm (g (e.symm τ))⁻¹ τ :=
      HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt
        (hσd (e.symm τ)) (hgpos _).ne'
        (Filter.Eventually.of_forall hσe)
    exact (hx (e.symm τ)).scomp τ hinv
  have hreeb : ∀ τ, HasDerivAt (fun v => (ψ v y : Phase)) (V (ψ τ y : Phase)) τ := hψ y
  have hlip : ∀ τ, ∃ K, ∃ s ∈ 𝓝 (x (e.symm τ)), LipschitzOnWith K V s := by
    intro τ
    have hz := hxm (e.symm τ)
    have hVc : ContDiffAt ℝ 1 V (x (e.symm τ)) :=
      ((rate_contDiffAt (hH2 _ hz)).inv (hGpos _ hz).ne').smul (hvf_contDiffAt (hH2 _ hz))
    exact hVc.exists_lipschitzOnWith
  have hagree := eq_of_ode hlip hcurve hreeb (by
    show x (e.symm 0) = (ψ 0 y : Phase)
    rw [he0, Flow.map_zero_apply]
    show (D.flow 0 y : Phase) = (y : Phase)
    rw [Flow.map_zero_apply])
  refine ⟨e, ?_, fun s => Subtype.ext ?_⟩
  · have h := congrArg e he0
    rw [OrderIso.apply_symm_apply] at h
    exact h.symm
  · have h := hagree (e s)
    rw [OrderIso.symm_apply_apply] at h
    exact h.symm

end BirkhoffGlobalSection.EllipticPage

open BirkhoffGlobalSection.EllipticPage

theorem solution {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (D : ConvexModelDynamics M φ) (γ : PeriodicOrbit φ)
    (Γ : PeriodicOrbit D.flow)
    (hsimple : IsSimplePeriodicOrbit D.flow Γ)
    (htrace : convexModelOrbitSet Γ = M.toModel '' orbitSet γ)
    (hsymmetric : ∀ y ∈ frontier M.body, -y ∈ frontier M.body)
    (hdc : IsDynamicallyConvexOn M.modelHamiltonian (frontier M.body))
    (disk : PositiveEllipticRationalDisk
      (radialNormalize '' convexModelOrbitSet Γ)) :
    Nonempty (ConvexModelRationalPage M D γ) := by
  obtain ⟨ψ, hψ⟩ := convex_model_complete_normalized_flow_of_model_fields M D
  obtain ⟨e, he0, he⟩ := reeb_reparam M D ψ hψ Γ.point
  have hes0 : e.symm 0 = 0 := by
    have h := congrArg e.symm he0
    rw [OrderIso.symm_apply_apply] at h
    exact h.symm
  -- the model orbit as a simple Reeb orbit with the same trace
  let Γ' : PeriodicOrbit ψ :=
    { point := Γ.point
      period := e Γ.period
      period_pos := by
        have h := e.strictMono Γ.period_pos
        rwa [he0] at h
      closed := (he Γ.period).trans Γ.closed }
  have hsimple' : IsSimplePeriodicOrbit ψ Γ' := by
    intro t ht0 htT heq
    have h0 : 0 < e.symm t := by rw [← hes0]; exact e.symm.strictMono ht0
    have hT : e.symm t < Γ.period := by
      have := e.symm.strictMono htT
      rwa [OrderIso.symm_apply_apply] at this
    apply hsimple (e.symm t) h0 hT
    rw [← he (e.symm t), OrderIso.apply_symm_apply]
    exact heq
  have htr : Set.range (fun t : ℝ => ((ψ t Γ'.point : ConvexModelState M) : Phase)) =
      convexModelOrbitSet Γ := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨e.symm t, ?_⟩
      show ((D.flow (e.symm t) Γ.point : ConvexModelState M) : Phase) =
        ((ψ t Γ.point : ConvexModelState M) : Phase)
      rw [← he (e.symm t), OrderIso.apply_symm_apply]
    · rintro ⟨s, rfl⟩
      refine ⟨e s, ?_⟩
      show ((ψ (e s) Γ.point : ConvexModelState M) : Phase) =
        ((D.flow s Γ.point : ConvexModelState M) : Phase)
      rw [he s]
  obtain ⟨page, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    reeb_elliptic_disk_page_of_dynamical_convexity M.body M.body_compact M.body_convex
      M.origin_interior hsymmetric M.modelHamiltonian (fun z hz => model_contDiffAt M hz)
      M.model_zero M.model_regular M.model_hessian (convex_model_boundary_contact_positive M)
      hdc ψ hψ Γ' hsimple' (by rw [htr]; exact disk)
  refine ⟨{
    page := page
    mapsTo := h1
    smooth := h2
    injective := h3
    immersion := h4
    transverse := ?_
    boundary := ?_
    antipodal_fibers := h7
    returns := ?_ }⟩
  · -- transversality to `X_H` follows from transversality to `X_H / λ(X_H)`
    intro u hu hX
    obtain ⟨w, hw⟩ := hX
    apply h5 u hu
    refine ⟨(phaseRadialContact (page u)
      (hamiltonianVectorField M.modelHamiltonian (page u)))⁻¹ • w, ?_⟩
    rw [map_smul, hw]
  · rw [h6, htr, htrace]
  · -- returns of the Reeb flow at unbounded times are returns of the model flow
    intro y hy
    have hy' : (y : Phase) ∉ Set.range
        (fun t : ℝ => ((ψ t Γ'.point : ConvexModelState M) : Phase)) := by
      rwa [htr, htrace]
    obtain ⟨hfwd, hbwd⟩ := h8 y hy'
    obtain ⟨ey, -, hey⟩ := reeb_reparam M D ψ hψ y
    have hflow : ∀ t, D.flow (ey.symm t) y = ψ t y := fun t => by
      rw [← hey, OrderIso.apply_symm_apply]
    constructor
    · intro R
      obtain ⟨t, hRt, u, hu, hor⟩ := hfwd (ey R)
      refine ⟨ey.symm t, ?_, u, hu, ?_⟩
      · have := ey.symm.strictMono hRt
        rwa [OrderIso.symm_apply_apply] at this
      · rw [hflow]; exact hor
    · intro R
      obtain ⟨t, htR, u, hu, hor⟩ := hbwd (ey R)
      refine ⟨ey.symm t, ?_, u, hu, ?_⟩
      · have := ey.symm.strictMono htR
        rwa [OrderIso.symm_apply_apply] at this
      · rw [hflow]; exact hor
