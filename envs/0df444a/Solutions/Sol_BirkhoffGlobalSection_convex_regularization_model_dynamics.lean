-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_regularization_model_dynamics
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T01:53:10.697621+00:00
-- url     : https://prove2.me/submissions/b6f9337f-bf11-44b1-b204-e1b2359cec46

import Definitions.Def_BirkhoffGlobalSection_ConvexModelDynamics
import Mathlib.Dynamics.Flow
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse

open Set Filter MeasureTheory
open scoped Topology

namespace FlowTimeChange
variable {S : Type*} [TopologicalSpace S]

lemma continuous_orderIso_symm (C : S → (ℝ ≃o ℝ))
    (hC : ∀ t, Continuous (fun s => C s t)) :
    Continuous (fun p : ℝ × S => (C p.2).symm p.1) := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  constructor
  · convert isOpen_lt ((hC a).comp continuous_snd) continuous_fst using 1
    ext p
    exact (C p.2).lt_symm_apply
  · convert isOpen_lt continuous_fst ((hC a).comp continuous_snd) using 1
    ext p
    exact (C p.2).symm_apply_lt

variable (φ : Flow ℝ S) (τ : S → ℝ) (hτ : Continuous τ)

noncomputable def clock (s : S) (t : ℝ) : ℝ := ∫ u in 0..t, τ (φ u s)

include hτ

lemma clock_deriv (s : S) (t : ℝ) : HasDerivAt (clock φ τ s) (τ (φ t s)) t := by
  have h : Continuous (fun u : ℝ => τ (φ u s)) := hτ.comp (φ.continuous continuous_id continuous_const)
  exact intervalIntegral.integral_hasDerivAt_right (h.intervalIntegrable _ _)
    h.aestronglyMeasurable.stronglyMeasurableAtFilter h.continuousAt

omit hτ in
@[simp] lemma clock_zero (s : S) : clock φ τ s 0 = 0 := by simp [clock]

lemma clock_continuous (t : ℝ) : Continuous (fun s => clock φ τ s t) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun s t => τ (φ t s))
    (hτ.comp (φ.continuous continuous_snd continuous_fst)) 0 t

lemma clock_add (s : S) (t u : ℝ) :
    clock φ τ s (t + u) = clock φ τ (φ u s) t + clock φ τ s u := by
  have h : Continuous (fun r : ℝ => τ (φ r s)) := hτ.comp (φ.continuous continuous_id continuous_const)
  unfold clock
  simp_rw [← φ.map_add]
  rw [show (∫ r in 0..t, τ (φ (r + u) s)) = ∫ r in u..t + u, τ (φ r s) from by
    simpa using intervalIntegral.integral_comp_add_right (fun r => τ (φ r s)) u (a := 0) (b := t)]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (h.intervalIntegrable 0 u) (h.intervalIntegrable u (t + u))).symm.trans (add_comm _ _)

variable (a : ℝ) (ha : 0 < a) (haτ : ∀ s, a ≤ τ s)

include a ha haτ

lemma clock_strictMono (s : S) : StrictMono (clock φ τ s) :=
  strictMono_of_hasDerivAt_pos (clock_deriv φ τ hτ s) (fun t => ha.trans_le (haτ (φ t s)))

lemma clock_surjective (s : S) : Function.Surjective (clock φ τ s) := by
  have hd := clock_deriv φ τ hτ s
  have hm : Monotone (fun t => clock φ τ s t - a * t) := by
    apply monotone_of_hasDerivAt_nonneg (fun t => (hd t).sub ((hasDerivAt_id t).const_mul a))
    intro t
    simpa using sub_nonneg.mpr (haτ (φ t s))
  have hp : ∀ t, 0 ≤ t → a * t ≤ clock φ τ s t := by
    intro t ht
    have := hm ht
    simpa using this
  have hn : ∀ t, t ≤ 0 → clock φ τ s t ≤ a * t := by
    intro t ht
    have := hm ht
    simpa using this
  apply (continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)).surjective
  · apply tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono (fun t ht => hp t ht))
    exact tendsto_id.const_mul_atTop ha
  · apply tendsto_atBot_mono' atBot ((eventually_le_atBot 0).mono (fun t ht => hn t ht))
    exact tendsto_id.const_mul_atBot ha

noncomputable def clockIso (s : S) : ℝ ≃o ℝ :=
  OrderIso.ofSurjective (OrderEmbedding.ofStrictMono (clock φ τ s) (clock_strictMono φ τ hτ a ha haτ s))
    (clock_surjective φ τ hτ a ha haτ s)

@[simp] lemma clockIso_apply (s : S) (t : ℝ) :
    clockIso φ τ hτ a ha haτ s t = clock φ τ s t := rfl

@[simp] lemma clockIso_zero (s : S) : clockIso φ τ hτ a ha haτ s 0 = 0 := by
  exact clock_zero φ τ s

lemma clockIso_deriv (s : S) (t : ℝ) :
    HasDerivAt (clockIso φ τ hτ a ha haτ s) (τ (φ t s)) t :=
  clock_deriv φ τ hτ s t

lemma clockIso_add (s : S) (t u : ℝ) :
    clockIso φ τ hτ a ha haτ s (t + u) =
      clockIso φ τ hτ a ha haτ (φ u s) t + clockIso φ τ hτ a ha haτ s u :=
  clock_add φ τ hτ s t u

@[simp] lemma clockIso_symm_zero (s : S) :
    (clockIso φ τ hτ a ha haτ s).symm 0 = 0 := by
  apply (clockIso φ τ hτ a ha haτ s).injective
  simp only [OrderIso.apply_symm_apply, clockIso_zero]

lemma clockIso_symm_continuous :
    Continuous (fun p : ℝ × S => (clockIso φ τ hτ a ha haτ p.2).symm p.1) := by
  apply continuous_orderIso_symm
  intro t
  exact clock_continuous φ τ hτ t

lemma clockIso_symm_deriv_zero (s : S) :
    HasDerivAt (clockIso φ τ hτ a ha haτ s).symm (τ s)⁻¹ 0 := by
  apply HasDerivAt.of_local_left_inverse (clockIso φ τ hτ a ha haτ s).symm.continuous.continuousAt
  · simpa only [clockIso_symm_zero, φ.map_zero_apply] using clockIso_deriv φ τ hτ a ha haτ s 0
  · exact ne_of_gt (ha.trans_le (haτ s))
  · exact Filter.Eventually.of_forall (clockIso φ τ hτ a ha haτ s).apply_symm_apply

noncomputable def flow : Flow ℝ S where
  toFun t s := φ ((clockIso φ τ hτ a ha haτ s).symm t) s
  cont' := φ.continuous (clockIso_symm_continuous φ τ hτ a ha haτ) continuous_snd
  map_zero' s := by simp only [clockIso_symm_zero, φ.map_zero_apply]
  map_add' t u s := by
    rw [← φ.map_add]
    congr 1
    apply (clockIso φ τ hτ a ha haτ s).injective
    rw [OrderIso.apply_symm_apply, clockIso_add]
    rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]

@[simp] lemma flow_apply (t : ℝ) (s : S) :
    flow φ τ hτ a ha haτ t s = φ ((clockIso φ τ hτ a ha haτ s).symm t) s := rfl

lemma flow_clock (s : S) (t : ℝ) :
    flow φ τ hτ a ha haτ (clockIso φ τ hτ a ha haτ s t) s = φ t s := by
  simp only [flow_apply, OrderIso.symm_apply_apply]

end FlowTimeChange


open scoped ContDiff Topology
open BirkhoffGlobalSection

namespace FlowTimeChange

/-- Conjugate a continuous flow by a homeomorphism of its state space. -/
def conjugate {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (H : S ≃ₜ T) (ψ : Flow ℝ S) : Flow ℝ T where
  toFun t y := H (ψ t (H.symm y))
  cont' := H.continuous.comp (ψ.continuous continuous_fst
    (H.symm.continuous.comp continuous_snd))
  map_add' t u y := by simp only [ψ.map_add, H.symm_apply_apply]
  map_zero' y := by simp only [ψ.map_zero_apply, H.apply_symm_apply]

end FlowTimeChange

/-- A uniformly positive regularization clock gives complete model Hamiltonian
motion by reparametrization and smooth conjugacy. -/
theorem solution (μ c : ℝ) (_hμ0 : 0 < μ) (_hμ1 : μ < 1)
    (_hc : belowFirstCriticalValue μ c)
    (M : ConvexRegularizationModel μ c)
    (a b : ℝ) (ha : 0 < a)
    (hclock : ∀ s ∈ leftEnergyComponent μ c,
      a ≤ M.timeScale s ∧ M.timeScale s ≤ b)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    Nonempty (ConvexModelDynamics M φ) := by
  let τ : LeftEnergyState μ c → ℝ := fun s => M.timeScale s
  have hτ : Continuous τ := M.timeScale_continuous.comp_continuous
    continuous_subtype_val (fun s => M.contains_component s.property)
  have haτ : ∀ s, a ≤ τ s := fun s => (hclock s s.property).1
  let C := FlowTimeChange.clockIso φ τ hτ a ha haτ
  let ψ := FlowTimeChange.flow φ τ hτ a ha haτ
  let H := M.stateHomeomorph
  let χ := FlowTimeChange.conjugate H ψ
  have hC0 : ∀ s, (C s).symm 0 = 0 :=
    FlowTimeChange.clockIso_symm_zero φ τ hτ a ha haτ
  refine ⟨⟨χ, ?_, C, ?_, ?_, ?_⟩⟩
  · intro y
    let s : LeftEnergyState μ c := H.symm y
    have hsy : M.toModel (s : Phase) = (y : Phase) :=
      congrArg Subtype.val (H.apply_symm_apply y)
    have hdt : DifferentiableAt ℝ M.toModel (s : Phase) :=
      (M.toModel_smooth.contDiffAt
        (M.source_open.mem_nhds (M.contains_component s.property))).differentiableAt
          (by simp)
    have hinv : HasDerivAt (C s).symm (τ s)⁻¹ 0 :=
      FlowTimeChange.clockIso_symm_deriv_zero φ τ hτ a ha haτ s
    have hcurve : HasDerivAt
        (fun t : ℝ => ((φ ((C s).symm t) s : LeftEnergyState μ c) : Phase))
        ((τ s)⁻¹ • hamiltonianVectorField (leviCivitaHamiltonian μ c) (s : Phase)) 0 :=
      (hφ s).scomp_of_eq 0 hinv (hC0 s).symm
    have hcomp := hdt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve
      (by simp only [hC0 s, φ.map_zero_apply])
    have hvec : fderiv ℝ M.toModel (s : Phase)
        ((τ s)⁻¹ • hamiltonianVectorField (leviCivitaHamiltonian μ c) (s : Phase)) =
        hamiltonianVectorField M.modelHamiltonian (y : Phase) := by
      rw [map_smul, M.vectorField _ s.property]
      change (τ s)⁻¹ • (τ s • hamiltonianVectorField M.modelHamiltonian
        (M.toModel (s : Phase))) = _
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt (ha.trans_le (haτ s))), one_smul, hsy]
    rw [hvec] at hcomp
    exact hcomp
  · intro s
    exact FlowTimeChange.clockIso_zero φ τ hτ a ha haτ s
  · intro s t
    exact FlowTimeChange.clockIso_deriv φ τ hτ a ha haτ s t
  · intro s t
    change M.toModel ((ψ (C s t) (H.symm (M.mapState s)) : LeftEnergyState μ c) : Phase) = _
    have hh : H.symm (M.mapState s) = s := H.symm_apply_apply s
    rw [hh]
    change M.toModel ((FlowTimeChange.flow φ τ hτ a ha haτ
      (FlowTimeChange.clockIso φ τ hτ a ha haτ s t) s : LeftEnergyState μ c) : Phase) = _
    rw [FlowTimeChange.flow_clock]
