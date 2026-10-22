-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_complete_normalized_flow_of_model_fields
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T08:02:22.08319+00:00
-- url     : https://prove2.me/submissions/f780393c-093c-4e50-b81f-409c5a0e503f

import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_characteristic_normalization

open Set
open scoped Topology ContDiff

/-- A positive continuous rate on a nonempty compact set has positive uniform
lower and finite upper bounds. -/
private theorem compact_positive_rate_bounds {S : Type*} [TopologicalSpace S]
    (K : Set S) (hK : IsCompact K) (hne : K.Nonempty)
    (r : S → ℝ) (hr : ContinuousOn r K) (hpos : ∀ x ∈ K, 0 < r x) :
    ∃ m M : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ r x ∧ r x ≤ M := by
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne hr
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne hr
  exact ⟨r a, r b, hpos a ha, fun x hx => ⟨hmin hx, hmax hx⟩⟩

/-- Integrating a continuous rate bounded below by a positive constant gives
a complete increasing clock, with its actual derivative and a quantitative
growth bound. No surjectivity or clock is assumed. -/
private theorem complete_positive_clock (r : ℝ → ℝ) (hr : Continuous r)
    (m : ℝ) (hm : 0 < m) (hbound : ∀ t, m ≤ r t) :
    ∃ clock : ℝ ≃o ℝ,
      clock 0 = 0 ∧
      (∀ t, HasDerivAt clock (r t) t) ∧
      (∀ a b : ℝ, a ≤ b → m * (b - a) ≤ clock b - clock a) ∧
      (∀ t, clock t = ∫ s in (0 : ℝ)..t, r s) := by
  let tau : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, r s
  have hd (t : ℝ) : HasDerivAt tau (r t) t :=
    intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable 0 t)
      hr.aestronglyMeasurable.stronglyMeasurableAtFilter hr.continuousAt
  have hzero : tau 0 = 0 := by simp [tau]
  have hstrict : StrictMono tau :=
    strictMono_of_hasDerivAt_pos hd (fun t => lt_of_lt_of_le hm (hbound t))
  have hmono : Monotone (fun t => tau t - m * t) := by
    apply monotone_of_hasDerivAt_nonneg
      (fun t => (hd t).sub ((hasDerivAt_id t).const_mul m))
    intro t
    simpa only [Pi.zero_apply, mul_one] using sub_nonneg.mpr (hbound t)
  have hgrowth (a b : ℝ) (hab : a ≤ b) : m * (b - a) ≤ tau b - tau a := by
    have h := hmono hab
    dsimp at h
    nlinarith
  have hsurj : Function.Surjective tau := by
    intro z
    let a := min 0 (z / m)
    let b := max 0 (z / m)
    have ha : a ≤ 0 := min_le_left _ _
    have hb : 0 ≤ b := le_max_left _ _
    have hdiv : m * (z / m) = z := by field_simp [hm.ne']
    have hma : m * a ≤ z := by
      have h := mul_le_mul_of_nonneg_left (min_le_right 0 (z / m)) hm.le
      simpa only [hdiv] using h
    have hmb : z ≤ m * b := by
      have h := mul_le_mul_of_nonneg_left (le_max_right 0 (z / m)) hm.le
      simpa only [hdiv] using h
    have hza : tau a ≤ z := by
      have h := hgrowth a 0 ha
      rw [hzero] at h
      nlinarith
    have hzb : z ≤ tau b := by
      have h := hgrowth 0 b hb
      rw [hzero] at h
      nlinarith
    have hcont : Continuous tau := continuous_iff_continuousAt.mpr
      (fun t => (hd t).continuousAt)
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (ha.trans hb)
      hcont.continuousOn ⟨hza, hzb⟩
    exact ⟨t, ht⟩
  let clock := StrictMono.orderIsoOfSurjective tau hstrict hsurj
  refine ⟨clock, hzero, hd, hgrowth, ?_⟩
  intro t
  rfl

/-- A complete continuous trajectory in a compact set acquires a complete
positive clock from any continuous positive rate on that set. -/
private theorem compact_trajectory_positive_clock {S : Type*} [TopologicalSpace S]
    (K : Set S) (hK : IsCompact K) (r : S → ℝ) (hr : ContinuousOn r K)
    (hpos : ∀ x ∈ K, 0 < r x) (y : ℝ → S) (hy : Continuous y)
    (hyK : ∀ t, y t ∈ K) :
    ∃ clock : ℝ ≃o ℝ,
      clock 0 = 0 ∧ (∀ t, HasDerivAt clock (r (y t)) t) ∧
      (∀ t, clock t = ∫ s in (0 : ℝ)..t, r (y s)) := by
  obtain ⟨m, M, hm, hbounds⟩ :=
    compact_positive_rate_bounds K hK ⟨y 0, hyK 0⟩ r hr hpos
  obtain ⟨clock, hz, hd, _, hi⟩ := complete_positive_clock (fun t => r (y t))
    (hr.comp_continuous hy hyK) m hm (fun t => (hbounds (y t) (hyK t)).1)
  exact ⟨clock, hz, hd, hi⟩

/-- The actual contact pairing along every complete convex-model trajectory
defines a complete Reeb clock, provided boundary contact positivity holds.
No pre-existing model-to-Reeb clock is assumed. -/
private theorem convex_model_contact_clock {μ c : ℝ}
    (M : BirkhoffGlobalSection.ConvexRegularizationModel μ c)
    {φ : Flow ℝ (BirkhoffGlobalSection.LeftEnergyState μ c)}
    (D : BirkhoffGlobalSection.ConvexModelDynamics M φ)
    (hcontact : ∀ y ∈ frontier M.body,
      0 < BirkhoffGlobalSection.phaseRadialContact y
        (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian y))
    (s : BirkhoffGlobalSection.ConvexModelState M) :
    ∃ clock : ℝ ≃o ℝ,
      clock 0 = 0 ∧
      (∀ t, HasDerivAt clock
        (BirkhoffGlobalSection.phaseRadialContact (D.flow t s)
          (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (D.flow t s))) t) ∧
      (∀ t, clock t = ∫ v in (0 : ℝ)..t,
        BirkhoffGlobalSection.phaseRadialContact (D.flow v s)
          (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (D.flow v s))) := by
  let r : BirkhoffGlobalSection.Phase → ℝ := fun y =>
    BirkhoffGlobalSection.phaseRadialContact y
      (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian y)
  have htarget : ∀ y ∈ frontier M.body, y ∈ M.target := by
    intro y hy
    rw [← M.image_frontier] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact M.toModel_mapsTo (M.contains_component hx)
  have hr : ContinuousOn r (frontier M.body) := by
    have hderiv : ContinuousOn (fun y => fderiv ℝ M.modelHamiltonian y y / 2)
        (frontier M.body) := by
      intro y hy
      have hf := M.model_smooth.contDiffAt (M.target_open.mem_nhds (htarget y hy))
      exact (((hf.fderiv_right (m := 0) (by simp)).continuousAt.clm_apply
        continuousAt_id).div_const 2).continuousWithinAt
    apply hderiv.congr
    intro y hy
    exact (BirkhoffGlobalSection.hamiltonian_radial_characteristic_normalization
      M.modelHamiltonian y (hcontact y hy)).2.2.2
  have hK : IsCompact (frontier M.body) :=
    M.body_compact.of_isClosed_subset isClosed_frontier (by
      simpa only [M.body_compact.isClosed.closure_eq] using
        (frontier_subset_closure : frontier M.body ⊆ closure M.body))
  exact compact_trajectory_positive_clock (frontier M.body) hK r hr hcontact
    (fun t => (D.flow t s : BirkhoffGlobalSection.Phase))
    (continuous_subtype_val.comp (D.flow.continuous continuous_id continuous_const))
    (fun t => (D.flow t s).property)

/-- The derivative of the inverse positive clock is the reciprocal rate. -/
private theorem positive_clock_inverse_derivative (clock : ℝ ≃o ℝ) (r : ℝ → ℝ)
    (hd : ∀ t, HasDerivAt clock (r t) t) (hpos : ∀ t, 0 < r t) (t : ℝ) :
    HasDerivAt clock.symm (r (clock.symm t))⁻¹ t := by
  exact (hd (clock.symm t)).of_local_left_inverse clock.symm.continuous.continuousAt
    (hpos (clock.symm t)).ne' (Filter.Eventually.of_forall clock.apply_symm_apply)

/-- Actual velocity after changing to the complete positive clock. -/
private theorem positive_clock_reparametrized_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (clock : ℝ ≃o ℝ) (r : ℝ → ℝ) (y X : ℝ → E)
    (hd : ∀ t, HasDerivAt clock (r t) t) (hpos : ∀ t, 0 < r t)
    (hy : ∀ t, HasDerivAt y (X t) t) (t : ℝ) :
    HasDerivAt (fun v => y (clock.symm v))
      ((r (clock.symm t))⁻¹ • X (clock.symm t)) t := by
  exact (hy (clock.symm t)).scomp t
    (positive_clock_inverse_derivative clock r hd hpos t)

/-- Each complete model trajectory is reparametrized for all real times with
the normalized Hamiltonian velocity X_H/alpha(X_H). This does not yet assert
joint continuity or the action law for a family of reparametrized curves. -/
private theorem convex_model_normalized_trajectory {μ c : ℝ}
    (M : BirkhoffGlobalSection.ConvexRegularizationModel μ c)
    {φ : Flow ℝ (BirkhoffGlobalSection.LeftEnergyState μ c)}
    (D : BirkhoffGlobalSection.ConvexModelDynamics M φ)
    (hcontact : ∀ y ∈ frontier M.body,
      0 < BirkhoffGlobalSection.phaseRadialContact y
        (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian y))
    (s : BirkhoffGlobalSection.ConvexModelState M) :
    ∃ clock : ℝ ≃o ℝ, clock 0 = 0 ∧
      ∀ t : ℝ,
        let y : BirkhoffGlobalSection.Phase := D.flow (clock.symm t) s
        HasDerivAt (fun v => (D.flow (clock.symm v) s : BirkhoffGlobalSection.Phase))
          ((BirkhoffGlobalSection.phaseRadialContact y
            (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
              BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian y) t := by
  obtain ⟨clock, hz, hd, _⟩ := convex_model_contact_clock M D hcontact s
  have hy (t : ℝ) :
      HasDerivAt (fun v => (D.flow v s : BirkhoffGlobalSection.Phase))
        (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (D.flow t s)) t := by
    have h := (D.hamiltonian (D.flow t s)).scomp_of_eq t
      ((hasDerivAt_id t).sub_const t) (by simp)
    have h' := h.congr_of_eventuallyEq
      (f₁ := fun v : ℝ => (D.flow v s : BirkhoffGlobalSection.Phase))
      (Filter.Eventually.of_forall (fun v => by
        simp only [Function.comp_apply, id, ← D.flow.map_add, sub_add_cancel]))
    simpa only [one_smul] using h'
  refine ⟨clock, hz, ?_⟩
  intro t
  exact positive_clock_reparametrized_derivative clock
    (fun v => BirkhoffGlobalSection.phaseRadialContact (D.flow v s)
      (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (D.flow v s)))
    (fun v => (D.flow v s : BirkhoffGlobalSection.Phase))
    (fun v => BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (D.flow v s))
    hd (fun v => hcontact _ (D.flow v s).property) hy t

/-- Composing the constructed model-contact clock with the existing LC-model
clock gives the complete LC-to-contact clock with the product of the two
actual time factors. -/
private theorem convex_model_lc_contact_clock {μ c : ℝ}
    (M : BirkhoffGlobalSection.ConvexRegularizationModel μ c)
    {φ : Flow ℝ (BirkhoffGlobalSection.LeftEnergyState μ c)}
    (D : BirkhoffGlobalSection.ConvexModelDynamics M φ)
    (hcontact : ∀ y ∈ frontier M.body,
      0 < BirkhoffGlobalSection.phaseRadialContact y
        (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian y))
    (s : BirkhoffGlobalSection.LeftEnergyState μ c) :
    ∃ clock : ℝ ≃o ℝ, clock 0 = 0 ∧
      ∀ t : ℝ, HasDerivAt clock
        (M.timeScale (φ t s) *
          BirkhoffGlobalSection.phaseRadialContact (M.toModel (φ t s))
            (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian
              (M.toModel (φ t s)))) t := by
  obtain ⟨modelClock, hz, hd, _⟩ := convex_model_contact_clock M D hcontact (M.mapState s)
  let clock := (D.clock s).trans modelClock
  refine ⟨clock, ?_, ?_⟩
  · change modelClock (D.clock s 0) = 0
    rw [D.clock_zero, hz]
  · intro t
    have h := (hd (D.clock s t)).comp t (D.clock_deriv s t)
    change HasDerivAt (fun v => modelClock (D.clock s v)) _ t
    convert h using 1 <;> first | rfl | (rw [D.conjugacy]; ring)

/-- Jointly continuous positive clock families have jointly continuous
inverses. The proof uses inverse images of the generating open rays. -/
private theorem continuous_inverse_clock_family {S : Type*} [TopologicalSpace S]
    (c : S → (ℝ ≃o ℝ)) (hc : Continuous (fun p : ℝ × S => c p.2 p.1)) :
    Continuous (fun p : ℝ × S => (c p.2).symm p.1) := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  constructor
  · have h := isOpen_lt
      (hc.comp ((continuous_const : Continuous (fun _ : ℝ × S => a)).prodMk continuous_snd))
      continuous_fst
    convert h using 1
    ext p
    exact (c p.2).lt_symm_apply
  · have h := isOpen_lt continuous_fst
      (hc.comp ((continuous_const : Continuous (fun _ : ℝ × S => a)).prodMk continuous_snd))
    convert h using 1
    ext p
    exact (c p.2).symm_apply_lt

/-- A continuous positive time factor with a uniform lower bound constructs
a complete jointly continuous time-changed flow. The integral clock satisfies
the cocycle identity; no action law or continuity of its inverse is assumed. -/
private theorem positive_time_change_flow {S : Type*} [TopologicalSpace S]
    (flow : Flow ℝ S) (r : S → ℝ) (hr : Continuous r)
    (m : ℝ) (hm : 0 < m) (hbound : ∀ s, m ≤ r s) :
    ∃ c : S → (ℝ ≃o ℝ), ∃ newFlow : Flow ℝ S,
      (∀ s, c s 0 = 0) ∧
      (∀ s t, HasDerivAt (c s) (r (flow t s)) t) ∧
      (∀ t s, newFlow t s = flow ((c s).symm t) s) ∧
      (∀ s a b, c s (a + b) = c s b + c (flow b s) a) ∧
      Continuous (fun p : ℝ × S => c p.2 p.1) := by
  classical
  have hex (s : S) := complete_positive_clock (fun t => r (flow t s))
    (hr.comp (flow.continuous continuous_id continuous_const)) m hm
    (fun t => hbound (flow t s))
  let c : S → (ℝ ≃o ℝ) := fun s => (hex s).choose
  have hz (s : S) : c s 0 = 0 := (hex s).choose_spec.1
  have hd (s : S) (t : ℝ) : HasDerivAt (c s) (r (flow t s)) t :=
    (hex s).choose_spec.2.1 t
  have hi (s : S) (t : ℝ) : c s t = ∫ v in (0 : ℝ)..t, r (flow v s) :=
    (hex s).choose_spec.2.2.2 t
  have hc : Continuous (fun p : ℝ × S => c p.2 p.1) := by
    have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := (0 : ℝ))
      (μ := MeasureTheory.volume)
      (f := fun p : ℝ × S => fun v : ℝ => r (flow v p.2))
      (hr.comp (flow.continuous continuous_snd (continuous_snd.comp continuous_fst)))
      continuous_fst
    convert h using 1
    funext p
    exact hi p.2 p.1
  have hinv := continuous_inverse_clock_family c hc
  have hcocycle (s : S) (a b : ℝ) : c s (a + b) = c s b + c (flow b s) a := by
    let g : ℝ → ℝ := fun v => c s (v + b) - c (flow b s) v
    have hg (v : ℝ) : HasDerivAt g 0 v := by
      have h := ((hd s (v + b)).comp v ((hasDerivAt_id v).add_const b)).sub
        (hd (flow b s) v)
      convert h using 1 <;> first | rfl | (simp only [flow.map_add, mul_one, sub_self])
    have heq := is_const_of_deriv_eq_zero (fun v => (hg v).differentiableAt)
      (fun v => (hg v).deriv) a 0
    dsimp [g] at heq
    rw [zero_add, hz] at heq
    linarith
  have hzInv (s : S) : (c s).symm 0 = 0 := by
    have h := (c s).symm_apply_apply 0
    rw [hz] at h
    exact h
  let newFlow : Flow ℝ S := {
    toFun := fun t s => flow ((c s).symm t) s
    cont' := flow.continuous hinv continuous_snd
    map_zero' := fun s => by simp only [hzInv, flow.map_zero, id_eq]
    map_add' := fun a b s => by
      have ht : (c s).symm (a + b) =
          (c (flow ((c s).symm b) s)).symm a + (c s).symm b := by
        apply (c s).injective
        rw [OrderIso.apply_symm_apply, hcocycle, OrderIso.apply_symm_apply,
          OrderIso.apply_symm_apply]
        exact add_comm a b
      rw [ht, flow.map_add]
  }
  exact ⟨c, newFlow, hz, hd, fun _ _ => rfl, hcocycle, hc⟩

/-- Compactness supplies the uniform bound needed for a genuine time-changed
flow, including when the state space is empty. -/
private theorem compact_positive_time_change_flow {S : Type*} [TopologicalSpace S] [CompactSpace S]
    (flow : Flow ℝ S) (r : S → ℝ) (hr : Continuous r) (hpos : ∀ s, 0 < r s) :
    ∃ c : S → (ℝ ≃o ℝ), ∃ newFlow : Flow ℝ S,
      (∀ s, c s 0 = 0) ∧
      (∀ s t, HasDerivAt (c s) (r (flow t s)) t) ∧
      (∀ t s, newFlow t s = flow ((c s).symm t) s) ∧
      (∀ s a b, c s (a + b) = c s b + c (flow b s) a) ∧
      Continuous (fun p : ℝ × S => c p.2 p.1) := by
  classical
  have hb : ∃ m : ℝ, 0 < m ∧ ∀ s, m ≤ r s := by
    by_cases hne : Nonempty S
    · obtain ⟨s⟩ := hne
      obtain ⟨m, _, hm, h⟩ := compact_positive_rate_bounds univ isCompact_univ
        ⟨s, mem_univ s⟩ r hr.continuousOn (fun s _ => hpos s)
      exact ⟨m, hm, fun s => (h s (mem_univ s)).1⟩
    · exact ⟨1, by norm_num, fun s => False.elim (hne ⟨s⟩)⟩
  obtain ⟨m, hm, hb⟩ := hb
  exact positive_time_change_flow flow r hr m hm hb

/-- Smoothness of the Hamiltonian makes its radial contact pairing continuous;
this continuity statement needs no contact-positivity assumption. -/
private theorem hamiltonian_radial_contact_continuousAt
    (F : BirkhoffGlobalSection.Phase → ℝ) (y : BirkhoffGlobalSection.Phase)
    (hF : ContDiffAt ℝ ∞ F y) :
    ContinuousAt (fun x => BirkhoffGlobalSection.phaseRadialContact x
      (BirkhoffGlobalSection.hamiltonianVectorField F x)) y := by
  have hD := (hF.fderiv_right (m := 0) (by simp)).continuousAt
  have hcoord (i : Fin 4) :
      ContinuousAt (fun x => BirkhoffGlobalSection.partialDerivative F x i) y :=
    hD.clm_apply continuousAt_const
  have hX : ContinuousAt (BirkhoffGlobalSection.hamiltonianVectorField F) y := by
    apply continuousAt_pi.mpr
    intro i
    fin_cases i <;> simp [BirkhoffGlobalSection.hamiltonianVectorField] <;>
      first | exact hcoord 2 | exact hcoord 3 | exact (hcoord 0).neg | exact (hcoord 1).neg
  have hAlpha : Continuous (fun p : BirkhoffGlobalSection.Phase × BirkhoffGlobalSection.Phase =>
      BirkhoffGlobalSection.phaseRadialContact p.1 p.2) := by
    unfold BirkhoffGlobalSection.phaseRadialContact BirkhoffGlobalSection.phaseSymplecticForm
    fun_prop
  exact hAlpha.continuousAt.comp (continuousAt_id.prodMk hX)

/-- The radial contact rate is continuous on the compact model state space. -/
private theorem convex_model_contact_rate_continuous {μ c : ℝ}
    (M : BirkhoffGlobalSection.ConvexRegularizationModel μ c) :
    Continuous (fun s : BirkhoffGlobalSection.ConvexModelState M =>
      BirkhoffGlobalSection.phaseRadialContact s
        (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian s)) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have htarget : (s : BirkhoffGlobalSection.Phase) ∈ M.target := by
    have hs : (s : BirkhoffGlobalSection.Phase) ∈ M.toModel ''
        BirkhoffGlobalSection.leftEnergyComponent μ c := by
      rw [M.image_frontier]
      exact s.property
    obtain ⟨x, hx, hxs⟩ := hs
    rw [← hxs]
    exact M.toModel_mapsTo (M.contains_component hx)
  have hF := M.model_smooth.contDiffAt (M.target_open.mem_nhds htarget)
  exact (hamiltonian_radial_contact_continuousAt M.modelHamiltonian s hF).comp
    continuous_subtype_val.continuousAt

/-- The constructed family defines a genuine complete continuous normalized
model flow. Positivity of the boundary pairing remains the only new geometric
input; cocycle and inverse continuity are proved by the clock construction. -/
private theorem convex_model_complete_contact_flow {μ c : ℝ}
    (M : BirkhoffGlobalSection.ConvexRegularizationModel μ c)
    {φ : Flow ℝ (BirkhoffGlobalSection.LeftEnergyState μ c)}
    (D : BirkhoffGlobalSection.ConvexModelDynamics M φ)
    (hcontact : ∀ y ∈ frontier M.body,
      0 < BirkhoffGlobalSection.phaseRadialContact y
        (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian y)) :
    ∃ c : BirkhoffGlobalSection.ConvexModelState M → (ℝ ≃o ℝ),
      ∃ newFlow : Flow ℝ (BirkhoffGlobalSection.ConvexModelState M),
        (∀ s, c s 0 = 0) ∧
        (∀ s t, HasDerivAt (c s)
          (BirkhoffGlobalSection.phaseRadialContact (D.flow t s)
            (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (D.flow t s))) t) ∧
        (∀ t s, newFlow t s = D.flow ((c s).symm t) s) ∧
        (∀ s a b, c s (a + b) = c s b + c (D.flow b s) a) ∧
        Continuous (fun p : ℝ × BirkhoffGlobalSection.ConvexModelState M => c p.2 p.1) := by
  have hK : IsCompact (frontier M.body) :=
    M.body_compact.of_isClosed_subset isClosed_frontier (by
      simpa only [M.body_compact.isClosed.closure_eq] using
        (frontier_subset_closure : frontier M.body ⊆ closure M.body))
  let : CompactSpace (BirkhoffGlobalSection.ConvexModelState M) :=
    isCompact_iff_compactSpace.mp hK
  exact compact_positive_time_change_flow D.flow
    (fun s => BirkhoffGlobalSection.phaseRadialContact s
      (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian s))
    (convex_model_contact_rate_continuous M) (fun s => hcontact s s.property)

/-- The derivative-at-zero field of the model flow determines its velocity
at every time by the flow action law. -/
private theorem convex_model_hamiltonian_trajectory_derivative {μ c : ℝ}
    (M : BirkhoffGlobalSection.ConvexRegularizationModel μ c)
    {φ : Flow ℝ (BirkhoffGlobalSection.LeftEnergyState μ c)}
    (D : BirkhoffGlobalSection.ConvexModelDynamics M φ)
    (s : BirkhoffGlobalSection.ConvexModelState M) (t : ℝ) :
    HasDerivAt (fun v => (D.flow v s : BirkhoffGlobalSection.Phase))
      (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (D.flow t s)) t := by
  have h := (D.hamiltonian (D.flow t s)).scomp_of_eq t
    ((hasDerivAt_id t).sub_const t) (by simp)
  have h' := h.congr_of_eventuallyEq
    (f₁ := fun v : ℝ => (D.flow v s : BirkhoffGlobalSection.Phase))
    (Filter.Eventually.of_forall (fun v => by
      simp only [Function.comp_apply, id, ← D.flow.map_add, sub_add_cancel]))
  simpa only [one_smul] using h'

/-- The genuine jointly continuous model-contact flow has the normalized
Hamiltonian velocity at all real times. -/
private theorem convex_model_complete_normalized_flow {μ c : ℝ}
    (M : BirkhoffGlobalSection.ConvexRegularizationModel μ c)
    {φ : Flow ℝ (BirkhoffGlobalSection.LeftEnergyState μ c)}
    (D : BirkhoffGlobalSection.ConvexModelDynamics M φ)
    (hcontact : ∀ y ∈ frontier M.body,
      0 < BirkhoffGlobalSection.phaseRadialContact y
        (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian y)) :
    ∃ newFlow : Flow ℝ (BirkhoffGlobalSection.ConvexModelState M),
      ∀ s t,
        HasDerivAt (fun v => (newFlow v s : BirkhoffGlobalSection.Phase))
          ((BirkhoffGlobalSection.phaseRadialContact (newFlow t s)
            (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (newFlow t s)))⁻¹ •
              BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (newFlow t s)) t := by
  obtain ⟨c, newFlow, _, hd, heq, _, _⟩ := convex_model_complete_contact_flow M D hcontact
  refine ⟨newFlow, ?_⟩
  intro s t
  have h := positive_clock_reparametrized_derivative (c s)
    (fun v => BirkhoffGlobalSection.phaseRadialContact (D.flow v s)
      (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (D.flow v s)))
    (fun v => (D.flow v s : BirkhoffGlobalSection.Phase))
    (fun v => BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (D.flow v s))
    (hd s) (fun v => hcontact _ (D.flow v s).property)
    (convex_model_hamiltonian_trajectory_derivative M D s) t
  have h' := h.congr_of_eventuallyEq
    (f₁ := fun v => (newFlow v s : BirkhoffGlobalSection.Phase))
    (Filter.Eventually.of_forall (fun v => congrArg Subtype.val (heq v s)))
  apply h'.congr_deriv
  rw [heq]

/-- The published model coorientation theorem supplies contact positivity. -/
theorem solution {μ c : ℝ}
    (M : BirkhoffGlobalSection.ConvexRegularizationModel μ c)
    {φ : Flow ℝ (BirkhoffGlobalSection.LeftEnergyState μ c)}
    (D : BirkhoffGlobalSection.ConvexModelDynamics M φ)
 :
    ∃ newFlow : Flow ℝ (BirkhoffGlobalSection.ConvexModelState M),
      ∀ s t,
        HasDerivAt (fun v => (newFlow v s : BirkhoffGlobalSection.Phase))
          ((BirkhoffGlobalSection.phaseRadialContact (newFlow t s)
            (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (newFlow t s)))⁻¹ •
              BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (newFlow t s)) t := by
  exact convex_model_complete_normalized_flow M D
    (BirkhoffGlobalSection.convex_model_boundary_contact_positive M)
