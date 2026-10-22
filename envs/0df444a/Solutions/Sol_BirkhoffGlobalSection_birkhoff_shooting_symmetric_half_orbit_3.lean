-- Prove2me | solution 3 for BirkhoffGlobalSection.birkhoff_shooting_symmetric_half_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T19:03:50.937313+00:00
-- url     : https://prove2.me/submissions/7a979cff-c480-4118-96b7-20c00b1ab48c

import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_shooting_family_rest
import Definitions.Def_BirkhoffGlobalSection
import Definitions.Def_BirkhoffShootingCoordinates
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic
import Definitions.Def_BirkhoffShootingArcs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.ExtendFrom
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_near_shooting_family_weak
import Theorems.Thm_BirkhoffGlobalSection_leviCivita_flow_antipodally_equivariant
import Theorems.Thm_PlanarTopology_interlaced_arcs_in_rectangle
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Order.Monotone.Union

open BirkhoffGlobalSection Set Filter Topology Function

-- ===== Solutions.Abstract =====
section Abstract

variable {X : Type*} [TopologicalSpace X]

-- ===== Solutions.CM29 =====
/-! Birkhoff's identity (59): the angular momentum about the primary along far arcs. -/

-- ===== Solutions.CM38 =====
lemma seg_coords {p q z : ℝ × ℝ} (hz : z ∈ range (Path.segment p q)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ z.1 = p.1 + θ * (q.1 - p.1) ∧ z.2 = p.2 + θ * (q.2 - p.2) := by
  rw [Path.range_segment] at hz
  obtain ⟨u, v, hu, hv, huv, rfl⟩ := hz
  refine ⟨v, hv, by linarith, ?_, ?_⟩ <;> simp <;> rw [show u = 1 - v by linarith] <;> ring

/-- A path on `[-1,1]` from a function continuous there. -/
def toPath (Γ : ℝ → ℝ × ℝ) (hΓ : ContinuousOn Γ (Icc (-1) 1)) : Path (Γ (-1)) (Γ 1) where
  toFun t := Γ (2 * (t : ℝ) - 1)
  continuous_toFun := hΓ.comp_continuous (by fun_prop) (fun t =>
    ⟨by linarith [t.2.1], by linarith [t.2.2]⟩)
  source' := by simp
  target' := by norm_num

lemma toPath_range {Γ : ℝ → ℝ × ℝ} {hΓ : ContinuousOn Γ (Icc (-1) 1)} {z : ℝ × ℝ}
    (hz : z ∈ range (toPath Γ hΓ)) : ∃ s ∈ Icc (-1 : ℝ) 1, Γ s = z := by
  obtain ⟨t, rfl⟩ := hz
  exact ⟨2 * (t : ℝ) - 1, ⟨by linarith [t.2.1], by linarith [t.2.2]⟩, rfl⟩

lemma extend_mem_range {x y : ℝ × ℝ} (γ : Path x y) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    γ.extend ((s + 1) / 2) ∈ range γ := by
  rw [← Path.extend_range]; exact mem_range_self _



lemma jacobiH_velocity_form (μ : ℝ) (J : Phase) :
    jacobiHamiltonian μ J =
      ((J 2 - J 1) ^ 2 + (J 3 + J 0) ^ 2) / 2 - (J 0 ^ 2 + J 1 ^ 2) / 2
        - (1 - μ) / Real.sqrt ((J 0 + μ) ^ 2 + J 1 ^ 2)
        - μ / Real.sqrt ((J 0 - 1 + μ) ^ 2 + J 1 ^ 2) := by
  unfold jacobiHamiltonian; ring

lemma lc_energy_identity (μ c : ℝ) (y : Phase) (hy : 0 < zNormSq y)
    (hDy : 0 < secondCollisionDistanceSq y) :
    jacobiHamiltonian μ (leviCivitaToJacobi μ y) =
      leviCivitaHamiltonian μ c y / zNormSq y - c := by
  have hr1 : Real.sqrt ((2 * (y 0 ^ 2 - y 1 ^ 2) - μ + μ) ^ 2 + (4 * y 0 * y 1) ^ 2) =
      2 * zNormSq y := by
    rw [show (2 * (y 0 ^ 2 - y 1 ^ 2) - μ + μ) ^ 2 + (4 * y 0 * y 1) ^ 2 =
      (2 * zNormSq y) ^ 2 by unfold zNormSq; ring]
    exact Real.sqrt_sq (by positivity)
  have hr2 : Real.sqrt ((2 * (y 0 ^ 2 - y 1 ^ 2) - μ - 1 + μ) ^ 2 + (4 * y 0 * y 1) ^ 2) =
      Real.sqrt (secondCollisionDistanceSq y) := by
    congr 1; unfold secondCollisionDistanceSq; ring
  have hSpos : 0 < Real.sqrt (secondCollisionDistanceSq y) := Real.sqrt_pos.2 hDy
  simp only [jacobiHamiltonian, leviCivitaToJacobi, leviCivitaPosition, leviCivitaMomentum,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  rw [hr1, hr2]
  unfold leviCivitaHamiltonian wNormSq
  have hy' : zNormSq y ≠ 0 := hy.ne'
  unfold zNormSq at hy' ⊢
  field_simp
  ring

/-- Two states on the regular energy level, both on the line `x_rel = 0` below the axis,
with the same shooting coordinates and positive horizontal velocity, agree up to sign. -/
lemma shooting_match (μ c : ℝ) (A B : Phase)
    (hA : A ∈ regularEnergyLocus μ c) (hB : B ∈ regularEnergyLocus μ c)
    (hA0 : relativePosition μ A 0 = 0) (hB0 : relativePosition μ B 0 = 0)
    (hAy : 0 < (shootingCoordinates μ A).2)
    (hvA : 0 < jacobiVelocity (leviCivitaToJacobi μ A) 0)
    (hvB : 0 < jacobiVelocity (leviCivitaToJacobi μ B) 0)
    (hAB : shootingCoordinates μ A = shootingCoordinates μ B) :
    B = A ∨ B = -A := by
  have e1 := congrArg Prod.fst hAB
  have e2 := congrArg Prod.snd hAB
  simp only [shootingCoordinates] at e1 e2 hAy
  simp only [relativePosition, leviCivitaPosition, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at hA0 hB0 e2 hAy
  -- positions
  have hA1 : A 1 = -A 0 := by
    have h : (A 1 + A 0) * (A 1 - A 0) = 0 := by linear_combination -hA0 / 2
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · have : A 1 = A 0 := by linarith
      rw [this] at hAy; nlinarith [sq_nonneg (A 0)]
  have hB1 : B 1 = -B 0 := by
    have h : (B 1 + B 0) * (B 1 - B 0) = 0 := by linear_combination -hB0 / 2
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · have : B 1 = B 0 := by linarith
      rw [this] at e2; nlinarith [sq_nonneg (B 0)]
  have hAne : A 0 ≠ 0 := by rintro h; rw [h] at hAy; simp at hAy
  have hsq : B 0 ^ 2 = A 0 ^ 2 := by rw [hA1, hB1] at e2; nlinarith
  have hzA : 0 < zNormSq A := by unfold zNormSq; positivity
  have hzB : 0 < zNormSq B := by
    unfold zNormSq; rw [hsq]; positivity
  -- energies
  have hHA := lc_energy_identity μ c A hzA hA.2
  have hHB := lc_energy_identity μ c B hzB hB.2
  rw [hA.1, zero_div] at hHA
  rw [hB.1, zero_div] at hHB
  set JA := leviCivitaToJacobi μ A with hJA
  set JB := leviCivitaToJacobi μ B with hJB
  have q0A : JA 0 = 2 * (A 0 ^ 2 - A 1 ^ 2) - μ := by
    simp [hJA, leviCivitaToJacobi, leviCivitaPosition]
  have q1A : JA 1 = 4 * A 0 * A 1 := by simp [hJA, leviCivitaToJacobi, leviCivitaPosition]
  have q0B : JB 0 = 2 * (B 0 ^ 2 - B 1 ^ 2) - μ := by
    simp [hJB, leviCivitaToJacobi, leviCivitaPosition]
  have q1B : JB 1 = 4 * B 0 * B 1 := by simp [hJB, leviCivitaToJacobi, leviCivitaPosition]
  have hq0 : JB 0 = JA 0 := by rw [q0A, q0B]; linarith
  have hq1 : JB 1 = JA 1 := by rw [q1A, q1B]; linarith
  have hnorm : (JB 2 - JB 1) ^ 2 + (JB 3 + JB 0) ^ 2 = (JA 2 - JA 1) ^ 2 + (JA 3 + JA 0) ^ 2 := by
    rw [jacobiH_velocity_form] at hHA hHB
    rw [hq0, hq1] at hHB
    rw [hq0, hq1]
    linarith
  simp only [jacobiVelocity, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    at e1 hvA hvB
  rw [hnorm] at e1
  have hsqrt : 0 < Real.sqrt ((JA 2 - JA 1) ^ 2 + (JA 3 + JA 0) ^ 2) :=
    Real.sqrt_pos.2 (by positivity)
  have hv1 : JB 3 + JB 0 = JA 3 + JA 0 := by
    field_simp at e1; linarith
  have hv0 : JB 2 - JB 1 = JA 2 - JA 1 := by
    rw [hv1] at hnorm
    have : (JB 2 - JB 1) ^ 2 = (JA 2 - JA 1) ^ 2 := by linarith
    nlinarith
  have p0 : JB 2 = JA 2 := by linarith
  have p1 : JB 3 = JA 3 := by linarith
  -- momenta in Levi-Civita coordinates
  have p0A : JA 2 = (A 2 * A 0 - A 3 * A 1) / zNormSq A := by
    simp [hJA, leviCivitaToJacobi, leviCivitaMomentum]
  have p1A : JA 3 = (A 2 * A 1 + A 3 * A 0) / zNormSq A := by
    simp [hJA, leviCivitaToJacobi, leviCivitaMomentum]
  have p0B : JB 2 = (B 2 * B 0 - B 3 * B 1) / zNormSq B := by
    simp [hJB, leviCivitaToJacobi, leviCivitaMomentum]
  have p1B : JB 3 = (B 2 * B 1 + B 3 * B 0) / zNormSq B := by
    simp [hJB, leviCivitaToJacobi, leviCivitaMomentum]
  rw [p0A, p0B] at p0
  rw [p1A, p1B] at p1
  have hzz : zNormSq B = zNormSq A := by unfold zNormSq; rw [hA1, hB1]; linear_combination 2 * hsq
  rw [hzz] at p0 p1
  have hzA' := hzA.ne'
  rw [div_left_inj' hzA', hA1, hB1] at p0 p1
  -- p0 : B2 B0 + B3 B0 = A2 A0 + A3 A0 ; p1 : -B2 B0 + B3 B0 = -A2 A0 + A3 A0
  have s1 : B 0 * (B 2 + B 3) = A 0 * (A 2 + A 3) := by linarith
  have s2 : B 0 * (B 3 - B 2) = A 0 * (A 3 - A 2) := by linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · left
    have hB0ne : B 0 ≠ 0 := by rw [h]; exact hAne
    have t1 : B 2 + B 3 = A 2 + A 3 := by
      rw [h] at s1; exact mul_left_cancel₀ hAne s1
    have t2 : B 3 - B 2 = A 3 - A 2 := by
      rw [h] at s2; exact mul_left_cancel₀ hAne s2
    funext i; fin_cases i
    · exact h
    · simp [hA1, hB1, h]
    · simp; linarith
    · simp; linarith
  · right
    have t1 : B 2 + B 3 = -(A 2 + A 3) := by
      rw [h] at s1
      have : A 0 * (-(B 2 + B 3)) = A 0 * (A 2 + A 3) := by linarith
      have := mul_left_cancel₀ hAne this; linarith
    have t2 : B 3 - B 2 = -(A 3 - A 2) := by
      rw [h] at s2
      have : A 0 * (-(B 3 - B 2)) = A 0 * (A 3 - A 2) := by linarith
      have := mul_left_cancel₀ hAne this; linarith
    funext i; fin_cases i
    · simpa using h
    · simp [hA1, hB1, h]
    · simp; linarith
    · simp; linarith

lemma relPos_neg' (μ : ℝ) (s : Phase) : relativePosition μ (-s) = relativePosition μ s := by
  funext i; fin_cases i <;> simp [relativePosition, leviCivitaPosition]

lemma mem_locus {μ c : ℝ} (x : LeftEnergyState μ c) : (x : Phase) ∈ regularEnergyLocus μ c :=
  connectedComponentIn_subset _ _ x.2

/-- Matching a near and a far crossing state with equal shooting coordinates gives the
symmetric half-orbit. -/
lemma finish_match (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (xN : LeftEnergyState μ c) (τN : ℝ) (hτN : 0 < τN)
    (hN1 : (xN : Phase) 1 = 0) (hN2 : (xN : Phase) 2 = 0) (hN0 : (xN : Phase) 0 ≠ 0)
    (hNlow : ∀ t ∈ Set.Ioo (-τN) 0,
      relativePosition μ ((φ t xN : LeftEnergyState μ c) : Phase) 1 < 0)
    (hNmono : StrictMonoOn
      (fun t : ℝ => relativePosition μ ((φ t xN : LeftEnergyState μ c) : Phase) 0)
      (Set.Icc (-τN) 0))
    (hNx : relativePosition μ ((φ (-τN) xN : LeftEnergyState μ c) : Phase) 0 = 0)
    (hNv : 0 < jacobiVelocity (leviCivitaToJacobi μ ((φ (-τN) xN : LeftEnergyState μ c) : Phase)) 0)
    (xF : LeftEnergyState μ c) (τF : ℝ) (hτF : 0 < τF)
    (hF0 : (xF : Phase) 0 = 0) (hF3 : (xF : Phase) 3 = 0) (hF1 : (xF : Phase) 1 ≠ 0)
    (hFlow : ∀ u ∈ Set.Ioo 0 τF,
      relativePosition μ ((φ u xF : LeftEnergyState μ c) : Phase) 1 < 0)
    (hFmono : StrictMonoOn
      (fun u : ℝ => relativePosition μ ((φ u xF : LeftEnergyState μ c) : Phase) 0)
      (Set.Icc 0 τF))
    (hFx : relativePosition μ ((φ τF xF : LeftEnergyState μ c) : Phase) 0 = 0)
    (hFv : 0 < jacobiVelocity (leviCivitaToJacobi μ ((φ τF xF : LeftEnergyState μ c) : Phase)) 0)
    (hη : 0 < (shootingCoordinates μ ((φ (-τN) xN : LeftEnergyState μ c) : Phase)).2)
    (hst : shootingCoordinates μ ((φ (-τN) xN : LeftEnergyState μ c) : Phase) =
      shootingCoordinates μ ((φ τF xF : LeftEnergyState μ c) : Phase)) :
    ∃ x : LeftEnergyState μ c, ∃ τ : ℝ, 0 < τ ∧
      (x : Phase) 0 = 0 ∧ (x : Phase) 3 = 0 ∧ (x : Phase) 1 ≠ 0 ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 1 = 0 ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 2 = 0 ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 0 ≠ 0 ∧
      (∀ t ∈ Set.Ioo 0 τ,
        relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0) ∧
      StrictMonoOn
        (fun t : ℝ => relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0)
        (Set.Icc 0 τ) := by
  have hanti := leviCivita_flow_antipodally_equivariant μ c hμ0 hμ1 hc φ hφ
  -- matching of the two crossing states
  set MN := φ (-τN) xN with hMN
  set MF := φ τF xF with hMF
  have hmatch : (MF : Phase) = (MN : Phase) ∨ (MF : Phase) = -(MN : Phase) := by
    apply shooting_match μ c _ _ (mem_locus MN) (mem_locus MF) hNx hFx
    · exact hη
    · exact hNv
    · exact hFv
    · exact hst
  -- transport along the flow
  have htrans : ∀ u : ℝ, (φ u MF : Phase) = (φ u MN : Phase) ∨
      (φ u MF : Phase) = -(φ u MN : Phase) := by
    intro u
    rcases hmatch with h | h
    · left; rw [Subtype.ext h]
    · right; exact hanti u MN MF h
  have hshift : ∀ u : ℝ, (φ (τF + u) xF : Phase) = (φ (u - τN) xN : Phase) ∨
      (φ (τF + u) xF : Phase) = -(φ (u - τN) xN : Phase) := by
    intro u
    have e1 : φ (τF + u) xF = φ u MF := by
      rw [hMF, ← Flow.map_add, add_comm]
    have e2 : φ (u - τN) xN = φ u MN := by
      rw [hMN, ← Flow.map_add, sub_eq_add_neg]
    rw [e1, e2]; exact htrans u
  have hrel : ∀ u : ℝ, relativePosition μ (φ (τF + u) xF : Phase) =
      relativePosition μ (φ (u - τN) xN : Phase) := by
    intro u
    rcases hshift u with h | h <;> rw [h]; rw [relPos_neg']
  refine ⟨xF, τF + τN, by linarith, hF0, hF3, hF1, ?_⟩
  have hendpt := hshift τN
  rw [sub_self, Flow.map_zero_apply] at hendpt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hendpt with h | h <;> rw [h] <;> simp [hN1]
  · rcases hendpt with h | h <;> rw [h] <;> simp [hN2]
  · rcases hendpt with h | h <;> rw [h] <;> simpa using hN0
  · intro u hu
    rcases lt_trichotomy u τF with h | h | h
    · exact hFlow u ⟨hu.1, h⟩
    · subst h
      have : (shootingCoordinates μ (MF : Phase)).2 =
          (shootingCoordinates μ (MN : Phase)).2 := by rw [hMF, hMN, hst]
      simp only [shootingCoordinates] at this hη
      rw [hMF] at this
      rw [hMN] at this
      linarith
    · have := hrel (u - τF)
      rw [show τF + (u - τF) = u by ring] at this
      rw [this]
      apply hNlow
      constructor <;> linarith [hu.2]
  · have hA : StrictMonoOn
        (fun t : ℝ => relativePosition μ ((φ t xF : LeftEnergyState μ c) : Phase) 0)
        (Icc (τF) (τF + τN)) := by
      intro a ha b hb hab
      have ea := hrel (a - τF)
      have eb := hrel (b - τF)
      rw [show τF + (a - τF) = a by ring] at ea
      rw [show τF + (b - τF) = b by ring] at eb
      simp only
      rw [ea, eb]
      apply hNmono
      · constructor <;> linarith [ha.1, ha.2]
      · constructor <;> linarith [hb.1, hb.2]
      · linarith
    have := StrictMonoOn.union hFmono hA
      (isGreatest_Icc hτF.le) (isLeast_Icc (by linarith))
    rwa [Icc_union_Icc_eq_Icc hτF.le (by linarith)] at this

theorem shooting_rest (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ x : LeftEnergyState μ c, ∃ τ : ℝ, 0 < τ ∧
      (x : Phase) 0 = 0 ∧ (x : Phase) 3 = 0 ∧ (x : Phase) 1 ≠ 0 ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 1 = 0 ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 2 = 0 ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 0 ≠ 0 ∧
      (∀ t ∈ Set.Ioo 0 τ,
        relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0) ∧
      StrictMonoOn
        (fun t : ℝ => relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0)
        (Set.Icc 0 τ) := by
  obtain ⟨Γ, α, hα1, hα2, hΓc, hΓ0, hΓ1, hΓR, hΓi⟩ :=
    birkhoff_near_shooting_family_weak μ c hμ0 hμ1 hc φ hφ
  obtain ⟨Γ', hΓ'0, hΓ'R, hΓ'i, hcase⟩ := birkhoff_far_shooting_family_rest μ c hμ0 hμ1 hc φ hφ
  have hr2 : 0 < Real.sqrt 2 / 2 := by positivity
  have hr2' : Real.sqrt 2 / 2 ≤ 1 := by
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  -- conclusion from an interior intersection
  have hfin : ∀ s ∈ Ioo (-1 : ℝ) 1, ∀ t ∈ Ioo (-1 : ℝ) 1, Γ s = Γ' t → ∃ x : LeftEnergyState μ c, ∃ τ : ℝ, 0 < τ ∧
          (x : Phase) 0 = 0 ∧ (x : Phase) 3 = 0 ∧ (x : Phase) 1 ≠ 0 ∧
          ((φ τ x : LeftEnergyState μ c) : Phase) 1 = 0 ∧
          ((φ τ x : LeftEnergyState μ c) : Phase) 2 = 0 ∧
          ((φ τ x : LeftEnergyState μ c) : Phase) 0 ≠ 0 ∧
          (∀ t ∈ Set.Ioo 0 τ,
            relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0) ∧
          StrictMonoOn
            (fun t : ℝ => relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0)
            (Set.Icc 0 τ) := by
    intro s hsi t hti hst
    obtain ⟨hσ, hη, xN, τN, hτN, hN1, hN2, hN0, hNlow, hNmono, hNx, hNv, hNc⟩ := hΓi s hsi
    obtain ⟨_, xF, τF, hτF, hF0, hF3, hF1, hFlow, hFmono, hFx, hFv, hFc⟩ := hΓ'i t hti
    exact finish_match μ c hμ0 hμ1 hc φ hφ xN τN hτN hN1 hN2 hN0 hNlow hNmono hNx hNv
      xF τF hτF hF0 hF3 hF1 hFlow hFmono hFx hFv (by rw [hNc]; exact hη)
      (by rw [hNc, hFc, hst])
  -- near endpoints are not hit at positive depth or at the far start
  have hsi_of : ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Ico (-1 : ℝ) 1, Γ s = Γ' t →
      s ∈ Ioo (-1 : ℝ) 1 ∧ t ∈ Ioo (-1 : ℝ) 1 := by
    intro s hs t ht hst
    have ht' : t ∈ Ioo (-1 : ℝ) 1 := by
      refine ⟨lt_of_le_of_ne ht.1 ?_, ht.2⟩
      rintro rfl
      rw [hΓ'0] at hst
      rcases eq_or_lt_of_le hs.1 with h | h
      · subst h; rw [hΓ0] at hst; have := congrArg Prod.fst hst; simp at this; linarith
      rcases eq_or_lt_of_le hs.2 with h' | h'
      · subst h'; rw [hΓ1] at hst; have := congrArg Prod.fst hst; simp at this; linarith
      have := (hΓi s ⟨h, h'⟩).2.1; rw [hst] at this; simp at this
    refine ⟨⟨lt_of_le_of_ne hs.1 ?_, lt_of_le_of_ne hs.2 ?_⟩, ht'⟩
    · rintro rfl
      have := (hΓ'i t ht').1; rw [← hst, hΓ0] at this; simp at this
    · rintro rfl
      have := (hΓ'i t ht').1; rw [← hst, hΓ1] at this; simp at this
  rcases hcase with ⟨hΓ'c, hΓ'end, hΓ'1R⟩ | ⟨hΓ'c, d, hd, hdB, hdT⟩
  · -- the far family reaches a side or the axis
    have hΓ'R' : ∀ t ∈ Icc (-1 : ℝ) 1,
        -1 ≤ (Γ' t).1 ∧ (Γ' t).1 ≤ 1 ∧ 0 ≤ (Γ' t).2 ∧ (Γ' t).2 ≤ 1 := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h]; exact hΓ'1R
      · exact hΓ'R t ⟨ht.1, h⟩
    have hend : (Γ' 1).1 = -1 ∨ (Γ' 1).1 = 1 ∨
        ((Γ' 1).2 = 0 ∧ ((Γ' 1).1 < α ∨ Real.sqrt 2 / 2 < (Γ' 1).1)) := by
      rcases hΓ'end with ⟨h | h, _⟩ | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h1, Or.inr h2⟩)
    obtain ⟨s, hs, t, ht, hst⟩ := PlanarTopology.interlaced_arcs_in_rectangle Γ Γ' (-1) 1 1 α
      (Real.sqrt 2 / 2) (-(Real.sqrt 2 / 2)) (by norm_num) one_pos (by linarith) hα1 hr2'
      hα2 (by linarith) hΓc hΓ'c hΓR hΓ'R' hΓ0 hΓ1 hΓ'0 hend
    rcases eq_or_lt_of_le ht.2 with h | h
    · exfalso; subst h
      rcases eq_or_lt_of_le hs.1 with h1 | h1
      · subst h1; rw [hΓ0] at hst
        rcases hΓ'end with ⟨_, h3⟩ | ⟨_, h3⟩
        · rw [← hst] at h3; simp at h3
        · rw [← hst] at h3; simp at h3; linarith
      rcases eq_or_lt_of_le hs.2 with h1' | h1'
      · subst h1'; rw [hΓ1] at hst
        rcases hΓ'end with ⟨_, h3⟩ | ⟨_, h3⟩
        · rw [← hst] at h3; simp at h3
        · rw [← hst] at h3; simp at h3
      have hσ := (hΓi s ⟨h1, h1'⟩).1
      rcases hΓ'end with ⟨h2 | h2, _⟩ | ⟨h2, _⟩
      · rw [← hst] at h2; rw [h2] at hσ; simp at hσ
      · rw [← hst] at h2; rw [h2] at hσ; simp at hσ
      · have := (hΓi s ⟨h1, h1'⟩).2.1; rw [hst, h2] at this; simp at this
    obtain ⟨hsi, hti⟩ := hsi_of s hs t ⟨ht.1, h⟩ hst
    exact hfin s hsi t hti hst
  · -- the far family ends at a state of rest: truncate below the rest depth
    have hΓd : ∀ s ∈ Icc (-1 : ℝ) 1, (Γ s).2 < d := by
      intro s hs
      rcases eq_or_lt_of_le hs.1 with h | h
      · subst h; rw [hΓ0]; exact hd
      rcases eq_or_lt_of_le hs.2 with h' | h'
      · subst h'; rw [hΓ1]; exact hd
      obtain ⟨-, hη, xN, τN, -, -, -, -, -, -, hNx, hNv, hNc⟩ := hΓi s ⟨h, h'⟩
      rw [← hNc] at hη ⊢
      simp only [shootingCoordinates] at hη ⊢
      exact hdB _ hNx (by linarith) hNv
    obtain ⟨sm, hsm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by norm_num : (-1:ℝ) ≤ 1))
      (continuous_snd.comp_continuousOn hΓc)
    set m := (Γ sm).2 with hm
    have hmd : m < d := hΓd sm hsm
    have hm0 : 0 ≤ m := by
      have := hmax (show (-1:ℝ) ∈ Icc (-1) 1 from ⟨le_rfl, by norm_num⟩)
      simp only [mem_setOf_eq, Function.comp] at this; rw [hΓ0] at this; exact this
    have hΓm : ∀ s ∈ Icc (-1 : ℝ) 1, (Γ s).2 ≤ m := fun s hs => hmax hs
    set h := (m + d) / 2 with hh
    have hmh : m < h := by linarith
    have hhd : h < d := by linarith
    have hh0 : 0 < h := by linarith
    obtain ⟨t0, ht0, ht0h⟩ : ∃ t0 ∈ Ioo (-1 : ℝ) 1, h < (Γ' t0).2 := by
      have h1 : ∀ᶠ t in 𝓝[<] (1:ℝ), h < (Γ' t).2 := hdT (Ioi_mem_nhds hhd)
      have h2 : ∀ᶠ t in 𝓝[<] (1:ℝ), t ∈ Ioo (-1 : ℝ) 1 :=
        Ioo_mem_nhdsLT (by norm_num)
      obtain ⟨t, ht1, ht2⟩ := (h2.and h1).exists
      exact ⟨t, ht1, ht2⟩
    set u : ℝ → ℝ := fun t => -1 + (t + 1) * (t0 + 1) / 2 with hu
    have huI : ∀ t ∈ Icc (-1 : ℝ) 1, u t ∈ Ico (-1 : ℝ) 1 := by
      intro t ht
      simp only [hu]
      constructor
      · nlinarith [ht.1, ht0.1]
      · nlinarith [ht.2, ht0.2, ht.1, ht0.1]
    set Γc : ℝ → ℝ × ℝ := fun t => ((Γ' (u t)).1, min (Γ' (u t)).2 h) with hΓcdef
    have hG : ContinuousOn (fun t => Γ' (u t)) (Icc (-1) 1) :=
      hΓ'c.comp (by fun_prop : Continuous u).continuousOn huI
    have hmin : ContinuousOn (fun t => min (Γ' (u t)).2 h) (Icc (-1) 1) :=
      continuous_min.comp_continuousOn
        ((continuous_snd.comp_continuousOn hG).prodMk continuousOn_const)
    have hΓcc : ContinuousOn Γc (Icc (-1) 1) :=
      (continuous_fst.comp_continuousOn hG).prodMk hmin
    have hu0 : u (-1) = -1 := by simp only [hu]; ring
    have hu1 : u 1 = t0 := by simp only [hu]; ring
    have hΓc0 : Γc (-1) = (-(Real.sqrt 2 / 2), 0) := by
      simp only [hΓcdef]; rw [hu0, hΓ'0]; simp [hh0.le]
    have hΓc1 : Γc 1 = ((Γ' t0).1, h) := by
      simp only [hΓcdef]; rw [hu1, min_eq_right ht0h.le]
    have hΓcR : ∀ t ∈ Icc (-1 : ℝ) 1, -1 ≤ (Γc t).1 ∧ (Γc t).1 ≤ 1 ∧ 0 ≤ (Γc t).2 ∧ (Γc t).2 ≤ h := by
      intro t ht
      have := hΓ'R (u t) (huI t ht)
      simp only [hΓcdef]
      exact ⟨this.1, this.2.1, le_min this.2.2.1 hh0.le, min_le_right _ _⟩
    set P : Path (Γc (-1)) ((-1 : ℝ), h) :=
      (toPath Γc hΓcc).trans (Path.segment (Γc 1) ((-1 : ℝ), h)) with hP
    set Γ3 : ℝ → ℝ × ℝ := fun t => P.extend ((t + 1) / 2) with hΓ3
    have hΓ3c : ContinuousOn Γ3 (Icc (-1) 1) :=
      (P.continuous_extend.comp (by fun_prop : Continuous fun t : ℝ => (t + 1) / 2)).continuousOn
    have hΓ30 : Γ3 (-1) = (-(Real.sqrt 2 / 2), 0) := by
      simp only [hΓ3]; rw [show ((-1:ℝ) + 1) / 2 = 0 by norm_num, Path.extend_zero]; exact hΓc0
    have hΓ31 : Γ3 1 = ((-1 : ℝ), h) := by
      simp only [hΓ3]; rw [show ((1:ℝ) + 1) / 2 = 1 by norm_num, Path.extend_one]
    have hseg : ∀ z ∈ range (Path.segment (Γc 1) ((-1 : ℝ), h)),
        -1 ≤ z.1 ∧ z.1 ≤ 1 ∧ z.2 = h := by
      intro z hz
      obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
      have hR1 := hΓcR 1 ⟨by norm_num, le_rfl⟩
      have hp2 : (Γc 1).2 = h := by rw [hΓc1]
      rw [hp2] at e2
      simp only at e1 e2
      refine ⟨?_, ?_, ?_⟩
      · rw [e1]; nlinarith [hR1.1, hR1.2.1]
      · rw [e1]; nlinarith [hR1.1, hR1.2.1]
      · rw [e2]; ring
    -- every point of the closed curve comes from the truncated far curve or lies at depth `h`
    have hrange : ∀ t ∈ Icc (-1 : ℝ) 1, (∃ t' ∈ Icc (-1 : ℝ) 1, Γc t' = Γ3 t) ∨
        (-1 ≤ (Γ3 t).1 ∧ (Γ3 t).1 ≤ 1 ∧ (Γ3 t).2 = h) := by
      intro t ht
      have hmem := extend_mem_range P ht
      simp only [hP, Path.trans_range, mem_union] at hmem
      rcases hmem with hz | hz
      · left; exact toPath_range hz
      · right; exact hseg _ hz
    have hΓ3R : ∀ t ∈ Icc (-1 : ℝ) 1,
        -1 ≤ (Γ3 t).1 ∧ (Γ3 t).1 ≤ 1 ∧ 0 ≤ (Γ3 t).2 ∧ (Γ3 t).2 ≤ h := by
      intro t ht
      rcases hrange t ht with ⟨t', ht', he⟩ | ⟨h1, h2, h3⟩
      · rw [← he]; exact hΓcR t' ht'
      · exact ⟨h1, h2, by rw [h3]; exact hh0.le, by rw [h3]⟩
    have hΓRh : ∀ s ∈ Icc (-1 : ℝ) 1,
        -1 ≤ (Γ s).1 ∧ (Γ s).1 ≤ 1 ∧ 0 ≤ (Γ s).2 ∧ (Γ s).2 ≤ h := by
      intro s hs
      have := hΓR s hs
      exact ⟨this.1, this.2.1, this.2.2.1, by linarith [hΓm s hs]⟩
    obtain ⟨s, hs, t, ht, hst⟩ := PlanarTopology.interlaced_arcs_in_rectangle Γ Γ3 (-1) 1 h α
      (Real.sqrt 2 / 2) (-(Real.sqrt 2 / 2)) (by norm_num) hh0 (by linarith) hα1 hr2'
      hα2 (by linarith) hΓc hΓ3c hΓRh hΓ3R hΓ0 hΓ1 hΓ30 (Or.inl (by rw [hΓ31]))
    rcases hrange t ht with ⟨t', ht', he⟩ | ⟨-, -, h3⟩
    · rw [← he] at hst
      have hsd : (Γ s).2 < h := lt_of_le_of_lt (hΓm s hs) hmh
      have hmin : min (Γ' (u t')).2 h = (Γ' (u t')).2 := by
        apply min_eq_left
        by_contra hc'
        push Not at hc'
        have : (Γ s).2 = h := by rw [hst]; simp only [hΓcdef]; exact min_eq_right hc'.le
        linarith
      have hst' : Γ s = Γ' (u t') := by
        rw [hst]; simp only [hΓcdef]; rw [hmin]
      obtain ⟨hsi, hti⟩ := hsi_of s hs (u t') (huI t' ht') hst'
      exact hfin s hsi (u t') hti hst'
    · exfalso
      have : (Γ s).2 = h := by rw [hst, h3]
      linarith [hΓm s hs]

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ x : LeftEnergyState μ c, ∃ τ : ℝ, 0 < τ ∧
      (x : Phase) 0 = 0 ∧ (x : Phase) 3 = 0 ∧ (x : Phase) 1 ≠ 0 ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 1 = 0 ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 2 = 0 ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 0 ≠ 0 ∧
      (∀ t ∈ Set.Ioo 0 τ,
        relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0) ∧
      StrictMonoOn
        (fun t : ℝ => relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0)
        (Set.Icc 0 τ) :=
  shooting_rest μ c hμ0 hμ1 hc φ hφ
