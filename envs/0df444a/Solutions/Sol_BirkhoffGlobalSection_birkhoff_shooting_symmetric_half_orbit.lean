-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_shooting_symmetric_half_orbit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T07:49:01.172385+00:00
-- url     : https://prove2.me/submissions/425fa83b-3d80-434f-96e7-439bb5db708c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BirkhoffGlobalSection
import Definitions.Def_BirkhoffShootingCoordinates
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_near_shooting_family
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_shooting_family
import Theorems.Thm_BirkhoffGlobalSection_leviCivita_flow_antipodally_equivariant
import Theorems.Thm_PlanarTopology_interlaced_arcs_in_rectangle
import Mathlib.Tactic
import Mathlib.Order.Monotone.Union

open BirkhoffGlobalSection Set

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
        (Set.Icc 0 τ) := by
  have hanti := leviCivita_flow_antipodally_equivariant μ c hμ0 hμ1 hc φ hφ
  obtain ⟨Γ, α, hα1, hα2, hΓc, hΓ0, hΓ1, hΓR, hΓi⟩ :=
    birkhoff_near_shooting_family μ c hμ0 hμ1 hc φ hφ
  obtain ⟨Γ', hΓ'c, hΓ'0, hΓ'end, hΓ'R, hΓ'i⟩ :=
    birkhoff_far_shooting_family μ c hμ0 hμ1 hc φ hφ
  have hr2 : 0 < Real.sqrt 2 / 2 := by positivity
  have hr2' : Real.sqrt 2 / 2 ≤ 1 := by
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  have hend : (Γ' 1).1 = -1 ∨ (Γ' 1).1 = 1 ∨
      ((Γ' 1).2 = 0 ∧ ((Γ' 1).1 < α ∨ Real.sqrt 2 / 2 < (Γ' 1).1)) := by
    rcases hΓ'end with ⟨h | h, _⟩ | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h1, Or.inr h2⟩)
  obtain ⟨s, hs, t, ht, hst⟩ := PlanarTopology.interlaced_arcs_in_rectangle Γ Γ' (-1) 1 1 α
    (Real.sqrt 2 / 2) (-(Real.sqrt 2 / 2)) (by norm_num) one_pos (by linarith) hα1.le hr2'
    hα2 (by linarith) hΓc hΓ'c hΓR hΓ'R hΓ0 hΓ1 hΓ'0 hend
  -- the intersection is interior on both curves
  have hsi : s ∈ Ioo (-1 : ℝ) 1 := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · exfalso; subst h
      rcases eq_or_lt_of_le ht.1 with h' | h'
      · subst h'; rw [hΓ0, hΓ'0] at hst
        have := congrArg Prod.fst hst; simp at this; linarith
      rcases eq_or_lt_of_le ht.2 with h'' | h''
      · subst h''; rw [hΓ0] at hst
        rcases hΓ'end with ⟨_, h⟩ | ⟨_, h⟩
        · rw [← hst] at h; simp at h
        · rw [← hst] at h; simp at h; linarith
      · have := (hΓ'i t ⟨h', h''⟩).1; rw [← hst, hΓ0] at this; simp at this
    rcases eq_or_lt_of_le hs.2 with h' | h'
    · exfalso; subst h'
      rcases eq_or_lt_of_le ht.1 with h'' | h''
      · subst h''; rw [hΓ1, hΓ'0] at hst
        have := congrArg Prod.fst hst; simp at this; linarith
      rcases eq_or_lt_of_le ht.2 with h''' | h'''
      · subst h'''; rw [hΓ1] at hst
        rcases hΓ'end with ⟨_, h⟩ | ⟨_, h⟩
        · rw [← hst] at h; simp at h
        · rw [← hst] at h; simp at h
      · have := (hΓ'i t ⟨h'', h'''⟩).1; rw [← hst, hΓ1] at this; simp at this
    exact ⟨h, h'⟩
  obtain ⟨hσ, hη, xN, τN, hτN, hN1, hN2, hN0, hNlow, hNmono, hNx, hNv, hNc⟩ := hΓi s hsi
  have hti : t ∈ Ioo (-1 : ℝ) 1 := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · exfalso; subst h; rw [hΓ'0] at hst; rw [hst] at hη; simp at hη
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · exfalso; subst h'
      rcases hΓ'end with ⟨h1 | h1, _⟩ | ⟨h2, _⟩
      · rw [← hst] at h1; rw [h1] at hσ; simp at hσ
      · rw [← hst] at h1; rw [h1] at hσ; simp at hσ
      · rw [← hst] at h2; rw [h2] at hη; simp at hη
    exact ⟨h, h'⟩
  obtain ⟨_, xF, τF, hτF, hF0, hF3, hF1, hFlow, hFmono, hFx, hFv, hFc⟩ := hΓ'i t hti
  -- matching of the two crossing states
  set MN := φ (-τN) xN with hMN
  set MF := φ τF xF with hMF
  have hmatch : (MF : Phase) = (MN : Phase) ∨ (MF : Phase) = -(MN : Phase) := by
    apply shooting_match μ c _ _ (mem_locus MN) (mem_locus MF) hNx hFx
    · rw [hNc]; exact hη
    · exact hNv
    · exact hFv
    · rw [hNc, hFc, hst]
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
      have : (shootingCoordinates μ (MF : Phase)).2 = (Γ' t).2 := by rw [hFc]
      rw [← hst] at this
      simp only [shootingCoordinates] at this
      rw [hMF] at this
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
