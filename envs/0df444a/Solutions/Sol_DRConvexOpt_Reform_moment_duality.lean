-- Prove2me | solution 1 for DRConvexOpt.Reform.moment_duality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:20:48.451746+00:00
-- url     : https://prove2.me/submissions/8c46faec-1c93-4a8d-99e9-f634cef1dd2a

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting

open MeasureTheory Matrix DRConvexOpt.Reform
open scoped NNReal

namespace DRCOMDAux

lemma conf_closed {nP nQ nK nI : ℕ} (d : AmbData nP nQ nK nI)
    (hK : ∀ i, IsProperCone (d.K i)) (i : Fin (nI + 1)) : IsClosed (d.conf i) := by
  have hc : Continuous fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) =>
      d.c i - (d.C i *ᵥ ω.1 + d.D i *ᵥ ω.2) :=
    continuous_const.sub ((continuous_const.matrix_mulVec continuous_fst).add
      (continuous_const.matrix_mulVec continuous_snd))
  exact (hK i).1.preimage hc

/-- the linear functional `y ↦ y ⬝ᵥ a` -/
def dotL {n : ℕ} (a : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun y := y ⬝ᵥ a
  map_add' y z := add_dotProduct y z a
  map_smul' r y := by simp [smul_dotProduct]


section
variable {nP nQ nK nI : ℕ} (d : AmbData nP nQ nK nI)

/-- the linear map `(z, u) ↦ A z + B u` -/
def Lg : ((Fin nP → ℝ) × (Fin nQ → ℝ)) →ₗ[ℝ] (Fin nK → ℝ) :=
  d.A.mulVecLin ∘ₗ LinearMap.fst ℝ _ _ + d.B.mulVecLin ∘ₗ LinearMap.snd ℝ _ _

lemma Lg_apply (ω : (Fin nP → ℝ) × (Fin nQ → ℝ)) : Lg d ω = d.A *ᵥ ω.1 + d.B *ᵥ ω.2 := rfl

lemma Fint (μ : Measure ((Fin nP → ℝ) × (Fin nQ → ℝ))) (hint : Integrable (fun ω => ω) μ) :
    Integrable (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) => d.A *ᵥ ω.1 + d.B *ᵥ ω.2) μ :=
  (Lg d).toContinuousLinearMap.integrable_comp hint

lemma Fdot_int (μ : Measure ((Fin nP → ℝ) × (Fin nQ → ℝ))) (hint : Integrable (fun ω => ω) μ)
    (β : Fin nK → ℝ) :
    Integrable (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) => (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β) μ :=
  (dotL β ∘ₗ Lg d).toContinuousLinearMap.integrable_comp hint

lemma Fdot_integral (μ : Measure ((Fin nP → ℝ) × (Fin nQ → ℝ)))
    (hint : Integrable (fun ω => ω) μ) (β : Fin nK → ℝ) :
    ∫ ω, (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β ∂μ = (∫ ω, (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ∂μ) ⬝ᵥ β := by
  have h1 := (dotL β ∘ₗ Lg d).toContinuousLinearMap.integral_comp_comm hint
  have h2 := (Lg d).toContinuousLinearMap.integral_comp_comm hint
  simp only [LinearMap.coe_toContinuousLinearMap'] at h1 h2
  change ∫ ω, (dotL β ∘ₗ Lg d) ω ∂μ = dotL β (∫ ω, Lg d ω ∂μ)
  rw [h1, h2]; rfl

lemma vint {nN nL : ℕ} [NeZero nL] (v : PWAff nN nP nL) (x : Fin nN → ℝ)
    (μ : Measure ((Fin nP → ℝ) × (Fin nQ → ℝ))) [IsFiniteMeasure μ]
    (hint : Integrable (fun ω => ω) μ) :
    Integrable (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) => v.eval x ω.1) μ := by
  have hvl : ∀ l, Integrable (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) =>
      (v.S l *ᵥ ω.1 + v.s l) ⬝ᵥ x + (v.tv l ⬝ᵥ ω.1 + v.t0 l)) μ := by
    intro l
    let Ll : ((Fin nP → ℝ) × (Fin nQ → ℝ)) →ₗ[ℝ] ℝ :=
      (dotL x ∘ₗ (v.S l).mulVecLin + dotL (v.tv l)) ∘ₗ LinearMap.fst ℝ _ _
    have h := (Ll.toContinuousLinearMap.integrable_comp hint).add
      (integrable_const (v.s l ⬝ᵥ x + v.t0 l))
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [LinearMap.coe_toContinuousLinearMap', Ll, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.fst_apply, dotL, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mulVecLin_apply, add_dotProduct]
    simp only [Pi.add_apply]
    rw [dotProduct_comm ω.1]
    ring
  have : (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) => v.eval x ω.1) =
      Finset.univ.sup' Finset.univ_nonempty (fun l => fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) =>
        (v.S l *ᵥ ω.1 + v.s l) ⬝ᵥ x + (v.tv l ⬝ᵥ ω.1 + v.t0 l)) := by
    funext ω; rw [Finset.sup'_apply]; rfl
  rw [this]
  exact Finset.sup'_induction (p := fun f => Integrable f μ) _ _
    (fun a ha b hb => Integrable.sup ha hb) fun l _ => hvl l

end

end DRCOMDAux

open DRCOMDAux in
theorem solution {nP nQ nK nI nN nL : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL)
    (hK : ∀ i, IsProperCone (d.K i))
    (hp : ∀ i, 0 ≤ d.plo i ∧ d.plo i ≤ d.phi i ∧ d.phi i ≤ 1)
    (hC1 : Bornology.IsBounded (d.conf (Fin.last nI)) ∧ d.plo (Fin.last nI) = 1 ∧
      d.phi (Fin.last nI) = 1)
    (hS1 : MomentSlater d) (x : Fin nN → ℝ) (w : ℝ) :
    (∀ μ ∈ ambiguitySet d, ∫ ω, v.eval x ω.1 ∂μ ≤ w) ↔
    ∃ (β : Fin nK → ℝ) (κ lam : Fin (nI + 1) → ℝ), (∀ i, 0 ≤ κ i) ∧ (∀ i, 0 ≤ lam i) ∧
      d.b ⬝ᵥ β + ∑ i, (d.phi i * κ i - d.plo i * lam i) ≤ w ∧
      ∀ ω ∈ d.conf (Fin.last nI),
        v.eval x ω.1 ≤ (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β +
          ∑ i, (d.conf i).indicator (fun _ => (1 : ℝ)) ω * (κ i - lam i) := by
  have hmeas : ∀ i, MeasurableSet (d.conf i) := fun i => (conf_closed d hK i).measurableSet
  have hind : ∀ (c : Fin (nI + 1) → ℝ) j ω, (d.conf j).indicator (fun _ => (1 : ℝ)) ω * c j =
      (d.conf j).indicator (fun _ => c j) ω := by
    intro c j ω; by_cases h : ω ∈ d.conf j <;> simp [h]
  constructor
  · intro H
    classical
    obtain ⟨ε, hε, hS1'⟩ := hS1
    set CI := d.conf (Fin.last nI) with hCIdef
    -- a lower bound for `v` on `C_I`
    obtain ⟨V0, hV0neg, hV0⟩ : ∃ V0 : ℝ, V0 ≤ 0 ∧ ∀ ω ∈ CI, V0 ≤ v.eval x ω.1 := by
      have hc : IsCompact CI :=
        Metric.isCompact_of_isClosed_isBounded (conf_closed d hK _) hC1.1
      have hcont : Continuous fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) =>
          (v.S 0 *ᵥ ω.1 + v.s 0) ⬝ᵥ x + (v.tv 0 ⬝ᵥ ω.1 + v.t0 0) := by fun_prop
      obtain ⟨m, hm⟩ := hc.bddBelow_image hcont.continuousOn
      refine ⟨min m 0, min_le_right _ _, fun ω hω => ?_⟩
      have h1 := hm ⟨ω, hω, rfl⟩
      have h2 : _ ≤ v.eval x ω.1 :=
        Finset.le_sup' (fun l => (v.S l *ᵥ ω.1 + v.s l) ⬝ᵥ x + (v.tv l ⬝ᵥ ω.1 + v.t0 l))
          (Finset.mem_univ 0)
      exact (min_le_left _ _).trans (h1.trans h2)
    -- the perturbation set of the moment problem
    let Good : Measure ((Fin nP → ℝ) × (Fin nQ → ℝ)) →
        (Fin nK → ℝ) × (Fin (nI + 1) → ℝ) × ℝ → Prop := fun μ q =>
      IsFiniteMeasure μ ∧ μ CIᶜ = 0 ∧ Integrable (fun ω => ω) μ ∧
      ∫ ω, (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ∂μ = d.b + q.1 ∧
      (∀ i, d.plo i + q.2.1 i ≤ μ.real (d.conf i) ∧ μ.real (d.conf i) ≤ d.phi i + q.2.1 i) ∧
      q.2.2 ≤ ∫ ω, v.eval x ω.1 ∂μ
    let S : Set ((Fin nK → ℝ) × (Fin (nI + 1) → ℝ) × ℝ) := {q | ∃ μ, Good μ q}
    let T : Set ((Fin nK → ℝ) × (Fin (nI + 1) → ℝ) × ℝ) := {q | q.1 = 0 ∧ q.2.1 = 0 ∧ w < q.2.2}
    have hSconv : Convex ℝ S := by
      rintro q1 ⟨μ1, hf1, hn1, hi1, hm1, hc1, hv1⟩ q2 ⟨μ2, hf2, hn2, hi2, hm2, hc2, hv2⟩ s t hs ht hst
      let s' : ℝ≥0 := ⟨s, hs⟩
      let t' : ℝ≥0 := ⟨t, ht⟩
      refine ⟨s' • μ1 + t' • μ2, ?_⟩
      haveI := hf1; haveI := hf2
      have hcomb : ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
          (φ : (Fin nP → ℝ) × (Fin nQ → ℝ) → G), Integrable φ μ1 → Integrable φ μ2 →
          ∫ ω, φ ω ∂(s' • μ1 + t' • μ2) = s • ∫ ω, φ ω ∂μ1 + t • ∫ ω, φ ω ∂μ2 := by
        intro G _ _ _ φ h1 h2
        rw [integral_add_measure h1.smul_measure_nnreal h2.smul_measure_nnreal,
          integral_smul_nnreal_measure, integral_smul_nnreal_measure]
        rfl
      have hreal : ∀ i, (s' • μ1 + t' • μ2).real (d.conf i) =
          s * μ1.real (d.conf i) + t * μ2.real (d.conf i) := by
        intro i
        rw [measureReal_add_apply, measureReal_nnreal_smul_apply, measureReal_nnreal_smul_apply]
        rfl
      refine ⟨inferInstance, ?_, hi1.smul_measure_nnreal.add_measure hi2.smul_measure_nnreal,
        ?_, fun i => ?_, ?_⟩
      · simp [hn1, hn2]
      · rw [hcomb _ (Fint d μ1 hi1) (Fint d μ2 hi2), hm1, hm2]
        have hb : s • d.b + t • d.b = d.b := by rw [← add_smul, hst, one_smul]
        simp only [Prod.fst_add, Prod.smul_fst]
        rw [smul_add, smul_add, add_add_add_comm, hb]
      · rw [hreal]
        have e1 : d.plo i = s * d.plo i + t * d.plo i := by rw [← add_mul, hst, one_mul]
        have e2 : d.phi i = s * d.phi i + t * d.phi i := by rw [← add_mul, hst, one_mul]
        have g1 : (s • q1 + t • q2).2.1 i = s * q1.2.1 i + t * q2.2.1 i := rfl
        rw [g1]
        constructor
        · nlinarith [mul_le_mul_of_nonneg_left (hc1 i).1 hs, mul_le_mul_of_nonneg_left (hc2 i).1 ht]
        · nlinarith [mul_le_mul_of_nonneg_left (hc1 i).2 hs, mul_le_mul_of_nonneg_left (hc2 i).2 ht]
      · rw [hcomb _ (vint v x μ1 hi1) (vint v x μ2 hi2)]
        simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        nlinarith [mul_le_mul_of_nonneg_left hv1 hs, mul_le_mul_of_nonneg_left hv2 ht]
    have hTconv : Convex ℝ T := by
      rintro q1 ⟨h1, h1', h1''⟩ q2 ⟨h2, h2', h2''⟩ s t hs ht hst
      refine ⟨?_, ?_, ?_⟩
      · show s • q1.1 + t • q2.1 = 0
        rw [h1, h2]; simp
      · show s • q1.2.1 + t • q2.2.1 = 0
        rw [h1', h2']; simp
      · show w < s * q1.2.2 + t * q2.2.2
        have : w = s * w + t * w := by rw [← add_mul, hst, one_mul]
        rcases hs.eq_or_lt with hs0 | hs0
        · subst hs0
          have : t = 1 := by linarith
          subst this; simpa using h2''
        · nlinarith [mul_lt_mul_of_pos_left h1'' hs0, mul_le_mul_of_nonneg_left h2''.le ht]
    -- a box in the interior of `S`, from (S1)
    set s0 := V0 * (1 + ε) - 1 with hs0
    let B : Set ((Fin nK → ℝ) × (Fin (nI + 1) → ℝ) × ℝ) :=
      {q | (∀ k, |q.1 k| < ε) ∧ (∀ i, |q.2.1 i| < ε) ∧ q.2.2 < s0}
    have hBS : B ⊆ S := by
      rintro q ⟨hq1, hq2, hq3⟩
      obtain ⟨μ, hfin, hnull, hint, hmean, hconf⟩ := hS1' (d.b + q.1) q.2.1
        (fun k => by simpa using (hq1 k).le) (fun i => (hq2 i).le)
      refine ⟨μ, hfin, hnull, hint, hmean, fun i => hconf i, ?_⟩
      haveI := hfin
      have hae : ∀ᵐ ω ∂μ, ω ∈ CI := mem_ae_iff.mpr hnull
      have hlow : ∫ _ω, V0 ∂μ ≤ ∫ ω, v.eval x ω.1 ∂μ :=
        integral_mono_ae (integrable_const _) (vint v x μ hint) (hae.mono fun ω hω => hV0 ω hω)
      rw [integral_const, smul_eq_mul] at hlow
      have hmass : μ.real Set.univ ≤ 1 + ε := by
        have h1 : μ Set.univ = μ CI := by
          rw [← measure_add_measure_compl (hmeas (Fin.last nI)), hnull, add_zero]
        have h1' : μ.real Set.univ = μ.real CI := by
          simp only [Measure.real, h1]
        have h2 := (hconf (Fin.last nI)).2
        rw [hC1.2.2] at h2
        have h3 := (abs_lt.mp (hq2 (Fin.last nI))).2
        rw [h1']
        linarith
      have : V0 * (1 + ε) ≤ μ.real Set.univ * V0 := by nlinarith [measureReal_nonneg (μ := μ) (s := Set.univ)]
      linarith
    have hBopen : IsOpen B := by
      have e : B = (⋂ k, {q : (Fin nK → ℝ) × (Fin (nI + 1) → ℝ) × ℝ | |q.1 k| < ε}) ∩
          ((⋂ i, {q : (Fin nK → ℝ) × (Fin (nI + 1) → ℝ) × ℝ | |q.2.1 i| < ε}) ∩
            {q : (Fin nK → ℝ) × (Fin (nI + 1) → ℝ) × ℝ | q.2.2 < s0}) := by
        ext q; simp only [B, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      rw [e]
      exact (isOpen_iInter_of_finite fun k => isOpen_lt (by fun_prop) continuous_const).inter
        ((isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const).inter
          (isOpen_lt (by fun_prop) continuous_const))
    have hBint : B ⊆ interior S := interior_maximal hBS hBopen
    have hq0 : ((0, 0, s0 - 1) : (Fin nK → ℝ) × (Fin (nI + 1) → ℝ) × ℝ) ∈ B :=
      ⟨fun k => by simpa using hε, fun i => by simpa using hε, by simp⟩
    -- `S` misses `T`, because of (3)
    have hdisj : Disjoint (interior S) T := by
      rw [Set.disjoint_left]
      rintro q hqS ⟨hq1, hq2, hq3⟩
      obtain ⟨μ, hfin, hnull, hint, hmean, hconf, hv⟩ := interior_subset hqS
      haveI := hfin
      have hprob : IsProbabilityMeasure μ := by
        constructor
        have h1 : μ Set.univ = μ CI := by
          rw [← measure_add_measure_compl (hmeas (Fin.last nI)), hnull, add_zero]
        rw [h1]
        have h := hconf (Fin.last nI)
        rw [hC1.2.1, hC1.2.2, hq2] at h
        simp only [Pi.zero_apply, add_zero] at h
        exact (ENNReal.toReal_eq_one_iff _).mp (le_antisymm h.2 h.1)
      have hmem : μ ∈ ambiguitySet d := ⟨hprob, hint, by rw [hmean, hq1, add_zero], fun i => by
        have := hconf i; rw [hq2] at this; simpa using this⟩
      have := H μ hmem
      linarith
    obtain ⟨f, u, hfS, hfT⟩ :=
      geometric_hahn_banach_open hSconv.interior isOpen_interior hTconv hdisj
    have hSne : (interior S).Nonempty := ⟨_, hBint hq0⟩
    have hfS' : ∀ q ∈ S, f q ≤ u := by
      intro q hq
      have hcl : closure (interior S) ⊆ {q | f q ≤ u} :=
        closure_minimal (fun q hq => (hfS q hq).le) (isClosed_le f.continuous continuous_const)
      rw [hSconv.closure_interior_eq_closure_of_nonempty_interior hSne] at hcl
      exact hcl (subset_closure hq)
    -- coordinates of the separating functional
    let α : Fin nK → ℝ := fun k => f (Pi.single k 1, 0, 0)
    let γ : Fin (nI + 1) → ℝ := fun i => f (0, Pi.single i 1, 0)
    set θ : ℝ := f (0, 0, 1) with hθ
    have hrep : ∀ q : (Fin nK → ℝ) × (Fin (nI + 1) → ℝ) × ℝ,
        f q = α ⬝ᵥ q.1 + γ ⬝ᵥ q.2.1 + θ * q.2.2 := by
      intro q
      have e : q = ∑ k, q.1 k • ((Pi.single k (1 : ℝ) : Fin nK → ℝ), (0 : Fin (nI + 1) → ℝ), (0 : ℝ)) +
          ∑ i, q.2.1 i • ((0 : Fin nK → ℝ), (Pi.single i (1 : ℝ) : Fin (nI + 1) → ℝ), (0 : ℝ)) +
          q.2.2 • ((0 : Fin nK → ℝ), (0 : Fin (nI + 1) → ℝ), (1 : ℝ)) := by
        ext j
        · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
        · simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
        · simp [Prod.snd_sum]
      conv_lhs => rw [e]
      rw [map_add, map_add, map_sum, map_sum, map_smul]
      simp only [map_smul, smul_eq_mul, dotProduct, α, γ, θ]
      have hc1 : ∀ k, q.1 k * f (Pi.single k 1, 0, 0) = f (Pi.single k 1, 0, 0) * q.1 k :=
        fun k => mul_comm _ _
      have hc2 : ∀ i, q.2.1 i * f (0, Pi.single i 1, 0) = f (0, Pi.single i 1, 0) * q.2.1 i :=
        fun i => mul_comm _ _
      simp only [hc1, hc2]; ring
    have hTu : ∀ s, w < s → u ≤ θ * s := by
      intro s hs
      have := hfT (0, 0, s) ⟨rfl, rfl, hs⟩
      rw [hrep] at this; simpa using this
    have hθpos : 0 < θ := by
      by_contra hneg
      push Not at hneg
      have h1 := hfS _ (hBint hq0)
      rw [hrep] at h1
      simp only [dotProduct_zero, zero_add] at h1
      have h2 := hTu (max (w + 1) (s0 - 1)) (lt_of_lt_of_le (by linarith) (le_max_left _ _))
      have h3 : θ * max (w + 1) (s0 - 1) ≤ θ * (s0 - 1) :=
        mul_le_mul_of_nonpos_left (le_max_right _ _) hneg
      linarith
    have huw : u ≤ θ * w := by
      by_contra hlt
      push Not at hlt
      have hδ : 0 < (u - θ * w) / (2 * θ) := div_pos (by linarith) (by linarith)
      have := hTu (w + (u - θ * w) / (2 * θ)) (by linarith)
      have e : θ * (w + (u - θ * w) / (2 * θ)) = θ * w + (u - θ * w) / 2 := by
        field_simp
      rw [e] at this
      linarith
    have hmain : ∀ q ∈ S, α ⬝ᵥ q.1 + γ ⬝ᵥ q.2.1 + θ * q.2.2 ≤ θ * w := by
      intro q hq; have := hfS' q hq; rw [hrep] at this; linarith
    -- testing against point masses
    let qs : Fin (nI + 1) → ℝ := fun i => if 0 ≤ γ i then d.plo i else d.phi i
    have hqs : ∀ i, d.plo i ≤ qs i ∧ qs i ≤ d.phi i := by
      intro i; simp only [qs]; split_ifs <;> constructor <;> linarith [(hp i).2.1]
    have hobj0 : α ⬝ᵥ (-d.b) + γ ⬝ᵥ (-qs) ≤ θ * w := by
      have := hmain (-d.b, -qs, 0) ⟨0, inferInstance, by simp, integrable_zero_measure,
        by simp, fun i => ⟨by simp [(hqs i).1], by simp [(hqs i).2]⟩, by simp⟩
      simpa using this
    have hpt : ∀ ω ∈ CI, ∀ t : ℝ≥0,
        α ⬝ᵥ ((t : ℝ) • (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) - d.b) +
          γ ⬝ᵥ ((t : ℝ) • (fun i => (d.conf i).indicator (fun _ => (1 : ℝ)) ω) - qs) +
          θ * ((t : ℝ) * v.eval x ω.1) ≤ θ * w := by
      intro ω hω t
      refine hmain ((t : ℝ) • (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) - d.b,
        (t : ℝ) • (fun i => (d.conf i).indicator (fun _ => (1 : ℝ)) ω) - qs,
        (t : ℝ) * v.eval x ω.1) ?_
      refine ⟨t • Measure.dirac ω, inferInstance, ?_, ?_, ?_, fun i => ?_, ?_⟩
      · simp [Measure.dirac_apply' _ (hmeas _).compl, hω]
      · exact (integrable_dirac (by simp)).smul_measure_nnreal
      · rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def]
        simp
      · have hr : (t • Measure.dirac ω).real (d.conf i) =
            (t : ℝ) * (d.conf i).indicator (fun _ => (1 : ℝ)) ω := by
          rw [measureReal_nnreal_smul_apply]
          by_cases h : ω ∈ d.conf i <;> simp [Measure.real, Measure.dirac_apply' _ (hmeas i), h]
        rw [hr]
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        constructor <;> linarith [(hqs i).1, (hqs i).2]
      · rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, smul_eq_mul]
    have hmx : ∀ a : ℝ, max (-a) 0 - max a 0 = -a := by
      intro a
      rcases le_total 0 a with h | h
      · rw [max_eq_right (by linarith), max_eq_left h]; ring
      · rw [max_eq_left (by linarith), max_eq_right h]; ring
    refine ⟨θ⁻¹ • (-α), fun i => θ⁻¹ * max (-γ i) 0, fun i => θ⁻¹ * max (γ i) 0,
      fun i => mul_nonneg (inv_nonneg.mpr hθpos.le) (le_max_right _ _),
      fun i => mul_nonneg (inv_nonneg.mpr hθpos.le) (le_max_right _ _), ?_, ?_⟩
    · have hterm : ∀ i, d.phi i * (θ⁻¹ * max (-γ i) 0) - d.plo i * (θ⁻¹ * max (γ i) 0) =
          θ⁻¹ * (γ i * (-qs i)) := by
        intro i
        simp only [qs]
        split_ifs with h
        · rw [max_eq_right (by linarith), max_eq_left h]; ring
        · push Not at h
          rw [max_eq_left (by linarith), max_eq_right h.le]; ring
      rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum]
      have e : d.b ⬝ᵥ (θ⁻¹ • -α) = θ⁻¹ * (α ⬝ᵥ (-d.b)) := by
        rw [dotProduct_smul, smul_eq_mul, dotProduct_neg, dotProduct_neg, dotProduct_comm]
      rw [e, ← mul_add]
      have e2 : ∑ i, γ i * (-qs i) = γ ⬝ᵥ (-qs) := rfl
      rw [e2, inv_mul_le_iff₀ hθpos]
      exact hobj0
    · intro ω hω
      set χ : Fin (nI + 1) → ℝ := fun i => (d.conf i).indicator (fun _ => (1 : ℝ)) ω with hχ
      set Fω := d.A *ᵥ ω.1 + d.B *ᵥ ω.2
      have hX : α ⬝ᵥ Fω + γ ⬝ᵥ χ + θ * v.eval x ω.1 ≤ 0 := by
        by_contra hpos
        push Not at hpos
        set X := α ⬝ᵥ Fω + γ ⬝ᵥ χ + θ * v.eval x ω.1
        set Y := α ⬝ᵥ (-d.b) + γ ⬝ᵥ (-qs)
        let t : ℝ≥0 := ⟨(|θ * w - Y| + 1) / X, div_nonneg (by positivity) hpos.le⟩
        have h := hpt ω hω t
        have e : α ⬝ᵥ ((t : ℝ) • Fω - d.b) + γ ⬝ᵥ ((t : ℝ) • χ - qs) +
            θ * ((t : ℝ) * v.eval x ω.1) = (t : ℝ) * X + Y := by
          simp only [X, Y, dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_neg]
          ring
        rw [e] at h
        have ht : (t : ℝ) * X = |θ * w - Y| + 1 := div_mul_cancel₀ _ hpos.ne'
        have := le_abs_self (θ * w - Y)
        linarith
      have e : Fω ⬝ᵥ (θ⁻¹ • -α) + ∑ i, χ i * (θ⁻¹ * max (-γ i) 0 - θ⁻¹ * max (γ i) 0) =
          θ⁻¹ * (-(α ⬝ᵥ Fω) - γ ⬝ᵥ χ) := by
        have : ∀ i, χ i * (θ⁻¹ * max (-γ i) 0 - θ⁻¹ * max (γ i) 0) = θ⁻¹ * (-(γ i * χ i)) := by
          intro i; rw [← mul_sub, hmx]; ring
        rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.mul_sum, dotProduct_smul, smul_eq_mul,
          dotProduct_neg, dotProduct_comm, Finset.sum_neg_distrib]
        simp only [dotProduct]
        ring
      rw [e, le_inv_mul_iff₀ hθpos]
      linarith
  · rintro ⟨β, κ, lam, hκ, hlam, hobj, hdual⟩ μ ⟨hprob, hint, hmean, hconf⟩
    have hCI : μ (d.conf (Fin.last nI)) = 1 := by
      have h := hconf (Fin.last nI)
      rw [hC1.2.1, hC1.2.2] at h
      have h1 : μ.real (d.conf (Fin.last nI)) = 1 := le_antisymm h.2 h.1
      exact (ENNReal.toReal_eq_one_iff _).mp h1
    have hae : ∀ᵐ ω ∂μ, ω ∈ d.conf (Fin.last nI) :=
      mem_ae_iff.mpr ((prob_compl_eq_zero_iff (hmeas _)).mpr hCI)
    have hFint : ∀ j, Integrable (fun ω => (d.conf j).indicator (fun _ => (1 : ℝ)) ω *
        (κ j - lam j)) μ := by
      intro j; simp_rw [hind (fun j => κ j - lam j)]
      exact (integrable_const _).indicator (hmeas j)
    have hLint := Fdot_int d μ hint β
    calc ∫ ω, v.eval x ω.1 ∂μ
        ≤ ∫ ω, ((d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β +
            ∑ j, (d.conf j).indicator (fun _ => (1 : ℝ)) ω * (κ j - lam j)) ∂μ := by
          refine integral_mono_ae (vint v x μ hint)
            (hLint.add (integrable_finsetSum _ fun j _ => hFint j)) ?_
          filter_upwards [hae] with ω hω
          exact hdual ω hω
      _ = d.b ⬝ᵥ β + ∑ j, μ.real (d.conf j) * (κ j - lam j) := by
          rw [integral_add hLint (integrable_finsetSum _ fun j _ => hFint j),
            Fdot_integral d μ hint β, hmean, integral_finsetSum _ fun j _ => hFint j]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          simp_rw [hind (fun j => κ j - lam j)]
          rw [integral_indicator_const _ (hmeas j), smul_eq_mul]
      _ ≤ d.b ⬝ᵥ β + ∑ i, (d.phi i * κ i - d.plo i * lam i) := by
          gcongr with j
          have h := hconf j
          nlinarith [mul_le_mul_of_nonneg_right h.2 (hκ j), mul_le_mul_of_nonneg_right h.1 (hlam j)]
      _ ≤ w := hobj
