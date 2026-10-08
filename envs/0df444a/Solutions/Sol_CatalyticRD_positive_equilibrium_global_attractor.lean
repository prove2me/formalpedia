-- Prove2me | solution 1 for CatalyticRD.positive_equilibrium_global_attractor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-04T18:28:39.312992+00:00
-- url     : https://prove2.me/submissions/c17de694-89d8-438c-9e64-b93445c1aede
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CatalyticRD_Setup
import Theorems.Thm_CatalyticRD_crd2_integral_laplacian_neumann
import Theorems.Thm_CatalyticRD_crd2_solution_pos
import Theorems.Thm_CatalyticRD_crd2_omega_limit_equilibria

open MeasureTheory Set Filter Topology Laplacian

/-! ## Abstract steps (vi)–(vii) -/

namespace CatalyticRD.Abstract

variable {X : Type*} [MeasurableSpace X]

/-- Uniform `ε`-closeness on `S` of `(a,b,c)(t)` to the constant state `(α, β, γ)`. -/
def Near (S : Set X) (a b c : ℝ → X → ℝ) (α β γ ε t : ℝ) : Prop :=
  ∀ x ∈ S, |a t x - α| < ε ∧ |b t x - β| < ε ∧ |c t x - γ| < ε

/-- Step (vi) algebra: spatially homogeneous equilibria with prescribed masses. -/
theorem crd_equilibria {M₁ M₂ α β γ : ℝ} (h1 : α + γ = M₁) (h2 : β + γ = M₂)
    (h3 : β * (γ - α) = 0) :
    (α = M₁ / 2 ∧ β = M₂ - M₁ / 2 ∧ γ = M₁ / 2) ∨ (α = M₁ - M₂ ∧ β = 0 ∧ γ = M₂) := by
  rcases mul_eq_zero.1 h3 with h | h
  · right; refine ⟨?_, h, ?_⟩ <;> linarith
  · left; refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- If `F k → k₀` uniformly on `S`, `μ S = 1` and the `F k` are integrable on `S`, then
`∫_S F k → k₀`. -/
theorem tendsto_setIntegral_of_tendstoUniformlyOn_const {μ : Measure X} {S : Set X}
    (hvol : μ S = 1) {F : ℕ → X → ℝ} {k₀ : ℝ}
    (hF : TendstoUniformlyOn F (fun _ => k₀) atTop S) (hint : ∀ k, IntegrableOn (F k) S μ) :
    Tendsto (fun k => ∫ x in S, F k x ∂μ) atTop (𝓝 k₀) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendstoUniformlyOn_iff] at hF
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hF (ε / 2) (by linarith))
  refine ⟨N, fun k hk => ?_⟩
  have hfin : μ S < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hreal : μ.real S = 1 := by simp [Measure.real, hvol]
  have hsub : ∫ x in S, F k x ∂μ - k₀ = ∫ x in S, (F k x - k₀) ∂μ := by
    rw [integral_sub (hint k) (integrableOn_const hfin.ne), setIntegral_const, hreal, one_smul]
  have hb : ‖∫ x in S, (F k x - k₀) ∂μ‖ ≤ ε / 2 * μ.real S :=
    norm_setIntegral_le_of_norm_le_const hfin fun x hx => by
      have := hN k hk x hx
      rw [Real.dist_eq, abs_sub_comm] at this
      rw [Real.norm_eq_abs]; exact this.le
  rw [Real.dist_eq, hsub]
  rw [hreal, mul_one, Real.norm_eq_abs] at hb
  linarith

/-- Steps (iv)+(v)+(vi), abstract form: if every sequence of times `→ ∞` has a subsequence along
which `(a,b,c)` converges uniformly on `S` to a constant equilibrium `(α,β,γ)` (`β(γ-α) = 0`), and
the masses are conserved, then for every `ε > 0` the state is eventually uniformly `ε`-close to
`E₊ = (M₁/2, M₂-M₁/2, M₁/2)` or to `E₀ = (M₁-M₂, 0, M₂)`. -/
theorem crd_near_one_of_omega {μ : Measure X} {S : Set X} (hvol : μ S = 1)
    {a b c : ℝ → X → ℝ} {M₁ M₂ : ℝ}
    (hint : ∀ t ≥ 0, IntegrableOn (a t) S μ ∧ IntegrableOn (b t) S μ ∧ IntegrableOn (c t) S μ)
    (hmass : ∀ t ≥ 0, (∫ x in S, (a t x + c t x) ∂μ) = M₁ ∧ (∫ x in S, (b t x + c t x) ∂μ) = M₂)
    (homega : ∀ u : ℕ → ℝ, Tendsto u atTop atTop → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ α β γ : ℝ, β * (γ - α) = 0 ∧
        TendstoUniformlyOn (fun k => a (u (ψ k))) (fun _ => α) atTop S ∧
        TendstoUniformlyOn (fun k => b (u (ψ k))) (fun _ => β) atTop S ∧
        TendstoUniformlyOn (fun k => c (u (ψ k))) (fun _ => γ) atTop S) :
    ∀ ε > 0, ∀ᶠ t in atTop,
      Near S a b c (M₁ / 2) (M₂ - M₁ / 2) (M₁ / 2) ε t ∨ Near S a b c (M₁ - M₂) 0 M₂ ε t := by
  intro ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨u, hu, hnot⟩ := exists_seq_forall_of_frequently hcon
  obtain ⟨ψ, hψ, α, β, γ, heq, ha, hb, hc⟩ := homega u hu
  have huψ : Tendsto (fun k => u (ψ k)) atTop atTop := hu.comp hψ.tendsto_atTop
  have hev0 : ∀ᶠ k in atTop, 0 ≤ u (ψ k) := huψ.eventually (eventually_ge_atTop 0)
  -- masses of the limit
  have hlimit : ∀ (f g : ℝ → X → ℝ) (p q M : ℝ),
      TendstoUniformlyOn (fun k => f (u (ψ k))) (fun _ => p) atTop S →
      TendstoUniformlyOn (fun k => g (u (ψ k))) (fun _ => q) atTop S →
      (∀ t ≥ 0, IntegrableOn (f t) S μ ∧ IntegrableOn (g t) S μ) →
      (∀ t ≥ 0, ∫ x in S, (f t x + g t x) ∂μ = M) → p + q = M := by
    intro f g p q M hf hg hfi hfm
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev0
    have hsum : TendstoUniformlyOn (fun k => fun x => f (u (ψ (k + N))) x + g (u (ψ (k + N))) x)
        (fun _ => p + q) atTop S := by
      rw [Metric.tendstoUniformlyOn_iff] at hf hg ⊢
      intro δ hδ
      have hf' := (tendsto_add_atTop_nat N).eventually (hf (δ / 2) (by linarith))
      have hg' := (tendsto_add_atTop_nat N).eventually (hg (δ / 2) (by linarith))
      filter_upwards [hf', hg'] with k h1 h2 x hx
      have e1 := h1 x hx; have e2 := h2 x hx
      rw [Real.dist_eq] at e1 e2 ⊢
      calc |p + q - (f (u (ψ (k + N))) x + g (u (ψ (k + N))) x)|
          = |(p - f (u (ψ (k + N))) x) + (q - g (u (ψ (k + N))) x)| := by ring_nf
        _ ≤ |p - f (u (ψ (k + N))) x| + |q - g (u (ψ (k + N))) x| := abs_add_le _ _
        _ < δ := by linarith
    have hT := tendsto_setIntegral_of_tendstoUniformlyOn_const hvol hsum (fun k => by
      have h := hfi _ (hN (k + N) (by omega))
      exact h.1.add h.2)
    have hconst : (fun k => ∫ x in S, (f (u (ψ (k + N))) x + g (u (ψ (k + N))) x) ∂μ) =
        fun _ => M := funext fun k => hfm _ (hN (k + N) (by omega))
    rw [hconst] at hT
    exact (tendsto_nhds_unique tendsto_const_nhds hT).symm
  have hm1 : α + γ = M₁ := hlimit a c α γ M₁ ha hc (fun t ht => ⟨(hint t ht).1, (hint t ht).2.2⟩)
    (fun t ht => (hmass t ht).1)
  have hm2 : β + γ = M₂ := hlimit b c β γ M₂ hb hc (fun t ht => ⟨(hint t ht).2.1, (hint t ht).2.2⟩)
    (fun t ht => (hmass t ht).2)
  rw [Metric.tendstoUniformlyOn_iff] at ha hb hc
  have hall : ∀ᶠ k in atTop, Near S a b c α β γ ε (u (ψ k)) := by
    filter_upwards [ha ε hε, hb ε hε, hc ε hε] with k h1 h2 h3 x hx
    refine ⟨?_, ?_, ?_⟩
    · have := h1 x hx; rwa [Real.dist_eq, abs_sub_comm] at this
    · have := h2 x hx; rwa [Real.dist_eq, abs_sub_comm] at this
    · have := h3 x hx; rwa [Real.dist_eq, abs_sub_comm] at this
  obtain ⟨k, hk⟩ := hall.exists
  apply hnot (ψ k)
  rcases crd_equilibria hm1 hm2 heq with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
  · left; subst e1 e2 e3; exact hk
  · right; subst e1 e2 e3; exact hk

omit [MeasurableSpace X] in
/-- Step (vi), connectedness: with `δ = M₂ - M₁/2 > 0` the two neighbourhoods are separated in
the `b`-coordinate, so by the intermediate value theorem (continuity of `t ↦ b t x₀`) the
trajectory eventually stays near one and the same equilibrium. -/
theorem crd_dichotomy {S : Set X} {a b c : ℝ → X → ℝ} {M₁ M₂ : ℝ} (hM : M₁ < 2 * M₂)
    {x₀ : X} (hx₀ : x₀ ∈ S) (hcont : ContinuousOn (fun t => b t x₀) (Ici 0))
    (hnear : ∀ ε > 0, ∀ᶠ t in atTop,
      Near S a b c (M₁ / 2) (M₂ - M₁ / 2) (M₁ / 2) ε t ∨ Near S a b c (M₁ - M₂) 0 M₂ ε t) :
    (∀ ε > 0, ∀ᶠ t in atTop, Near S a b c (M₁ / 2) (M₂ - M₁ / 2) (M₁ / 2) ε t) ∨
      (∀ ε > 0, ∀ᶠ t in atTop, Near S a b c (M₁ - M₂) 0 M₂ ε t) := by
  set δ := M₂ - M₁ / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set ε₀ := δ / 3 with hε₀
  have hε₀pos : 0 < ε₀ := by positivity
  -- at x₀ the two neighbourhoods (radius ≤ ε₀) are disjoint in the `b` coordinate
  have hP_b : ∀ {ε t}, ε ≤ ε₀ → Near S a b c (M₁ / 2) δ (M₁ / 2) ε t → 2 * ε₀ < b t x₀ :=
    fun hε h => by have := (h x₀ hx₀).2.1; rw [abs_lt] at this; linarith
  have hB_b : ∀ {ε t}, ε ≤ ε₀ → Near S a b c (M₁ - M₂) 0 M₂ ε t → b t x₀ < ε₀ :=
    fun hε h => by have := (h x₀ hx₀).2.1; rw [abs_lt] at this; linarith
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 ((hnear ε₀ hε₀pos).and (eventually_ge_atTop 0))
  -- no switching on `[T₀, ∞)`
  have hnoswitch : ∀ t₁ ≥ T₀, ∀ t₂ ≥ T₀, Near S a b c (M₁ / 2) δ (M₁ / 2) ε₀ t₁ →
      Near S a b c (M₁ - M₂) 0 M₂ ε₀ t₂ → False := by
    intro t₁ h₁ t₂ h₂ hP hB
    have hsub : uIcc t₁ t₂ ⊆ Ici 0 := fun s hs => by
      have := (hT₀ t₁ h₁).2; have := (hT₀ t₂ h₂).2
      simp only [mem_Ici]; rcases le_total t₁ t₂ with h | h
      · rw [uIcc_of_le h] at hs; linarith [hs.1]
      · rw [uIcc_of_ge h] at hs; linarith [hs.1]
    have hivt := intermediate_value_uIcc (hcont.mono hsub)
    have hmid : (3 / 2 : ℝ) * ε₀ ∈ uIcc (b t₁ x₀) (b t₂ x₀) := by
      have := hP_b le_rfl hP; have := hB_b le_rfl hB
      rw [mem_uIcc]; right; constructor <;> linarith
    obtain ⟨s, hs, hbs⟩ := hivt hmid
    have hsT : T₀ ≤ s := by
      rcases le_total t₁ t₂ with h | h
      · rw [uIcc_of_le h] at hs; linarith [hs.1]
      · rw [uIcc_of_ge h] at hs; linarith [hs.1]
    rcases (hT₀ s hsT).1 with h | h
    · have := hP_b le_rfl h; simp only at hbs; linarith
    · have := hB_b le_rfl h; simp only at hbs; linarith
  by_cases hallP : ∀ t ≥ T₀, Near S a b c (M₁ / 2) δ (M₁ / 2) ε₀ t
  · left
    intro ε hε
    filter_upwards [hnear (min ε ε₀) (lt_min hε hε₀pos), eventually_ge_atTop T₀] with t ht htT
    rcases ht with h | h
    · intro x hx
      obtain ⟨h1, h2, h3⟩ := h x hx
      exact ⟨h1.trans_le (min_le_left _ _), h2.trans_le (min_le_left _ _),
        h3.trans_le (min_le_left _ _)⟩
    · exact absurd ((hP_b le_rfl (hallP t htT)).trans (hB_b (min_le_right _ _) h)) (by linarith)
  · right
    push Not at hallP
    obtain ⟨t₁, ht₁, hnP⟩ := hallP
    have hB₁ : Near S a b c (M₁ - M₂) 0 M₂ ε₀ t₁ := by
      rcases (hT₀ t₁ ht₁).1 with h | h
      · exact absurd h hnP
      · exact h
    intro ε hε
    filter_upwards [hnear (min ε ε₀) (lt_min hε hε₀pos), eventually_ge_atTop T₀] with t ht htT
    rcases ht with h | h
    · exfalso
      refine hnoswitch t htT t₁ ht₁ ?_ hB₁
      intro x hx
      obtain ⟨h1, h2, h3⟩ := h x hx
      exact ⟨h1.trans_le (min_le_right _ _), h2.trans_le (min_le_right _ _),
        h3.trans_le (min_le_right _ _)⟩
    · intro x hx
      obtain ⟨h1, h2, h3⟩ := h x hx
      exact ⟨h1.trans_le (min_le_left _ _), h2.trans_le (min_le_left _ _),
        h3.trans_le (min_le_left _ _)⟩

/-- Step (vii): the boundary equilibrium `E₀ = (M₁-M₂, 0, M₂)` cannot attract when `M₁ < 2M₂`.
Near `E₀`, `c - a ≥ (2M₂-M₁)/2 > 0`, so `d/dt ∫b = ∫ b (c - a) ≥ 0` and `∫ b` is eventually
nondecreasing and strictly positive, contradicting `∫ b → 0`. -/
theorem crd_exclude_boundary {μ : Measure X} {S : Set X} (hS : MeasurableSet S)
    (hvol : μ S = 1) {a b c : ℝ → X → ℝ} {M₁ M₂ : ℝ} (hM : M₁ < 2 * M₂)
    (hbpos : ∀ t ≥ 0, ∀ x ∈ S, 0 < b t x)
    (hIpos : ∀ t ≥ 0, 0 < ∫ x in S, b t x ∂μ)
    (hderiv : ∀ t > 0, HasDerivAt (fun s => ∫ x in S, b s x ∂μ)
      (∫ x in S, b t x * (c t x - a t x) ∂μ) t)
    (hB : ∀ ε > 0, ∀ᶠ t in atTop, Near S a b c (M₁ - M₂) 0 M₂ ε t) : False := by
  set κ := 2 * M₂ - M₁ with hκ
  have hκpos : 0 < κ := by rw [hκ]; linarith
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (hB (κ / 4) (by positivity))
  set T := max T₁ 1 with hT
  have hTpos : 0 < T := lt_of_lt_of_le one_pos (le_max_right _ _)
  set F : ℝ → ℝ := fun s => ∫ x in S, b s x ∂μ with hF
  -- `F` is nondecreasing on `[T, ∞)`
  have hmono : MonotoneOn F (Ici T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici T)
    · intro t ht
      exact (hderiv t (lt_of_lt_of_le hTpos ht)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hderiv t (hTpos.trans ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have htpos : 0 < t := hTpos.trans ht
      rw [(hderiv t htpos).deriv]
      refine setIntegral_nonneg hS fun x hx => ?_
      have hN := hT₁ t (le_trans (le_max_left _ _) ht.le) x hx
      obtain ⟨h1, -, h3⟩ := hN
      rw [abs_lt] at h1 h3
      have : 0 ≤ c t x - a t x := by linarith
      exact mul_nonneg (hbpos t htpos.le x hx).le this
  have hFT : 0 < F T := hIpos T hTpos.le
  -- but `F → 0`
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.1 (hB (F T / 2) (by positivity))
  set t := max T T₂
  have hFt : F T ≤ F t := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 (le_max_left _ _))
    (le_max_left _ _)
  have hfin : μ S < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hbound : ‖F t‖ ≤ F T / 2 * μ.real S :=
    norm_setIntegral_le_of_norm_le_const hfin fun x hx => by
      have := (hT₂ t (le_max_right _ _) x hx).2.1
      rw [sub_zero] at this
      rw [Real.norm_eq_abs]; exact this.le
  have hreal : μ.real S = 1 := by simp [Measure.real, hvol]
  rw [hreal, mul_one, Real.norm_eq_abs] at hbound
  have := le_abs_self (F t)
  linarith

omit [MeasurableSpace X] in
/-- Uniform convergence from the `Near` formulation. -/
theorem tendstoUniformlyOn_of_near {S : Set X} {a b c : ℝ → X → ℝ} {α β γ : ℝ}
    (h : ∀ ε > 0, ∀ᶠ t in atTop, Near S a b c α β γ ε t) :
    TendstoUniformlyOn a (fun _ => α) atTop S ∧ TendstoUniformlyOn b (fun _ => β) atTop S ∧
      TendstoUniformlyOn c (fun _ => γ) atTop S := by
  simp only [Metric.tendstoUniformlyOn_iff, Real.dist_eq]
  refine ⟨fun ε hε => ?_, fun ε hε => ?_, fun ε hε => ?_⟩ <;>
    filter_upwards [h ε hε] with t ht x hx
  · rw [abs_sub_comm]; exact (ht x hx).1
  · rw [abs_sub_comm]; exact (ht x hx).2.1
  · rw [abs_sub_comm]; exact (ht x hx).2.2

/-- Assembly of steps (vi)–(vii) at the abstract level. -/
theorem crd_abstract_attractor {μ : Measure X} {S : Set X} (hS : MeasurableSet S)
    (hvol : μ S = 1) {a b c : ℝ → X → ℝ} {M₁ M₂ : ℝ} (hM : M₁ < 2 * M₂)
    {x₀ : X} (hx₀ : x₀ ∈ S) (hcont : ContinuousOn (fun t => b t x₀) (Ici 0))
    (hint : ∀ t ≥ 0, IntegrableOn (a t) S μ ∧ IntegrableOn (b t) S μ ∧ IntegrableOn (c t) S μ)
    (hmass : ∀ t ≥ 0, (∫ x in S, (a t x + c t x) ∂μ) = M₁ ∧ (∫ x in S, (b t x + c t x) ∂μ) = M₂)
    (hbpos : ∀ t ≥ 0, ∀ x ∈ S, 0 < b t x)
    (hIpos : ∀ t ≥ 0, 0 < ∫ x in S, b t x ∂μ)
    (hderiv : ∀ t > 0, HasDerivAt (fun s => ∫ x in S, b s x ∂μ)
      (∫ x in S, b t x * (c t x - a t x) ∂μ) t)
    (homega : ∀ u : ℕ → ℝ, Tendsto u atTop atTop → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ α β γ : ℝ, β * (γ - α) = 0 ∧
        TendstoUniformlyOn (fun k => a (u (ψ k))) (fun _ => α) atTop S ∧
        TendstoUniformlyOn (fun k => b (u (ψ k))) (fun _ => β) atTop S ∧
        TendstoUniformlyOn (fun k => c (u (ψ k))) (fun _ => γ) atTop S) :
    TendstoUniformlyOn a (fun _ => M₁ / 2) atTop S ∧
      TendstoUniformlyOn b (fun _ => M₂ - M₁ / 2) atTop S ∧
      TendstoUniformlyOn c (fun _ => M₁ / 2) atTop S := by
  have hnear := crd_near_one_of_omega hvol hint hmass homega
  rcases crd_dichotomy hM hx₀ hcont hnear with hP | hB
  · exact tendstoUniformlyOn_of_near hP
  · exact (crd_exclude_boundary hS hvol hM hbpos hIpos hderiv hB).elim

end CatalyticRD.Abstract

/-! ## Calculus of spatial integrals (mass conservation, d/dt ∫b) -/

namespace CatalyticRD

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {φ : EuclideanSpace ℝ (Fin n) → ℝ}

theorem IsSmoothBoundedDomain.isCompact_closure (hΩ : IsSmoothBoundedDomain Ω φ) :
    IsCompact (closure Ω) :=
  hΩ.isBounded.isCompact_closure

theorem IsC12.continuousOn_slice {u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ} (hu : IsC12 Ω u)
    {t : ℝ} (ht : 0 ≤ t) : ContinuousOn (u t) (closure Ω) :=
  hu.continuousOn.comp (Continuous.continuousOn (by fun_prop :
    Continuous fun x : EuclideanSpace ℝ (Fin n) => (t, x))) (fun _ hx => ⟨mem_Ici.2 ht, hx⟩)

theorem IsC12.continuousOn_time {u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ} (hu : IsC12 Ω u)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ closure Ω) : ContinuousOn (fun t => u t x) (Ici 0) :=
  hu.continuousOn.comp (Continuous.continuousOn (by fun_prop :
    Continuous fun t : ℝ => (t, x))) (fun _ ht => ⟨ht, hx⟩)

theorem IsC12.continuousOn_time_deriv_slice {u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : IsC12 Ω u) {t : ℝ} (ht : 0 < t) :
    ContinuousOn (fun x => deriv (fun s => u s x) t) (closure Ω) :=
  hu.continuousOn_time_deriv.comp (Continuous.continuousOn (by fun_prop :
    Continuous fun x : EuclideanSpace ℝ (Fin n) => (t, x))) (fun _ hx => ⟨mem_Ioi.2 ht, hx⟩)

theorem integrableOn_of_continuousOn_closure (hΩ : IsSmoothBoundedDomain Ω φ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContinuousOn f (closure Ω)) : IntegrableOn f Ω :=
  (hf.integrableOn_compact hΩ.isCompact_closure).mono_set subset_closure

theorem IsC12.integrableOn {u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsSmoothBoundedDomain Ω φ)
    (hu : IsC12 Ω u) {t : ℝ} (ht : 0 ≤ t) : IntegrableOn (u t) Ω :=
  integrableOn_of_continuousOn_closure hΩ (hu.continuousOn_slice ht)

/-- A function continuous and positive on `Ω̄` has positive integral over `Ω` (`|Ω| = 1`). -/
theorem integral_pos_of_continuousOn_pos (hΩ : IsSmoothBoundedDomain Ω φ) (hvol : volume Ω = 1)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContinuousOn f (closure Ω))
    (hpos : ∀ x ∈ closure Ω, 0 < f x) : 0 < ∫ x in Ω, f x := by
  have hne : (closure Ω).Nonempty := hΩ.isConnected.nonempty.closure
  obtain ⟨x₀, hx₀, hmin⟩ := hΩ.isCompact_closure.exists_isMinOn hne hf
  have hfin : volume Ω < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hle : ∫ _ in Ω, f x₀ ≤ ∫ x in Ω, f x :=
    setIntegral_mono_on (integrableOn_const hfin.ne) (integrableOn_of_continuousOn_closure hΩ hf)
      hΩ.isOpen.measurableSet fun x hx => hmin (subset_closure hx)
  have hreal : volume.real Ω = 1 := by simp [Measure.real, hvol]
  rw [setIntegral_const, hreal, one_smul] at hle
  exact lt_of_lt_of_le (hpos x₀ hx₀) hle

/-- Differentiation under the integral sign for `C^{1,2}` functions on `(0,∞) × Ω̄`. -/
theorem IsC12.hasDerivAt_integral {u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hΩ : IsSmoothBoundedDomain Ω φ) (hu : IsC12 Ω u) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x => deriv (fun s => u s x) t) Ω ∧
      HasDerivAt (fun s => ∫ x in Ω, u s x) (∫ x in Ω, deriv (fun s => u s x) t) t := by
  have hmeas : MeasurableSet Ω := hΩ.isOpen.measurableSet
  have hK : IsCompact (Icc (t / 2) (2 * t) ×ˢ closure Ω) :=
    isCompact_Icc.prod hΩ.isCompact_closure
  have hKsub : Icc (t / 2) (2 * t) ×ˢ closure Ω ⊆ Ioi 0 ×ˢ closure Ω :=
    prod_mono (fun s hs => mem_Ioi.2 (by linarith [hs.1])) le_rfl
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hu.continuousOn_time_deriv.mono hKsub)
  have hfin : volume Ω < ⊤ := hΩ.isBounded.measure_lt_top
  have hs : Ioo (t / 2) (2 * t) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict Ω)
    (F := fun s x => u s x) (F' := fun s x => deriv (fun s => u s x) s) (x₀ := t)
    (bound := fun _ => C) hs
    (by
      filter_upwards [Ioi_mem_nhds ht] with s hs'
      exact (hu.continuousOn_slice (le_of_lt hs')).mono subset_closure |>.aestronglyMeasurable
        hmeas)
    (hu.integrableOn hΩ ht.le)
    ((hu.continuousOn_time_deriv_slice ht).mono subset_closure |>.aestronglyMeasurable hmeas)
    (ae_restrict_of_forall_mem hmeas fun x hx s hs' =>
      hC (s, x) ⟨Ioo_subset_Icc_self hs', subset_closure hx⟩)
    (integrableOn_const hfin.ne)
    (ae_restrict_of_forall_mem hmeas fun x hx s hs' =>
      (hu.differentiableAt_time x (subset_closure hx) s (by linarith [hs'.1])).hasDerivAt)
  exact this

/-- Continuity of `t ↦ ∫_Ω u t` on `[0, T]`. -/
theorem IsC12.continuousOn_integral {u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hΩ : IsSmoothBoundedDomain Ω φ) (hu : IsC12 Ω u) (T : ℝ) :
    ContinuousOn (fun s => ∫ x in Ω, u s x) (Icc 0 T) := by
  have hmeas : MeasurableSet Ω := hΩ.isOpen.measurableSet
  have hK : IsCompact (Icc 0 T ×ˢ closure Ω) := isCompact_Icc.prod hΩ.isCompact_closure
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hu.continuousOn.mono (prod_mono Icc_subset_Ici_self le_rfl))
  have hfin : volume Ω < ⊤ := hΩ.isBounded.measure_lt_top
  refine continuousOn_of_dominated (bound := fun _ => C)
    (fun s hs => (hu.continuousOn_slice hs.1).mono subset_closure |>.aestronglyMeasurable hmeas)
    (fun s hs => ae_restrict_of_forall_mem hmeas fun x hx => hC (s, x) ⟨hs, subset_closure hx⟩)
    (integrableOn_const hfin.ne)
    (ae_restrict_of_forall_mem hmeas fun x hx =>
      (hu.continuousOn_time (subset_closure hx)).mono Icc_subset_Ici_self)

/-- Integrating a reaction–diffusion equation with Neumann data over `Ω`: the diffusion term
integrates to zero (divergence theorem). -/
theorem integral_time_deriv_eq {u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hΩ : IsSmoothBoundedDomain Ω φ) (hu : IsC12 Ω u) {t d : ℝ} (ht : 0 < t) (hd : 0 < d)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IntegrableOn f Ω)
    (heq : ∀ x ∈ Ω, deriv (fun s => u s x) t - d * Δ (u t) x = f x)
    (hN : NeumannBC Ω φ (u t)) :
    ∫ x in Ω, deriv (fun s => u s x) t = ∫ x in Ω, f x := by
  have hmeas : MeasurableSet Ω := hΩ.isOpen.measurableSet
  have hdt := (hu.hasDerivAt_integral hΩ ht).1
  have hlap : EqOn (fun x => (deriv (fun s => u s x) t - f x) / d) (fun x => Δ (u t) x) Ω :=
    fun x hx => by
      have := heq x hx
      field_simp
      linarith
  have h1 : IntegrableOn (fun x => (deriv (fun s => u s x) t - f x) / d) Ω :=
    (hdt.sub hf).div_const d
  have hlapint : IntegrableOn (fun x => Δ (u t) x) Ω := h1.congr_fun hlap hmeas
  have hzero := crd2_integral_laplacian_neumann Ω φ hΩ (u t) (hu.contDiffOn_space t ht) hN
  calc ∫ x in Ω, deriv (fun s => u s x) t = ∫ x in Ω, (d * Δ (u t) x + f x) :=
        setIntegral_congr_fun hmeas fun x hx => by have := heq x hx; linarith
    _ = d * (∫ x in Ω, Δ (u t) x) + ∫ x in Ω, f x := by
        rw [integral_add (hlapint.const_mul d) hf, integral_const_mul]
    _ = ∫ x in Ω, f x := by simp only [hzero, mul_zero, zero_add]

section Solution

variable {d₁ d₂ d₃ : ℝ} {a₀ b₀ c₀ : EuclideanSpace ℝ (Fin n) → ℝ}
  {a b c : ℝ → EuclideanSpace ℝ (Fin n) → ℝ}

theorem reaction_integrable (hΩ : IsSmoothBoundedDomain Ω φ)
    (hsol : IsClassicalSolution Ω φ d₁ d₂ d₃ a₀ b₀ c₀ a b c) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun x => b t x * (c t x - a t x)) Ω :=
  integrableOn_of_continuousOn_closure hΩ ((hsol.reg_b.continuousOn_slice ht).mul
    ((hsol.reg_c.continuousOn_slice ht).sub (hsol.reg_a.continuousOn_slice ht)))

theorem hasDerivAt_integral_a (hΩ : IsSmoothBoundedDomain Ω φ) (hd₁ : 0 < d₁)
    (hsol : IsClassicalSolution Ω φ d₁ d₂ d₃ a₀ b₀ c₀ a b c) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in Ω, a s x) (∫ x in Ω, b t x * (c t x - a t x)) t := by
  have h := (hsol.reg_a.hasDerivAt_integral hΩ ht).2
  rwa [integral_time_deriv_eq hΩ hsol.reg_a ht hd₁ (reaction_integrable hΩ hsol ht.le)
    (hsol.eq_a t ht) (hsol.bc_a t ht)] at h

theorem hasDerivAt_integral_b (hΩ : IsSmoothBoundedDomain Ω φ) (hd₂ : 0 < d₂)
    (hsol : IsClassicalSolution Ω φ d₁ d₂ d₃ a₀ b₀ c₀ a b c) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in Ω, b s x) (∫ x in Ω, b t x * (c t x - a t x)) t := by
  have h := (hsol.reg_b.hasDerivAt_integral hΩ ht).2
  rwa [integral_time_deriv_eq hΩ hsol.reg_b ht hd₂ (reaction_integrable hΩ hsol ht.le)
    (hsol.eq_b t ht) (hsol.bc_b t ht)] at h

theorem hasDerivAt_integral_c (hΩ : IsSmoothBoundedDomain Ω φ) (hd₃ : 0 < d₃)
    (hsol : IsClassicalSolution Ω φ d₁ d₂ d₃ a₀ b₀ c₀ a b c) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in Ω, c s x) (-∫ x in Ω, b t x * (c t x - a t x)) t := by
  have h := (hsol.reg_c.hasDerivAt_integral hΩ ht).2
  rw [integral_time_deriv_eq hΩ hsol.reg_c ht hd₃ (reaction_integrable hΩ hsol ht.le).neg
    (hsol.eq_c t ht) (hsol.bc_c t ht)] at h
  have e : (∫ x in Ω, (-fun x => b t x * (c t x - a t x)) x) =
      -∫ x in Ω, b t x * (c t x - a t x) := by
    rw [← integral_neg]; rfl
  rwa [e] at h

/-- If `F, G` are continuous on `[0,∞)`, differentiable on `(0,∞)` with `F' + G' = 0`, then
`F + G` is constant on `[0,∞)`. -/
theorem sum_const_of_deriv {F G : ℝ → ℝ} (hF : ∀ T, ContinuousOn F (Icc 0 T))
    (hG : ∀ T, ContinuousOn G (Icc 0 T)) (F' : ℝ → ℝ)
    (hF' : ∀ t > 0, HasDerivAt F (F' t) t) (hG' : ∀ t > 0, HasDerivAt G (-F' t) t) :
    ∀ t ≥ 0, F t + G t = F 0 + G 0 := by
  intro t ht
  rcases ht.lt_or_eq with ht | ht
  · obtain ⟨s, hs, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => F s + G s) (fun _ => 0) ht
      ((hF t).add (hG t)) (fun s hs => ((hF' s hs.1).add (hG' s hs.1)).congr_deriv (by ring))
    have : (F t + G t) - (F 0 + G 0) = 0 := by
      rw [eq_div_iff (by linarith)] at hslope; linarith
    linarith
  · rw [← ht]

theorem crd2_hasDerivAt_integral_b {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hΩ : IsSmoothBoundedDomain Ω φ)
    (d₁ d₂ d₃ : ℝ) (hd₂ : 0 < d₂) (a₀ b₀ c₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (a b c : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hsol : IsClassicalSolution Ω φ d₁ d₂ d₃ a₀ b₀ c₀ a b c) :
    ∀ t > 0, HasDerivAt (fun s => ∫ x in Ω, b s x) (∫ x in Ω, b t x * (c t x - a t x)) t :=
  fun _ ht => hasDerivAt_integral_b hΩ hd₂ hsol ht

/-- Step (i): mass conservation. -/
theorem crd2_mass_conservation {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hΩ : IsSmoothBoundedDomain Ω φ)
    (d₁ d₂ d₃ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (a₀ b₀ c₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (a b c : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hsol : IsClassicalSolution Ω φ d₁ d₂ d₃ a₀ b₀ c₀ a b c) :
    ∀ t ≥ 0, (∫ x in Ω, (a t x + c t x)) = ∫ x in Ω, (a₀ x + c₀ x) ∧
      (∫ x in Ω, (b t x + c t x)) = ∫ x in Ω, (b₀ x + c₀ x) := by
  have hmeas : MeasurableSet Ω := hΩ.isOpen.measurableSet
  intro t ht
  have hinit : ∀ (u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) (u₀ : EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ x ∈ closure Ω, u 0 x = u₀ x) → ∫ x in Ω, u 0 x = ∫ x in Ω, u₀ x :=
    fun u u₀ h => setIntegral_congr_fun hmeas fun x hx => h x (subset_closure hx)
  have hac := sum_const_of_deriv (hsol.reg_a.continuousOn_integral hΩ)
    (hsol.reg_c.continuousOn_integral hΩ) _ (fun s hs => hasDerivAt_integral_a hΩ hd₁ hsol hs)
    (fun s hs => hasDerivAt_integral_c hΩ hd₃ hsol hs) t ht
  have hbc := sum_const_of_deriv (hsol.reg_b.continuousOn_integral hΩ)
    (hsol.reg_c.continuousOn_integral hΩ) _ (fun s hs => hasDerivAt_integral_b hΩ hd₂ hsol hs)
    (fun s hs => hasDerivAt_integral_c hΩ hd₃ hsol hs) t ht
  have ia0 : IntegrableOn a₀ Ω := (hsol.reg_a.integrableOn hΩ le_rfl).congr_fun
    (fun x hx => hsol.init_a x (subset_closure hx)) hmeas
  have ib0 : IntegrableOn b₀ Ω := (hsol.reg_b.integrableOn hΩ le_rfl).congr_fun
    (fun x hx => hsol.init_b x (subset_closure hx)) hmeas
  have ic0 : IntegrableOn c₀ Ω := (hsol.reg_c.integrableOn hΩ le_rfl).congr_fun
    (fun x hx => hsol.init_c x (subset_closure hx)) hmeas
  rw [hinit a a₀ hsol.init_a, hinit c c₀ hsol.init_c] at hac
  rw [hinit b b₀ hsol.init_b, hinit c c₀ hsol.init_c] at hbc
  refine ⟨?_, ?_⟩
  · rw [integral_add (hsol.reg_a.integrableOn hΩ ht) (hsol.reg_c.integrableOn hΩ ht),
      integral_add ia0 ic0, hac]
  · rw [integral_add (hsol.reg_b.integrableOn hΩ ht) (hsol.reg_c.integrableOn hΩ ht),
      integral_add ib0 ic0, hbc]

end Solution

end CatalyticRD

/-! ## Main reduction -/

open CatalyticRD

theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hΩ : IsSmoothBoundedDomain Ω φ) (hvol : volume Ω = 1)
    (d₁ d₂ d₃ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (a₀ b₀ c₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (ha₀ : IsAdmissibleDatum Ω φ a₀) (hb₀ : IsAdmissibleDatum Ω φ b₀)
    (hc₀ : IsAdmissibleDatum Ω φ c₀)
    (M₁ M₂ : ℝ) (hM₁ : M₁ = ∫ x in Ω, (a₀ x + c₀ x)) (hM₂ : M₂ = ∫ x in Ω, (b₀ x + c₀ x))
    (hM : M₂ ≤ M₁ ∧ M₁ < 2 * M₂)
    (a b c : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hsol : IsClassicalSolution Ω φ d₁ d₂ d₃ a₀ b₀ c₀ a b c) :
    TendstoUniformlyOn a (fun _ => M₁ / 2) atTop Ω ∧
      TendstoUniformlyOn b (fun _ => M₂ - M₁ / 2) atTop Ω ∧
      TendstoUniformlyOn c (fun _ => M₁ / 2) atTop Ω := by
  have hpos := crd2_solution_pos Ω φ hΩ hvol d₁ d₂ d₃ hd₁ hd₂ hd₃ a₀ b₀ c₀ ha₀ hb₀ hc₀ a b c hsol
  have hmass := crd2_mass_conservation Ω φ hΩ d₁ d₂ d₃ hd₁ hd₂ hd₃ a₀ b₀ c₀ a b c hsol
  have hderiv := crd2_hasDerivAt_integral_b Ω φ hΩ d₁ d₂ d₃ hd₂ a₀ b₀ c₀ a b c hsol
  have homega := crd2_omega_limit_equilibria Ω φ hΩ hvol d₁ d₂ d₃ hd₁ hd₂ hd₃ a₀ b₀ c₀
    ha₀ hb₀ hc₀ a b c hsol
  obtain ⟨x₀, hx₀⟩ := hΩ.isConnected.nonempty
  refine Abstract.crd_abstract_attractor (μ := volume) hΩ.isOpen.measurableSet hvol hM.2 hx₀
    (hsol.reg_b.continuousOn_time (subset_closure hx₀))
    (fun t ht => ⟨hsol.reg_a.integrableOn hΩ ht, hsol.reg_b.integrableOn hΩ ht,
      hsol.reg_c.integrableOn hΩ ht⟩)
    (fun t ht => by rw [hM₁, hM₂]; exact hmass t ht)
    (fun t ht x hx => (hpos t ht x (subset_closure hx)).2.1)
    (fun t ht => integral_pos_of_continuousOn_pos hΩ hvol (hsol.reg_b.continuousOn_slice ht)
      fun x hx => (hpos t ht x hx).2.1)
    hderiv homega
