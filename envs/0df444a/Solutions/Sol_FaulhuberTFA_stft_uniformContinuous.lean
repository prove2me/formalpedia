-- Prove2me | solution 1 for FaulhuberTFA.stft_uniformContinuous
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T20:33:39.82684+00:00
-- url     : https://prove2.me/submissions/9ab0c3d5-b2e9-4cbe-8612-a463c2b9e5c1

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

set_option autoImplicit false

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem uc_fact_two : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
attribute [local instance] uc_fact_two

variable {d : ℕ}

lemma uc_ePhase_norm (s : ℝ) : ‖ePhase s‖ = 1 := by
  unfold ePhase
  rw [show (2 * Real.pi * Complex.I * (s : ℂ)) = ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma uc_ePhase_cont : Continuous ePhase := by unfold ePhase; fun_prop

lemma uc_ePhase_add (a b : ℝ) : ePhase (a + b) = ePhase a * ePhase b := by
  unfold ePhase; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma uc_norm_sq (F : Lp ℂ 2 (volume : Measure (Rd d))) : ‖F‖ ^ 2 = ∫ t, ‖F t‖ ^ 2 := by
  have h1 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) F
  rw [L2.inner_def] at h1
  have h3 : ∫ a, ⟪(F : Rd d → ℂ) a, F a⟫_ℂ = ∫ a, ((‖F a‖ ^ 2 : ℝ) : ℂ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [RCLike.inner_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h3, integral_complex_ofReal] at h1
  have h4 := congrArg Complex.re h1
  simp only [Complex.ofReal_re] at h4
  rw [h4]; norm_cast

/-- Translation `T_x G` as an element of `L²`. -/
noncomputable def uc_A (G : Lp ℂ 2 (volume : Measure (Rd d))) (x : Rd d) : Lp ℂ 2 (volume : Measure (Rd d)) :=
  DomAddAct.mk (-x) +ᵥ G

lemma uc_A_dist (G : Lp ℂ 2 (volume : Measure (Rd d))) (x x' : Rd d) :
    dist (uc_A G x) (uc_A G x') = dist (DomAddAct.mk (x' - x) +ᵥ G) G := by
  unfold uc_A
  have : DomAddAct.mk (-x) = DomAddAct.mk (-x') + DomAddAct.mk (x' - x) := by
    rw [← DomAddAct.mk_add]; congr 1; abel
  rw [this, add_vadd, DomAddAct.dist_vadd_Lp]

lemma uc_A_uc (G : Lp ℂ 2 (volume : Measure (Rd d))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x x' : Rd d, dist x x' < δ → dist (uc_A G x) (uc_A G x') < ε := by
  have hc : Continuous (fun h : Rd d => DomAddAct.mk h +ᵥ G) :=
    DomAddAct.continuous_mk.vadd continuous_const
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 hc 0 ε hε
  refine ⟨δ, hδ, fun x x' hxx => ?_⟩
  rw [uc_A_dist]
  have h0 : DomAddAct.mk (0 : Rd d) +ᵥ G = G := zero_vadd _ _
  have := h (x' - x) (by rw [dist_zero_right, ← dist_eq_norm, dist_comm]; exact hxx)
  rwa [h0] at this

lemma uc_A_norm (G : Lp ℂ 2 (volume : Measure (Rd d))) (x : Rd d) : ‖uc_A G x‖ = ‖G‖ :=
  DomAddAct.norm_vadd_Lp _ _

lemma uc_A_ae {g : Rd d → ℂ} (hg : MemLp g 2 volume) (x : Rd d) :
    (uc_A (hg.toLp g) x : Rd d → ℂ) =ᵐ[volume] fun t => g (t - x) := by
  unfold uc_A
  rw [DomAddAct.mk_vadd_toLp]
  refine (MemLp.coeFn_toLp _).trans (Filter.Eventually.of_forall fun t => ?_)
  simp only [vadd_eq_add]; rw [neg_add_eq_sub]

lemma uc_memLp_mod {f : Rd d → ℂ} (hf : MemLp f 2 volume) (ω : Rd d) :
    MemLp (fun t => ePhase (-⟪ω, t⟫_ℝ) * f t) 2 volume := by
  refine hf.of_le ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact ((uc_ePhase_cont.comp (by fun_prop : Continuous fun t : Rd d => -⟪ω, t⟫_ℝ)
      ).aestronglyMeasurable).mul hf.1
  · rw [norm_mul, uc_ePhase_norm, one_mul]

/-- Modulation `M_{-ω} f` as an element of `L²`. -/
noncomputable def uc_B {f : Rd d → ℂ} (hf : MemLp f 2 volume) (ω : Rd d) : Lp ℂ 2 (volume : Measure (Rd d)) :=
  (uc_memLp_mod hf ω).toLp _

lemma uc_B_norm {f : Rd d → ℂ} (hf : MemLp f 2 volume) (ω : Rd d) :
    ‖uc_B hf ω‖ ≤ ‖hf.toLp f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [MemLp.coeFn_toLp (uc_memLp_mod hf ω), MemLp.coeFn_toLp hf] with t h1 h2
  unfold uc_B; rw [h1, h2, norm_mul, uc_ePhase_norm, one_mul]

noncomputable def uc_Phi (f : Rd d → ℂ) (η : Rd d) : ℝ := ∫ t, ‖ePhase (-⟪η, t⟫_ℝ) - 1‖ ^ 2 * ‖f t‖ ^ 2

lemma uc_Phi_cont {f : Rd d → ℂ} (hf : MemLp f 2 volume) : Continuous (uc_Phi f) := by
  have hc := uc_ePhase_cont
  apply continuous_of_dominated (bound := fun t => 4 * ‖f t‖ ^ 2)
  · intro η
    exact ((by fun_prop : Continuous fun t : Rd d => ‖ePhase (-⟪η, t⟫_ℝ) - 1‖ ^ 2
      ).aestronglyMeasurable).mul (hf.1.norm.pow 2)
  · intro η
    refine Filter.Eventually.of_forall fun t => ?_
    have h1 : ‖ePhase (-⟪η, t⟫_ℝ) - 1‖ ≤ 2 := by
      calc _ ≤ ‖ePhase (-⟪η, t⟫_ℝ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [uc_ePhase_norm, norm_one]; norm_num
    rw [Real.norm_of_nonneg (by positivity)]
    have h2 : ‖ePhase (-⟪η, t⟫_ℝ) - 1‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (ePhase (-⟪η, t⟫_ℝ) - 1)]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  · exact hf.norm.integrable_sq.const_mul 4
  · exact Filter.Eventually.of_forall fun t => by fun_prop

lemma uc_Phi_zero (f : Rd d → ℂ) : uc_Phi f 0 = 0 := by
  simp [uc_Phi, ePhase]

lemma uc_dist_B {f : Rd d → ℂ} (hf : MemLp f 2 volume) (ω ω' : Rd d) :
    dist (uc_B hf ω) (uc_B hf ω') ^ 2 = uc_Phi f (ω - ω') := by
  rw [dist_eq_norm, uc_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (uc_B hf ω) (uc_B hf ω'), MemLp.coeFn_toLp (uc_memLp_mod hf ω),
    MemLp.coeFn_toLp (uc_memLp_mod hf ω')] with t h h1 h2
  rw [h, Pi.sub_apply]
  unfold uc_B; rw [h1, h2]
  have : ePhase (-⟪ω, t⟫_ℝ) = ePhase (-⟪ω - ω', t⟫_ℝ) * ePhase (-⟪ω', t⟫_ℝ) := by
    rw [← uc_ePhase_add]; congr 1; rw [inner_sub_left]; ring
  rw [this, show ePhase (-⟪ω - ω', t⟫_ℝ) * ePhase (-⟪ω', t⟫_ℝ) * f t - ePhase (-⟪ω', t⟫_ℝ) * f t
      = (ePhase (-⟪ω - ω', t⟫_ℝ) - 1) * (ePhase (-⟪ω', t⟫_ℝ) * f t) by ring,
    norm_mul, norm_mul, uc_ePhase_norm, one_mul, mul_pow]

lemma uc_B_uc {f : Rd d → ℂ} (hf : MemLp f 2 volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ω ω' : Rd d, dist ω ω' < δ → dist (uc_B hf ω) (uc_B hf ω') < ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 (uc_Phi_cont hf) 0 (ε ^ 2) (by positivity)
  refine ⟨δ, hδ, fun ω ω' hω => ?_⟩
  have h1 := h (ω - ω') (by rw [dist_zero_right, ← dist_eq_norm]; exact hω)
  rw [uc_Phi_zero, Real.dist_eq, sub_zero, ← uc_dist_B hf] at h1
  have h2 : dist (uc_B hf ω) (uc_B hf ω') ^ 2 < ε ^ 2 := lt_of_le_of_lt (le_abs_self _) h1
  exact lt_of_pow_lt_pow_left₀ 2 hε.le h2

lemma uc_stft_eq {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x ω : Rd d) :
    stft g f x ω = ⟪uc_A (hg.toLp g) x, uc_B hf ω⟫_ℂ := by
  rw [L2.inner_def]; unfold stft
  apply integral_congr_ae
  filter_upwards [uc_A_ae hg x, MemLp.coeFn_toLp (uc_memLp_mod hf ω)] with t h1 h2
  rw [RCLike.inner_apply]; unfold uc_B; rw [h1, h2]; ring

end FaulhuberTFA

open FaulhuberTFA in
theorem solution {d : ℕ} {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    UniformContinuous (fun p : Rd d × Rd d => stft g f p.1 p.2) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  set G := hg.toLp g
  set K := ‖hf.toLp f‖ + ‖G‖ + 1 with hKdef
  have hK : 0 < K := by positivity
  have hc : 0 < ε / (2 * K) := by positivity
  obtain ⟨δ₁, hδ₁, h₁⟩ := uc_A_uc G hc
  obtain ⟨δ₂, hδ₂, h₂⟩ := uc_B_uc hf hc
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun {p q} hpq => ?_⟩
  rw [Prod.dist_eq, max_lt_iff] at hpq
  have ha := h₁ p.1 q.1 (lt_of_lt_of_le hpq.1 (min_le_left _ _))
  have hb := h₂ p.2 q.2 (lt_of_lt_of_le hpq.2 (min_le_right _ _))
  rw [dist_eq_norm] at ha hb ⊢
  rw [uc_stft_eq hf hg, uc_stft_eq hf hg]
  set a := uc_A G p.1
  set a' := uc_A G q.1
  set b := uc_B hf p.2
  set b' := uc_B hf q.2
  have e : ⟪a, b⟫_ℂ - ⟪a', b'⟫_ℂ = ⟪a - a', b⟫_ℂ + ⟪a', b - b'⟫_ℂ := by
    rw [inner_sub_left, inner_sub_right]; ring
  have hbK : ‖b‖ ≤ K := by
    have := uc_B_norm hf p.2; linarith [norm_nonneg G]
  have ha'K : ‖a'‖ ≤ K := by
    rw [uc_A_norm]; linarith [norm_nonneg (hf.toLp f)]
  have hcK : ε / (2 * K) * K = ε / 2 := by field_simp
  rw [e]
  calc ‖⟪a - a', b⟫_ℂ + ⟪a', b - b'⟫_ℂ‖ ≤ ‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    _ ≤ ‖a - a'‖ * K + K * ‖b - b'‖ := by
        gcongr
    _ < ε / (2 * K) * K + K * (ε / (2 * K)) := by
        have := mul_lt_mul_of_pos_right ha hK
        have := mul_lt_mul_of_pos_left hb hK
        linarith
    _ = ε := by rw [mul_comm K, hcK]; ring
