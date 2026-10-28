-- Prove2me | solution 1 for DriverSurge.IC.remark_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T01:28:31.226985+00:00
-- url     : https://prove2.me/submissions/7faa3215-9e19-4ef0-bcd9-218d657f7368

import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing

open DriverSurge.IC MeasureTheory Set Filter Topology

namespace H4Aux

open DriverSurge.IC MeasureTheory Set Filter Topology

lemma sum_sw_pos (P : Primitives) (i : Fin 2) : 0 < P.sw i + P.sw (other i) :=
  add_pos (P.sw_pos i) (P.sw_pos _)

lemma hasDerivAt_q (P : Primitives) (i : Fin 2) (u : ℝ) :
    HasDerivAt (q P i) (P.sw i * Real.exp (-(P.sw i + P.sw (other i)) * u)) u := by
  have ha0 : P.sw i + P.sw (other i) ≠ 0 := (sum_sw_pos P i).ne'
  have h1 : HasDerivAt (fun u : ℝ => -(P.sw i + P.sw (other i)) * u)
      (-(P.sw i + P.sw (other i))) u := by
    simpa using (hasDerivAt_id u).const_mul (-(P.sw i + P.sw (other i)))
  have h3 := (h1.exp.const_sub 1).const_mul (P.sw i / (P.sw i + P.sw (other i)))
  have hfun : q P i = fun y => P.sw i / (P.sw i + P.sw (other i)) *
      (1 - Real.exp (-(P.sw i + P.sw (other i)) * y)) := by
    funext y; rfl
  rw [hfun]
  refine h3.congr_deriv ?_
  field_simp

lemma q_nonneg (P : Primitives) (i : Fin 2) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ q P i u := by
  unfold q
  apply mul_nonneg (div_nonneg (P.sw_pos i).le (sum_sw_pos P i).le)
  have : Real.exp (-(P.sw i + P.sw (other i)) * u) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sum_sw_pos P i]
  linarith

lemma q_le (P : Primitives) (i : Fin 2) (u : ℝ) :
    q P i u ≤ P.sw i / (P.sw i + P.sw (other i)) := by
  unfold q
  have h1 : 0 ≤ Real.exp (-(P.sw i + P.sw (other i)) * u) := (Real.exp_pos _).le
  have h2 : 0 ≤ P.sw i / (P.sw i + P.sw (other i)) :=
    div_nonneg (P.sw_pos i).le (sum_sw_pos P i).le
  nlinarith

/-- `q(u) ≤ λ_{i→j} u` for `u ≥ 0`. -/
lemma q_le_sw_mul (P : Primitives) (i : Fin 2) {u : ℝ} (hu : 0 ≤ u) : q P i u ≤ P.sw i * u := by
  unfold q
  set a := P.sw i + P.sw (other i) with ha
  have ha0 : 0 < a := sum_sw_pos P i
  have h : 1 - Real.exp (-a * u) ≤ a * u := by
    have := Real.add_one_le_exp (-a * u)
    linarith
  calc P.sw i / a * (1 - Real.exp (-a * u)) ≤ P.sw i / a * (a * u) := by
        apply mul_le_mul_of_nonneg_left h (div_nonneg (P.sw_pos i).le ha0.le)
    _ = P.sw i * u := by field_simp

lemma hasDerivAt_q_div (P : Primitives) (i : Fin 2) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun u => q P i u / u)
      ((P.sw i * Real.exp (-(P.sw i + P.sw (other i)) * u) * u - q P i u) / u ^ 2) u := by
  have := (hasDerivAt_q P i u).div (hasDerivAt_id u) hu
  simp only [id, mul_one] at this
  exact this

lemma q_div_deriv_neg (P : Primitives) (i : Fin 2) {u : ℝ} (hu : 0 < u) :
    (P.sw i * Real.exp (-(P.sw i + P.sw (other i)) * u) * u - q P i u) / u ^ 2 < 0 := by
  apply div_neg_of_neg_of_pos _ (by positivity)
  unfold q
  set a := P.sw i + P.sw (other i) with ha
  have ha0 : 0 < a := sum_sw_pos P i
  have hx : a * u ≠ 0 := by positivity
  have key := Real.add_one_lt_exp hx
  have h2 : Real.exp (-a * u) * (a * u + 1) < 1 := by
    have := Real.exp_neg (a * u)
    rw [show -a * u = -(a * u) by ring, this]
    rw [inv_mul_lt_iff₀ (Real.exp_pos _), mul_one]
    linarith
  have hsw : 0 < P.sw i := P.sw_pos i
  have : P.sw i * Real.exp (-a * u) * u - P.sw i / a * (1 - Real.exp (-a * u)) =
      P.sw i / a * (Real.exp (-a * u) * (a * u + 1) - 1) := by
    field_simp
    ring
  rw [this]
  exact mul_neg_of_pos_of_neg (div_pos hsw ha0) (by linarith)

lemma q_div_strictAnti (P : Primitives) (i : Fin 2) :
    StrictAntiOn (fun u : ℝ => q P i u / u) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx
    exact (hasDerivAt_q_div P i (ne_of_gt hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hasDerivAt_q_div P i (ne_of_gt hx)).deriv]
    exact q_div_deriv_neg P i hx

/-- Almost every trip length is positive. -/
lemma ae_pos (P : Primitives) (i : Fin 2) : ∀ᵐ τ ∂(P.F i), 0 < τ := by
  have h := P.support i
  rw [ae_iff]
  convert h using 2
  ext τ; simp

lemma ae_pos_restrict (P : Primitives) (i : Fin 2) (s : Set ℝ) :
    ∀ᵐ τ ∂((P.F i).restrict s), 0 < τ :=
  ae_restrict_of_ae (ae_pos P i)

lemma integral_tau_nonneg (P : Primitives) (i : Fin 2) (s : Set ℝ) :
    0 ≤ ∫ τ in s, τ ∂(P.F i) :=
  integral_nonneg_of_ae ((ae_pos_restrict P i s).mono fun τ hτ => hτ.le)

lemma integral_q_nonneg (P : Primitives) (i : Fin 2) (s : Set ℝ) :
    0 ≤ ∫ τ in s, q P i τ ∂(P.F i) :=
  integral_nonneg_of_ae ((ae_pos_restrict P i s).mono fun τ hτ => q_nonneg P i hτ.le)

lemma one_le_Tn (P : Primitives) (i : Fin 2) (s : Set ℝ) : 1 ≤ Tn P i s := by
  unfold Tn
  have := integral_tau_nonneg P i s
  have := P.lam_pos i
  nlinarith

lemma Tn_pos (P : Primitives) (i : Fin 2) (s : Set ℝ) : 0 < Tn P i s :=
  lt_of_lt_of_le one_pos (one_le_Tn P i s)

lemma sw_le_Qn (P : Primitives) (i : Fin 2) (s : Set ℝ) : P.sw i ≤ Qn P i s := by
  unfold Qn
  have := integral_q_nonneg P i s
  have := P.lam_pos i
  nlinarith

lemma Qn_pos (P : Primitives) (i : Fin 2) (s : Set ℝ) : 0 < Qn P i s :=
  lt_of_lt_of_le (P.sw_pos i) (sw_le_Qn P i s)

lemma q_continuous (P : Primitives) (i : Fin 2) : Continuous (q P i) := by
  unfold q
  fun_prop

lemma q_integrableOn (P : Primitives) (i : Fin 2) (s : Set ℝ) :
    IntegrableOn (q P i) s (P.F i) := by
  have := P.prob i
  refine (integrable_const (P.sw i / (P.sw i + P.sw (other i)))).mono'
    (q_continuous P i).aestronglyMeasurable ?_
  refine (ae_pos_restrict P i s).mono fun τ hτ => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (q_nonneg P i hτ.le)]
  exact q_le P i τ


end H4Aux

namespace H4Aux

open DriverSurge.IC MeasureTheory Set Filter Topology

lemma signChange_of_strictMono {f : ℝ → ℝ} (hf : StrictMonoOn f (Ioi 0)) :
    ∃ U : EReal, 0 ≤ U ∧ (∀ u : ℝ, 0 < u → (u : EReal) < U → f u < 0) ∧
      (∀ u : ℝ, 0 < u → U < (u : EReal) → 0 < f u) := by
  classical
  let S : Set ℝ := {u | 0 < u ∧ f u ≤ 0}
  refine ⟨max 0 (sSup ((fun u : ℝ => (u : EReal)) '' S)), le_max_left _ _, ?_, ?_⟩
  · intro u hu huU
    have hlt : (u : EReal) < sSup ((fun u : ℝ => (u : EReal)) '' S) := by
      rcases lt_max_iff.mp huU with h | h
      · exfalso
        have : (0 : EReal) < (u : EReal) := by exact_mod_cast hu
        exact absurd h (not_lt.mpr this.le)
      · exact h
    obtain ⟨_, ⟨s, hs, rfl⟩, hus⟩ := lt_sSup_iff.mp hlt
    have hus' : u < s := by exact_mod_cast (show (u : EReal) < (s : EReal) from hus)
    have := hf (show u ∈ Ioi 0 from hu) (show s ∈ Ioi 0 from hs.1) hus'
    linarith [hs.2]
  · intro u hu hUu
    by_contra hcon
    push_neg at hcon
    have hmem : u ∈ S := ⟨hu, hcon⟩
    have h1 : (u : EReal) ≤ sSup ((fun u : ℝ => (u : EReal)) '' S) := le_sSup ⟨u, hmem, rfl⟩
    have h2 : sSup ((fun u : ℝ => (u : EReal)) '' S) < (u : EReal) :=
      lt_of_le_of_lt (le_max_right _ _) hUu
    exact absurd h1 (not_le.mpr h2)

lemma signChange_of_strictAnti {f : ℝ → ℝ} (hf : StrictAntiOn f (Ioi 0)) :
    ∃ U : EReal, 0 ≤ U ∧ (∀ u : ℝ, 0 < u → (u : EReal) < U → 0 < f u) ∧
      (∀ u : ℝ, 0 < u → U < (u : EReal) → f u < 0) := by
  obtain ⟨U, hU, h1, h2⟩ := signChange_of_strictMono hf.neg
  refine ⟨U, hU, fun u hu huU => ?_, fun u hu hUu => ?_⟩
  · have := h1 u hu huU; simp at this; exact this
  · have := h2 u hu hUu; simp at this; exact this

lemma rFun_eq (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (i : Fin 2) (u : ℝ) :
    rFun P w σ i u =
      q P i u / u * (stateRate P (other i) (w (other i)) (σ (other i)) - stateRate P i (w i) (σ i)) +
      w i u / u * (Qn P i (σ i) / Tn P i (σ i) + Qn P (other i) (σ (other i)) / Tn P (other i) (σ (other i))) -
      (Qn P i (σ i) / Tn P i (σ i) * stateRate P (other i) (w (other i)) (σ (other i)) +
        Qn P (other i) (σ (other i)) / Tn P (other i) (σ (other i)) * stateRate P i (w i) (σ i)) := rfl

lemma A_pos (P : Primitives) (σ : Fin 2 → Set ℝ) (i : Fin 2) :
    0 < Qn P i (σ i) / Tn P i (σ i) + Qn P (other i) (σ (other i)) / Tn P (other i) (σ (other i)) :=
  add_pos (div_pos (Qn_pos P i _) (Tn_pos P i _)) (div_pos (Qn_pos P _ _) (Tn_pos P _ _))

lemma rFun_strictMono (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (i : Fin 2)
    (hΔ : stateRate P (other i) (w (other i)) (σ (other i)) - stateRate P i (w i) (σ i) < 0)
    (hmono : MonotoneOn (fun u : ℝ => w i u / u) (Ioi 0)) :
    StrictMonoOn (rFun P w σ i) (Ioi 0) := by
  intro x hx y hy hxy
  have hq := q_div_strictAnti P i hx hy hxy
  have h1 := mul_lt_mul_of_neg_right hq hΔ
  have h2 := mul_le_mul_of_nonneg_right (hmono hx hy hxy.le) (A_pos P σ i).le
  simp only [rFun_eq]
  simp only at h1 h2
  linarith

lemma rFun_strictAnti (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (i : Fin 2)
    (hΔ : 0 < stateRate P (other i) (w (other i)) (σ (other i)) - stateRate P i (w i) (σ i))
    (hmono : AntitoneOn (fun u : ℝ => w i u / u) (Ioi 0)) :
    StrictAntiOn (rFun P w σ i) (Ioi 0) := by
  intro x hx y hy hxy
  have hq := q_div_strictAnti P i hx hy hxy
  have h1 := mul_lt_mul_of_pos_right hq hΔ
  have h2 := mul_le_mul_of_nonneg_right (hmono hx hy hxy.le) (A_pos P σ i).le
  simp only [rFun_eq]
  simp only at h1 h2
  linarith

end H4Aux

namespace H4Aux

lemma Wn_price (P : Primitives) (i : Fin 2) (s : Set ℝ)
    (hτ : IntegrableOn (fun τ : ℝ => τ) s (P.F i)) (m z : ℝ) :
    Wn P i (fun u => m * u + z * q P i u) s = m * (Tn P i s - 1) + z * (Qn P i s - P.sw i) := by
  unfold Wn Tn Qn
  rw [integral_add (hτ.const_mul m) ((q_integrableOn P i s).const_mul z), integral_const_mul,
    integral_const_mul]
  ring

theorem remark_2 (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (hσ : IsPolicy σ)
    (hτ : ∀ k, IntegrableOn (fun τ : ℝ => τ) (σ k) (P.F k)) (i : Fin 2)
    (hwj : IntegrableOn (w (other i)) (σ (other i)) (P.F (other i))) (m z : ℝ)
    (hwi : w i = fun u => m * u + z * q P i u) :
    Wn P i (w i) (σ i) = m * (Tn P i (σ i) - 1) + z * (Qn P i (σ i) - P.sw i) ∧
    ∀ u : ℝ, 0 < u →
      u * Tn P i (σ i) * Tn P (other i) (σ (other i)) * rFun P w σ i u =
          q P i u * ((stateRate P (other i) (w (other i)) (σ (other i)) - m) *
                Tn P (other i) (σ (other i)) * Tn P i (σ i) + m * Tn P (other i) (σ (other i)) +
              z * Qn P (other i) (σ (other i)) * Tn P i (σ i) +
              z * Tn P (other i) (σ (other i)) * P.sw i) +
            u * (Qn P i (σ i) * Tn P (other i) (σ (other i)) *
                (m - stateRate P (other i) (w (other i)) (σ (other i))) +
              Qn P (other i) (σ (other i)) * (m - z * Qn P i (σ i) + z * P.sw i)) ∧
      SignType.sign (rFun P w σ i u) =
        SignType.sign (q P i u * ((stateRate P (other i) (w (other i)) (σ (other i)) - m) *
                Tn P (other i) (σ (other i)) * Tn P i (σ i) + m * Tn P (other i) (σ (other i)) +
              z * Qn P (other i) (σ (other i)) * Tn P i (σ i) +
              z * Tn P (other i) (σ (other i)) * P.sw i) +
            u * (Qn P i (σ i) * Tn P (other i) (σ (other i)) *
                (m - stateRate P (other i) (w (other i)) (σ (other i))) +
              Qn P (other i) (σ (other i)) * (m - z * Qn P i (σ i) + z * P.sw i))) := by
  have hW : Wn P i (w i) (σ i) = m * (Tn P i (σ i) - 1) + z * (Qn P i (σ i) - P.sw i) := by
    rw [hwi]; exact Wn_price P i (σ i) (hτ i) m z
  refine ⟨hW, fun u hu => ?_⟩
  have hTi := Tn_pos P i (σ i)
  have hTj := Tn_pos P (other i) (σ (other i))
  have hRi : stateRate P i (w i) (σ i) =
      (m * (Tn P i (σ i) - 1) + z * (Qn P i (σ i) - P.sw i)) / Tn P i (σ i) := by
    unfold stateRate; rw [hW]
  have hwu : w i u = m * u + z * q P i u := by rw [hwi]
  have key : u * Tn P i (σ i) * Tn P (other i) (σ (other i)) * rFun P w σ i u =
          q P i u * ((stateRate P (other i) (w (other i)) (σ (other i)) - m) *
                Tn P (other i) (σ (other i)) * Tn P i (σ i) + m * Tn P (other i) (σ (other i)) +
              z * Qn P (other i) (σ (other i)) * Tn P i (σ i) +
              z * Tn P (other i) (σ (other i)) * P.sw i) +
            u * (Qn P i (σ i) * Tn P (other i) (σ (other i)) *
                (m - stateRate P (other i) (w (other i)) (σ (other i))) +
              Qn P (other i) (σ (other i)) * (m - z * Qn P i (σ i) + z * P.sw i)) := by
    unfold rFun
    rw [hRi, hwu]
    field_simp
    ring
  refine ⟨key, ?_⟩
  rw [← key, sign_mul, sign_pos (mul_pos (mul_pos hu hTi) hTj), one_mul]

end H4Aux

theorem solution (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (hσ : IsPolicy σ)
    (hτ : ∀ k, IntegrableOn (fun τ : ℝ => τ) (σ k) (P.F k)) (i : Fin 2)
    (hwj : IntegrableOn (w (other i)) (σ (other i)) (P.F (other i))) (m z : ℝ)
    (hwi : w i = fun u => m * u + z * q P i u) :
    Wn P i (w i) (σ i) = m * (Tn P i (σ i) - 1) + z * (Qn P i (σ i) - P.sw i) ∧
    ∀ u : ℝ, 0 < u →
      u * Tn P i (σ i) * Tn P (other i) (σ (other i)) * rFun P w σ i u =
          q P i u * ((stateRate P (other i) (w (other i)) (σ (other i)) - m) *
                Tn P (other i) (σ (other i)) * Tn P i (σ i) + m * Tn P (other i) (σ (other i)) +
              z * Qn P (other i) (σ (other i)) * Tn P i (σ i) +
              z * Tn P (other i) (σ (other i)) * P.sw i) +
            u * (Qn P i (σ i) * Tn P (other i) (σ (other i)) *
                (m - stateRate P (other i) (w (other i)) (σ (other i))) +
              Qn P (other i) (σ (other i)) * (m - z * Qn P i (σ i) + z * P.sw i)) ∧
      SignType.sign (rFun P w σ i u) =
        SignType.sign (q P i u * ((stateRate P (other i) (w (other i)) (σ (other i)) - m) *
                Tn P (other i) (σ (other i)) * Tn P i (σ i) + m * Tn P (other i) (σ (other i)) +
              z * Qn P (other i) (σ (other i)) * Tn P i (σ i) +
              z * Tn P (other i) (σ (other i)) * P.sw i) +
            u * (Qn P i (σ i) * Tn P (other i) (σ (other i)) *
                (m - stateRate P (other i) (w (other i)) (σ (other i))) +
              Qn P (other i) (σ (other i)) * (m - z * Qn P i (σ i) + z * P.sw i))) :=
  H4Aux.remark_2 P w σ hσ hτ i hwj m z hwi
