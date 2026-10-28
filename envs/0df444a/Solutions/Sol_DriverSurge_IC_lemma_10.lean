-- Prove2me | solution 1 for DriverSurge.IC.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T01:47:10.876973+00:00
-- url     : https://prove2.me/submissions/caa944ef-35a1-4606-82c7-733517088324

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


lemma tau_integrableOn (P : Primitives) (hmean : FiniteMean P) (i : Fin 2) (s : Set ℝ) :
    IntegrableOn (fun τ : ℝ => τ) s (P.F i) :=
  (hmean i).integrableOn

/-- `sw * Tn - Qn = lam * ∫_s (sw τ - q τ)`. -/
lemma swTn_sub_Qn (P : Primitives) (hmean : FiniteMean P) (i : Fin 2) (s : Set ℝ) :
    P.sw i * Tn P i s - Qn P i s =
      P.lam i * ∫ τ in s, (P.sw i * τ - q P i τ) ∂(P.F i) := by
  unfold Tn Qn
  rw [integral_sub ((tau_integrableOn P hmean i s).const_mul _) (q_integrableOn P i s),
    integral_const_mul]
  ring

lemma g_integrableOn (P : Primitives) (hmean : FiniteMean P) (i : Fin 2) (s : Set ℝ) :
    IntegrableOn (fun τ : ℝ => P.sw i * τ - q P i τ) s (P.F i) :=
  ((tau_integrableOn P hmean i s).const_mul _).sub (q_integrableOn P i s)

lemma g_ae_nonneg (P : Primitives) (i : Fin 2) (s : Set ℝ) :
    0 ≤ᵐ[(P.F i).restrict s] fun τ : ℝ => P.sw i * τ - q P i τ :=
  (ae_pos_restrict P i s).mono fun τ hτ => by
    simp only [Pi.zero_apply]
    linarith [q_le_sw_mul P i hτ.le]

lemma q_ae_nonneg (P : Primitives) (i : Fin 2) (s : Set ℝ) :
    0 ≤ᵐ[(P.F i).restrict s] fun τ : ℝ => q P i τ :=
  (ae_pos_restrict P i s).mono fun τ hτ => by
    simp only [Pi.zero_apply]
    exact q_nonneg P i hτ.le

theorem remark_4 (P : Primitives) (hmean : FiniteMean P) (i : Fin 2) (s : Set ℝ)
    (hs : IsAdmissible s) :
    0 ≤ P.sw i * Tn P i s - Qn P i s ∧
    P.sw i * Tn P i s - Qn P i s ≤ P.sw i * Tn P i (Ioi 0) - Qn P i (Ioi 0) ∧
    0 ≤ Qn P i s ∧ Qn P i s ≤ Qn P i (Ioi 0) := by
  have hlam := P.lam_pos i
  refine ⟨?_, ?_, (Qn_pos P i s).le, ?_⟩
  · rw [swTn_sub_Qn P hmean]
    exact mul_nonneg hlam.le (integral_nonneg_of_ae (g_ae_nonneg P i s))
  · rw [swTn_sub_Qn P hmean, swTn_sub_Qn P hmean]
    apply mul_le_mul_of_nonneg_left _ hlam.le
    exact setIntegral_mono_set (g_integrableOn P hmean i _) (g_ae_nonneg P i _)
      (Filter.Eventually.of_forall hs.2)
  · unfold Qn
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ hlam.le
    exact setIntegral_mono_set (q_integrableOn P i _) (q_ae_nonneg P i _)
      (Filter.Eventually.of_forall hs.2)


/-- Affine interpolation: an affine function positive at both ends of `[a, b]` is positive on it. -/
lemma affine_pos_of_endpoints {c d a b x : ℝ} (hax : a ≤ x) (hxb : x ≤ b)
    (ha : 0 < c * a + d) (hb : 0 < c * b + d) : 0 < c * x + d := by
  rcases le_or_gt 0 c with hc | hc
  · nlinarith
  · nlinarith

/-- Key inequality for Lemma 10 (in the variable `y = z / R₂`). Here `l = λ_{1→2}`,
`T1, Q1` are the varying non-surge quantities, `T1b, Q1b` their accept-all values, `T2, Q2` the fixed
surge quantities, `qu = q(u)` with `0 < qu < l u`. -/
lemma key10 (l T1 Q1 T1b Q1b T2 Q2 y u qu : ℝ) (hl : 0 < l) (hT1 : 0 < T1) (hT2 : 0 < T2)
    (hQ2 : 0 < Q2) (hQ1l : l ≤ Q1) (hQ1b : Q1 - l ≤ Q1b - l)
    (hE0 : 0 ≤ l * T1 - Q1) (hEb : l * T1 - Q1 ≤ l * T1b - Q1b)
    (hu : 0 < u) (hq0 : 0 < qu) (hql : qu < l * u)
    (hlow : -(T2 * l + Q2) < y * (Q2 * (l * T1b - Q1b) + l * (T2 * l + Q2)))
    (hup : y * (Q1b - l) < 1) :
    0 < qu * (T2 + y * Q2 * T1 + y * T2 * l) + u * (Q2 * (1 - y * Q1 + y * l)) := by
  have hB : 0 < Q2 * (1 - y * Q1 + y * l) := by
    apply mul_pos hQ2
    rcases le_or_gt 0 y with hy | hy
    · nlinarith
    · nlinarith
  have hG : 0 < l * (T2 + y * Q2 * T1 + y * T2 * l) + Q2 * (1 - y * Q1 + y * l) := by
    -- affine in `E = l T1 - Q1 ∈ [0, Eb]`
    have : l * (T2 + y * Q2 * T1 + y * T2 * l) + Q2 * (1 - y * Q1 + y * l) =
        (y * Q2) * (l * T1 - Q1) + ((T2 * l + Q2) + y * l * (T2 * l + Q2)) := by ring
    rw [this]
    apply affine_pos_of_endpoints hE0 hEb
    · -- value at `E = 0`
      have hN : 0 < T2 * l + Q2 := by positivity
      -- from `hlow`: `y > -N / D̄ ≥ -1/l`
      have : 0 < 1 + y * l := by
        by_contra h
        push Not at h
        have h1 : y * l ≤ -1 := by linarith
        have hy : y < 0 := by nlinarith
        nlinarith [mul_nonneg hQ2.le (sub_nonneg.mpr hEb), mul_nonneg hQ2.le hE0, mul_nonneg hE0 hl.le]
      nlinarith
    · nlinarith
  rcases le_or_gt 0 (T2 + y * Q2 * T1 + y * T2 * l) with hA | hA
  · nlinarith
  · nlinarith [mul_lt_mul_of_neg_right hql hA]

/-- Key inequality for Lemma 9 (in the variables `δ = m − R₁ > 0`, `y = z/δ`). Here `l = λ_{2→1}`,
`T1, Q1` fixed non-surge quantities, `T2, Q2` varying surge quantities, `T2b, Q2b` their accept-all
values. -/
lemma key9 (l T1 Q1 T2 Q2 T2b Q2b y u qu R δ : ℝ) (hl : 0 < l) (hT1 : 0 < T1) (hQ1 : 0 < Q1)
    (hT2 : 0 < T2) (hQ2l : l ≤ Q2) (hQ2b : Q2 ≤ Q2b)
    (hE0 : 0 ≤ l * T2 - Q2) (hEb : l * T2 - Q2 ≤ l * T2b - Q2b)
    (hu : 0 < u) (hq0 : 0 < qu) (hql : qu < l * u) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hlow : T1 * (l * T2b - Q2b) - (Q1 + T1 * l) <
      y * (Q1 * (l * T2b - Q2b) + l * (Q1 + T1 * l)))
    (hup : y * (Q1 * (Q2b - l)) < Q2b * T1 + Q1) :
    0 < qu * ((R - (R + δ)) * T1 * T2 + (R + δ) * T1 + (y * δ) * Q1 * T2 + (y * δ) * T1 * l) +
      u * (Q2 * T1 * ((R + δ) - R) + Q1 * ((R + δ) - (y * δ) * Q2 + (y * δ) * l)) := by
  -- lower bounds `A'`, `B'`
  set A' := -T1 * T2 + T1 + y * (Q1 * T2 + T1 * l) with hA'
  set B' := Q2 * T1 + Q1 - y * Q1 * (Q2 - l) with hB'
  have hA : (R - (R + δ)) * T1 * T2 + (R + δ) * T1 + (y * δ) * Q1 * T2 + (y * δ) * T1 * l =
      δ * A' + R * T1 := by rw [hA']; ring
  have hB : Q2 * T1 * ((R + δ) - R) + Q1 * ((R + δ) - (y * δ) * Q2 + (y * δ) * l) =
      δ * B' + Q1 * R := by rw [hB']; ring
  rw [hA, hB]
  have hBpos : 0 < B' := by
    rw [hB']
    have : Q2 * T1 + Q1 - y * Q1 * (Q2 - l) = (T1 - y * Q1) * Q2 + (Q1 + y * Q1 * l) := by ring
    rw [this]
    apply affine_pos_of_endpoints hQ2l hQ2b
    · nlinarith
    · rcases le_or_gt 0 y with hy | hy
      · nlinarith
      · nlinarith [mul_nonneg hQ1.le (sub_nonneg.mpr (hQ2l.trans hQ2b))]
  have hGpos : 0 < l * A' + B' := by
    have : l * A' + B' = (-T1 + y * Q1) * (l * T2 - Q2) +
        ((Q1 + T1 * l) + y * l * (Q1 + T1 * l)) := by rw [hA', hB']; ring
    rw [this]
    apply affine_pos_of_endpoints hE0 hEb
    · have hK : 0 < Q1 + T1 * l := by positivity
      have : 0 < 1 + y * l := by
        by_contra h
        push Not at h
        have h1 : y * l ≤ -1 := by linarith
        have hy : y < 0 := by nlinarith
        nlinarith [mul_nonneg hQ1.le (sub_nonneg.mpr hEb), mul_nonneg hQ1.le hE0, mul_nonneg hE0 hl.le,
          mul_nonneg hT1.le hE0, mul_nonneg hT1.le (sub_nonneg.mpr hEb)]
      nlinarith
    · nlinarith
  have h1 : 0 ≤ qu * (R * T1) := by positivity
  have h2 : 0 ≤ u * (Q1 * R) := by positivity
  have h3 : 0 < qu * A' + u * B' := by
    rcases le_or_gt 0 A' with hA | hA
    · nlinarith
    · nlinarith [mul_lt_mul_of_neg_right hql hA]
  nlinarith

lemma q_pos (P : Primitives) (i : Fin 2) {u : ℝ} (hu : 0 < u) : 0 < q P i u := by
  unfold q
  apply mul_pos (div_pos (P.sw_pos i) (sum_sw_pos P i))
  have : Real.exp (-(P.sw i + P.sw (other i)) * u) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [sum_sw_pos P i]
  linarith

/-- `q(u) < λ_{i→j} u` for `u > 0`. -/
lemma q_lt_sw_mul (P : Primitives) (i : Fin 2) {u : ℝ} (hu : 0 < u) : q P i u < P.sw i * u := by
  unfold q
  set a := P.sw i + P.sw (other i) with ha
  have ha0 : 0 < a := sum_sw_pos P i
  have h : 1 - Real.exp (-a * u) < a * u := by
    have hne : -a * u ≠ 0 := (mul_neg_of_neg_of_pos (neg_neg_of_pos ha0) hu).ne
    have := Real.add_one_lt_exp hne
    linarith
  calc P.sw i / a * (1 - Real.exp (-a * u)) < P.sw i / a * (a * u) := by
        apply mul_lt_mul_of_pos_left h (div_pos (P.sw_pos i) ha0)
    _ = P.sw i * u := by field_simp

lemma F_Ioi_eq_one (P : Primitives) (i : Fin 2) : P.F i (Ioi 0) = 1 := by
  have := P.prob i
  have h : Ioi (0 : ℝ) = (Iic 0)ᶜ := by ext x; simp
  rw [h, measure_compl measurableSet_Iic (measure_ne_top _ _), P.support i, measure_univ]
  simp

lemma integral_q_Ioi_pos (P : Primitives) (i : Fin 2) : 0 < ∫ τ in Ioi 0, q P i τ ∂(P.F i) := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae (q_ae_nonneg P i _) (q_integrableOn P i _)]
  have : Function.support (q P i) ∩ Ioi 0 = Ioi 0 := by
    ext x
    simp only [mem_inter_iff, Function.mem_support, mem_Ioi, and_iff_right_iff_imp]
    intro hx
    exact (q_pos P i hx).ne'
  rw [this, F_Ioi_eq_one]
  exact one_pos

lemma sw_lt_Qn_Ioi (P : Primitives) (i : Fin 2) : P.sw i < Qn P i (Ioi 0) := by
  unfold Qn
  have := mul_pos (P.lam_pos i) (integral_q_Ioi_pos P i)
  linarith

lemma Wn_price' (P : Primitives) (i : Fin 2) (s : Set ℝ)
    (hτ : IntegrableOn (fun τ : ℝ => τ) s (P.F i)) (m z : ℝ) :
    Wn P i (fun u => m * u + z * q P i u) s = m * (Tn P i s - 1) + z * (Qn P i s - P.sw i) := by
  unfold Wn Tn Qn
  rw [integral_add (hτ.const_mul m) ((q_integrableOn P i s).const_mul z), integral_const_mul,
    integral_const_mul]
  ring

/-- The identity of Remark 2. -/
lemma rFun_identity (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ)
    (i : Fin 2) (hτ : IntegrableOn (fun τ : ℝ => τ) (σ i) (P.F i)) (m z : ℝ)
    (hwi : w i = fun u => m * u + z * q P i u) (u : ℝ) (hu : 0 < u) :
    u * Tn P i (σ i) * Tn P (other i) (σ (other i)) * rFun P w σ i u =
        q P i u * ((stateRate P (other i) (w (other i)) (σ (other i)) - m) *
              Tn P (other i) (σ (other i)) * Tn P i (σ i) + m * Tn P (other i) (σ (other i)) +
            z * Qn P (other i) (σ (other i)) * Tn P i (σ i) +
            z * Tn P (other i) (σ (other i)) * P.sw i) +
          u * (Qn P i (σ i) * Tn P (other i) (σ (other i)) *
              (m - stateRate P (other i) (w (other i)) (σ (other i))) +
            Qn P (other i) (σ (other i)) * (m - z * Qn P i (σ i) + z * P.sw i)) := by
  have hW : Wn P i (w i) (σ i) = m * (Tn P i (σ i) - 1) + z * (Qn P i (σ i) - P.sw i) := by
    rw [hwi]; exact Wn_price' P i (σ i) hτ m z
  have hTi := Tn_pos P i (σ i)
  have hTj := Tn_pos P (other i) (σ (other i))
  have hRi : stateRate P i (w i) (σ i) =
      (m * (Tn P i (σ i) - 1) + z * (Qn P i (σ i) - P.sw i)) / Tn P i (σ i) := by
    unfold stateRate; rw [hW]
  have hwu : w i u = m * u + z * q P i u := by rw [hwi]
  unfold rFun
  rw [hRi, hwu]
  field_simp
  ring

lemma other_zero : other 0 = 1 := by decide
lemma other_one : other 1 = 0 := by decide

theorem lemma_10 (P : Primitives) (hmean : FiniteMean P) (w : Fin 2 → ℝ → ℝ) (s₂ : Set ℝ)
    (hs₂ : IsAdmissible s₂) (hw1 : IntegrableOn (w 1) s₂ (P.F 1)) (z : ℝ)
    (hR : 0 < stateRate P 1 (w 1) s₂)
    (hw0 : w 0 = fun τ => stateRate P 1 (w 1) s₂ * τ + z * q P 0 τ) :
    (-(Tn P 1 s₂ * P.sw 0 + Qn P 1 s₂) /
          (Qn P 1 s₂ * (P.sw 0 * Tn P 0 (Ioi 0) - Qn P 0 (Ioi 0)) +
            P.sw 0 * (Tn P 1 s₂ * P.sw 0 + Qn P 1 s₂)) <
        z / stateRate P 1 (w 1) s₂ →
      z / stateRate P 1 (w 1) s₂ < 1 / (Qn P 0 (Ioi 0) - P.sw 0) →
      ∀ s₁ : Set ℝ, IsAdmissible s₁ → ∀ u : ℝ, 0 < u → 0 < rFun P w ![s₁, s₂] 0 u) ∧
    -(Tn P 1 s₂ * P.sw 0 + Qn P 1 s₂) /
          (Qn P 1 s₂ * (P.sw 0 * Tn P 0 (Ioi 0) - Qn P 0 (Ioi 0)) +
            P.sw 0 * (Tn P 1 s₂ * P.sw 0 + Qn P 1 s₂)) <
      1 / (Qn P 0 (Ioi 0) - P.sw 0) := by
  set R₂ := stateRate P 1 (w 1) s₂ with hR₂
  set l := P.sw 0 with hl
  set T2 := Tn P 1 s₂ with hT2
  set Q2 := Qn P 1 s₂ with hQ2
  set T1b := Tn P 0 (Ioi 0) with hT1b
  set Q1b := Qn P 0 (Ioi 0) with hQ1b
  have hlpos : 0 < l := P.sw_pos 0
  have hT2pos : 0 < T2 := Tn_pos P 1 s₂
  have hQ2pos : 0 < Q2 := Qn_pos P 1 s₂
  have hEb0 : 0 ≤ l * T1b - Q1b := (remark_4 P hmean 0 (Ioi 0) ⟨isOpen_Ioi, subset_rfl⟩).1
  have hN : 0 < T2 * l + Q2 := by positivity
  have hD : 0 < Q2 * (l * T1b - Q1b) + l * (T2 * l + Q2) := by positivity
  have hd0 : 0 ≤ Q1b - l := sub_nonneg.mpr (sw_le_Qn P 0 (Ioi 0))
  refine ⟨fun hlow hup s₁ hs₁ u hu => ?_, ?_⟩
  · set y := z / R₂ with hy
    have hz : z = y * R₂ := by rw [hy]; field_simp
    have hlow' : -(T2 * l + Q2) < y * (Q2 * (l * T1b - Q1b) + l * (T2 * l + Q2)) := by
      rwa [div_lt_iff₀ hD] at hlow
    have hup' : y * (Q1b - l) < 1 := by
      rcases hd0.lt_or_eq with hd | hd
      · rwa [lt_div_iff₀ hd] at hup
      · rw [← hd, mul_zero]; exact one_pos
    set T1 := Tn P 0 s₁ with hT1
    set Q1 := Qn P 0 s₁ with hQ1
    have hT1pos : 0 < T1 := Tn_pos P 0 s₁
    have hQ1l : l ≤ Q1 := sw_le_Qn P 0 s₁
    have hr4 := remark_4 P hmean 0 s₁ hs₁
    have hE0 : 0 ≤ l * T1 - Q1 := hr4.1
    have hEb : l * T1 - Q1 ≤ l * T1b - Q1b := hr4.2.1
    have hQ1b' : Q1 - l ≤ Q1b - l := by linarith [hr4.2.2.2]
    have hq0 : 0 < q P 0 u := q_pos P 0 hu
    have hql : q P 0 u < l * u := q_lt_sw_mul P 0 hu
    have key := key10 l T1 Q1 T1b Q1b T2 Q2 y u (q P 0 u) hlpos hT1pos hT2pos hQ2pos hQ1l hQ1b'
      hE0 hEb hu hq0 hql hlow' hup'
    have hid := rFun_identity P w ![s₁, s₂] 0 (tau_integrableOn P hmean 0 _) R₂ z hw0 u hu
    simp only [other_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hid
    rw [← hT1, ← hT2, ← hQ1, ← hQ2, ← hR₂, ← hl] at hid
    have hpos : 0 < u * T1 * T2 := by positivity
    have : 0 < u * T1 * T2 * rFun P w ![s₁, s₂] 0 u := by
      rw [hid, hz]
      have e : q P 0 u * ((R₂ - R₂) * T2 * T1 + R₂ * T2 + y * R₂ * Q2 * T1 + y * R₂ * T2 * l) +
          u * (Q1 * T2 * (R₂ - R₂) + Q2 * (R₂ - y * R₂ * Q1 + y * R₂ * l)) =
          R₂ * (q P 0 u * (T2 + y * Q2 * T1 + y * T2 * l) + u * (Q2 * (1 - y * Q1 + y * l))) := by
        ring
      rw [e]
      exact mul_pos hR key
    exact pos_of_mul_pos_right this hpos.le
  · apply lt_of_lt_of_le _ (div_nonneg zero_le_one hd0)
    exact div_neg_of_neg_of_pos (by linarith) hD

end H4Aux

theorem solution (P : Primitives) (hmean : FiniteMean P) (w : Fin 2 → ℝ → ℝ) (s₂ : Set ℝ)
    (hs₂ : IsAdmissible s₂) (hw1 : IntegrableOn (w 1) s₂ (P.F 1)) (z : ℝ)
    (hR : 0 < stateRate P 1 (w 1) s₂)
    (hw0 : w 0 = fun τ => stateRate P 1 (w 1) s₂ * τ + z * q P 0 τ) :
    (-(Tn P 1 s₂ * P.sw 0 + Qn P 1 s₂) /
          (Qn P 1 s₂ * (P.sw 0 * Tn P 0 (Ioi 0) - Qn P 0 (Ioi 0)) +
            P.sw 0 * (Tn P 1 s₂ * P.sw 0 + Qn P 1 s₂)) <
        z / stateRate P 1 (w 1) s₂ →
      z / stateRate P 1 (w 1) s₂ < 1 / (Qn P 0 (Ioi 0) - P.sw 0) →
      ∀ s₁ : Set ℝ, IsAdmissible s₁ → ∀ u : ℝ, 0 < u → 0 < rFun P w ![s₁, s₂] 0 u) ∧
    -(Tn P 1 s₂ * P.sw 0 + Qn P 1 s₂) /
          (Qn P 1 s₂ * (P.sw 0 * Tn P 0 (Ioi 0) - Qn P 0 (Ioi 0)) +
            P.sw 0 * (Tn P 1 s₂ * P.sw 0 + Qn P 1 s₂)) <
      1 / (Qn P 0 (Ioi 0) - P.sw 0) :=
  H4Aux.lemma_10 P hmean w s₂ hs₂ hw1 z hR hw0
