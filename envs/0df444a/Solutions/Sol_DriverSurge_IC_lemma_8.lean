-- Prove2me | solution 1 for DriverSurge.IC.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T01:39:15.054564+00:00
-- url     : https://prove2.me/submissions/5d21a4a3-9341-4104-a837-35949cc8a2e4

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

/-- `h(u) = u q'(u) - q(u)`. -/
noncomputable def hAux (P : Primitives) (i : Fin 2) (u : ℝ) : ℝ :=
  P.sw i * Real.exp (-(P.sw i + P.sw (other i)) * u) * u - q P i u

lemma hasDerivAt_hAux (P : Primitives) (i : Fin 2) (u : ℝ) :
    HasDerivAt (hAux P i)
      (-((P.sw i + P.sw (other i)) * P.sw i * u * Real.exp (-(P.sw i + P.sw (other i)) * u))) u := by
  have h1 : HasDerivAt (fun u : ℝ => -(P.sw i + P.sw (other i)) * u)
      (-(P.sw i + P.sw (other i))) u := by
    simpa using (hasDerivAt_id u).const_mul (-(P.sw i + P.sw (other i)))
  have h2 := ((h1.exp.const_mul (P.sw i)).mul (hasDerivAt_id u)).sub (hasDerivAt_q P i u)
  refine h2.congr_deriv ?_
  simp only [id]
  ring

lemma hAux_strictAnti (P : Primitives) (i : Fin 2) : StrictAntiOn (hAux P i) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x _
    exact (hasDerivAt_hAux P i x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hasDerivAt_hAux P i x).deriv]
    have := sum_sw_pos P i
    have := P.sw_pos i
    have hx' : (0 : ℝ) < x := hx
    have := Real.exp_pos (-(P.sw i + P.sw (other i)) * x)
    have : 0 < (P.sw i + P.sw (other i)) * P.sw i * x *
        Real.exp (-(P.sw i + P.sw (other i)) * x) := by positivity
    linarith

lemma hasDerivAt_rFun_affine (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ)
    (i : Fin 2) (m a : ℝ) (hwi : w i = fun τ => m * τ + a) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (rFun P w σ i)
      (((stateRate P (other i) (w (other i)) (σ (other i)) - stateRate P i (w i) (σ i)) * hAux P i u -
        a * (Qn P i (σ i) / Tn P i (σ i) +
          Qn P (other i) (σ (other i)) / Tn P (other i) (σ (other i)))) / u ^ 2) u := by
  have hw : ∀ v, w i v = m * v + a := fun v => by rw [hwi]
  have hne : u ≠ 0 := hu.ne'
  have h1 := (hasDerivAt_q_div P i hne).mul_const
    (stateRate P (other i) (w (other i)) (σ (other i)) - stateRate P i (w i) (σ i))
  have h2 : HasDerivAt (fun v : ℝ => w i v / v) ((m * u - (m * u + a) * 1) / u ^ 2) u := by
    have := (((hasDerivAt_id u).const_mul m).add_const a).div (hasDerivAt_id u) hne
    simp only [id] at this
    refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_
    · ring
    · exact Filter.Eventually.of_forall fun v => by simp [hw]
  have h3 := h2.mul_const (Qn P i (σ i) / Tn P i (σ i) +
    Qn P (other i) (σ (other i)) / Tn P (other i) (σ (other i)))
  have h4 := (h1.add h3).sub_const (Qn P i (σ i) / Tn P i (σ i) *
    stateRate P (other i) (w (other i)) (σ (other i)) +
      Qn P (other i) (σ (other i)) / Tn P (other i) (σ (other i)) * stateRate P i (w i) (σ i))
  refine h4.congr_deriv ?_
  unfold hAux
  field_simp
  ring

/-- Quasi-convexity from a derivative `g u / u^2` with `g` strictly increasing or everywhere
negative. -/
lemma quasiconvex_of_deriv (r g : ℝ → ℝ)
    (hd : ∀ u : ℝ, 0 < u → HasDerivAt r (g u / u ^ 2) u)
    (hg : StrictMonoOn g (Ioi 0) ∨ ∀ u : ℝ, 0 < u → g u < 0) :
    StrictQuasiconvexIoi r := by
  rcases hg with hg | hg
  · obtain ⟨U, hU, h1, h2⟩ := signChange_of_strictMono hg
    refine ⟨U, hU, fun u hu huU => ⟨_, hd u hu, ?_⟩, fun u hu hUu => ⟨_, hd u hu, ?_⟩⟩
    · exact div_neg_of_neg_of_pos (h1 u hu huU) (by positivity)
    · exact div_pos (h2 u hu hUu) (by positivity)
  · refine ⟨⊤, le_top, fun u hu _ => ⟨_, hd u hu, ?_⟩, fun u _ h => ?_⟩
    · exact div_neg_of_neg_of_pos (hg u hu) (by positivity)
    · exact absurd h (not_lt.mpr le_top)

lemma quasiconcave_of_deriv (r g : ℝ → ℝ)
    (hd : ∀ u : ℝ, 0 < u → HasDerivAt r (g u / u ^ 2) u)
    (hg : StrictAntiOn g (Ioi 0) ∨ ∀ u : ℝ, 0 < u → 0 < g u) :
    StrictQuasiconcaveIoi r := by
  rcases hg with hg | hg
  · obtain ⟨U, hU, h1, h2⟩ := signChange_of_strictAnti hg
    refine ⟨U, hU, fun u hu huU => ⟨_, hd u hu, ?_⟩, fun u hu hUu => ⟨_, hd u hu, ?_⟩⟩
    · exact div_pos (h1 u hu huU) (by positivity)
    · exact div_neg_of_neg_of_pos (h2 u hu hUu) (by positivity)
  · refine ⟨⊤, le_top, fun u hu _ => ⟨_, hd u hu, ?_⟩, fun u _ h => ?_⟩
    · exact div_pos (hg u hu) (by positivity)
    · exact absurd h (not_lt.mpr le_top)

theorem lemma_7 (P : Primitives) (w : Fin 2 → ℝ → ℝ) (i : Fin 2) (m a : ℝ) (hm : 0 < m)
    (ha : 0 < a) (hwi : w i = fun τ => m * τ + a) (σ : Fin 2 → Set ℝ) (hσ : IsPolicy σ)
    (hw : ∀ k, IntegrableOn (w k) (σ k) (P.F k))
    (hτ : ∀ k, IntegrableOn (fun τ : ℝ => τ) (σ k) (P.F k))
    (hΔ : stateRate P (other i) (w (other i)) (σ (other i)) - stateRate P i (w i) (σ i) ≤ 0) :
    StrictQuasiconvexIoi (rFun P w σ i) := by
  set Δ := stateRate P (other i) (w (other i)) (σ (other i)) - stateRate P i (w i) (σ i) with hΔdef
  set A := Qn P i (σ i) / Tn P i (σ i) +
    Qn P (other i) (σ (other i)) / Tn P (other i) (σ (other i)) with hAdef
  have hA : 0 < A := A_pos P σ i
  refine quasiconvex_of_deriv (rFun P w σ i) (fun u => Δ * hAux P i u - a * A)
    (fun u hu => hasDerivAt_rFun_affine P w σ i m a hwi hu) ?_
  rcases hΔ.lt_or_eq with hlt | heq
  · left
    intro x hx y hy hxy
    have := hAux_strictAnti P i hx hy hxy
    have := mul_lt_mul_of_neg_left this hlt
    simp only
    linarith
  · right
    intro u _
    simp only [heq, zero_mul, zero_sub]
    have : 0 < a * A := mul_pos ha hA
    linarith

theorem lemma_8 (P : Primitives) (w : Fin 2 → ℝ → ℝ) (i : Fin 2) (m a : ℝ) (hm : 0 < m)
    (ha : a < 0) (hwi : w i = fun τ => m * τ + a) (σ : Fin 2 → Set ℝ) (hσ : IsPolicy σ)
    (hw : ∀ k, IntegrableOn (w k) (σ k) (P.F k))
    (hτ : ∀ k, IntegrableOn (fun τ : ℝ => τ) (σ k) (P.F k))
    (hΔ : 0 ≤ stateRate P (other i) (w (other i)) (σ (other i)) - stateRate P i (w i) (σ i)) :
    StrictQuasiconcaveIoi (rFun P w σ i) := by
  set Δ := stateRate P (other i) (w (other i)) (σ (other i)) - stateRate P i (w i) (σ i) with hΔdef
  set A := Qn P i (σ i) / Tn P i (σ i) +
    Qn P (other i) (σ (other i)) / Tn P (other i) (σ (other i)) with hAdef
  have hA : 0 < A := A_pos P σ i
  refine quasiconcave_of_deriv (rFun P w σ i) (fun u => Δ * hAux P i u - a * A)
    (fun u hu => hasDerivAt_rFun_affine P w σ i m a hwi hu) ?_
  rcases hΔ.lt_or_eq with hlt | heq
  · left
    intro x hx y hy hxy
    have := hAux_strictAnti P i hx hy hxy
    have := mul_lt_mul_of_pos_left this hlt
    simp only
    linarith
  · right
    intro u _
    simp only [← heq, zero_mul, zero_sub]
    have : a * A < 0 := mul_neg_of_neg_of_pos ha hA
    linarith

end H4Aux

theorem solution (P : Primitives) (w : Fin 2 → ℝ → ℝ) (i : Fin 2) (m a : ℝ) (hm : 0 < m)
    (ha : a < 0) (hwi : w i = fun τ => m * τ + a) (σ : Fin 2 → Set ℝ) (hσ : IsPolicy σ)
    (hw : ∀ k, IntegrableOn (w k) (σ k) (P.F k))
    (hτ : ∀ k, IntegrableOn (fun τ : ℝ => τ) (σ k) (P.F k))
    (hΔ : 0 ≤ stateRate P (other i) (w (other i)) (σ (other i)) - stateRate P i (w i) (σ i)) :
    StrictQuasiconcaveIoi (rFun P w σ i) :=
  H4Aux.lemma_8 P w i m a hm ha hwi σ hσ hw hτ hΔ
