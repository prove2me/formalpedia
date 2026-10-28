-- Prove2me | solution 1 for ContextualAuctions.RevEquiv.theorem_2
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T21:53:55.865587+00:00
-- url     : https://prove2.me/submissions/b7a5994c-4d60-4fd2-ac53-331fb7104a91

import Mathlib
import Definitions.Def_ContextualAuctions_RevEquiv_Setting
import Definitions.Def_ContextualAuctions_RevEquiv_FixedPoint
import Definitions.Def_ContextualAuctions_RevEquiv_Auctions

-- ===== part D =====
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Set

namespace CA63

/-! ## Part 1. Abstract first-price best response (one context).
`Φ` plays the role of `H(x) = Fc(x)^(n-1)`; `sig0` is the model's `sigma` formula. -/

section Abstract

variable (Φ : ℝ → ℝ) (r : ℝ)

noncomputable def Aint (x : ℝ) : ℝ := ∫ s in r..x, Φ s

/-- the `r`-patched (monotone) bid -/
noncomputable def sigR (x : ℝ) : ℝ :=
  if x < r then x else if Φ x = 0 then r else x - Aint Φ r x / Φ x

/-- the model's bid formula (`0` in the degenerate case) -/
noncomputable def sig0 (x : ℝ) : ℝ :=
  if x < r then x else if Φ x = 0 then 0 else x - Aint Φ r x / Φ x

/-- optimal Lagrangian value of a bidder with value `x` -/
noncomputable def Vopt (x : ℝ) : ℝ := if x < r then 0 else Aint Φ r x

variable {Φ r}

lemma Aint_sub (hΦ : Continuous Φ) (x y : ℝ) :
    Aint Φ r x - Aint Φ r y = ∫ s in y..x, Φ s := by
  unfold Aint
  exact intervalIntegral.integral_interval_sub_left (hΦ.intervalIntegrable _ _)
    (hΦ.intervalIntegrable _ _)

lemma key1 (hΦ : Continuous Φ) (hm : Monotone Φ) (x y : ℝ) :
    (x - y) * Φ y ≤ Aint Φ r x - Aint Φ r y := by
  rw [Aint_sub hΦ]
  rcases le_total y x with hyx | hxy
  · have h1 : ∫ s in y..x, Φ y ≤ ∫ s in y..x, Φ s :=
      intervalIntegral.integral_mono_on hyx intervalIntegrable_const
        (hΦ.intervalIntegrable _ _) (fun s hs => hm hs.1)
    simpa [intervalIntegral.integral_const, smul_eq_mul] using h1
  · have h1 : ∫ s in x..y, Φ s ≤ ∫ s in x..y, Φ y :=
      intervalIntegral.integral_mono_on hxy (hΦ.intervalIntegrable _ _) intervalIntegrable_const
        (fun s hs => hm hs.2)
    rw [intervalIntegral.integral_symm]
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h1
    nlinarith

lemma Aint_nonneg (hΦ : Continuous Φ) (h0 : ∀ x, 0 ≤ Φ x) {y : ℝ} (hy : r ≤ y) :
    0 ≤ Aint Φ r y :=
  intervalIntegral.integral_nonneg hy (fun s _ => h0 s)

lemma Aint_le (hΦ : Continuous Φ) (hm : Monotone Φ) {y : ℝ} (hy : r ≤ y) :
    Aint Φ r y ≤ (y - r) * Φ y := by
  have h1 : ∫ s in r..y, Φ s ≤ ∫ s in r..y, Φ y :=
    intervalIntegral.integral_mono_on hy (hΦ.intervalIntegrable _ _) intervalIntegrable_const
      (fun s hs => hm hs.2)
  simpa [Aint, intervalIntegral.integral_const, smul_eq_mul] using h1

lemma sigR_mul (hΦ : Continuous Φ) (hm : Monotone Φ) (h0 : ∀ x, 0 ≤ Φ x) {y : ℝ} (hy : r ≤ y) :
    sigR Φ r y * Φ y = y * Φ y - Aint Φ r y := by
  unfold sigR
  rw [if_neg (not_lt.mpr hy)]
  by_cases hz : Φ y = 0
  · rw [if_pos hz, hz]
    have h1 := Aint_nonneg hΦ h0 hy
    have h2 := Aint_le hΦ hm hy
    rw [hz] at h2
    have : Aint Φ r y = 0 := le_antisymm (by simpa using h2) h1
    rw [this]; ring
  · rw [if_neg hz]
    field_simp

lemma r_le_sigR (hΦ : Continuous Φ) (hm : Monotone Φ) (h0 : ∀ x, 0 ≤ Φ x) {y : ℝ} (hy : r ≤ y) :
    r ≤ sigR Φ r y := by
  unfold sigR
  rw [if_neg (not_lt.mpr hy)]
  by_cases hz : Φ y = 0
  · rw [if_pos hz]
  · rw [if_neg hz]
    have hp : 0 < Φ y := lt_of_le_of_ne (h0 y) (Ne.symm hz)
    have h2 := Aint_le hΦ hm hy
    have : Aint Φ r y / Φ y ≤ y - r := by rw [div_le_iff₀ hp]; exact h2
    linarith

lemma sigR_le (hΦ : Continuous Φ) (h0 : ∀ x, 0 ≤ Φ x) {y : ℝ} (hy : r ≤ y) :
    sigR Φ r y ≤ y := by
  unfold sigR
  rw [if_neg (not_lt.mpr hy)]
  by_cases hz : Φ y = 0
  · rw [if_pos hz]; exact hy
  · rw [if_neg hz]
    have hp : 0 < Φ y := lt_of_le_of_ne (h0 y) (Ne.symm hz)
    have := div_nonneg (Aint_nonneg hΦ h0 hy) hp.le
    linarith

lemma sigR_mono (hΦ : Continuous Φ) (hm : Monotone Φ) (h0 : ∀ x, 0 ≤ Φ x) :
    Monotone (sigR Φ r) := by
  intro y1 y2 h12
  by_cases h1 : y1 < r
  · have e1 : sigR Φ r y1 = y1 := by unfold sigR; rw [if_pos h1]
    rw [e1]
    by_cases h2 : y2 < r
    · have e2 : sigR Φ r y2 = y2 := by unfold sigR; rw [if_pos h2]
      rw [e2]; exact h12
    · have := r_le_sigR hΦ hm h0 (not_lt.mp h2); linarith
  · have hy1 : r ≤ y1 := not_lt.mp h1
    have hy2 : r ≤ y2 := le_trans hy1 h12
    by_cases z2 : Φ y2 = 0
    · have z1 : Φ y1 = 0 := le_antisymm (z2 ▸ hm h12) (h0 y1)
      have e1 : sigR Φ r y1 = r := by unfold sigR; rw [if_neg h1, if_pos z1]
      rw [e1]; exact r_le_sigR hΦ hm h0 hy2
    · by_cases z1 : Φ y1 = 0
      · have e1 : sigR Φ r y1 = r := by unfold sigR; rw [if_neg h1, if_pos z1]
        rw [e1]; exact r_le_sigR hΦ hm h0 hy2
      · have p1 : 0 < Φ y1 := lt_of_le_of_ne (h0 y1) (Ne.symm z1)
        have p2 : 0 < Φ y2 := lt_of_le_of_ne (h0 y2) (Ne.symm z2)
        have e1 : sigR Φ r y1 = y1 - Aint Φ r y1 / Φ y1 := by
          unfold sigR; rw [if_neg h1, if_neg z1]
        have e2 : sigR Φ r y2 = y2 - Aint Φ r y2 / Φ y2 := by
          unfold sigR; rw [if_neg (not_lt.mpr hy2), if_neg z2]
        rw [e1, e2]
        set I := ∫ s in y1..y2, Φ s with hI
        have hA2 : Aint Φ r y2 = Aint Φ r y1 + I := by
          have := Aint_sub (r := r) hΦ y2 y1; linarith
        have hIle : I ≤ (y2 - y1) * Φ y2 := by
          have h3 : ∫ s in y1..y2, Φ s ≤ ∫ s in y1..y2, Φ y2 :=
            intervalIntegral.integral_mono_on h12 (hΦ.intervalIntegrable _ _)
              intervalIntegrable_const (fun s hs => hm hs.2)
          simpa [intervalIntegral.integral_const, smul_eq_mul] using h3
        have hA1 := Aint_nonneg hΦ h0 hy1
        have hq1 : Aint Φ r y1 / Φ y2 ≤ Aint Φ r y1 / Φ y1 :=
          div_le_div_of_nonneg_left hA1 p1 (hm h12)
        have hq2 : I / Φ y2 ≤ y2 - y1 := by rw [div_le_iff₀ p2]; exact hIle
        rw [hA2, add_div]
        linarith

/-- every bid earns at most the optimal value (`k` competitors, law of bids `K`) -/
lemma value_bound_of (hΦ : Continuous Φ) (hm : Monotone Φ) (h0 : ∀ x, 0 ≤ Φ x)
    {x b : ℝ} (hrb : r ≤ b) (hrx : r ≤ x) (hbx : b < x) {c : ℝ} (hc : sigR Φ r c ≤ b)
    (hcr : r ≤ c) : (x - b) * Φ c ≤ Aint Φ r x := by
  have h1 := key1 (r := r) hΦ hm x c
  have h2 := sigR_mul hΦ hm h0 hcr
  have h3 : (x - b) * Φ c ≤ (x - sigR Φ r c) * Φ c :=
    mul_le_mul_of_nonneg_right (by linarith) (h0 c)
  have h4 : (x - sigR Φ r c) * Φ c = (x - c) * Φ c + Aint Φ r c := by
    have : (x - sigR Φ r c) * Φ c = x * Φ c - sigR Φ r c * Φ c := by ring
    rw [this, h2]; ring
  linarith

end Abstract

/-! ## Part 2. One context, a law `H` of competitor values, `k` competitors. -/

section OneContext

open ProbabilityTheory Filter Topology

variable (H : Measure ℝ) [IsProbabilityMeasure H]

lemma cdf_cont [NullSingletonClass H] : Continuous (cdf H) := by
  rw [continuous_iff_continuousAt]; intro a
  rw [(cdf H).mono.continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  have hs := (cdf H).measure_singleton a
  rw [measure_cdf, measure_singleton] at hs
  have h1 : Function.leftLim (cdf H) a ≤ cdf H a := (cdf H).mono.leftLim_le le_rfl
  have h2 : cdf H a - Function.leftLim (cdf H) a ≤ 0 := by
    have := (ENNReal.ofReal_eq_zero.mp hs.symm); linarith
  linarith

lemma cdf_zero_null [NullSingletonClass H] : H {y | cdf H y = 0} = 0 := by
  set T := {y | cdf H y = 0} with hT
  by_cases hne : T.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp
  have hbdd : BddAbove T := by
    have ev : ∀ᶠ y in atTop, (1:ℝ)/2 < cdf H y :=
      (tendsto_cdf_atTop (μ := H)).eventually (lt_mem_nhds (by norm_num))
    obtain ⟨N, hN⟩ := eventually_atTop.mp ev
    refine ⟨N, fun y hy => ?_⟩
    by_contra hlt
    have := hN y (le_of_lt (not_le.mp hlt))
    have h0 : cdf H y = 0 := hy
    linarith
  have hc : sSup T ∈ T :=
    IsClosed.csSup_mem (isClosed_eq (cdf_cont H) continuous_const) hne hbdd
  have hsub : T ⊆ Iic (sSup T) := fun y hy => le_csSup hbdd hy
  refine measure_mono_null hsub ?_
  have h0 : cdf H (sSup T) = 0 := hc
  rw [cdf_eq_real, measureReal_def, ENNReal.toReal_eq_zero_iff] at h0
  exact h0.resolve_right (measure_ne_top _ _)

variable (k : ℕ)

/-- `Φ = H(x) = cdf^k` -/
noncomputable def Phi (x : ℝ) : ℝ := cdf H x ^ k

lemma Phi_cont [NullSingletonClass H] : Continuous (Phi H k) := (cdf_cont H).pow k
lemma Phi_mono : Monotone (Phi H k) := fun a b h =>
  pow_le_pow_left₀ (cdf_nonneg H a) ((cdf H).mono h) k
lemma Phi_nonneg (x : ℝ) : 0 ≤ Phi H k x := pow_nonneg (cdf_nonneg H x) k

/-- winning probability of bid `b` against `k` bids `sig0(Y_i)`, `Y_i ~ H` -/
noncomputable def Win (r b : ℝ) : ℝ :=
  if r ≤ b then (H {y | sig0 (Phi H k) r y ≤ b}).toReal ^ k else 0

lemma Vopt_nonneg [NullSingletonClass H] (r x : ℝ) : 0 ≤ Vopt (Phi H k) r x := by
  unfold Vopt
  split_ifs with h
  · exact le_rfl
  · exact Aint_nonneg (Phi_cont H k) (Phi_nonneg H k) (not_lt.mp h)

lemma Win_nonneg (r b : ℝ) : 0 ≤ Win H k r b := by
  unfold Win; split_ifs
  · exact pow_nonneg ENNReal.toReal_nonneg k
  · exact le_rfl

lemma br_bound [NullSingletonClass H] (hk : k ≠ 0) {r : ℝ} (x b : ℝ) :
    (x - b) * Win H k r b ≤ Vopt (Phi H k) r x := by
  have hV := Vopt_nonneg H k r x
  unfold Win
  by_cases hrb : r ≤ b
  swap
  · rw [if_neg hrb, mul_zero]; exact hV
  rw [if_pos hrb]
  by_cases hxb : x ≤ b
  · have : 0 ≤ (H {y | sig0 (Phi H k) r y ≤ b}).toReal ^ k := pow_nonneg ENNReal.toReal_nonneg k
    nlinarith
  have hbx : b < x := not_le.mp hxb
  have hrx : r ≤ x := le_trans hrb hbx.le
  have hVx : Vopt (Phi H k) r x = Aint (Phi H k) r x := by
    unfold Vopt; rw [if_neg (not_lt.mpr hrx)]
  rw [hVx]
  have hΦ := Phi_cont H k
  have hm := Phi_mono H k
  have h0 := Phi_nonneg H k
  set S := {y | sigR (Phi H k) r y ≤ b} with hS
  -- the bid sets differ by a null set
  have hsubset : {y | sig0 (Phi H k) r y ≤ b} ⊆ S ∪ {y | cdf H y = 0} := by
    intro y hy
    by_cases hz : cdf H y = 0
    · exact Or.inr hz
    · left
      have hΦy : Phi H k y ≠ 0 := pow_ne_zero k hz
      show sigR (Phi H k) r y ≤ b
      have : sigR (Phi H k) r y = sig0 (Phi H k) r y := by
        unfold sigR sig0; split_ifs <;> rfl
      rw [this]; exact hy
  have hK : H {y | sig0 (Phi H k) r y ≤ b} ≤ H S := by
    calc H {y | sig0 (Phi H k) r y ≤ b} ≤ H (S ∪ {y | cdf H y = 0}) := measure_mono hsubset
      _ ≤ H S + H {y | cdf H y = 0} := measure_union_le _ _
      _ = H S := by rw [cdf_zero_null H, add_zero]
  have hKr : (H {y | sig0 (Phi H k) r y ≤ b}).toReal ≤ (H S).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) hK
  have hrS : r ∈ S := by
    show sigR (Phi H k) r r ≤ b
    have : sigR (Phi H k) r r = r := by
      have h1 := r_le_sigR hΦ hm h0 (le_refl r)
      have h2 := sigR_le hΦ h0 (le_refl r)
      linarith
    rw [this]; exact hrb
  -- every point of `S` above `r` satisfies the bound
  have hpt : ∀ c ∈ S, r ≤ c → (x - b) * Phi H k c ≤ Aint (Phi H k) r x :=
    fun c hc hcr => value_bound_of hΦ hm h0 hrb hrx hbx hc hcr
  have hxb0 : 0 ≤ x - b := by linarith
  have hKpow : (H {y | sig0 (Phi H k) r y ≤ b}).toReal ^ k ≤ (H S).toReal ^ k :=
    pow_le_pow_left₀ ENNReal.toReal_nonneg hKr k
  by_cases hbdd : BddAbove S
  · set c := sSup S
    have hS' : (S ∩ Ici r).Nonempty := ⟨r, hrS, le_refl r⟩
    have hbdd' : BddAbove (S ∩ Ici r) := hbdd.mono inter_subset_left
    have hcS : sSup (S ∩ Ici r) = c := by
      apply le_antisymm (csSup_le_csSup hbdd hS' inter_subset_left)
      apply csSup_le ⟨r, hrS⟩
      intro y hy
      by_cases hyr : r ≤ y
      · exact le_csSup hbdd' ⟨hy, hyr⟩
      · exact le_trans (not_le.mp hyr).le (le_csSup hbdd' ⟨hrS, le_refl r⟩)
    have hclosed : IsClosed {y | (x - b) * Phi H k y ≤ Aint (Phi H k) r x} :=
      isClosed_le (continuous_const.mul hΦ) continuous_const
    have hcmem : c ∈ {y | (x - b) * Phi H k y ≤ Aint (Phi H k) r x} := by
      have h1 := csSup_mem_closure hS' hbdd'
      rw [hcS] at h1
      have h2 : closure (S ∩ Ici r) ⊆ {y | (x - b) * Phi H k y ≤ Aint (Phi H k) r x} :=
        closure_minimal (fun y hy => hpt y hy.1 hy.2) hclosed
      exact h2 h1
    have hSc : (H S).toReal ≤ cdf H c := by
      rw [cdf_eq_real, measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun y hy => le_csSup hbdd hy))
    have : (H S).toReal ^ k ≤ Phi H k c := pow_le_pow_left₀ ENNReal.toReal_nonneg hSc k
    calc (x - b) * (H {y | sig0 (Phi H k) r y ≤ b}).toReal ^ k
        ≤ (x - b) * Phi H k c := mul_le_mul_of_nonneg_left (hKpow.trans this) hxb0
      _ ≤ _ := hcmem
  · -- `S` unbounded: the bound holds with `Φ = 1` in the limit
    have hle1 : (H S).toReal ^ k ≤ 1 :=
      pow_le_one₀ ENNReal.toReal_nonneg (by
        have := prob_le_one (μ := H) (s := S)
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this))
    have hlim : x - b ≤ Aint (Phi H k) r x := by
      by_contra hcon'
      have hcon : Aint (Phi H k) r x < x - b := not_le.mp hcon'
      have ht : Tendsto (Phi H k) atTop (𝓝 1) := by
        have := (tendsto_cdf_atTop (μ := H)).pow k
        rw [one_pow] at this
        exact this
      have ht2 : Tendsto (fun y => (x - b) * Phi H k y) atTop (𝓝 (x - b)) := by
        simpa using ht.const_mul (x - b)
      obtain ⟨N, hN⟩ := eventually_atTop.mp (ht2.eventually (lt_mem_nhds hcon))
      obtain ⟨y, hyS, hyN⟩ := not_bddAbove_iff.mp hbdd (max N r)
      have := hN y (le_trans (le_max_left _ _) hyN.le)
      have := hpt y hyS (le_trans (le_max_right _ _) hyN.le)
      linarith
    calc (x - b) * (H {y | sig0 (Phi H k) r y ≤ b}).toReal ^ k
        ≤ (x - b) * 1 := mul_le_mul_of_nonneg_left (hKpow.trans hle1) hxb0
      _ ≤ _ := by linarith

lemma br_attain [NullSingletonClass H] (hk : k ≠ 0) {r : ℝ} (hr : 0 < r) (x : ℝ) :
    Vopt (Phi H k) r x ≤ (x - sig0 (Phi H k) r x) * Win H k r (sig0 (Phi H k) r x) := by
  have hΦ := Phi_cont H k
  have hm := Phi_mono H k
  have h0 := Phi_nonneg H k
  by_cases hxr : x < r
  · have e : sig0 (Phi H k) r x = x := by unfold sig0; rw [if_pos hxr]
    have hV : Vopt (Phi H k) r x = 0 := by unfold Vopt; rw [if_pos hxr]
    rw [hV, e]; unfold Win; rw [if_neg (not_le.mpr hxr)]; simp
  have hrx : r ≤ x := not_lt.mp hxr
  have hV : Vopt (Phi H k) r x = Aint (Phi H k) r x := by unfold Vopt; rw [if_neg hxr]
  rw [hV]
  by_cases hz : Phi H k x = 0
  · have e : sig0 (Phi H k) r x = 0 := by unfold sig0; rw [if_neg hxr, if_pos hz]
    have hA : Aint (Phi H k) r x = 0 := by
      have h1 := Aint_nonneg hΦ h0 hrx
      have h2 := Aint_le hΦ hm hrx
      rw [hz, mul_zero] at h2
      linarith
    rw [hA, e]; unfold Win; rw [if_neg (not_le.mpr hr)]; simp
  have e : sig0 (Phi H k) r x = sigR (Phi H k) r x := by
    unfold sig0 sigR; rw [if_neg hxr, if_neg hz, if_neg hxr, if_neg hz]
  rw [e]
  have hrs : r ≤ sigR (Phi H k) r x := r_le_sigR hΦ hm h0 hrx
  have hsx : sigR (Phi H k) r x ≤ x := sigR_le hΦ h0 hrx
  have hsub : Iic x ⊆ {y | sig0 (Phi H k) r y ≤ sigR (Phi H k) r x} := by
    intro y hy
    show sig0 (Phi H k) r y ≤ sigR (Phi H k) r x
    unfold sig0
    split_ifs with h1 h2
    · linarith
    · linarith
    · have : sigR (Phi H k) r y = y - Aint (Phi H k) r y / Phi H k y := by
        unfold sigR; rw [if_neg h1, if_neg h2]
      rw [← this]; exact sigR_mono hΦ hm h0 hy
  have hW : Phi H k x ≤ Win H k r (sigR (Phi H k) r x) := by
    unfold Win; rw [if_pos hrs]
    apply pow_le_pow_left₀ (cdf_nonneg H x)
    rw [cdf_eq_real, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hmul := sigR_mul hΦ hm h0 hrx
  have : (x - sigR (Phi H k) r x) * Phi H k x = Aint (Phi H k) r x := by
    have : (x - sigR (Phi H k) r x) * Phi H k x = x * Phi H k x - sigR (Phi H k) r x * Phi H k x := by ring
    rw [this, hmul]; ring
  rw [← this]
  exact mul_le_mul_of_nonneg_left hW (by linarith)

end OneContext

/-! ## Part 3. Link to the model's `sigma`, `H`, `lam` and the competitor integral. -/

section ModelLink

open ContextualAuctions.RevEquiv

lemma Aint_cont {Φ : ℝ → ℝ} (hΦ : Continuous Φ) (r : ℝ) : Continuous (Aint Φ r) :=
  intervalIntegral.continuous_primitive (fun a b => hΦ.intervalIntegrable a b) r

lemma sig0_meas {Φ : ℝ → ℝ} (hΦm : Measurable Φ)
    (hint : ∀ a b, IntervalIntegrable Φ volume a b) (r : ℝ) : Measurable (sig0 Φ r) := by
  unfold sig0
  have hA : Continuous (Aint Φ r) := intervalIntegral.continuous_primitive hint r
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_id
    (Measurable.ite (measurableSet_eq_fun hΦm measurable_const) measurable_const
      (measurable_id.sub (hA.measurable.div hΦm)))

lemma Phi_meas (H : Measure ℝ) [IsProbabilityMeasure H] (k : ℕ) : Measurable (Phi H k) :=
  (Phi_mono H k).measurable

lemma Phi_ii (H : Measure ℝ) [IsProbabilityMeasure H] (k : ℕ) (a b : ℝ) :
    IntervalIntegrable (Phi H k) volume a b :=
  (Phi_mono H k).intervalIntegrable

variable (M : Model) (μ : Buyer M → ℝ)

lemma val_meas_left (α : Context M) : Measurable (fun θ : Buyer M => val M θ α) := by
  unfold val
  exact Finset.measurable_sum _ (fun i _ =>
    ((measurable_pi_apply i).comp measurable_fst).mul measurable_const)

lemma paced_meas (hμ : Measurable μ) (α : Context M) :
    Measurable (fun θ : Buyer M => paced M μ θ α) := by
  unfold paced
  exact (val_meas_left M α).div (measurable_const.add hμ)

lemma lam_prob [IsProbabilityMeasure M.G] (hμ : Measurable μ) (α : Context M) :
    IsProbabilityMeasure (lam M μ α) :=
  ⟨by rw [lam, Measure.map_apply (paced_meas M μ hμ α) MeasurableSet.univ, Set.preimage_univ]
      exact measure_univ⟩

lemma H_eq [IsProbabilityMeasure M.G] (hμ : Measurable μ) (α : Context M) (x : ℝ) :
    H M μ α x = Phi (lam M μ α) (M.n - 1) x := by
  haveI := lam_prob M μ hμ α
  unfold H Phi
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def, lam,
    Measure.map_apply (paced_meas M μ hμ α) measurableSet_Iic]
  rfl

lemma sigma_eq [IsProbabilityMeasure M.G] (hμ : Measurable μ) (α : Context M) :
    sigma M μ α = sig0 (Phi (lam M μ α) (M.n - 1)) (M.r α) := by
  funext x
  have hH : H M μ α = Phi (lam M μ α) (M.n - 1) := funext (H_eq M μ hμ α)
  unfold sigma sig0 Aint
  rw [hH]

/-- the competitor integral of a winning payoff equals `c * Win` -/
lemma competitor_integral [IsProbabilityMeasure M.G] (hμ : Measurable μ) (α : Context M)
    (b c : ℝ) :
    ∫ θs : Fin (M.n - 1) → Buyer M,
        (if (M.r α ≤ b ∧ ∀ i, beta M μ (θs i) α ≤ b) then c else 0)
          ∂(Measure.pi fun _ : Fin (M.n - 1) => M.G) =
      c * Win (lam M μ α) (M.n - 1) (M.r α) b := by
  haveI := lam_prob M μ hμ α
  set Φ := Phi (lam M μ α) (M.n - 1) with hΦdef
  set Q : Set (Buyer M) := {θ' | beta M μ θ' α ≤ b} with hQ
  have hsig := sigma_eq M μ hμ α
  have hQ' : Q = (fun θ => paced M μ θ α) ⁻¹' {y | sig0 Φ (M.r α) y ≤ b} := by
    ext θ'
    show beta M μ θ' α ≤ b ↔ sig0 Φ (M.r α) (paced M μ θ' α) ≤ b
    rw [beta, hsig]
  have hmeasS : MeasurableSet {y | sig0 Φ (M.r α) y ≤ b} :=
    measurableSet_le (sig0_meas (Phi_meas _ _) (Phi_ii _ _) _) measurable_const
  have hQm : MeasurableSet Q := by rw [hQ']; exact (paced_meas M μ hμ α) hmeasS
  have hGQ : M.G Q = lam M μ α {y | sig0 Φ (M.r α) y ≤ b} := by
    rw [hQ', lam, Measure.map_apply (paced_meas M μ hμ α) hmeasS]
  unfold Win
  by_cases hP : M.r α ≤ b
  · simp only [hP, true_and, if_true]
    have hfun : (fun θs : Fin (M.n - 1) → Buyer M => if ∀ i, beta M μ (θs i) α ≤ b then c else 0)
        = (Set.univ.pi fun _ : Fin (M.n - 1) => Q).indicator (fun _ => c) := by
      funext θs
      simp only [Set.indicator, Set.mem_univ_pi, hQ, Set.mem_setOf_eq]
    rw [hfun, integral_indicator_const c (MeasurableSet.univ_pi fun _ => hQm), measureReal_def,
      Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hGQ,
      ENNReal.toReal_pow, smul_eq_mul, mul_comm]
  · simp [hP]

end ModelLink

/-! ## Part 3b. Joint measurability of `sigma` and `beta`. -/

section JointMeas

open ContextualAuctions.RevEquiv

variable (M : Model) (μ : Buyer M → ℝ)

lemma val_meas_joint : Measurable (fun q : Buyer M × Context M => val M q.1 q.2) := by
  unfold val
  exact Finset.measurable_sum _ (fun i _ =>
    ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).mul
      ((measurable_pi_apply i).comp measurable_snd))

lemma paced_meas_joint (hμ : Measurable μ) :
    Measurable (fun q : Buyer M × Context M => paced M μ q.1 q.2) := by
  unfold paced
  exact (val_meas_joint M).div (measurable_const.add (hμ.comp measurable_fst))

lemma H_meas_joint [IsProbabilityMeasure M.G] (hμ : Measurable μ) :
    Measurable (fun p : Context M × ℝ => H M μ p.1 p.2) := by
  unfold H
  have hs : MeasurableSet {z : (Context M × ℝ) × Buyer M | paced M μ z.2 z.1.1 ≤ z.1.2} := by
    have h1 : Measurable (fun z : (Context M × ℝ) × Buyer M => paced M μ z.2 z.1.1) := by
      simpa only [Function.comp_def] using (paced_meas_joint M μ hμ).comp
        (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    exact measurableSet_le h1 (measurable_snd.comp measurable_fst)
  have := measurable_measure_prodMk_left (ν := M.G) hs
  exact (this.ennreal_toReal).pow_const _

lemma Ioc_integral_meas {f : (Context M × ℝ) → ℝ → ℝ} (hf : Measurable (Function.uncurry f))
    {a b : Context M × ℝ → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun p => ∫ s in Ioc (a p) (b p), f p s) := by
  have e : (fun p => ∫ s in Ioc (a p) (b p), f p s) =
      fun p => ∫ s, (if a p < s ∧ s ≤ b p then f p s else 0) := by
    funext p
    rw [← integral_indicator measurableSet_Ioc]
    congr 1; funext s
    simp only [Set.indicator, Set.mem_Ioc]
  rw [e]
  have hg : Measurable (Function.uncurry fun p (s : ℝ) => if a p < s ∧ s ≤ b p then f p s else 0) := by
    refine Measurable.ite ?_ hf measurable_const
    exact (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hb.comp measurable_fst))
  exact (hg.stronglyMeasurable.integral_prod_right (ν := volume)).measurable

lemma sigma_meas_joint [IsProbabilityMeasure M.G] (hμ : Measurable μ) (hr : Measurable M.r) :
    Measurable (fun p : Context M × ℝ => sigma M μ p.1 p.2) := by
  have hH := H_meas_joint M μ hμ
  have hR : Measurable (fun p : Context M × ℝ => M.r p.1) := hr.comp measurable_fst
  have hHf : Measurable (Function.uncurry fun (p : Context M × ℝ) (s : ℝ) => H M μ p.1 s) :=
    by simpa only [Function.comp_def, Function.uncurry_def] using
      hH.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hI : Measurable (fun p : Context M × ℝ => ∫ s in (M.r p.1)..p.2, H M μ p.1 s) := by
    simp only [intervalIntegral]
    exact (Ioc_integral_meas M hHf hR measurable_snd).sub (Ioc_integral_meas M hHf measurable_snd hR)
  unfold sigma
  exact Measurable.ite (measurableSet_lt measurable_snd hR) measurable_snd
    (Measurable.ite (measurableSet_eq_fun hH measurable_const) measurable_const
      (measurable_snd.sub (hI.div hH)))

lemma beta_meas_joint [IsProbabilityMeasure M.G] (hμ : Measurable μ) (hr : Measurable M.r) :
    Measurable (fun q : Buyer M × Context M => beta M μ q.1 q.2) := by
  unfold beta
  simpa only [Function.comp_def] using
    (sigma_meas_joint M μ hμ hr).comp (measurable_snd.prodMk (paced_meas_joint M μ hμ))

end JointMeas

/-! ## Part 3c. The Lagrangian of a bid, integrated over competitors. -/

section Lagr

open ContextualAuctions.RevEquiv Classical

variable (M : Model) (μ : Buyer M → ℝ)

lemma lagr_fubini [IsProbabilityMeasure M.G] [IsProbabilityMeasure M.F] (hμ : Measurable μ) (θ : Buyer M) (t : ℝ)
    (b : Context M → ℝ)
    (hint : Integrable (fun ω : Context M × (Fin (M.n - 1) → Buyer M) =>
      if wins M (beta M μ) b ω then val M θ ω.1 - (1 + t) * b ω.1 else 0) (P M)) :
    ∫ ω, (if wins M (beta M μ) b ω then val M θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M =
      ∫ α, (val M θ α - (1 + t) * b α) * Win (lam M μ α) (M.n - 1) (M.r α) (b α) ∂M.F := by
  haveI : SigmaFinite (Measure.pi fun _ : Fin (M.n - 1) => M.G) := Measure.pi.sigmaFinite _
  rw [P] at hint ⊢
  rw [integral_prod _ hint]
  congr 1; funext α
  rw [← competitor_integral M μ hμ α (b α) (val M θ α - (1 + t) * b α)]
  congr 1; funext θs
  exact if_congr Iff.rfl rfl rfl

/-- same for the payment `b * 1{wins}` -/
lemma pay_fubini [IsProbabilityMeasure M.G] [IsProbabilityMeasure M.F] (hμ : Measurable μ) (b : Context M → ℝ)
    (hint : Integrable (fun ω : Context M × (Fin (M.n - 1) → Buyer M) =>
      if wins M (beta M μ) b ω then b ω.1 else 0) (P M)) :
    ∫ ω, (if wins M (beta M μ) b ω then b ω.1 else 0) ∂P M =
      ∫ α, b α * Win (lam M μ α) (M.n - 1) (M.r α) (b α) ∂M.F := by
  haveI : SigmaFinite (Measure.pi fun _ : Fin (M.n - 1) => M.G) := Measure.pi.sigmaFinite _
  rw [P] at hint ⊢
  rw [integral_prod _ hint]
  congr 1; funext α
  rw [← competitor_integral M μ hμ α (b α) (b α)]
  congr 1; funext θs
  exact if_congr Iff.rfl rfl rfl

end Lagr


/-! ## Part 3d. The first-price dual: closed form, attainment, subgradient. -/

section Dual

open ContextualAuctions.RevEquiv Classical

lemma Aint_le_mono {Φ : ℝ → ℝ} {r : ℝ} (hm : Monotone Φ) {y : ℝ} (hy : r ≤ y) :
    Aint Φ r y ≤ (y - r) * Φ y := by
  have h1 : ∫ s in r..y, Φ s ≤ ∫ s in r..y, Φ y :=
    intervalIntegral.integral_mono_on hy (hm.intervalIntegrable) intervalIntegrable_const
      (fun s hs => hm hs.2)
  simpa [Aint, intervalIntegral.integral_const, smul_eq_mul] using h1

lemma sig0_ge_r {Φ : ℝ → ℝ} {r : ℝ} (hm : Monotone Φ) (h0 : ∀ x, 0 ≤ Φ x) {x : ℝ}
    (hx : r ≤ x) (hΦ : Φ x ≠ 0) : r ≤ sig0 Φ r x ∧ sig0 Φ r x ≤ x := by
  have hpos : 0 < Φ x := lt_of_le_of_ne (h0 x) (Ne.symm hΦ)
  have hA := Aint_le_mono hm hx
  have hA0 : 0 ≤ Aint Φ r x := intervalIntegral.integral_nonneg hx (fun s _ => h0 s)
  have e : sig0 Φ r x = x - Aint Φ r x / Φ x := by
    simp [sig0, not_lt.mpr hx, hΦ]
  rw [e]
  constructor
  · have : Aint Φ r x / Φ x ≤ x - r := by rw [div_le_iff₀ hpos]; linarith
    linarith
  · have : 0 ≤ Aint Φ r x / Φ x := div_nonneg hA0 hpos.le
    linarith

lemma sig0_nonneg {Φ : ℝ → ℝ} {r : ℝ} (hm : Monotone Φ) (h0 : ∀ x, 0 ≤ Φ x) (hr : 0 < r)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ sig0 Φ r x := by
  by_cases h1 : x < r
  · simp [sig0, h1, hx]
  by_cases h2 : Φ x = 0
  · simp [sig0, h1, h2]
  · exact hr.le.trans (sig0_ge_r hm h0 (not_lt.mp h1) h2).1

lemma sig0_abs_le {Φ : ℝ → ℝ} {r : ℝ} (hm : Monotone Φ) (h0 : ∀ x, 0 ≤ Φ x) (hr : 0 < r)
    (x : ℝ) : |sig0 Φ r x| ≤ |x| := by
  by_cases h1 : x < r
  · simp [sig0, h1]
  by_cases h2 : Φ x = 0
  · simp [sig0, h1, h2]
  · have h := sig0_ge_r hm h0 (not_lt.mp h1) h2
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact h.2

variable (M : Model) (μ : Buyer M → ℝ)

lemma val_meas_right (θ : Buyer M) : Measurable (fun α : Context M => val M θ α) := by
  unfold val
  exact Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i))

lemma Vopt_nonneg' (H : Measure ℝ) [IsProbabilityMeasure H] (k : ℕ) (r x : ℝ) :
    0 ≤ Vopt (Phi H k) r x := by
  unfold Vopt
  split_ifs with h
  · exact le_rfl
  · exact intervalIntegral.integral_nonneg (not_lt.mp h) (fun s _ => Phi_nonneg H k s)

/-- the first-price bid of type `θ` paced at `t` -/
noncomputable def bt (θ : Buyer M) (t : ℝ) (α : Context M) : ℝ :=
  sigma M μ α (val M θ α / (1 + t))

lemma wins_meas [IsProbabilityMeasure M.G] (hμ : Measurable μ) (hr : Measurable M.r)
    {b : Context M → ℝ} (hb : Measurable b) :
    MeasurableSet {ω : Context M × (Fin (M.n - 1) → Buyer M) | wins M (beta M μ) b ω} := by
  have e : {ω : Context M × (Fin (M.n - 1) → Buyer M) | wins M (beta M μ) b ω} =
      {ω | M.r ω.1 ≤ b ω.1} ∩ ⋂ i, {ω | beta M μ (ω.2 i) ω.1 ≤ b ω.1} := by
    ext ω; simp [wins]
  rw [e]
  refine (measurableSet_le (hr.comp measurable_fst) (hb.comp measurable_fst)).inter
    (MeasurableSet.iInter fun i => ?_)
  have hs : Measurable (fun ω : Context M × (Fin (M.n - 1) → Buyer M) => (ω.2 i, ω.1)) :=
    ((measurable_pi_apply i).comp measurable_snd).prodMk measurable_fst
  have h1 : Measurable (fun ω : Context M × (Fin (M.n - 1) → Buyer M) => beta M μ (ω.2 i) ω.1) :=
    by simpa only [Function.comp_def] using (beta_meas_joint M μ hμ hr).comp hs
  exact measurableSet_le h1 (hb.comp measurable_fst)

lemma ite_wins_integrable [IsProbabilityMeasure M.G] [IsProbabilityMeasure M.F]
    (hμ : Measurable μ) (hr : Measurable M.r) {b c : Context M → ℝ} (hb : Measurable b)
    (hc : Measurable c) {C : ℝ} (hC : ∀ᵐ α ∂M.F, |c α| ≤ C) :
    Integrable (fun ω : Context M × (Fin (M.n - 1) → Buyer M) =>
      if wins M (beta M μ) b ω then c ω.1 else 0) (P M) := by
  haveI : SigmaFinite (Measure.pi fun _ : Fin (M.n - 1) => M.G) := Measure.pi.sigmaFinite _
  haveI : IsProbabilityMeasure (P M) := by rw [P]; infer_instance
  refine Integrable.of_bound ?_ (max C 0) ?_
  · exact (Measurable.ite (wins_meas M μ hμ hr hb) (hc.comp measurable_fst)
      measurable_const).aestronglyMeasurable
  · have h2 : ∀ᵐ ω ∂P M, |c ω.1| ≤ C := by
      rw [P]; exact Measure.quasiMeasurePreserving_fst.ae hC
    filter_upwards [h2] with ω hω
    split_ifs
    · rw [Real.norm_eq_abs]; exact hω.trans (le_max_left _ _)
    · simp

lemma Vopt_meas [IsProbabilityMeasure M.G] (hμ : Measurable μ) (hr : Measurable M.r) :
    Measurable (fun p : Context M × ℝ => Vopt (Phi (lam M μ p.1) (M.n - 1)) (M.r p.1) p.2) := by
  have e : (fun p : Context M × ℝ => Vopt (Phi (lam M μ p.1) (M.n - 1)) (M.r p.1) p.2) =
      fun p => if p.2 < M.r p.1 then 0 else ∫ s in (M.r p.1)..p.2, H M μ p.1 s := by
    funext p
    unfold Vopt Aint
    have hH : Phi (lam M μ p.1) (M.n - 1) = H M μ p.1 := funext fun x => (H_eq M μ hμ p.1 x).symm
    rw [hH]
  rw [e]
  have hH := H_meas_joint M μ hμ
  have hR : Measurable (fun p : Context M × ℝ => M.r p.1) := hr.comp measurable_fst
  have hHf : Measurable (Function.uncurry fun (p : Context M × ℝ) (s : ℝ) => H M μ p.1 s) :=
    by simpa only [Function.comp_def, Function.uncurry_def] using
      hH.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hI : Measurable (fun p : Context M × ℝ => ∫ s in (M.r p.1)..p.2, H M μ p.1 s) := by
    simp only [intervalIntegral]
    exact (Ioc_integral_meas M hHf hR measurable_snd).sub (Ioc_integral_meas M hHf measurable_snd hR)
  exact Measurable.ite (measurableSet_lt measurable_snd hR) measurable_const hI

lemma Vopt_le (H : Measure ℝ) [IsProbabilityMeasure H] (k : ℕ) {r : ℝ} (hr : 0 < r) (x : ℝ) :
    Vopt (Phi H k) r x ≤ |x| := by
  unfold Vopt
  split_ifs with h
  · exact abs_nonneg x
  · have hx : r ≤ x := not_lt.mp h
    have h1 := Aint_le_mono (Phi_mono H k) hx
    have h2 : Phi H k x ≤ 1 := pow_le_one₀ (ProbabilityTheory.cdf_nonneg H x) (ProbabilityTheory.cdf_le_one H x)
    have h3 : 0 ≤ Phi H k x := Phi_nonneg H k x
    calc Aint (Phi H k) r x ≤ (x - r) * Phi H k x := h1
      _ ≤ (x - r) * 1 := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ ≤ |x| := by rw [mul_one]; linarith [le_abs_self x]

/-- the closed-form value of the dual at `t` -/
noncomputable def Vval (θ : Buyer M) (t : ℝ) : ℝ :=
  ∫ α, (1 + t) * Vopt (Phi (lam M μ α) (M.n - 1)) (M.r α) (val M θ α / (1 + t)) ∂M.F

lemma Vval_integrable [IsProbabilityMeasure M.G] [IsProbabilityMeasure M.F] (hμ : Measurable μ)
    (hr : Measurable M.r) (hrp : ∀ α, 0 < M.r α) (θ : Buyer M) {t : ℝ} (ht : -1 < t)
    {C : ℝ} (hC : ∀ᵐ α ∂M.F, |val M θ α| ≤ C) :
    Integrable (fun α => (1 + t) * Vopt (Phi (lam M μ α) (M.n - 1)) (M.r α)
      (val M θ α / (1 + t))) M.F := by
  have ht1 : 0 < 1 + t := by linarith
  have hm : Measurable (fun α => (1 + t) * Vopt (Phi (lam M μ α) (M.n - 1)) (M.r α)
      (val M θ α / (1 + t))) :=
    measurable_const.mul ((Vopt_meas M μ hμ hr).comp
      (measurable_id.prodMk ((val_meas_right M θ).div_const _)))
  refine Integrable.of_bound hm.aestronglyMeasurable (max C 0) ?_
  filter_upwards [hC] with α hα
  haveI := lam_prob M μ hμ α
  have h0 := Vopt_nonneg' (lam M μ α) (M.n - 1) (M.r α) (val M θ α / (1 + t))
  have h1 := Vopt_le (lam M μ α) (M.n - 1) (hrp α) (val M θ α / (1 + t))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht1.le h0)]
  calc (1 + t) * Vopt (Phi (lam M μ α) (M.n - 1)) (M.r α) (val M θ α / (1 + t))
      ≤ (1 + t) * |val M θ α / (1 + t)| := mul_le_mul_of_nonneg_left h1 ht1.le
    _ = |val M θ α| := by rw [abs_div, abs_of_pos ht1]; field_simp
    _ ≤ max C 0 := hα.trans (le_max_left _ _)

end Dual


section Dual2

open ContextualAuctions.RevEquiv Classical

variable (M : Model) (μ : Buyer M → ℝ)

lemma lagr_integrable [IsProbabilityMeasure M.G] [IsProbabilityMeasure M.F] (hμ : Measurable μ)
    (hr : Measurable M.r) (θ : Buyer M) (t : ℝ) {C : ℝ} (hC : ∀ᵐ α ∂M.F, |val M θ α| ≤ C)
    {b : Context M → ℝ} (hb : Admissible M (beta M μ) b) :
    Integrable (fun ω : Context M × (Fin (M.n - 1) → Buyer M) =>
      if wins M (beta M μ) b ω then val M θ ω.1 - (1 + t) * b ω.1 else 0) (P M) := by
  have e : (fun ω : Context M × (Fin (M.n - 1) → Buyer M) =>
      if wins M (beta M μ) b ω then val M θ ω.1 - (1 + t) * b ω.1 else 0) =
      fun ω => (if wins M (beta M μ) b ω then val M θ ω.1 else 0) -
        (1 + t) * (if wins M (beta M μ) b ω then b ω.1 else 0) := by
    funext ω; split_ifs <;> ring
  rw [e]
  exact (ite_wins_integrable M μ hμ hr hb.1 (val_meas_right M θ) hC).sub (hb.2.2.const_mul _)

lemma scale_eq (v t b W : ℝ) (ht1 : 0 < 1 + t) :
    (v - (1 + t) * b) * W = (1 + t) * ((v / (1 + t) - b) * W) := by
  have hv : (1 + t) * (v / (1 + t)) = v := by field_simp
  calc (v - (1 + t) * b) * W = ((1 + t) * (v / (1 + t)) - (1 + t) * b) * W := by rw [hv]
    _ = (1 + t) * ((v / (1 + t) - b) * W) := by ring

lemma lagr_le [IsProbabilityMeasure M.G] [IsProbabilityMeasure M.F] (hμ : Measurable μ)
    (hr : Measurable M.r) (hrp : ∀ α, 0 < M.r α) (hk : M.n - 1 ≠ 0)
    (hatom : ∀ᵐ α ∂M.F, ∀ y, lam M μ α {y} = 0)
    (θ : Buyer M) {t : ℝ} (ht : -1 < t) {C : ℝ} (hC : ∀ᵐ α ∂M.F, |val M θ α| ≤ C)
    {b : Context M → ℝ} (hb : Admissible M (beta M μ) b) :
    ∫ ω, (if wins M (beta M μ) b ω then val M θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M ≤
      Vval M μ θ t := by
  have ht1 : 0 < 1 + t := by linarith
  rw [lagr_fubini M μ hμ θ t b (lagr_integrable M μ hμ hr θ t hC hb)]
  by_cases hI : Integrable (fun α => (val M θ α - (1 + t) * b α) *
      Win (lam M μ α) (M.n - 1) (M.r α) (b α)) M.F
  · refine integral_mono_ae hI (Vval_integrable M μ hμ hr hrp θ ht hC) ?_
    filter_upwards [hatom] with α hα
    haveI := lam_prob M μ hμ α
    haveI : NullSingletonClass (lam M μ α) := ⟨hα⟩
    have := br_bound (lam M μ α) (M.n - 1) hk (r := M.r α) (val M θ α / (1 + t)) (b α)
    rw [scale_eq _ _ _ _ ht1]
    exact mul_le_mul_of_nonneg_left this ht1.le
  · rw [integral_undef hI]
    exact integral_nonneg fun α => by
      haveI := lam_prob M μ hμ α
      exact mul_nonneg ht1.le (Vopt_nonneg' _ _ _ _)

lemma bt_meas [IsProbabilityMeasure M.G] (hμ : Measurable μ) (hr : Measurable M.r)
    (θ : Buyer M) (t : ℝ) : Measurable (bt M μ θ t) :=
  (sigma_meas_joint M μ hμ hr).comp (measurable_id.prodMk ((val_meas_right M θ).div_const _))

lemma bt_eq [IsProbabilityMeasure M.G] (hμ : Measurable μ) (θ : Buyer M) (t : ℝ)
    (α : Context M) :
    bt M μ θ t α = sig0 (Phi (lam M μ α) (M.n - 1)) (M.r α) (val M θ α / (1 + t)) := by
  unfold bt; rw [sigma_eq M μ hμ α]

lemma bt_adm [IsProbabilityMeasure M.G] [IsProbabilityMeasure M.F] (hμ : Measurable μ)
    (hr : Measurable M.r) (hrp : ∀ α, 0 < M.r α) (θ : Buyer M) {t : ℝ} (ht : -1 < t)
    (hval : ∀ α ∈ M.A, 0 ≤ val M θ α) {C : ℝ} (hC : ∀ᵐ α ∂M.F, |val M θ α| ≤ C) :
    Admissible M (beta M μ) (bt M μ θ t) := by
  have ht1 : 0 < 1 + t := by linarith
  refine ⟨bt_meas M μ hμ hr θ t, fun α hα => ?_, ?_⟩
  · haveI := lam_prob M μ hμ α
    rw [bt_eq M μ hμ]
    exact sig0_nonneg (Phi_mono _ _) (Phi_nonneg _ _) (hrp α) (div_nonneg (hval α hα) ht1.le)
  · refine ite_wins_integrable M μ hμ hr (bt_meas M μ hμ hr θ t) (bt_meas M μ hμ hr θ t)
      (C := C / (1 + t)) ?_
    filter_upwards [hC] with α hα
    haveI := lam_prob M μ hμ α
    rw [bt_eq M μ hμ]
    refine (sig0_abs_le (Phi_mono _ _) (Phi_nonneg _ _) (hrp α) _).trans ?_
    rw [abs_div, abs_of_pos ht1]
    exact div_le_div_of_nonneg_right hα ht1.le

lemma lagr_bt [IsProbabilityMeasure M.G] [IsProbabilityMeasure M.F] (hμ : Measurable μ)
    (hr : Measurable M.r) (hrp : ∀ α, 0 < M.r α) (hk : M.n - 1 ≠ 0)
    (hatom : ∀ᵐ α ∂M.F, ∀ y, lam M μ α {y} = 0)
    (θ : Buyer M) {t : ℝ} (ht : -1 < t) (hval : ∀ α ∈ M.A, 0 ≤ val M θ α)
    {C : ℝ} (hC : ∀ᵐ α ∂M.F, |val M θ α| ≤ C) :
    ∫ ω, (if wins M (beta M μ) (bt M μ θ t) ω then
      val M θ ω.1 - (1 + t) * bt M μ θ t ω.1 else 0) ∂P M = Vval M μ θ t := by
  have ht1 : 0 < 1 + t := by linarith
  have hb := bt_adm M μ hμ hr hrp θ ht hval hC
  rw [lagr_fubini M μ hμ θ t _ (lagr_integrable M μ hμ hr θ t hC hb)]
  unfold Vval
  refine integral_congr_ae ?_
  filter_upwards [hatom] with α hα
  haveI := lam_prob M μ hμ α
  haveI : NullSingletonClass (lam M μ α) := ⟨hα⟩
  have h1 := br_bound (lam M μ α) (M.n - 1) hk (r := M.r α) (val M θ α / (1 + t))
    (sig0 (Phi (lam M μ α) (M.n - 1)) (M.r α) (val M θ α / (1 + t)))
  have h2 := br_attain (lam M μ α) (M.n - 1) hk (hrp α) (val M θ α / (1 + t))
  simp only [bt_eq M μ hμ θ t α]
  rw [scale_eq _ _ _ _ ht1]
  exact le_antisymm (mul_le_mul_of_nonneg_left h1 ht1.le) (mul_le_mul_of_nonneg_left h2 ht1.le)

lemma qDual_eq [IsProbabilityMeasure M.G] [IsProbabilityMeasure M.F] (hμ : Measurable μ)
    (hr : Measurable M.r) (hrp : ∀ α, 0 < M.r α) (hk : M.n - 1 ≠ 0)
    (hatom : ∀ᵐ α ∂M.F, ∀ y, lam M μ α {y} = 0)
    (θ : Buyer M) {t : ℝ} (ht : -1 < t) (hval : ∀ α ∈ M.A, 0 ≤ val M θ α)
    {C : ℝ} (hC : ∀ᵐ α ∂M.F, |val M θ α| ≤ C) :
    qDual M μ θ t = Vval M μ θ t + t * θ.2 := by
  unfold qDual
  congr 1
  apply IsGreatest.csSup_eq
  refine ⟨⟨bt M μ θ t, bt_adm M μ hμ hr hrp θ ht hval hC,
    (lagr_bt M μ hμ hr hrp hk hatom θ ht hval hC).symm⟩, ?_⟩
  rintro v ⟨b, hb, rfl⟩
  exact lagr_le M μ hμ hr hrp hk hatom θ ht hC hb

/-- the expected first-price payment of type `θ` paced at `t` -/
noncomputable def Spend (θ : Buyer M) (t : ℝ) : ℝ :=
  ∫ ω, (if wins M (beta M μ) (bt M μ θ t) ω then bt M μ θ t ω.1 else 0) ∂P M

lemma qDual_subgrad [IsProbabilityMeasure M.G] [IsProbabilityMeasure M.F] (hμ : Measurable μ)
    (hr : Measurable M.r) (hrp : ∀ α, 0 < M.r α) (hk : M.n - 1 ≠ 0)
    (hatom : ∀ᵐ α ∂M.F, ∀ y, lam M μ α {y} = 0)
    (θ : Buyer M) {t t' : ℝ} (ht : -1 < t) (ht' : -1 < t') (hval : ∀ α ∈ M.A, 0 ≤ val M θ α)
    {C : ℝ} (hC : ∀ᵐ α ∂M.F, |val M θ α| ≤ C) :
    qDual M μ θ t + (t' - t) * (θ.2 - Spend M μ θ t) ≤ qDual M μ θ t' := by
  rw [qDual_eq M μ hμ hr hrp hk hatom θ ht hval hC, qDual_eq M μ hμ hr hrp hk hatom θ ht' hval hC]
  have hb := bt_adm M μ hμ hr hrp θ ht hval hC
  have hL : ∫ ω, (if wins M (beta M μ) (bt M μ θ t) ω then
      val M θ ω.1 - (1 + t') * bt M μ θ t ω.1 else 0) ∂P M =
      Vval M μ θ t - (t' - t) * Spend M μ θ t := by
    rw [← lagr_bt M μ hμ hr hrp hk hatom θ ht hval hC]
    unfold Spend
    rw [← integral_const_mul, ← integral_sub (lagr_integrable M μ hμ hr θ t hC hb)
      (hb.2.2.const_mul _)]
    congr 1; funext ω; split_ifs <;> ring
  have hle := lagr_le M μ hμ hr hrp hk hatom θ ht' hC hb
  linarith

end Dual2


/-! ## Part 4. The second-price family is valid (when the reserve is positive). -/

section SecondPrice

open ContextualAuctions.RevEquiv Classical

variable (M : Model)

/-- second-price payment with reserve `r α`; ties win -/
noncomputable def spPay (α : Context M) (b : ℝ) (bs : Fin (M.n - 1) → ℝ) : ℝ :=
  if (M.r α ≤ b ∧ ∀ i, bs i ≤ b) then max (M.r α) (⨆ i, bs i) else 0

/-- the second-price family: truthful bidding -/
noncomputable def spFam : StdFamily M where
  pay := spPay M
  psi := fun _ _ x => x

lemma spPay_nonneg (α : Context M) (b : ℝ) (bs : Fin (M.n - 1) → ℝ) (hbs : ∀ i, 0 ≤ bs i) :
    0 ≤ spPay M α b bs := by
  unfold spPay
  split_ifs
  · exact le_trans (Real.iSup_nonneg hbs) (le_max_right _ _)
  · exact le_rfl

lemma spPay_nonneg' (hrp : ∀ α, 0 < M.r α) (α : Context M) (b : ℝ) (bs : Fin (M.n - 1) → ℝ) :
    0 ≤ spPay M α b bs := by
  unfold spPay
  split_ifs
  · exact le_trans (hrp α).le (le_max_left _ _)
  · exact le_rfl

lemma spPay_le (α : Context M) (b : ℝ) (bs : Fin (M.n - 1) → ℝ) :
    spPay M α b bs ≤ max b 0 := by
  unfold spPay
  split_ifs with h
  · exact max_le (h.1.trans (le_max_left _ _))
      (Real.iSup_le (fun i => (h.2 i).trans (le_max_left _ _)) (le_max_right _ _))
  · exact le_max_right _ _

lemma spPay_meas (hr : Measurable M.r) (X : Type) [MeasurableSpace X] (a : X → Context M)
    (b : X → ℝ) (bs : Fin (M.n - 1) → X → ℝ) (ha : Measurable a) (hb : Measurable b)
    (hbs : ∀ i, Measurable (bs i)) :
    Measurable (fun x => spPay M (a x) (b x) (fun i => bs i x)) := by
  unfold spPay
  have hra : Measurable (fun x => M.r (a x)) := hr.comp ha
  have hS : MeasurableSet {x | M.r (a x) ≤ b x ∧ ∀ i, bs i x ≤ b x} := by
    have e : {x | M.r (a x) ≤ b x ∧ ∀ i, bs i x ≤ b x} =
        {x | M.r (a x) ≤ b x} ∩ ⋂ i, {x | bs i x ≤ b x} := by ext x; simp
    rw [e]
    exact (measurableSet_le hra hb).inter (MeasurableSet.iInter fun i => measurableSet_le (hbs i) hb)
  exact Measurable.ite hS (hra.max (Measurable.iSup hbs)) measurable_const

lemma iidLaw_prob (H : Measure ℝ) [IsProbabilityMeasure H] : IsProbabilityMeasure (iidLaw M H) := by
  unfold iidLaw; infer_instance

/-- the per-draw surplus of bid `b` at value `c` -/
noncomputable def spU (α : Context M) (c b : ℝ) (ys : Fin (M.n - 1) → ℝ) : ℝ :=
  if (M.r α ≤ b ∧ ∀ i, ys i ≤ b) then c - max (M.r α) (⨆ i, ys i) else 0

lemma spU_int (hr : Measurable M.r) (H : Measure ℝ) [IsProbabilityMeasure H] (α : Context M)
    (c b : ℝ) : Integrable (spU M α c b) (iidLaw M H) := by
  haveI := iidLaw_prob M H
  have hm : Measurable (spU M α c b) := by
    have h := spPay_meas M hr (Fin (M.n - 1) → ℝ) (fun _ => α) (fun _ => b)
      (fun i ys => ys i) measurable_const measurable_const (fun i => measurable_pi_apply i)
    have e : spU M α c b = fun ys => (if (M.r α ≤ b ∧ ∀ i, ys i ≤ b) then c else 0) -
        spPay M α b (fun i => ys i) := by
      funext ys; unfold spU spPay; split_ifs <;> ring
    rw [e]
    refine Measurable.sub (Measurable.ite ?_ measurable_const measurable_const) h
    have e2 : {ys : Fin (M.n - 1) → ℝ | M.r α ≤ b ∧ ∀ i, ys i ≤ b} =
        {_ys | M.r α ≤ b} ∩ ⋂ i, {ys | ys i ≤ b} := by ext ys; simp
    rw [e2]
    exact (MeasurableSet.const _).inter
      (MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i) measurable_const)
  refine Integrable.of_bound hm.aestronglyMeasurable (|c| + |b| + |M.r α|) (ae_of_all _ fun ys => ?_)
  rw [Real.norm_eq_abs]
  unfold spU
  split_ifs with h
  · have h1 : M.r α ≤ max (M.r α) (⨆ i, ys i) := le_max_left _ _
    have h2 : max (M.r α) (⨆ i, ys i) ≤ max b 0 :=
      max_le (h.1.trans (le_max_left _ _))
        (Real.iSup_le (fun i => (h.2 i).trans (le_max_left _ _)) (le_max_right _ _))
    have h3 : max b 0 ≤ |b| := max_le (le_abs_self b) (abs_nonneg b)
    rw [abs_le]; constructor <;>
      nlinarith [abs_nonneg c, abs_nonneg b, abs_nonneg (M.r α), le_abs_self c, neg_abs_le c,
        le_abs_self (M.r α), neg_abs_le (M.r α)]
  · simp; positivity

lemma sp_rep (hr : Measurable M.r) (hrp : ∀ α, 0 < M.r α) (H : Measure ℝ) [IsProbabilityMeasure H]
    (α : Context M) (x b : ℝ) :
    x * oracleWinProb M (spFam M) α H b - (oraclePay M (spFam M) α H b).toReal =
      ∫ ys, spU M α x b ys ∂iidLaw M H := by
  haveI := iidLaw_prob M H
  set S := {ys : Fin (M.n - 1) → ℝ | M.r α ≤ b ∧ ∀ i, ys i ≤ b} with hSdef
  have hS : MeasurableSet S := by
    have e2 : S = {_ys | M.r α ≤ b} ∩ ⋂ i, {ys : Fin (M.n - 1) → ℝ | ys i ≤ b} := by
      ext ys; simp [hSdef]
    rw [e2]
    exact (MeasurableSet.const _).inter
      (MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i) measurable_const)
  have hpm : Measurable (fun ys : Fin (M.n - 1) → ℝ => spPay M α b ys) :=
    spPay_meas M hr (Fin (M.n - 1) → ℝ) (fun _ => α) (fun _ => b)
      (fun i ys => ys i) measurable_const measurable_const (fun i => measurable_pi_apply i)
  have hpi : Integrable (fun ys : Fin (M.n - 1) → ℝ => spPay M α b ys) (iidLaw M H) := by
    refine Integrable.of_bound hpm.aestronglyMeasurable (max b 0) (ae_of_all _ fun ys => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (spPay_nonneg' M hrp α b ys)]
    exact spPay_le M α b ys
  have h1 : (oraclePay M (spFam M) α H b).toReal = ∫ ys, spPay M α b ys ∂iidLaw M H := by
    unfold oraclePay
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ys => spPay_nonneg' M hrp α b ys)
      hpm.aestronglyMeasurable]
    rfl
  have h2 : oracleWinProb M (spFam M) α H b = ∫ ys, S.indicator 1 ys ∂iidLaw M H := by
    rw [integral_indicator_one hS, measureReal_def]
    rfl
  have hI : Integrable (fun ys => x * S.indicator 1 ys) (iidLaw M H) :=
    ((integrable_const (1 : ℝ)).indicator hS).const_mul x
  rw [h1, h2, ← integral_const_mul, ← integral_sub hI hpi]
  congr 1; funext ys
  simp only [Set.indicator_apply, hSdef, Set.mem_setOf_eq, Pi.one_apply, spPay, spU]
  split_ifs <;> ring

lemma sp_opt (hr : Measurable M.r) (hrp : ∀ α, 0 < M.r α) (H : Measure ℝ) [IsProbabilityMeasure H]
    (α : Context M) (x b : ℝ) :
    x * oracleWinProb M (spFam M) α H b - (oraclePay M (spFam M) α H b).toReal ≤
      x * oracleWinProb M (spFam M) α H x - (oraclePay M (spFam M) α H x).toReal := by
  rw [sp_rep M hr hrp, sp_rep M hr hrp]
  refine integral_mono (spU_int M hr H α x b) (spU_int M hr H α x x) (fun ys => ?_)
  unfold spU
  split_ifs with hb hx hx
  · exact le_rfl
  · -- wins at `b`, loses at `x`: the price is at least `x`
    have : x ≤ max (M.r α) (⨆ i, ys i) := by
      by_contra hlt
      push_neg at hlt
      apply hx
      refine ⟨(le_max_left _ _).trans hlt.le, fun i => ?_⟩
      exact (le_ciSup (Finite.bddAbove_range _) i).trans ((le_max_right _ _).trans hlt.le)
    linarith
  · have h0 : 0 ≤ x := (hrp α).le.trans hx.1
    have : max (M.r α) (⨆ i, ys i) ≤ x := max_le hx.1 (Real.iSup_le hx.2 h0)
    linarith
  · exact le_rfl

lemma sp_pay_lt_top (H : Measure ℝ) [IsProbabilityMeasure H] (α : Context M) (b : ℝ) :
    oraclePay M (spFam M) α H b < ⊤ := by
  haveI := iidLaw_prob M H
  unfold oraclePay
  calc ∫⁻ ys, ENNReal.ofReal ((spFam M).pay α b fun i => (spFam M).psi α H (ys i)) ∂iidLaw M H
      ≤ ∫⁻ _ys, ENNReal.ofReal (max b 0) ∂iidLaw M H :=
        lintegral_mono fun ys => ENNReal.ofReal_le_ofReal (spPay_le M α b _)
    _ < ⊤ := by rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_lt_top

lemma sp_valid (hr : Measurable M.r) (hrp : ∀ α, 0 < M.r α) : (spFam M).Valid M := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α b bs _ hbs; exact spPay_nonneg M α b bs hbs
  · intro α b bs σ
    show spPay M α b (bs ∘ σ) = spPay M α b bs
    unfold spPay
    have h1 : (∀ i, (bs ∘ σ) i ≤ b) ↔ ∀ i, bs i ≤ b :=
      ⟨fun h i => by simpa using h (σ.symm i), fun h i => h (σ i)⟩
    have h2 : (⨆ i, (bs ∘ σ) i) = ⨆ i, bs i := σ.iSup_comp
    rw [h2]
    exact if_congr (and_congr Iff.rfl h1) rfl rfl
  · intro X _ a b bs ha hb hbs; exact spPay_meas M hr X a b bs ha hb hbs
  · intro α _ H hH _ _ x hx
    exact ⟨hx.1, sp_pay_lt_top M H α x, fun b _ _ => sp_opt M hr hrp H α x b⟩
  · intro α _ H _ _ _
    exact ⟨fun a _ b _ h => h, fun x _ => Iff.rfl⟩
  · intro α _ H _ _ _
    show ∫⁻ ys, ENNReal.ofReal (spPay M α 0 fun i => ys i) ∂iidLaw M H = 0
    have : ∀ ys : Fin (M.n - 1) → ℝ, spPay M α 0 (fun i => ys i) = 0 := fun ys => by
      unfold spPay; rw [if_neg (fun h => absurd h.1 (not_le.mpr (hrp α)))]
    simp [this]
  · intro α _ H _ hat _ y
    exact hat y

end SecondPrice


/-! ## Part 5. Mollification and total-variation tools. -/

section TVTools

open Filter Topology
open scoped Convolution


section Mollify

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- a bounded integrable function is an a.e. limit of smooth functions with the same bound -/
lemma smooth_approx {k : E → ℝ} (hk : Integrable k) {K : ℝ} (hK : ∀ x, |k x| ≤ K) :
    ∃ kj : ℕ → E → ℝ, (∀ j, ContDiff ℝ 1 (kj j)) ∧ (∀ j x, |kj j x| ≤ K) ∧
      ∀ᵐ x ∂(volume : Measure E), Tendsto (fun j => kj j x) atTop (𝓝 (k x)) := by
  let φ : ℕ → ContDiffBump (0 : E) := fun j =>
    ⟨1 / ((j : ℝ) + 2), 2 / ((j : ℝ) + 2), by positivity, by
      apply div_lt_div_of_pos_right (by norm_num) (by positivity)⟩
  refine ⟨fun j => (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] k, fun j => ?_,
    fun j x => ?_, ?_⟩
  · exact (φ j).hasCompactSupport_normed.contDiff_convolution_left _ (φ j).contDiff_normed
      hk.locallyIntegrable
  · show |((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] k) x| ≤ K
    rw [convolution_def]
    have h1 : ∀ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) ((φ j).normed volume t) (k (x - t))‖ ≤
        K * (φ j).normed volume t := fun t => by
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg ((φ j).nonneg_normed t)]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hK _) ((φ j).nonneg_normed t)
    have h2 := norm_integral_le_of_norm_le (((φ j).integrable_normed).const_mul K)
      (ae_of_all _ h1)
    rw [integral_const_mul, (φ j).integral_normed, mul_one, Real.norm_eq_abs] at h2
    exact h2
  · refine ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (K := 2) ?_ ?_
      hk.locallyIntegrable
    · show Tendsto (fun j : ℕ => 2 / ((j : ℝ) + 2)) atTop (𝓝 0)
      exact tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    · refine Eventually.of_forall fun j => ?_
      show 2 / ((j : ℝ) + 2) ≤ 2 * (1 / ((j : ℝ) + 2))
      rw [mul_one_div]

end Mollify



open ContextualAuctions.RevEquiv



/-- a limit of test-field integrals is bounded by the total variation -/
lemma approx_le_totVar {m : ℕ} (u : (Fin m → ℝ) → ℝ) (Ω : Set (Fin m → ℝ)) (D : (Fin m → ℝ) → ℝ)
    (φ : ℕ → (Fin m → ℝ) → (Fin m → ℝ))
    (hφ : ∀ j, ContDiff ℝ 1 (φ j) ∧ HasCompactSupport (φ j) ∧ tsupport (φ j) ⊆ Ω ∧
      ∀ z, Real.sqrt (∑ i, (φ j z i) ^ 2) ≤ 1)
    (hlim : Tendsto (fun j => ∫ z in Ω, u z * divergence (φ j) z) atTop
      (𝓝 (∫ z in Ω, u z * D z))) :
    ((∫ z in Ω, u z * D z : ℝ) : EReal) ≤ totVar u Ω := by
  have hle : ∀ j, ((∫ z in Ω, u z * divergence (φ j) z : ℝ) : EReal) ≤ totVar u Ω := fun j =>
    le_sSup ⟨φ j, (hφ j).1, (hφ j).2.1, (hφ j).2.2.1, (hφ j).2.2.2, rfl⟩
  exact le_of_tendsto' ((continuous_coe_real_ereal.tendsto _).comp hlim) hle

lemma fderiv_comp_apply_eq {m : ℕ} (ψ : (Fin m → ℝ) → (Fin m → ℝ)) (hψ : Differentiable ℝ ψ)
    (z v : Fin m → ℝ) (i : Fin m) :
    (fderiv ℝ ψ z v) i = fderiv ℝ (fun z => ψ z i) z v := by
  have h := (hasFDerivAt_apply i (ψ z)).comp z (hψ z).hasFDerivAt
  rw [show (fun z => ψ z i) = (fun f : Fin m → ℝ => f i) ∘ ψ from rfl, h.fderiv]
  rfl

lemma divergence_eq {m : ℕ} (ψ : (Fin m → ℝ) → (Fin m → ℝ)) (hψ : Differentiable ℝ ψ)
    (z : Fin m → ℝ) :
    divergence ψ z = ∑ i, fderiv ℝ (fun z => ψ z i) z (Pi.single i 1) := by
  unfold divergence
  exact Finset.sum_congr rfl fun i _ => fderiv_comp_apply_eq ψ hψ z _ i

/-- integration by parts against a function of the first coordinate -/
lemma ibp_first {m : ℕ} (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (ψ : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    ∫ z, f (z 0) * divergence ψ z = - ∫ z, deriv f (z 0) * ψ z 0 := by
  have hψd : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hF : Continuous (fun z : Fin (m + 1) → ℝ => f (z 0)) :=
    hf.continuous.comp (continuous_apply 0)
  have hF' : Continuous (fun z : Fin (m + 1) → ℝ => deriv f (z 0)) :=
    (hf.continuous_deriv le_rfl).comp (continuous_apply 0)
  have hFd : ∀ z : Fin (m + 1) → ℝ, HasFDerivAt (fun z : Fin (m + 1) → ℝ => f (z 0))
      (deriv f (z 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ)
        (0 : Fin (m + 1))) z := fun z => by
    have h1 : HasDerivAt f (deriv f (z 0)) (z 0) := (hf.differentiable one_ne_zero (z 0)).hasDerivAt
    have h2 : HasFDerivAt (fun y : Fin (m + 1) → ℝ => y 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) 0) z :=
      hasFDerivAt_apply 0 z
    exact h1.comp_hasFDerivAt z h2
  have hci : ∀ i, ContDiff ℝ 1 (fun z => ψ z i) := fun i => (contDiff_apply ℝ ℝ i).comp hψ
  have hcsi : ∀ i, HasCompactSupport (fun z => ψ z i) := fun i =>
    hc.comp_left (g := fun y : Fin (m + 1) → ℝ => y i) rfl
  have hgi : ∀ i (v : Fin (m + 1) → ℝ), Continuous (fun z => fderiv ℝ (fun z => ψ z i) z v) :=
    fun i v => ((hci i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hgsi : ∀ i (v : Fin (m + 1) → ℝ),
      HasCompactSupport (fun z => fderiv ℝ (fun z => ψ z i) z v) := fun i v =>
    ((hcsi i).fderiv (𝕜 := ℝ)).comp_left (g := fun L : (Fin (m + 1) → ℝ) →L[ℝ] ℝ => L v) rfl
  have hterm : ∀ i, ∫ z, f (z 0) * fderiv ℝ (fun z => ψ z i) z (Pi.single i 1) =
      - ∫ z, (deriv f (z 0) * (Pi.single i (1 : ℝ) : Fin (m + 1) → ℝ) 0) * ψ z i := by
    intro i
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure (Fin (m + 1) → ℝ)))
      (f := fun z : Fin (m + 1) → ℝ => f (z 0)) (g := fun z => ψ z i) (v := Pi.single i 1) ?_ ?_ ?_
      (fun z _ => (hFd z).differentiableAt) (fun z _ => ((hci i).differentiable one_ne_zero) z)
    · rw [h]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [(hFd z).fderiv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
        smul_eq_mul]
    · have e : (fun z => fderiv ℝ (fun z : Fin (m + 1) → ℝ => f (z 0)) z (Pi.single i 1) * ψ z i) =
          fun z => (deriv f (z 0) * (Pi.single i (1 : ℝ) : Fin (m + 1) → ℝ) 0) * ψ z i := by
        funext z
        simp only [(hFd z).fderiv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
          smul_eq_mul]
      rw [e]
      exact ((hF'.mul continuous_const).mul ((hci i).continuous)).integrable_of_hasCompactSupport
        ((hcsi i).mul_left)
    · exact (hF.mul (hgi i _)).integrable_of_hasCompactSupport ((hgsi i _).mul_left)
    · exact (hF.mul (hci i).continuous).integrable_of_hasCompactSupport ((hcsi i).mul_left)
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
      Integrable (fun z => f (z 0) * fderiv ℝ (fun z => ψ z i) z (Pi.single i 1)) := fun i _ =>
    (hF.mul (hgi i _)).integrable_of_hasCompactSupport ((hgsi i _).mul_left)
  simp_rw [divergence_eq ψ hψd, Finset.mul_sum]
  rw [integral_finset_sum _ hint]
  simp_rw [hterm]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    simp [Pi.single_apply, Ne.symm hi]
  · intro h; exact absurd (Finset.mem_univ 0) h


lemma field_comp_le {m : ℕ} (ψ : (Fin m → ℝ) → (Fin m → ℝ)) (hn : ∀ z, Real.sqrt (∑ i, (ψ z i) ^ 2) ≤ 1)
    (z : Fin m → ℝ) (i : Fin m) : |ψ z i| ≤ 1 := by
  have h0 : 0 ≤ ∑ j, (ψ z j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h1 : ∑ j, (ψ z j) ^ 2 ≤ 1 := by
    rw [← Real.sq_sqrt h0]; exact pow_le_one₀ (Real.sqrt_nonneg _) (hn z)
  have h2 : (ψ z i) ^ 2 ≤ 1 :=
    (Finset.single_le_sum (fun j _ => sq_nonneg (ψ z j)) (Finset.mem_univ i)).trans h1
  exact (sq_le_one_iff_abs_le_one _).mp h2

/-- the total-variation bound for a function of the first coordinate on a box in `ℝ³` -/
lemma tv_first_le (lo hi : Fin 3 → ℝ) (hlh : ∀ i, lo i ≤ hi i) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hf' : ∀ t, 0 ≤ deriv f t)
    (ψ : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Set.pi Set.univ (fun i => Set.Ioo (lo i) (hi i)))
    (hn : ∀ z, Real.sqrt (∑ i, (ψ z i) ^ 2) ≤ 1) :
    ∫ z in Set.pi Set.univ (fun i => Set.Ioo (lo i) (hi i)), f (z 0) * divergence ψ z ≤
      (∫ t in Set.Ioo (lo 0) (hi 0), deriv f t) * ((hi 1 - lo 1) * (hi 2 - lo 2)) := by
  set Ω := Set.pi Set.univ (fun i => Set.Ioo (lo i) (hi i)) with hΩ
  have hdiv0 : ∀ z ∉ Ω, divergence ψ z = 0 := fun z hz => by
    unfold divergence
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hz (hs h))]
    simp
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hdiv0 z hz, mul_zero])]
  rw [ibp_first (m := 2) f hf ψ hψ hc]
  let g : Fin 3 → ℝ → ℝ := fun i => (Set.Ioo (lo i) (hi i)).indicator (if i = 0 then deriv f else 1)
  have hg0 : ∀ i t, 0 ≤ g i t := fun i t => by
    simp only [g]
    by_cases hi : i = 0
    · subst hi; exact Set.indicator_nonneg (fun t _ => by simpa using hf' t) t
    · exact Set.indicator_nonneg (fun t _ => by simp [hi]) t
  have hF' : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hgi : ∀ i, Integrable (g i) := fun i => by
    simp only [g]
    rw [integrable_indicator_iff measurableSet_Ioo]
    by_cases hi : i = 0
    · subst hi; simp only [if_true]
      exact (hF'.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    · simp only [hi, if_false]
      exact integrableOn_const (by simp [Real.volume_Ioo])
  have hpt : ∀ z : Fin 3 → ℝ, -(deriv f (z 0) * ψ z 0) ≤ ∏ i, g i (z i) := fun z => by
    by_cases hz : z ∈ Ω
    · have hm : ∀ i, z i ∈ Set.Ioo (lo i) (hi i) := fun i => hz i (Set.mem_univ i)
      simp only [Fin.prod_univ_three, g, Set.indicator_of_mem (hm _)]
      simp only [Fin.isValue, if_true, show (1 : Fin 3) ≠ 0 from by decide,
        show (2 : Fin 3) ≠ 0 from by decide, if_false, Pi.one_apply, mul_one]
      have h1 := field_comp_le ψ hn z 0
      have h2 := hf' (z 0)
      nlinarith [neg_abs_le (ψ z 0)]
    · have : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hs h))
      rw [this]
      simp only [Pi.zero_apply, mul_zero, neg_zero]
      exact Finset.prod_nonneg fun i _ => hg0 i _
  have hpsi0 : Continuous (fun z : Fin 3 → ℝ => ψ z 0) := (continuous_apply 0).comp hψ.continuous
  have hcs0 : HasCompactSupport (fun z : Fin 3 → ℝ => ψ z 0) :=
    hc.comp_left (g := fun y : Fin 3 → ℝ => y 0) rfl
  have hL : Integrable (fun z : Fin 3 → ℝ => -(deriv f (z 0) * ψ z 0)) :=
    ((hF'.comp (continuous_apply 0)).mul hpsi0).integrable_of_hasCompactSupport hcs0.mul_left |>.neg
  have hR : Integrable (fun z : Fin 3 → ℝ => ∏ i, g i (z i)) := by
    rw [volume_pi]; exact Integrable.fintype_prod hgi
  rw [← integral_neg]
  refine (integral_mono hL hR hpt).trans (le_of_eq ?_)
  rw [volume_pi, integral_fintype_prod_eq_prod, Fin.prod_univ_three]
  simp only [g, integral_indicator measurableSet_Ioo, if_true,
    show (1 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 0 from by decide, if_false,
    Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (hlh _))]
  ring


end TVTools

section SpendBounds

open ProbabilityTheory

lemma sig0_upper {Φ : ℝ → ℝ} {r : ℝ} (hΦc : Continuous Φ) (hm : Monotone Φ) (h0 : ∀ x, 0 ≤ Φ x)
    (h1 : ∀ x, Φ x ≤ 1) {δ : ℝ} (hδ : 1 - δ ≤ Φ r) {x : ℝ} (hx : r ≤ x) (hΦ : Φ x ≠ 0) :
    sig0 Φ r x ≤ r + δ * (x - r) := by
  have hpos : 0 < Φ x := lt_of_le_of_ne (h0 x) (Ne.symm hΦ)
  have hk := key1 (r := r) hΦc hm x r
  have hAr : Aint Φ r r = 0 := by simp [Aint]
  rw [hAr, sub_zero] at hk
  have e : sig0 Φ r x = x - Aint Φ r x / Φ x := by
    simp [sig0, not_lt.mpr hx, hΦ]
  rw [e]
  have h2 : (x - r) * (1 - δ) ≤ Aint Φ r x / Φ x := by
    rw [le_div_iff₀ hpos]
    have hxr : 0 ≤ x - r := by linarith
    have := h1 x
    calc (x - r) * (1 - δ) * Φ x ≤ (x - r) * Φ r * 1 := by
          rcases le_or_gt (1 - δ) 0 with hneg | hpos'
          · have : (x - r) * (1 - δ) * Φ x ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hxr hneg) (h0 x)
            nlinarith [h0 r]
          · have a1 : (x - r) * (1 - δ) ≤ (x - r) * Φ r := mul_le_mul_of_nonneg_left hδ hxr
            exact mul_le_mul a1 (h1 x) (h0 x) (mul_nonneg hxr (h0 r))
      _ ≤ Aint Φ r x := by linarith
  linarith

variable (H : Measure ℝ) [IsProbabilityMeasure H] (k : ℕ)

lemma Win_le_one (r b : ℝ) : Win H k r b ≤ 1 := by
  unfold Win
  split_ifs
  · exact pow_le_one₀ ENNReal.toReal_nonneg (by
      rw [← measureReal_def]; exact measureReal_le_one)
  · norm_num

lemma Win_ge (r b : ℝ) (hb : r ≤ b) : (H (Set.Iio r)).toReal ^ k ≤ Win H k r b := by
  unfold Win
  rw [if_pos hb]
  gcongr
  · exact measure_ne_top _ _
  · intro y hy
    simp only [Set.mem_Iio] at hy
    simp only [Set.mem_setOf_eq, sig0, if_pos hy]
    linarith

/-- the expected first-price payment per context is close to the reserve -/
lemma spend_pt_bounds [NullSingletonClass H] {r : ℝ} (hr : 0 < r) {δ : ℝ} (hδ1 : δ < 1)
    (hlo : 1 - δ ≤ (H (Set.Iio r)).toReal ^ k) {x : ℝ} (hx : r ≤ x) :
    r * (1 - δ) ≤ sig0 (Phi H k) r x * Win H k r (sig0 (Phi H k) r x) ∧
      sig0 (Phi H k) r x * Win H k r (sig0 (Phi H k) r x) ≤ r + δ * (x - r) := by
  have hm := Phi_mono H k
  have h0 := Phi_nonneg H k
  have h1 : ∀ x, Phi H k x ≤ 1 := fun x => pow_le_one₀ (cdf_nonneg H x) (cdf_le_one H x)
  have hPr : 1 - δ ≤ Phi H k r := by
    refine hlo.trans ?_
    unfold Phi
    gcongr
    rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.Iio_subset_Iic_self)
  have hΦx : Phi H k x ≠ 0 := by
    have := hm hx; intro h; linarith
  have hs := sig0_ge_r hm h0 hx hΦx
  have hW1 := Win_le_one H k r (sig0 (Phi H k) r x)
  have hW0 := Win_ge H k r _ hs.1
  have hup := sig0_upper (Phi_cont H k) hm h0 h1 hPr hx hΦx
  constructor
  · calc r * (1 - δ) ≤ r * (H (Set.Iio r)).toReal ^ k := mul_le_mul_of_nonneg_left hlo hr.le
      _ ≤ sig0 (Phi H k) r x * Win H k r (sig0 (Phi H k) r x) :=
          mul_le_mul hs.1 hW0 (pow_nonneg ENNReal.toReal_nonneg _) (by linarith)
  · calc sig0 (Phi H k) r x * Win H k r (sig0 (Phi H k) r x) ≤ sig0 (Phi H k) r x * 1 :=
          mul_le_mul_of_nonneg_left hW1 (by linarith)
      _ ≤ r + δ * (x - r) := by linarith

end SpendBounds

end CA63

-- ===== part P6 =====
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open ContextualAuctions.RevEquiv

namespace CA63


section Profiles

/-- smooth ramp from 0 (at `a`) to 1 (at `b`) -/
noncomputable def ramp (a b x : ℝ) : ℝ := Real.smoothTransition ((x - a) / (b - a))

variable {a b : ℝ}

lemma ramp_contDiff (a b : ℝ) {n : ℕ∞} : ContDiff ℝ n (ramp a b) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

lemma ramp_nonneg (x : ℝ) : 0 ≤ ramp a b x := Real.smoothTransition.nonneg _
lemma ramp_le_one (x : ℝ) : ramp a b x ≤ 1 := Real.smoothTransition.le_one _

lemma ramp_zero (hab : a < b) {x : ℝ} (hx : x ≤ a) : ramp a b x = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

lemma ramp_one (hab : a < b) {x : ℝ} (hx : b ≤ x) : ramp a b x = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by linarith)]; linarith)

lemma ramp_mono (hab : a < b) : Monotone (ramp a b) := fun x y hxy =>
  Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) (by linarith))

lemma ramp_hasDerivAt (x : ℝ) : HasDerivAt (ramp a b) (deriv (ramp a b) x) x :=
  ((ramp_contDiff a b (n := 1)).differentiable one_ne_zero x).hasDerivAt

lemma ramp_deriv_nonneg (hab : a < b) (x : ℝ) : 0 ≤ deriv (ramp a b) x :=
  (ramp_mono hab).deriv_nonneg

lemma ramp_deriv_zero (hab : a < b) {x : ℝ} (hx : x ∉ Ioo a b) : deriv (ramp a b) x = 0 := by
  rcases le_or_gt x a with h | h
  · rcases h.lt_or_eq with h | h
    · have : ramp a b =ᶠ[𝓝 x] fun _ => 0 :=
        (eventually_lt_nhds h).mono fun y hy => ramp_zero hab hy.le
      rw [this.deriv_eq]; simp
    · -- at the left end point: local minimum of a monotone C¹ function with value 0
      subst h
      have hmin : IsLocalMin (ramp x b) x := Filter.Eventually.of_forall fun y => by
        rw [ramp_zero hab le_rfl]; exact ramp_nonneg y
      exact hmin.deriv_eq_zero
  · have hb : b ≤ x := by
      by_contra hc; exact hx ⟨h, lt_of_not_ge hc⟩
    have hmax : IsLocalMax (ramp a b) x := Filter.Eventually.of_forall fun y => by
      rw [ramp_one hab hb]; exact ramp_le_one y
    exact hmax.deriv_eq_zero

lemma ramp_deriv_contDiff (a b : ℝ) {n : ℕ} : ContDiff ℝ n (deriv (ramp a b)) :=
  (ramp_contDiff a b (n := ((n + 1 : ℕ) : ℕ∞))).deriv'

lemma ramp_deriv_tsupport (hab : a < b) : tsupport (deriv (ramp a b)) ⊆ Icc a b := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hc
  exact hx (ramp_deriv_zero hab fun h => hc (Ioo_subset_Icc_self h))

lemma ramp_deriv_integral (hab : a < b) {lo hi : ℝ} (hlo : lo ≤ a) (hhi : b ≤ hi) :
    ∫ t in Ioo lo hi, deriv (ramp a b) t = 1 := by
  have hc : Continuous (deriv (ramp a b)) := (ramp_deriv_contDiff a b (n := 0)).continuous
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => ramp_hasDerivAt x)
    (hc.intervalIntegrable _ _)]
  rw [ramp_one hab hhi, ramp_zero hab hlo]; ring

/-- cutoff equal to one on most of `(lo, hi)` with closed support inside it -/
noncomputable def cutE (lo hi : ℝ) (j : ℕ) : ℝ := (hi - lo) / (4 * ((j : ℝ) + 1))

noncomputable def cut (lo hi : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  ramp (lo + cutE lo hi j) (lo + 2 * cutE lo hi j) t *
    (1 - ramp (hi - 2 * cutE lo hi j) (hi - cutE lo hi j) t)

variable {lo hi : ℝ}

lemma cutE_pos (h : lo < hi) (j : ℕ) : 0 < cutE lo hi j := by
  unfold cutE; apply div_pos (by linarith); positivity

lemma cutE_le (h : lo < hi) (j : ℕ) : cutE lo hi j ≤ (hi - lo) / 4 := by
  unfold cutE
  apply div_le_div_of_nonneg_left (by linarith) (by norm_num)
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

lemma cut_contDiff (lo hi : ℝ) (j : ℕ) {n : ℕ∞} : ContDiff ℝ n (cut lo hi j) :=
  (ramp_contDiff _ _).mul (contDiff_const.sub (ramp_contDiff _ _))

lemma cut_nonneg (j : ℕ) (t : ℝ) : 0 ≤ cut lo hi j t :=
  mul_nonneg (ramp_nonneg t) (by
    have := ramp_le_one (a := hi - 2 * cutE lo hi j) (b := hi - cutE lo hi j) t
    linarith)

lemma cut_le_one (j : ℕ) (t : ℝ) : cut lo hi j t ≤ 1 := by
  unfold cut
  have h1 := ramp_le_one (a := lo + cutE lo hi j) (b := lo + 2 * cutE lo hi j) t
  have h2 := ramp_nonneg (a := lo + cutE lo hi j) (b := lo + 2 * cutE lo hi j) t
  have h3 := ramp_le_one (a := hi - 2 * cutE lo hi j) (b := hi - cutE lo hi j) t
  have h4 := ramp_nonneg (a := hi - 2 * cutE lo hi j) (b := hi - cutE lo hi j) t
  nlinarith

lemma cut_zero (h : lo < hi) (j : ℕ) {t : ℝ} (ht : t ∉ Icc (lo + cutE lo hi j) (hi - cutE lo hi j)) :
    cut lo hi j t = 0 := by
  have he := cutE_pos h j
  unfold cut
  rcases le_or_gt t (lo + cutE lo hi j) with h1 | h1
  · rw [ramp_zero (by linarith) h1, zero_mul]
  · have h2 : hi - cutE lo hi j ≤ t := by
      by_contra hc; exact ht ⟨h1.le, (lt_of_not_ge hc).le⟩
    rw [ramp_one (by linarith) h2]; ring

lemma cut_tsupport (h : lo < hi) (j : ℕ) :
    tsupport (cut lo hi j) ⊆ Icc (lo + cutE lo hi j) (hi - cutE lo hi j) := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hc; exact hx (cut_zero h j hc)

lemma cut_tsupport_Ioo (h : lo < hi) (j : ℕ) : tsupport (cut lo hi j) ⊆ Ioo lo hi := by
  have he := cutE_pos h j
  exact (cut_tsupport h j).trans (Icc_subset_Ioo (by linarith) (by linarith))

lemma cut_tendsto (h : lo < hi) {t : ℝ} (ht : t ∈ Ioo lo hi) :
    Tendsto (fun j => cut lo hi j t) atTop (𝓝 1) := by
  have hE : Tendsto (fun j : ℕ => cutE lo hi j) atTop (𝓝 0) := by
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul ((hi - lo) / 4)
    rw [mul_zero] at h1
    refine h1.congr fun j => ?_
    unfold cutE
    have : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    field_simp
  have hev : ∀ᶠ j : ℕ in atTop, 2 * cutE lo hi j < min (t - lo) (hi - t) := by
    have hpos : 0 < min (t - lo) (hi - t) := lt_min (by linarith [ht.1]) (by linarith [ht.2])
    exact (hE.const_mul 2).eventually (gt_mem_nhds (show (2 : ℝ) * 0 < min (t - lo) (hi - t) by
      linarith))
  refine tendsto_const_nhds.congr' (hev.mono fun j hj => ?_)
  have hm1 := min_le_left (t - lo) (hi - t)
  have hm2 := min_le_right (t - lo) (hi - t)
  have he := cutE_pos h j
  show 1 = cut lo hi j t
  unfold cut
  rw [ramp_one (by linarith) (by linarith), ramp_zero (by linarith) (by linarith)]; ring

end Profiles


section Angle

variable (a0 a1 a2 a3 : ℝ)

noncomputable def vth (x : ℝ) : ℝ := (Real.pi / 2) * (1 - ramp a0 a1 x + ramp a2 a3 x)
noncomputable def eta (x : ℝ) : ℝ := Real.cos (vth a0 a1 a2 a3 x)
noncomputable def lowD (x : ℝ) : ℝ :=
  Real.sin (vth a0 a1 a2 a3 x) * (Real.pi / 2) * deriv (ramp a0 a1) x
noncomputable def hiD (x : ℝ) : ℝ :=
  Real.sin (vth a0 a1 a2 a3 x) * (Real.pi / 2) * deriv (ramp a2 a3) x

variable {a0 a1 a2 a3}

lemma vth_contDiff {n : ℕ∞} : ContDiff ℝ n (vth a0 a1 a2 a3) :=
  contDiff_const.mul ((contDiff_const.sub (ramp_contDiff a0 a1)).add (ramp_contDiff a2 a3))

lemma eta_contDiff {n : ℕ∞} : ContDiff ℝ n (eta a0 a1 a2 a3) :=
  Real.contDiff_cos.comp vth_contDiff

lemma hiD_contDiff {n : ℕ} : ContDiff ℝ n (hiD a0 a1 a2 a3) :=
  ((Real.contDiff_sin.comp vth_contDiff).mul contDiff_const).mul (ramp_deriv_contDiff a2 a3)

lemma lowD_contDiff {n : ℕ} : ContDiff ℝ n (lowD a0 a1 a2 a3) :=
  ((Real.contDiff_sin.comp vth_contDiff).mul contDiff_const).mul (ramp_deriv_contDiff a0 a1)

lemma eta_hasDerivAt (x : ℝ) :
    HasDerivAt (eta a0 a1 a2 a3) (lowD a0 a1 a2 a3 x - hiD a0 a1 a2 a3 x) x := by
  have hv : HasDerivAt (vth a0 a1 a2 a3)
      ((Real.pi / 2) * (0 - deriv (ramp a0 a1) x + deriv (ramp a2 a3) x)) x :=
    (((hasDerivAt_const x (1 : ℝ)).sub (ramp_hasDerivAt x)).add (ramp_hasDerivAt x)).const_mul _
  have := hv.cos
  unfold eta lowD hiD
  convert this using 1
  ring

lemma eta_deriv : deriv (eta a0 a1 a2 a3) = fun x => lowD a0 a1 a2 a3 x - hiD a0 a1 a2 a3 x :=
  funext fun x => (eta_hasDerivAt x).deriv

variable (h01 : a0 < a1) (h12 : a1 ≤ a2) (h23 : a2 < a3)
include h01 h12 h23

lemma vth_mem (x : ℝ) : vth a0 a1 a2 a3 x ∈ Icc 0 (Real.pi / 2) := by
  unfold vth
  have hp := Real.pi_pos
  have l0 := ramp_nonneg (a := a0) (b := a1) x
  have l1 := ramp_le_one (a := a0) (b := a1) x
  have r0 := ramp_nonneg (a := a2) (b := a3) x
  have r1 := ramp_le_one (a := a2) (b := a3) x
  rcases le_or_gt x a2 with hx | hx
  · rw [ramp_zero h23 hx]
    constructor <;> nlinarith
  · rw [ramp_one h01 (by linarith)]
    constructor <;> nlinarith

lemma eta_nonneg (x : ℝ) : 0 ≤ eta a0 a1 a2 a3 x := by
  have h := vth_mem h01 h12 h23 x
  exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [h.1, Real.pi_pos], h.2⟩

lemma sin_vth_nonneg (x : ℝ) : 0 ≤ Real.sin (vth a0 a1 a2 a3 x) := by
  have h := vth_mem h01 h12 h23 x
  exact Real.sin_nonneg_of_nonneg_of_le_pi h.1 (by linarith [h.2, Real.pi_pos])

lemma hiD_nonneg (x : ℝ) : 0 ≤ hiD a0 a1 a2 a3 x :=
  mul_nonneg (mul_nonneg (sin_vth_nonneg h01 h12 h23 x) (by positivity)) (ramp_deriv_nonneg h23 x)

lemma lowD_nonneg (x : ℝ) : 0 ≤ lowD a0 a1 a2 a3 x :=
  mul_nonneg (mul_nonneg (sin_vth_nonneg h01 h12 h23 x) (by positivity)) (ramp_deriv_nonneg h01 x)

lemma eta_one {x : ℝ} (hx1 : a1 ≤ x) (hx2 : x ≤ a2) : eta a0 a1 a2 a3 x = 1 := by
  unfold eta vth
  rw [ramp_one h01 hx1, ramp_zero h23 hx2]; simp

lemma eta_zero {x : ℝ} (hx : x ∉ Ioo a0 a3) : eta a0 a1 a2 a3 x = 0 := by
  unfold eta vth
  rcases le_or_gt x a0 with h | h
  · rw [ramp_zero h01 h, ramp_zero h23 (by linarith)]; simp
  · have : a3 ≤ x := by by_contra hc; exact hx ⟨h, lt_of_not_ge hc⟩
    rw [ramp_one h01 (by linarith), ramp_one h23 this]; simp

lemma eta_tsupport : tsupport (eta a0 a1 a2 a3) ⊆ Icc a0 a3 := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hc; exact hx (eta_zero h01 h12 h23 fun h => hc (Ioo_subset_Icc_self h))

lemma hiD_tsupport : tsupport (hiD a0 a1 a2 a3) ⊆ Icc a2 a3 := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hc
  apply hx
  unfold hiD
  rw [ramp_deriv_zero h23 fun h => hc (Ioo_subset_Icc_self h), mul_zero]

lemma lowD_tsupport : tsupport (lowD a0 a1 a2 a3) ⊆ Icc a0 a1 := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hc
  apply hx
  unfold lowD
  rw [ramp_deriv_zero h01 fun h => hc (Ioo_subset_Icc_self h), mul_zero]

/-- the field-norm bound: `η² + (h c)² ≤ 1` when `(π/2) ρ' |c| ≤ 1` -/
lemma eta_norm_bound (x c : ℝ) (hc : Real.pi / 2 * deriv (ramp a2 a3) x * |c| ≤ 1) :
    eta a0 a1 a2 a3 x ^ 2 + (hiD a0 a1 a2 a3 x * c) ^ 2 ≤ 1 := by
  unfold eta hiD
  set v := vth a0 a1 a2 a3 x
  have hs := sin_vth_nonneg h01 h12 h23 x
  have hd := ramp_deriv_nonneg h23 x
  have hq : 0 ≤ Real.pi / 2 * deriv (ramp a2 a3) x * |c| := by positivity
  have e : (Real.sin v * (Real.pi / 2) * deriv (ramp a2 a3) x * c) ^ 2 =
      Real.sin v ^ 2 * (Real.pi / 2 * deriv (ramp a2 a3) x * |c|) ^ 2 := by
    rw [show (Real.pi / 2 * deriv (ramp a2 a3) x * |c|) ^ 2 =
      (Real.pi / 2 * deriv (ramp a2 a3) x) ^ 2 * |c| ^ 2 by ring, sq_abs]; ring
  rw [e]
  have h1 : (Real.pi / 2 * deriv (ramp a2 a3) x * |c|) ^ 2 ≤ 1 := pow_le_one₀ hq hc
  have h2 := Real.cos_sq_add_sin_sq v
  nlinarith [sq_nonneg (Real.sin v)]

end Angle




section Field

/-- partial derivative as a one-variable derivative -/
lemma fderiv_single {m : ℕ} (F : (Fin m → ℝ) → ℝ) (z : Fin m → ℝ) (hF : DifferentiableAt ℝ F z)
    (i : Fin m) :
    fderiv ℝ F z (Pi.single i 1) = deriv (fun t => F (Function.update z i t)) (z i) := by
  have h := hF.hasFDerivAt.comp_hasDerivAt_of_eq (z i) (hasDerivAt_update z i (z i))
    (Function.update_eq_self i z).symm
  exact h.deriv.symm

lemma init_contDiff {n : ℕ∞} : ContDiff ℝ n (fun z : Fin 3 → ℝ => Fin.init z) :=
  contDiff_pi.2 fun i => contDiff_apply ℝ ℝ _

/-- the generic test field -/
noncomputable def fld (a c1 c2 hh e : ℝ → ℝ) (kk : (Fin 2 → ℝ) → ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-(a (z 0) * c1 (z 1) * c2 (z 2)), 0, hh (z 0) * kk (Fin.init z) * e (z 2) * c1 (z 1)]

variable {a c1 c2 hh e : ℝ → ℝ} {kk : (Fin 2 → ℝ) → ℝ}

lemma fld_contDiff (ha : ContDiff ℝ 1 a) (hc1 : ContDiff ℝ 1 c1) (hc2 : ContDiff ℝ 1 c2)
    (hh1 : ContDiff ℝ 1 hh) (he : ContDiff ℝ 1 e) (hk : ContDiff ℝ 1 kk) :
    ContDiff ℝ 1 (fld a c1 c2 hh e kk) := by
  have p0 : ContDiff ℝ 1 (fun z : Fin 3 → ℝ => z 0) := contDiff_apply ℝ ℝ 0
  have p1 : ContDiff ℝ 1 (fun z : Fin 3 → ℝ => z 1) := contDiff_apply ℝ ℝ 1
  have p2 : ContDiff ℝ 1 (fun z : Fin 3 → ℝ => z 2) := contDiff_apply ℝ ℝ 2
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact (((ha.comp p0).mul (hc1.comp p1)).mul (hc2.comp p2)).neg
  · exact contDiff_const
  · exact (((hh1.comp p0).mul (hk.comp init_contDiff)).mul (he.comp p2)).mul (hc1.comp p1)

lemma fld_div (ha : ContDiff ℝ 1 a) (hc1 : ContDiff ℝ 1 c1) (hc2 : ContDiff ℝ 1 c2)
    (hh1 : ContDiff ℝ 1 hh) (he : ContDiff ℝ 1 e) (hk : ContDiff ℝ 1 kk) (z : Fin 3 → ℝ) :
    divergence (fld a c1 c2 hh e kk) z =
      -(deriv a (z 0) * c1 (z 1) * c2 (z 2)) +
        hh (z 0) * kk (Fin.init z) * deriv e (z 2) * c1 (z 1) := by
  have hd := (fld_contDiff ha hc1 hc2 hh1 he hk).differentiable one_ne_zero
  have hdi : ∀ i, Differentiable ℝ (fun z => fld a c1 c2 hh e kk z i) := fun i =>
    ((contDiff_apply ℝ ℝ i).comp (fld_contDiff ha hc1 hc2 hh1 he hk)).differentiable one_ne_zero
  rw [divergence_eq _ hd, Fin.sum_univ_three]
  rw [fderiv_single _ z (hdi 0 z) 0, fderiv_single _ z (hdi 1 z) 1, fderiv_single _ z (hdi 2 z) 2]
  have e0 : (fun t => fld a c1 c2 hh e kk (Function.update z 0 t) 0) =
      fun t => -(a t * c1 (z 1) * c2 (z 2)) := by
    funext t; simp [fld, Function.update_apply]
  have e1 : (fun t => fld a c1 c2 hh e kk (Function.update z 1 t) 1) = fun _ => 0 := by
    funext t; simp [fld]
  have e2 : (fun t => fld a c1 c2 hh e kk (Function.update z 2 t) 2) =
      fun t => hh (z 0) * kk (Fin.init z) * e t * c1 (z 1) := by
    funext t
    have hi : Fin.init (Function.update z 2 t) = Fin.init z := Fin.init_update_last (q := z) (z := t)
    simp only [fld, hi]
    simp [Function.update_apply]
  have ha' : HasDerivAt a (deriv a (z 0)) (z 0) :=
    ((ha.differentiable one_ne_zero) (z 0)).hasDerivAt
  have he' : HasDerivAt e (deriv e (z 2)) (z 2) :=
    ((he.differentiable one_ne_zero) (z 2)).hasDerivAt
  have d0 : HasDerivAt (fun t => -(a t * c1 (z 1) * c2 (z 2)))
      (-(deriv a (z 0) * c1 (z 1) * c2 (z 2))) (z 0) :=
    ((ha'.mul_const (c1 (z 1))).mul_const (c2 (z 2))).neg
  have d2 : HasDerivAt (fun t => hh (z 0) * kk (Fin.init z) * e t * c1 (z 1))
      (hh (z 0) * kk (Fin.init z) * deriv e (z 2) * c1 (z 1)) (z 2) :=
    (he'.const_mul (hh (z 0) * kk (Fin.init z))).mul_const (c1 (z 1))
  rw [e0, e1, e2, d0.deriv, d2.deriv]
  simp

lemma fld_zero (p q : Fin 3 → ℝ)
    (ha : ∀ x, x ∉ Icc (p 0) (q 0) → a x = 0) (hh0 : ∀ x, x ∉ Icc (p 0) (q 0) → hh x = 0)
    (hc1 : ∀ x, x ∉ Icc (p 1) (q 1) → c1 x = 0) (hc2 : ∀ x, x ∉ Icc (p 2) (q 2) → c2 x = 0)
    (he : ∀ x, x ∉ Icc (p 2) (q 2) → e x = 0)
    (z : Fin 3 → ℝ) (hz : z ∉ Set.pi univ (fun i => Icc (p i) (q i))) :
    fld a c1 c2 hh e kk z = 0 := by
  have : ¬ (z 0 ∈ Icc (p 0) (q 0) ∧ z 1 ∈ Icc (p 1) (q 1) ∧ z 2 ∈ Icc (p 2) (q 2)) := by
    intro h; apply hz; intro i _; fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  funext i
  fin_cases i
  · simp only [fld]
    by_cases h0 : z 0 ∈ Icc (p 0) (q 0)
    · by_cases h1 : z 1 ∈ Icc (p 1) (q 1)
      · have h2 : z 2 ∉ Icc (p 2) (q 2) := fun h2 => this ⟨h0, h1, h2⟩
        simp [hc2 _ h2]
      · simp [hc1 _ h1]
    · simp [ha _ h0]
  · simp [fld]
  · simp only [fld]
    by_cases h0 : z 0 ∈ Icc (p 0) (q 0)
    · by_cases h1 : z 1 ∈ Icc (p 1) (q 1)
      · have h2 : z 2 ∉ Icc (p 2) (q 2) := fun h2 => this ⟨h0, h1, h2⟩
        simp [he _ h2]
      · simp [hc1 _ h1]
    · simp [hh0 _ h0]

lemma fld_support (p q lo hi : Fin 3 → ℝ) (hp : ∀ i, lo i < p i) (hq : ∀ i, q i < hi i)
    (ha : ∀ x, x ∉ Icc (p 0) (q 0) → a x = 0) (hh0 : ∀ x, x ∉ Icc (p 0) (q 0) → hh x = 0)
    (hc1 : ∀ x, x ∉ Icc (p 1) (q 1) → c1 x = 0) (hc2 : ∀ x, x ∉ Icc (p 2) (q 2) → c2 x = 0)
    (he : ∀ x, x ∉ Icc (p 2) (q 2) → e x = 0) :
    HasCompactSupport (fld a c1 c2 hh e kk) ∧
      tsupport (fld a c1 c2 hh e kk) ⊆ Set.pi univ (fun i => Ioo (lo i) (hi i)) := by
  have hK : tsupport (fld a c1 c2 hh e kk) ⊆ Set.pi univ (fun i => Icc (p i) (q i)) :=
    closure_minimal (fun z hz => by
      by_contra hc; exact hz (fld_zero p q ha hh0 hc1 hc2 he z hc))
      (isClosed_set_pi fun i _ => isClosed_Icc)
  refine ⟨HasCompactSupport.intro' (isCompact_univ_pi fun i => isCompact_Icc)
    (isClosed_set_pi fun i _ => isClosed_Icc)
    (fun z hz => fld_zero p q ha hh0 hc1 hc2 he z hz), hK.trans ?_⟩
  exact Set.pi_mono fun i _ => Icc_subset_Ioo (hp i) (hq i)

lemma fld_norm (hc1 : ∀ x, |c1 x| ≤ 1) (hc2 : ∀ x, |c2 x| ≤ 1)
    (hb : ∀ x w s, a x ^ 2 + (hh x * (kk w * e s)) ^ 2 ≤ 1) (z : Fin 3 → ℝ) :
    Real.sqrt (∑ i, (fld a c1 c2 hh e kk z i) ^ 2) ≤ 1 := by
  rw [Real.sqrt_le_one]
  simp only [Fin.sum_univ_three, fld]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have h := hb (z 0) (Fin.init z) (z 2)
  have q1 : c1 (z 1) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (hc1 _)
  have q2 : c2 (z 2) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (hc2 _)
  have e1 : (-(a (z 0) * c1 (z 1) * c2 (z 2))) ^ 2 = a (z 0) ^ 2 * (c1 (z 1) ^ 2 * c2 (z 2) ^ 2) := by
    ring
  have e2 : (hh (z 0) * kk (Fin.init z) * e (z 2) * c1 (z 1)) ^ 2 =
      (hh (z 0) * (kk (Fin.init z) * e (z 2))) ^ 2 * c1 (z 1) ^ 2 := by ring
  rw [e1, e2]
  have q12 : c1 (z 1) ^ 2 * c2 (z 2) ^ 2 ≤ 1 :=
    mul_le_one₀ q1 (sq_nonneg _) q2
  have s1 := sq_nonneg (a (z 0))
  have s2 := sq_nonneg (hh (z 0) * (kk (Fin.init z) * e (z 2)))
  nlinarith [mul_le_mul_of_nonneg_left q12 s1, mul_le_mul_of_nonneg_left q1 s2]

end Field


section Conv

lemma init_ae {P : (Fin 2 → ℝ) → Prop} (h : ∀ᵐ w ∂(volume : Measure (Fin 2 → ℝ)), P w) :
    ∀ᵐ z ∂(volume : Measure (Fin 3 → ℝ)), P (Fin.init z) := by
  let eqv := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)
  have hq : Measure.QuasiMeasurePreserving (fun z => (eqv z).2)
      (volume : Measure (Fin 3 → ℝ)) (volume : Measure (Fin 2 → ℝ)) :=
    Measure.quasiMeasurePreserving_snd.comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)).quasiMeasurePreserving
  have he : ∀ z : Fin 3 → ℝ, (eqv z).2 = Fin.init z := fun z => by
    funext j
    simp [eqv, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.init, Fin.removeNth]
    fin_cases j <;> rfl
  have := hq.ae h
  simpa only [he] using this

lemma cut_abs_le {lo hi : ℝ} (j : ℕ) (t : ℝ) : |cut lo hi j t| ≤ 1 :=
  abs_le.2 ⟨by linarith [cut_nonneg (lo := lo) (hi := hi) j t], cut_le_one j t⟩

/-- the divergences of the cut-off, mollified test fields converge in `L¹(u)` -/
lemma div_tendsto {a hh e : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (hh1 : ContDiff ℝ 1 hh)
    (he : ContDiff ℝ 1 e) {A1 A2 A3 K : ℝ} (hA1 : ∀ x, |deriv a x| ≤ A1) (hA2 : ∀ x, |hh x| ≤ A2)
    (hA3 : ∀ x, |deriv e x| ≤ A3)
    (kj : ℕ → (Fin 2 → ℝ) → ℝ) (k : (Fin 2 → ℝ) → ℝ) (hkj : ∀ j, ContDiff ℝ 1 (kj j))
    (hK : ∀ j w, |kj j w| ≤ K)
    (hlim : ∀ᵐ w ∂(volume : Measure (Fin 2 → ℝ)), Tendsto (fun j => kj j w) atTop (𝓝 (k w)))
    (lo hi : Fin 3 → ℝ) (hlh : ∀ i, lo i < hi i) (u : (Fin 3 → ℝ) → ℝ)
    (hu : IntegrableOn u (Set.pi univ (fun i => Ioo (lo i) (hi i)))) :
    Tendsto (fun j => ∫ z in Set.pi univ (fun i => Ioo (lo i) (hi i)),
        u z * divergence (fld a (cut (lo 1) (hi 1) j) (cut (lo 2) (hi 2) j) hh e (kj j)) z)
      atTop (𝓝 (∫ z in Set.pi univ (fun i => Ioo (lo i) (hi i)),
        u z * (-(deriv a (z 0)) + hh (z 0) * k (Fin.init z) * deriv e (z 2)))) := by
  set Ω := Set.pi univ (fun i => Ioo (lo i) (hi i)) with hΩ
  have hΩm : MeasurableSet Ω := MeasurableSet.univ_pi fun i => measurableSet_Ioo
  have hcd : ∀ (l h : ℝ) (j : ℕ), ContDiff ℝ 1 (cut l h j) := fun l h j => cut_contDiff l h j
  have hdiv : ∀ j z, divergence (fld a (cut (lo 1) (hi 1) j) (cut (lo 2) (hi 2) j) hh e (kj j)) z =
      -(deriv a (z 0) * cut (lo 1) (hi 1) j (z 1) * cut (lo 2) (hi 2) j (z 2)) +
        hh (z 0) * kj j (Fin.init z) * deriv e (z 2) * cut (lo 1) (hi 1) j (z 1) := fun j z =>
    fld_div ha (hcd _ _ j) (hcd _ _ j) hh1 he (hkj j) z
  simp_rw [hdiv]
  have hda : Continuous (deriv a) := ha.continuous_deriv le_rfl
  have hde : Continuous (deriv e) := he.continuous_deriv le_rfl
  have p0 : Continuous (fun z : Fin 3 → ℝ => z 0) := continuous_apply 0
  have p1 : Continuous (fun z : Fin 3 → ℝ => z 1) := continuous_apply 1
  have p2 : Continuous (fun z : Fin 3 → ℝ => z 2) := continuous_apply 2
  have pin : Continuous (fun z : Fin 3 → ℝ => Fin.init z) := init_contDiff.continuous (n := 0)
  refine tendsto_integral_of_dominated_convergence (fun z => |u z| * (A1 + A2 * K * A3))
    (fun j => ?_) ?_ (fun j => ?_) ?_
  · refine hu.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
    exact (((hda.comp p0).mul ((hcd _ _ j).continuous.comp p1)).mul
      ((hcd _ _ j).continuous.comp p2)).neg.add
      ((((hh1.continuous.comp p0).mul ((hkj j).continuous.comp pin)).mul (hde.comp p2)).mul
        ((hcd _ _ j).continuous.comp p1))
  · exact hu.norm.mul_const _
  · refine ae_of_all _ fun z => ?_
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have c1 := cut_abs_le (lo := lo 1) (hi := hi 1) j (z 1)
    have c2 := cut_abs_le (lo := lo 2) (hi := hi 2) j (z 2)
    have k1 := hK j (Fin.init z)
    have a1 := hA1 (z 0)
    have a2 := hA2 (z 0)
    have a3 := hA3 (z 2)
    have hK0 : 0 ≤ K := (abs_nonneg _).trans k1
    have hA20 : 0 ≤ A2 := (abs_nonneg _).trans a2
    have hA10 : 0 ≤ A1 := (abs_nonneg _).trans a1
    have hA30 : 0 ≤ A3 := (abs_nonneg _).trans a3
    calc |-(deriv a (z 0) * cut (lo 1) (hi 1) j (z 1) * cut (lo 2) (hi 2) j (z 2)) +
          hh (z 0) * kj j (Fin.init z) * deriv e (z 2) * cut (lo 1) (hi 1) j (z 1)|
        ≤ |deriv a (z 0)| * |cut (lo 1) (hi 1) j (z 1)| * |cut (lo 2) (hi 2) j (z 2)| +
          |hh (z 0)| * |kj j (Fin.init z)| * |deriv e (z 2)| * |cut (lo 1) (hi 1) j (z 1)| := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          simp only [abs_neg, abs_mul]
      _ ≤ A1 * 1 * 1 + A2 * K * A3 * 1 := by
          gcongr
          all_goals nlinarith [mul_nonneg hA20 hK0, mul_nonneg (mul_nonneg hA20 hK0) hA30]
      _ = A1 + A2 * K * A3 := by ring
  · have h1 := init_ae hlim
    rw [ae_restrict_iff' hΩm]
    filter_upwards [h1] with z hz hzΩ
    have hz1 : z 1 ∈ Ioo (lo 1) (hi 1) := hzΩ 1 (mem_univ _)
    have hz2 : z 2 ∈ Ioo (lo 2) (hi 2) := hzΩ 2 (mem_univ _)
    have t1 := cut_tendsto (hlh 1) hz1
    have t2 := cut_tendsto (hlh 2) hz2
    have := (((tendsto_const_nhds (x := deriv a (z 0))).mul t1).mul t2).neg.add
      (((tendsto_const_nhds (x := hh (z 0))).mul hz).mul (tendsto_const_nhds (x := deriv e (z 2)))
        |>.mul t1)
    refine (this.const_mul (u z)).congr' (Eventually.of_forall fun j => rfl) |>.trans ?_
    simp

end Conv

end CA63

-- ===== part M7 =====
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open ContextualAuctions.RevEquiv

namespace CA63

section ModelDef

/-! ### P7a: the concrete model (numbers, item law, standing assumptions, `ω`) -/

noncomputable def cU : ℝ := 1 / 100
noncomputable def cBmin : ℝ := 1 / 200
noncomputable def cr0 : ℝ := 1 / 50
noncomputable def cK0 : ℝ := 100
noncomputable def cEps : ℝ := 1 / 100

noncomputable def cAlo : Fin 2 → ℝ := ![cK0, cEps]
noncomputable def cAhi : Fin 2 → ℝ := ![cK0 + 1, 2 * cEps]
noncomputable def cA : Set (Fin 2 → ℝ) := Icc cAlo cAhi

noncomputable def cF : Measure (Fin 2 → ℝ) := (100 : ENNReal) • volume.restrict cA

/-- the model, parametrized by the buyer law -/
noncomputable def mdl (G : Measure ((Fin 2 → ℝ) × ℝ)) : Model where
  d := 2
  n := 2
  U := cU
  Bmin := cBmin
  A := cA
  F := cF
  G := G
  r := fun _ => cr0

lemma cA_mem {α : Fin 2 → ℝ} : α ∈ cA ↔
    (cK0 ≤ α 0 ∧ α 0 ≤ cK0 + 1) ∧ (cEps ≤ α 1 ∧ α 1 ≤ 2 * cEps) := by
  simp only [cA, mem_Icc, Pi.le_def, Fin.forall_fin_two, cAlo, cAhi, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  tauto

lemma cA_le : cAlo ≤ cAhi := by
  rw [Pi.le_def, Fin.forall_fin_two]; norm_num [cAlo, cAhi, cK0, cEps]

lemma cA_vol : volume cA = ENNReal.ofReal (1 / 100) := by
  rw [cA, Real.volume_Icc_pi, Fin.prod_univ_two]
  simp only [cAlo, cAhi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, cK0, cEps]
  rw [← ENNReal.ofReal_mul (by norm_num)]
  norm_num

lemma cF_prob : IsProbabilityMeasure cF := by
  constructor
  rw [cF, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, cA_vol,
    smul_eq_mul]
  rw [show (100 : ENNReal) = ENNReal.ofReal 100 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

lemma cF_ac : cF ≪ volume := by
  intro s hs
  rw [cF, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (show MeasurableSet cA from measurableSet_Icc)]
  · have : volume (s ∩ cA) = 0 := measure_mono_null inter_subset_left hs
    rw [this, mul_zero]

lemma cF_supp : cF cAᶜ = 0 := by
  rw [cF, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (show MeasurableSet cA from measurableSet_Icc)]
  simp

variable (G : Measure ((Fin 2 → ℝ) × ℝ))

lemma mdl_standing [IsProbabilityMeasure G] (hac : G ≪ volume) (hs : G (Theta (mdl G))ᶜ = 0) :
    (mdl G).Standing where
  dim := le_rfl
  buyers := le_rfl
  budget_pos := by show (0 : ℝ) < cBmin; norm_num [cBmin]
  budget_lt := by show cBmin < cU; norm_num [cBmin, cU]
  measurableA := measurableSet_Icc
  positiveA := fun α hα => by
    have h := (cA_mem (α := α)).1 hα
    have h0 : (0 : ℝ) < cK0 := by norm_num [cK0]
    have h1 : (0 : ℝ) < cEps := by norm_num [cEps]
    show ∀ i : Fin 2, 0 < α i
    rw [Fin.forall_fin_two]
    exact ⟨by linarith [h.1.1], by linarith [h.2.1]⟩
  nonemptyA := ⟨cAlo, left_mem_Icc.2 cA_le⟩
  boundedA := Metric.isBounded_Icc _ _
  probF := cF_prob
  densityF := cF_ac
  supportedF := cF_supp
  probG := show IsProbabilityMeasure G from inferInstance
  densityG := hac
  supportedG := hs
  measurableR := measurable_const

lemma mdl_val (θ : (Fin 2 → ℝ) × ℝ) (α : Fin 2 → ℝ) :
    val (mdl G) θ α = θ.1 0 * α 0 + θ.1 1 * α 1 := by
  simp only [val]; exact Fin.sum_univ_two _

lemma mdl_theta {θ : (Fin 2 → ℝ) × ℝ} : θ ∈ Theta (mdl G) ↔
    ((0 < θ.1 0 ∧ θ.1 0 < cU) ∧ (0 < θ.1 1 ∧ θ.1 1 < cU)) ∧ cBmin < θ.2 ∧ θ.2 < cU := by
  show ((∀ i : Fin 2, 0 < θ.1 i ∧ θ.1 i < cU) ∧ cBmin < θ.2 ∧ θ.2 < cU) ↔ _
  rw [Fin.forall_fin_two]

noncomputable def cOmega : ℝ := cU * (cK0 + 1 + 2 * cEps)

lemma mdl_omega : omega (mdl G) = cOmega := by
  unfold omega
  have hW : (0 : ℝ) < cOmega := by norm_num [cOmega, cU, cK0, cEps]
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · refine ⟨_, ⟨(fun _ => cU / 2, (cBmin + cU) / 2), ?_, cAhi, ?_, rfl⟩⟩
    · exact (mdl_theta G).2 (by norm_num [cU, cBmin])
    · exact right_mem_Icc.2 cA_le
  · rintro v ⟨θ, hθ, α, hα, rfl⟩
    replace hθ := (mdl_theta G).1 hθ
    replace hα := (cA_mem (α := α)).1 hα
    rw [mdl_val G θ α]
    have h0 : (0 : ℝ) < cK0 := by norm_num [cK0]
    have h1 : (0 : ℝ) < cEps := by norm_num [cEps]
    unfold cOmega
    nlinarith [hθ.1.1.1, hθ.1.1.2, hθ.1.2.1, hθ.1.2.2, hα.1.1, hα.1.2, hα.2.1, hα.2.2]
  · intro v hv
    set s : ℝ := (1 + max (v / cOmega) 0) / 2 with hs
    have hm0 := le_max_right (v / cOmega) 0
    have hm1 : max (v / cOmega) 0 < 1 := max_lt (by rw [div_lt_one hW]; exact hv) one_pos
    have hs1 : s < 1 := by rw [hs]; linarith
    have hs0 : 1 / 2 ≤ s := by rw [hs]; linarith
    have hvs : v < s * cOmega := by
      have : v / cOmega < s := by rw [hs]; linarith [le_max_left (v / cOmega) 0]
      rwa [div_lt_iff₀ hW] at this
    refine ⟨s * cOmega, ⟨(fun _ => cU * s, (cBmin + cU) / 2), ?_, cAhi, ?_, ?_⟩, hvs⟩
    · refine (mdl_theta G).2 ?_
      have hU : (0 : ℝ) < cU := by norm_num [cU]
      refine ⟨⟨⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩⟩, ?_, ?_⟩ <;>
        norm_num [cU, cBmin] at * <;> nlinarith
    · exact right_mem_Icc.2 cA_le
    · refine Eq.trans ?_ (mdl_val G _ _).symm
      simp only [cAhi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, cOmega]
      ring

end ModelDef


section MuDef

/-! ### P7b: `V0`, the pacing level `m2`, zone end points -/

noncomputable def cV0 : ℝ := 3 * cU ^ 3 * cOmega / cBmin
noncomputable def cm2 : ℝ := cV0 / (cU * (cU - cBmin))
noncomputable def ca0 : ℝ := 1 / 20000
noncomputable def ca1 : ℝ := 1 / 10000
noncomputable def ca2 : ℝ := 1 / 250
noncomputable def ca3 : ℝ := 9 / 1000

variable (G : Measure ((Fin 2 → ℝ) × ℝ))

lemma mdl_V0 : V0 (mdl G) = cV0 := by
  unfold V0
  rw [mdl_omega]
  show ((2 + 1 : ℕ) : ℝ) * cU ^ (2 + 1) * cOmega / cBmin = cV0
  unfold cV0; push_cast; ring

lemma cm2_eq : cm2 * (cU * (cU - cBmin)) = cV0 := by
  unfold cm2; exact div_mul_cancel₀ _ (by norm_num [cU, cBmin])

lemma cm2_pos : 0 < cm2 := by
  norm_num [cm2, cV0, cOmega, cU, cBmin, cK0, cEps]

lemma cm2_le : cm2 ≤ cOmega / cBmin := by
  norm_num [cm2, cV0, cOmega, cU, cBmin, cK0, cEps]

/-- the zone constants in order, all inside `(0, U)` -/
lemma zones : 0 < ca0 ∧ ca0 < ca1 ∧ ca1 < ca2 ∧ ca2 < ca3 ∧ ca3 < cU := by
  norm_num [ca0, ca1, ca2, ca3, cU]

/-- low zone: values stay below the reserve -/
lemma low_val_lt {w : Fin 2 → ℝ} (hw0 : 0 < w 0) (hw0' : w 0 ≤ ca1) (hw1 : 0 < w 1) (hw1' : w 1 < cU)
    {α : Fin 2 → ℝ} (hα : α ∈ cA) : w 0 * α 0 + w 1 * α 1 < cr0 := by
  have h := cA_mem.1 hα
  have hK : (0:ℝ) ≤ cK0 := by norm_num [cK0]
  have hE : (0:ℝ) < cEps := by norm_num [cEps]
  have ha0 : 0 ≤ α 0 := by linarith [h.1.1]
  have ha1 : 0 < α 1 := by linarith [h.2.1]
  have e1 : w 0 * α 0 ≤ ca1 * (cK0 + 1) := by nlinarith [h.1.2]
  have e2 : w 1 * α 1 < cU * (2 * cEps) := by nlinarith [h.2.2]
  have : ca1 * (cK0 + 1) + cU * (2 * cEps) < cr0 := by norm_num [ca1, cK0, cU, cEps, cr0]
  linarith

/-- high zone: paced values at level `m2` stay above the reserve -/
lemma high_paced_ge {w : Fin 2 → ℝ} (hw0 : ca2 ≤ w 0) (hw1 : 0 < w 1)
    {α : Fin 2 → ℝ} (hα : α ∈ cA) : cr0 ≤ (w 0 * α 0 + w 1 * α 1) / (1 + cm2) := by
  have h := cA_mem.1 hα
  have hp : 0 < 1 + cm2 := by linarith [cm2_pos]
  rw [le_div_iff₀ hp]
  have hE : (0:ℝ) < cEps := by norm_num [cEps]
  have h1 : 0 < α 1 := by linarith [h.2.1]
  have e1 : ca2 * cK0 ≤ w 0 * α 0 := by
    have : (0:ℝ) ≤ ca2 := by norm_num [ca2]
    have : (0:ℝ) ≤ cK0 := by norm_num [cK0]
    nlinarith [h.1.1]
  have : cr0 * (1 + cm2) ≤ ca2 * cK0 := by
    norm_num [cm2, cV0, cOmega, cU, cBmin, cK0, cEps, cr0, ca2]
  nlinarith

end MuDef

end CA63

-- ===== part P7 =====
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open ContextualAuctions.RevEquiv

namespace CA63

section P7

/-! ### P7c: pacing function, spend formula, dependence on the `w`-marginal only -/

open Classical in
/-- integrability of the per-context payment (companion of `pay_fubini`) -/
lemma pay_int (M : Model) (μ : Buyer M → ℝ) [IsProbabilityMeasure M.G] [IsProbabilityMeasure M.F]
    (hμ : Measurable μ) (b : Context M → ℝ)
    (hint : Integrable (fun ω : Context M × (Fin (M.n - 1) → Buyer M) =>
      if wins M (beta M μ) b ω then b ω.1 else 0) (P M)) :
    Integrable (fun α => b α * Win (lam M μ α) (M.n - 1) (M.r α) (b α)) M.F := by
  haveI : SigmaFinite (Measure.pi fun _ : Fin (M.n - 1) => M.G) := Measure.pi.sigmaFinite _
  rw [P] at hint
  refine (hint.integral_prod_left).congr (Eventually.of_forall fun α => ?_)
  simp only
  rw [← competitor_integral M μ hμ α (b α) (b α)]
  congr 1; funext θs
  exact if_congr Iff.rfl rfl rfl

/-- the pacing function: `0` for `w₀ ≤ a₁`, `m₂` for `w₀ ≥ a₂` -/
noncomputable def muF (θ : (Fin 2 → ℝ) × ℝ) : ℝ := cm2 * ramp ca1 ca2 (θ.1 0)

lemma muF_meas : Measurable muF :=
  measurable_const.mul ((ramp_contDiff ca1 ca2 (n := 0)).continuous.measurable.comp
    ((measurable_pi_apply 0).comp measurable_fst))

lemma muF_nonneg (θ : (Fin 2 → ℝ) × ℝ) : 0 ≤ muF θ :=
  mul_nonneg cm2_pos.le (ramp_nonneg _)

lemma muF_le (θ : (Fin 2 → ℝ) × ℝ) : muF θ ≤ cm2 := by
  unfold muF
  have := ramp_le_one (a := ca1) (b := ca2) (θ.1 0)
  nlinarith [cm2_pos]

lemma muF_zero {θ : (Fin 2 → ℝ) × ℝ} (h : θ.1 0 ≤ ca1) : muF θ = 0 := by
  unfold muF; rw [ramp_zero zones.2.2.1 h, mul_zero]

lemma muF_top {θ : (Fin 2 → ℝ) × ℝ} (h : ca2 ≤ θ.1 0) : muF θ = cm2 := by
  unfold muF; rw [ramp_one zones.2.2.1 h, mul_one]

variable {G G' : Measure ((Fin 2 → ℝ) × ℝ)}

/-- `λ^μ_α` depends on `G` only through its `w`-marginal -/
lemma lam_marg (h : G.map Prod.fst = G'.map Prod.fst) (α : Fin 2 → ℝ) :
    lam (mdl G) muF α = lam (mdl G') muF α := by
  have hφ : Measurable (fun w : Fin 2 → ℝ => paced (mdl G) muF (w, 0) α) :=
    (paced_meas (mdl G) muF muF_meas α).comp (measurable_id.prodMk measurable_const)
  have k1 : G.map (fun θ => paced (mdl G) muF θ α) =
      (G.map Prod.fst).map (fun w : Fin 2 → ℝ => paced (mdl G) muF (w, 0) α) :=
    (Measure.map_map hφ measurable_fst).symm
  have k2 : G'.map (fun θ => paced (mdl G') muF θ α) =
      (G'.map Prod.fst).map (fun w : Fin 2 → ℝ => paced (mdl G) muF (w, 0) α) :=
    (Measure.map_map hφ measurable_fst).symm
  exact k1.trans ((congrArg (Measure.map _) h).trans k2.symm)

lemma mdl_val_bound {θ : (Fin 2 → ℝ) × ℝ} (h0 : 0 ≤ θ.1 0) (h0' : θ.1 0 ≤ 1)
    (h1 : 0 ≤ θ.1 1) (h1' : θ.1 1 ≤ 1) :
    ∀ᵐ α ∂cF, |val (mdl G) θ α| ≤ 102 := by
  have hs : ∀ᵐ α ∂cF, α ∈ cA := by
    rw [ae_iff]; simpa [Set.compl_def] using cF_supp
  refine hs.mono fun (α : Fin 2 → ℝ) hα => ?_
  have hv : val (mdl G) θ α = θ.1 0 * α 0 + θ.1 1 * α 1 := mdl_val G θ α
  rw [hv]
  have h := cA_mem.1 hα
  have hK : cK0 = 100 := rfl
  have hE : cEps = 1 / 100 := rfl
  have ha0 : 0 ≤ α 0 := by linarith [h.1.1, hK]
  have ha1 : 0 ≤ α 1 := by linarith [h.2.1, hE]
  have e0 : θ.1 0 * α 0 ≤ 101 := by nlinarith [h.1.2]
  have e1 : θ.1 1 * α 1 ≤ 1 := by nlinarith [h.2.2]
  rw [abs_of_nonneg (by positivity)]
  linarith

lemma mdl_val_nonneg {θ : (Fin 2 → ℝ) × ℝ} (h0 : 0 ≤ θ.1 0) (h1 : 0 ≤ θ.1 1) :
    ∀ α ∈ (mdl G).A, 0 ≤ val (mdl G) θ α := by
  rintro (α : Fin 2 → ℝ) hα
  have h := cA_mem.1 hα
  have hv : val (mdl G) θ α = θ.1 0 * α 0 + θ.1 1 * α 1 := mdl_val G θ α
  rw [hv]
  have ha0 : 0 ≤ α 0 := by linarith [h.1.1, show cK0 = 100 from rfl]
  have ha1 : 0 ≤ α 1 := by linarith [h.2.1, show cEps = 1 / 100 from rfl]
  positivity

/-- the spend as an integral over contexts -/
lemma spend_formula [IsProbabilityMeasure G] {θ : (Fin 2 → ℝ) × ℝ} (h0 : 0 ≤ θ.1 0) (h0' : θ.1 0 ≤ 1)
    (h1 : 0 ≤ θ.1 1) (h1' : θ.1 1 ≤ 1) {t : ℝ} (ht : -1 < t) :
    Spend (mdl G) muF θ t =
      ∫ α, sig0 (Phi (lam (mdl G) muF α) 1) cr0 (val (mdl G) θ α / (1 + t)) *
        Win (lam (mdl G) muF α) 1 cr0
          (sig0 (Phi (lam (mdl G) muF α) 1) cr0 (val (mdl G) θ α / (1 + t))) ∂cF ∧
    Integrable (fun α => sig0 (Phi (lam (mdl G) muF α) 1) cr0 (val (mdl G) θ α / (1 + t)) *
        Win (lam (mdl G) muF α) 1 cr0
          (sig0 (Phi (lam (mdl G) muF α) 1) cr0 (val (mdl G) θ α / (1 + t)))) cF := by
  haveI : IsProbabilityMeasure (mdl G).F := cF_prob
  haveI : IsProbabilityMeasure (mdl G).G := ‹IsProbabilityMeasure G›
  have hr : Measurable (mdl G).r := measurable_const
  have hrp : ∀ α, 0 < (mdl G).r α := fun _ => by show (0:ℝ) < cr0; norm_num [cr0]
  have hb := bt_adm (mdl G) muF muF_meas hr hrp θ ht (mdl_val_nonneg h0 h1)
    (mdl_val_bound (G := G) h0 h0' h1 h1')
  have e : ∀ α, bt (mdl G) muF θ t α =
      sig0 (Phi (lam (mdl G) muF α) 1) cr0 (val (mdl G) θ α / (1 + t)) :=
    fun α => bt_eq (mdl G) muF muF_meas θ t α
  refine ⟨?_, ?_⟩
  · unfold Spend
    rw [pay_fubini (mdl G) muF muF_meas _ hb.2.2]
    refine integral_congr_ae (Eventually.of_forall fun α => ?_)
    show bt (mdl G) muF θ t α * _ = _
    rw [e α]; rfl
  · have := pay_int (mdl G) muF muF_meas _ hb.2.2
    exact this.congr (Eventually.of_forall fun α => by simp only [e]; rfl)

/-- the spend depends on `G` only through its `w`-marginal -/
lemma spend_marg [IsProbabilityMeasure G] [IsProbabilityMeasure G']
    (h : G.map Prod.fst = G'.map Prod.fst) {θ : (Fin 2 → ℝ) × ℝ} (h0 : 0 ≤ θ.1 0) (h0' : θ.1 0 ≤ 1)
    (h1 : 0 ≤ θ.1 1) (h1' : θ.1 1 ≤ 1) {t : ℝ} (ht : -1 < t) :
    Spend (mdl G) muF θ t = Spend (mdl G') muF θ t := by
  rw [(spend_formula (G := G) h0 h0' h1 h1' ht).1, (spend_formula (G := G') h0 h0' h1 h1' ht).1]
  congr 1; funext α
  rw [lam_marg h α]
  rfl

end P7

end CA63

-- ===== part P7b =====
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open ContextualAuctions.RevEquiv

namespace CA63

section P7b

/-! ### P7b: buyer laws with a prescribed `w`-marginal -/

noncomputable def cZ : ℝ → ℝ := cut cBmin cU 1
noncomputable def Lf (S : ℝ) : ℝ := ∫ B in cBmin..cU, 1 / (S - B)
noncomputable def J1 (S : ℝ) : ℝ := ∫ B in cBmin..cU, deriv cZ B / (S - B)
noncomputable def cLbar : ℝ := Lf cr0
noncomputable def cc (gam : ℝ) : ℝ := 1 / (cU * (gam * (cU - cBmin) + cLbar))
noncomputable def lowDc : ℝ → ℝ := lowD ca0 ca1 ca2 ca3
noncomputable def hiDc : ℝ → ℝ := hiD ca0 ca1 ca2 ca3
/-- the weight box `(0,U)²` -/
def cW : Set (Fin 2 → ℝ) := Set.pi univ (fun _ => Ioo 0 cU)
def cBI : Set ℝ := Ioo cBmin cU

lemma cW_meas : MeasurableSet cW := MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)
lemma cBI_meas : MeasurableSet cBI := measurableSet_Ioo

lemma cLbar_bounds : 1 / 3 ≤ cLbar ∧ cLbar ≤ 1 / 2 := by
  have hBU : cBmin ≤ cU := by norm_num [cBmin, cU]
  have hc : ContinuousOn (fun B : ℝ => 1 / (cr0 - B)) (Icc cBmin cU) := by
    refine continuousOn_const.div (continuousOn_const.sub continuousOn_id) (fun B hB => ?_)
    have := hB.2; norm_num [cr0, cU] at this ⊢; linarith
  have hii := hc.intervalIntegrable_of_Icc (μ := volume) hBU
  have lo : ∫ B in cBmin..cU, (1 / (cr0 - cBmin)) ≤ cLbar := by
    refine intervalIntegral.integral_mono_on hBU intervalIntegrable_const hii (fun B hB => ?_)
    have h1 := hB.1; have h2 := hB.2
    have hp : 0 < cr0 - B := by norm_num [cr0, cU] at h2 ⊢; linarith
    exact one_div_le_one_div_of_le hp (by linarith)
  have hi : cLbar ≤ ∫ B in cBmin..cU, (1 / (cr0 - cU)) := by
    refine intervalIntegral.integral_mono_on hBU hii intervalIntegrable_const (fun B hB => ?_)
    have h2 := hB.2
    have hp : 0 < cr0 - cU := by norm_num [cr0, cU]
    exact one_div_le_one_div_of_le hp (by linarith)
  rw [intervalIntegral.integral_const, smul_eq_mul] at lo hi
  constructor
  · refine le_trans (le_of_eq ?_) lo; norm_num [cr0, cU, cBmin]
  · refine hi.trans (le_of_eq ?_); norm_num [cr0, cU, cBmin]

lemma cc_pos {gam : ℝ} (hg : 0 ≤ gam) : 0 < cc gam := by
  unfold cc
  have h1 : 0 < cU - cBmin := by norm_num [cU, cBmin]
  have h2 : (0:ℝ) < cU := by norm_num [cU]
  have := cLbar_bounds.1
  have : 0 < gam * (cU - cBmin) + cLbar := by nlinarith
  positivity

lemma lowDc_nonneg (x : ℝ) : 0 ≤ lowDc x :=
  lowD_nonneg zones.2.1 zones.2.2.1.le zones.2.2.2.1 x
lemma hiDc_nonneg (x : ℝ) : 0 ≤ hiDc x :=
  hiD_nonneg zones.2.1 zones.2.2.1.le zones.2.2.2.1 x
lemma lowDc_cont : Continuous lowDc := (lowD_contDiff (n := 0)).continuous
lemma hiDc_cont : Continuous hiDc := (hiD_contDiff (n := 0)).continuous

/-- the (unnormalized-free) density of a buyer law with high-zone profile `h` -/
noncomputable def gden (gam : ℝ) (h : (Fin 2 → ℝ) → ℝ → ℝ) (θ : (Fin 2 → ℝ) × ℝ) : ℝ :=
  (cW ×ˢ cBI).indicator
    (fun θ => cc gam * (gam * lowDc (θ.1 0) + hiDc (θ.1 0) * h θ.1 θ.2)) θ

/-- the common `w`-marginal -/
noncomputable def margM (gam : ℝ) : Measure (Fin 2 → ℝ) :=
  volume.withDensity (cW.indicator fun w =>
    ENNReal.ofReal (cc gam * (gam * lowDc (w 0) * (cU - cBmin) + hiDc (w 0) * cLbar)))

/-- the buyer law with profile `h` -/
noncomputable def Gh (gam : ℝ) (h : (Fin 2 → ℝ) → ℝ → ℝ) : Measure ((Fin 2 → ℝ) × ℝ) :=
  volume.withDensity (fun θ => ENNReal.ofReal (gden gam h θ))

lemma gden_meas (gam : ℝ) {h : (Fin 2 → ℝ) → ℝ → ℝ} (hm : Measurable (Function.uncurry h)) :
    Measurable (gden gam h) := by
  unfold gden
  refine Measurable.indicator ?_ (cW_meas.prod measurableSet_Ioo)
  have hw0 : Measurable (fun θ : (Fin 2 → ℝ) × ℝ => θ.1 0) := (measurable_pi_apply 0).comp measurable_fst
  exact measurable_const.mul ((measurable_const.mul (lowDc_cont.measurable.comp hw0)).add
    ((hiDc_cont.measurable.comp hw0).mul hm))

/-- a profile is admissible: nonnegative, integrable, with `B`-integral `L̄` -/
structure Prof (h : (Fin 2 → ℝ) → ℝ → ℝ) : Prop where
  meas : Measurable (Function.uncurry h)
  nonneg : ∀ w ∈ cW, ∀ B ∈ cBI, 0 ≤ h w B
  int : ∀ w ∈ cW, IntegrableOn (h w) cBI
  mass : ∀ w ∈ cW, ∫ B in cBI, h w B = cLbar

lemma gden_nonneg {gam : ℝ} (hg : 0 ≤ gam) {h : (Fin 2 → ℝ) → ℝ → ℝ} (hp : Prof h)
    (θ : (Fin 2 → ℝ) × ℝ) : 0 ≤ gden gam h θ := by
  unfold gden
  by_cases hθ : θ ∈ cW ×ˢ cBI
  · rw [Set.indicator_of_mem hθ]
    have := hp.nonneg θ.1 hθ.1 θ.2 hθ.2
    have h1 := lowDc_nonneg (θ.1 0)
    have h2 := hiDc_nonneg (θ.1 0)
    exact mul_nonneg (cc_pos hg).le (add_nonneg (mul_nonneg hg h1) (mul_nonneg h2 this))
  · rw [Set.indicator_of_notMem hθ]

lemma inner_lint {gam : ℝ} (hg : 0 ≤ gam) {h : (Fin 2 → ℝ) → ℝ → ℝ} (hp : Prof h)
    (w : Fin 2 → ℝ) :
    ∫⁻ B, ENNReal.ofReal (gden gam h (w, B)) =
      cW.indicator (fun w => ENNReal.ofReal
        (cc gam * (gam * lowDc (w 0) * (cU - cBmin) + hiDc (w 0) * cLbar))) w := by
  by_cases hw : w ∈ cW
  · rw [Set.indicator_of_mem hw]
    have e2 : ∀ B, ENNReal.ofReal (gden gam h (w, B)) = cBI.indicator
        (fun B => ENNReal.ofReal (cc gam * (gam * lowDc (w 0) + hiDc (w 0) * h w B))) B := by
      intro B
      by_cases hB : B ∈ cBI
      · rw [gden, Set.indicator_of_mem (Set.mk_mem_prod hw hB), Set.indicator_of_mem hB]
      · rw [gden, Set.indicator_of_notMem (fun h' => hB h'.2), Set.indicator_of_notMem hB,
          ENNReal.ofReal_zero]
    simp_rw [e2]
    rw [lintegral_indicator cBI_meas]
    have hvol : volume cBI ≠ ⊤ := by simp [cBI, Real.volume_Ioo]
    have hc1 : IntegrableOn (fun _ : ℝ => gam * lowDc (w 0)) cBI := integrableOn_const hvol
    have hc2 : IntegrableOn (fun B => hiDc (w 0) * h w B) cBI := (hp.int w hw).const_mul _
    have hfi : IntegrableOn (fun B => cc gam * (gam * lowDc (w 0) + hiDc (w 0) * h w B)) cBI :=
      (hc1.add hc2).const_mul _
    have hnn : 0 ≤ᵐ[volume.restrict cBI]
        (fun B => cc gam * (gam * lowDc (w 0) + hiDc (w 0) * h w B)) := by
      refine ae_restrict_of_forall_mem cBI_meas fun B hB => ?_
      have := hp.nonneg w hw B hB
      have h1 := lowDc_nonneg (w 0)
      have h2 := hiDc_nonneg (w 0)
      exact mul_nonneg (cc_pos hg).le (add_nonneg (mul_nonneg hg h1) (mul_nonneg h2 this))
    rw [← ofReal_integral_eq_lintegral_ofReal hfi hnn]
    congr 1
    rw [integral_const_mul, integral_add hc1 hc2, integral_const_mul,
      integral_const_mul (hiDc (w 0)), hp.mass w hw, setIntegral_const]
    have hr : volume.real cBI = cU - cBmin := by
      simp only [cBI, measureReal_def, Real.volume_Ioo]
      rw [ENNReal.toReal_ofReal (by norm_num [cU, cBmin])]
    rw [hr, smul_eq_mul]; ring
  · rw [Set.indicator_of_notMem hw]
    have : ∀ B, gden gam h (w, B) = 0 := fun B => by
      rw [gden, Set.indicator_of_notMem (fun h' => hw h'.1)]
    simp [this]

end P7b

end CA63

-- ===== part P7c =====
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open ContextualAuctions.RevEquiv

namespace CA63

section P7c

/-! ### P7c: the marginal of `Gh`, total mass, profile integrals -/

lemma marg_eq {gam : ℝ} (hg : 0 ≤ gam) {h : (Fin 2 → ℝ) → ℝ → ℝ} (hp : Prof h) :
    (Gh gam h).map Prod.fst = margM gam := by
  ext E hE
  have hmeas : Measurable (fun θ : (Fin 2 → ℝ) × ℝ => ENNReal.ofReal (gden gam h θ)) :=
    ENNReal.measurable_ofReal.comp (gden_meas gam hp.meas)
  rw [Measure.map_apply measurable_fst hE, Gh, withDensity_apply _ (measurable_fst hE), margM,
    withDensity_apply _ hE, ← Set.prod_univ, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ, lintegral_prod _ hmeas.aemeasurable]
  exact lintegral_congr fun w => inner_lint hg hp w

lemma lowDc_zero {x : ℝ} (hx : x ∉ Ioo ca0 ca1) : lowDc x = 0 := by
  simp only [lowDc, lowD, ramp_deriv_zero zones.2.1 hx, mul_zero]

lemma hiDc_zero {x : ℝ} (hx : x ∉ Ioo ca2 ca3) : hiDc x = 0 := by
  simp only [hiDc, hiD, ramp_deriv_zero zones.2.2.2.1 hx, mul_zero]

lemma etac_hasDerivAt (x : ℝ) :
    HasDerivAt (eta ca0 ca1 ca2 ca3) (lowDc x - hiDc x) x := eta_hasDerivAt x

lemma int_lowDc : ∫ x in (0:ℝ)..cU, lowDc x = 1 := by
  have z := zones
  have hc : ∀ a b : ℝ, IntervalIntegrable lowDc volume a b :=
    fun a b => lowDc_cont.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc 0 ca2) (hc ca2 cU)]
  have h2 : ∫ x in ca2..cU, lowDc x = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun x hx => ?_)]
    · simp
    · rw [Set.uIcc_of_le (by linarith)] at hx
      exact lowDc_zero (fun h => by linarith [h.2, hx.1])
  have h1 : ∫ x in (0:ℝ)..ca2, lowDc x = ∫ x in (0:ℝ)..ca2, (lowDc x - hiDc x) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (by linarith)] at hx
    rw [hiDc_zero (x := x) (fun h => by linarith [h.1, hx.2]), sub_zero]
  rw [h2, add_zero, h1, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => etac_hasDerivAt x) ((lowDc_cont.sub hiDc_cont).intervalIntegrable _ _)]
  rw [eta_one zones.2.1 zones.2.2.1.le zones.2.2.2.1 zones.2.2.1.le le_rfl,
    eta_zero zones.2.1 zones.2.2.1.le zones.2.2.2.1 (x := 0) (fun h => by linarith [h.1])]
  · norm_num
  all_goals first | exact zones.2.1 | exact zones.2.2.1.le | exact zones.2.2.2.1 | linarith

lemma int_hiDc : ∫ x in (0:ℝ)..cU, hiDc x = 1 := by
  have z := zones
  have hc : ∀ a b : ℝ, IntervalIntegrable hiDc volume a b :=
    fun a b => hiDc_cont.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc 0 ca1) (hc ca1 cU)]
  have h2 : ∫ x in (0:ℝ)..ca1, hiDc x = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun x hx => ?_)]
    · simp
    · rw [Set.uIcc_of_le (by linarith)] at hx
      exact hiDc_zero (fun h => by linarith [h.1, hx.2])
  have h1 : ∫ x in ca1..cU, hiDc x = -∫ x in ca1..cU, (lowDc x - hiDc x) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (by linarith)] at hx
    rw [lowDc_zero (x := x) (fun h => by linarith [h.2, hx.1])]; ring
  rw [h2, zero_add, h1, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => etac_hasDerivAt x) ((lowDc_cont.sub hiDc_cont).intervalIntegrable _ _)]
  rw [eta_one zones.2.1 zones.2.2.1.le zones.2.2.2.1 le_rfl zones.2.2.1.le,
    eta_zero zones.2.1 zones.2.2.1.le zones.2.2.2.1 (x := cU) (fun h => by linarith [h.2])]
  · norm_num
  all_goals first | exact zones.2.1 | exact zones.2.2.1.le | exact zones.2.2.2.1 | linarith

lemma cW_eq : cW = MeasurableEquiv.finTwoArrow ⁻¹' (Ioo 0 cU ×ˢ Ioo 0 cU) := by
  ext w
  simp [cW, Set.mem_pi, Fin.forall_fin_two, MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo]

/-- integral over the weight box of a function of `w₀` -/
lemma int_cW (f : ℝ → ℝ) :
    ∫ w in cW, f (w 0) = (∫ x in Ioo 0 cU, f x) * cU := by
  have hmp := volume_preserving_finTwoArrow ℝ
  rw [cW_eq]
  have := hmp.setIntegral_preimage_emb (MeasurableEquiv.finTwoArrow.measurableEmbedding)
    (fun p : ℝ × ℝ => f p.1 * (fun _ => (1:ℝ)) p.2) (Ioo 0 cU ×ˢ Ioo 0 cU)
  simp only [mul_one] at this
  rw [show (fun w : Fin 2 → ℝ => f (w 0)) = fun w => f (MeasurableEquiv.finTwoArrow w).1 from rfl,
    this, Measure.volume_eq_prod]
  have h2 := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    f (fun _ => (1:ℝ)) (Ioo 0 cU) (Ioo 0 cU)
  simp only [mul_one] at h2
  rw [h2, setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by norm_num [cU]), sub_zero]

lemma margM_univ {gam : ℝ} (hg : 0 ≤ gam) : margM gam univ = 1 := by
  rw [margM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_indicator cW_meas]
  have hint : IntegrableOn (fun w : Fin 2 → ℝ =>
      cc gam * (gam * lowDc (w 0) * (cU - cBmin) + hiDc (w 0) * cLbar)) cW := by
    have hc : Continuous (fun w : Fin 2 → ℝ =>
        cc gam * (gam * lowDc (w 0) * (cU - cBmin) + hiDc (w 0) * cLbar)) :=
      continuous_const.mul (((continuous_const.mul (lowDc_cont.comp (continuous_apply 0))).mul
        continuous_const).add ((hiDc_cont.comp (continuous_apply 0)).mul continuous_const))
    have hK : IsCompact (Set.pi univ (fun _ : Fin 2 => Icc (0:ℝ) cU)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    exact (hc.continuousOn.integrableOn_compact hK).mono_set
      (Set.pi_mono (fun _ _ => Ioo_subset_Icc_self))
  rw [← ofReal_integral_eq_lintegral_ofReal hint ?_]
  · rw [int_cW (fun x => cc gam * (gam * lowDc x * (cU - cBmin) + hiDc x * cLbar)),
      ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num [cU] : (0:ℝ) ≤ cU)]
    have hl := lowDc_cont.intervalIntegrable (μ := volume) 0 cU
    have hh := hiDc_cont.intervalIntegrable (μ := volume) 0 cU
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      ((hl.const_mul gam).mul_const _) (hh.mul_const _)]
    simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
      int_lowDc, int_hiDc]
    rw [ENNReal.ofReal_eq_one]
    unfold cc
    have h1 : (0:ℝ) < cU - cBmin := by norm_num [cU, cBmin]
    have h2 : (0:ℝ) < cU := by norm_num [cU]
    have := cLbar_bounds.1
    have h3 : 0 < gam * (cU - cBmin) + cLbar := by nlinarith
    field_simp
  · refine ae_restrict_of_forall_mem cW_meas fun w _ => ?_
    have := cLbar_bounds.1
    have h1 : (0:ℝ) ≤ cU - cBmin := by norm_num [cU, cBmin]
    have := lowDc_nonneg (w 0); have := hiDc_nonneg (w 0)
    exact mul_nonneg (cc_pos hg).le (by positivity)

end P7c

end CA63

-- ===== part P7d =====
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open ContextualAuctions.RevEquiv

namespace CA63

section P7d

/-! ### P7d: `Gh` is a valid buyer law; `Spend` is measurable; low-zone mass -/

lemma Gh_prob {gam : ℝ} (hg : 0 ≤ gam) {h : (Fin 2 → ℝ) → ℝ → ℝ} (hp : Prof h) :
    IsProbabilityMeasure (Gh gam h) := by
  constructor
  rw [← Set.preimage_univ (f := (Prod.fst : (Fin 2 → ℝ) × ℝ → Fin 2 → ℝ)),
    ← Measure.map_apply measurable_fst MeasurableSet.univ, marg_eq hg hp, margM_univ hg]

lemma Gh_ac (gam : ℝ) (h : (Fin 2 → ℝ) → ℝ → ℝ) : Gh gam h ≪ volume :=
  withDensity_absolutelyContinuous _ _

lemma theta_eq (G : Measure ((Fin 2 → ℝ) × ℝ)) : Theta (mdl G) = cW ×ˢ cBI := by
  refine Set.ext fun (θ : (Fin 2 → ℝ) × ℝ) => ?_
  show ((∀ i : Fin 2, 0 < θ.1 i ∧ θ.1 i < cU) ∧ cBmin < θ.2 ∧ θ.2 < cU) ↔
    ((∀ i : Fin 2, i ∈ univ → θ.1 i ∈ Ioo 0 cU) ∧ θ.2 ∈ Ioo cBmin cU)
  simp [Set.mem_Ioo]

lemma Gh_supp (gam : ℝ) (h : (Fin 2 → ℝ) → ℝ → ℝ) (hm : Measurable (Function.uncurry h))
    (G : Measure ((Fin 2 → ℝ) × ℝ)) : Gh gam h (Theta (mdl G))ᶜ = 0 := by
  rw [theta_eq, Gh, withDensity_apply _ (cW_meas.prod cBI_meas).compl]
  rw [← lintegral_indicator (cW_meas.prod cBI_meas).compl]
  have : (cW ×ˢ cBI)ᶜ.indicator (fun θ => ENNReal.ofReal (gden gam h θ)) = fun _ => 0 := by
    funext θ
    by_cases hθ : θ ∈ cW ×ˢ cBI
    · exact Set.indicator_of_notMem (Set.notMem_compl_iff.2 hθ) _
    · rw [Set.indicator_of_mem hθ, gden, Set.indicator_of_notMem hθ, ENNReal.ofReal_zero]
  rw [this, lintegral_zero]

/-- the reference profile: uniform in `B` -/
noncomputable def h0 : (Fin 2 → ℝ) → ℝ → ℝ := fun _ _ => cLbar / (cU - cBmin)

lemma h0_prof : Prof h0 where
  meas := measurable_const
  nonneg := fun _ _ _ _ => div_nonneg (by linarith [cLbar_bounds.1]) (by norm_num [cU, cBmin])
  int := fun _ _ => integrableOn_const (by simp [cBI, Real.volume_Ioo])
  mass := fun _ _ => by
    show ∫ B in cBI, cLbar / (cU - cBmin) = cLbar
    rw [setIntegral_const, smul_eq_mul, measureReal_def, cBI, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by norm_num [cU, cBmin])]
    field_simp [show (cU - cBmin) ≠ 0 by norm_num [cU, cBmin]]

open Classical in
lemma spend_meas (M : Model) (μ : Buyer M → ℝ) [IsProbabilityMeasure M.G]
    [IsProbabilityMeasure M.F] (hμ : Measurable μ) (hr : Measurable M.r) (t : ℝ) :
    Measurable (fun θ => Spend M μ θ t) := by
  haveI : SigmaFinite (Measure.pi fun _ : Fin (M.n - 1) => M.G) := Measure.pi.sigmaFinite _
  haveI : SFinite (P M) := by rw [P]; infer_instance
  have hbt : Measurable (fun q : Buyer M × Context M => bt M μ q.1 t q.2) := by
    unfold bt
    exact (sigma_meas_joint M μ hμ hr).comp
      (measurable_snd.prodMk ((val_meas_joint M).div_const _))
  have hb : Measurable (fun q : Buyer M × (Context M × (Fin (M.n - 1) → Buyer M)) =>
      bt M μ q.1 t q.2.1) := by
    simpa only [Function.comp_def] using hbt.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hS : MeasurableSet {q : Buyer M × (Context M × (Fin (M.n - 1) → Buyer M)) |
      wins M (beta M μ) (bt M μ q.1 t) q.2} := by
    have e : {q : Buyer M × (Context M × (Fin (M.n - 1) → Buyer M)) |
        wins M (beta M μ) (bt M μ q.1 t) q.2} =
        {q | M.r q.2.1 ≤ bt M μ q.1 t q.2.1} ∩
          ⋂ i, {q | beta M μ (q.2.2 i) q.2.1 ≤ bt M μ q.1 t q.2.1} := by
      ext q; simp [wins]
    rw [e]
    have hA : MeasurableSet {q : Buyer M × (Context M × (Fin (M.n - 1) → Buyer M)) |
        M.r q.2.1 ≤ bt M μ q.1 t q.2.1} :=
      measurableSet_le (hr.comp (measurable_fst.comp measurable_snd)) hb
    have hB : ∀ i, MeasurableSet {q : Buyer M × (Context M × (Fin (M.n - 1) → Buyer M)) |
        beta M μ (q.2.2 i) q.2.1 ≤ bt M μ q.1 t q.2.1} := by
      intro i
      have hpair : Measurable (fun q : Buyer M × (Context M × (Fin (M.n - 1) → Buyer M)) =>
          (q.2.2 i, q.2.1)) :=
        ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)).prodMk
          (measurable_fst.comp measurable_snd)
      have hbeta : Measurable (fun q : Buyer M × (Context M × (Fin (M.n - 1) → Buyer M)) =>
          beta M μ (q.2.2 i) q.2.1) := by
        simpa only [Function.comp_def] using (beta_meas_joint M μ hμ hr).comp hpair
      exact measurableSet_le hbeta hb
    exact hA.inter (MeasurableSet.iInter hB)
  have hF : Measurable (fun q : Buyer M × (Context M × (Fin (M.n - 1) → Buyer M)) =>
      if wins M (beta M μ) (bt M μ q.1 t) q.2 then bt M μ q.1 t q.2.1 else 0) :=
    Measurable.ite hS hb measurable_const
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := P M)).measurable

end P7d

end CA63

-- ===== part P7e =====
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open ContextualAuctions.RevEquiv

namespace CA63

section P7e

/-! ### P7e: atomless `λ`, low-zone mass, spend bounds in the high zone -/

/-- the high-zone mass `δ` -/
noncomputable def cdel (gam : ℝ) : ℝ := cc gam * cU * cLbar

lemma cdel_nonneg {gam : ℝ} (hg : 0 ≤ gam) : 0 ≤ cdel gam :=
  mul_nonneg (mul_nonneg (cc_pos hg).le (by norm_num [cU])) (by linarith [cLbar_bounds.1])

lemma margM_high {gam : ℝ} (hg : 0 ≤ gam) :
    margM gam {w | ca1 < w 0} ≤ ENNReal.ofReal (cdel gam) := by
  have hS : MeasurableSet {w : Fin 2 → ℝ | ca1 < w 0} :=
    measurableSet_lt measurable_const (measurable_pi_apply 0)
  rw [margM, withDensity_apply _ hS]
  calc ∫⁻ w in {w | ca1 < w 0}, cW.indicator (fun w => ENNReal.ofReal
          (cc gam * (gam * lowDc (w 0) * (cU - cBmin) + hiDc (w 0) * cLbar))) w
      ≤ ∫⁻ w in {w | ca1 < w 0}, cW.indicator
          (fun w => ENNReal.ofReal (cc gam * hiDc (w 0) * cLbar)) w := by
        refine setLIntegral_mono' hS fun w hw => ?_
        have h0 : lowDc (w 0) = 0 := lowDc_zero (fun h' => absurd h'.2 (not_lt.2 (le_of_lt hw)))
        by_cases hwc : w ∈ cW
        · rw [indicator_of_mem hwc, indicator_of_mem hwc, h0]
          apply le_of_eq; congr 1; ring
        · rw [indicator_of_notMem hwc, indicator_of_notMem hwc]
    _ ≤ ∫⁻ w, cW.indicator (fun w => ENNReal.ofReal (cc gam * hiDc (w 0) * cLbar)) w :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (cdel gam) := by
        have hc : Continuous (fun w : Fin 2 → ℝ => cc gam * hiDc (w 0) * cLbar) :=
          (continuous_const.mul (hiDc_cont.comp (continuous_apply 0))).mul continuous_const
        have hK : IsCompact (Set.pi univ (fun _ : Fin 2 => Icc (0:ℝ) cU)) :=
          isCompact_univ_pi (fun _ => isCompact_Icc)
        have hint : IntegrableOn (fun w : Fin 2 → ℝ => cc gam * hiDc (w 0) * cLbar) cW :=
          (hc.continuousOn.integrableOn_compact hK).mono_set
            (Set.pi_mono (fun _ _ => Ioo_subset_Icc_self))
        have hnn : 0 ≤ᵐ[volume.restrict cW] (fun w : Fin 2 → ℝ => cc gam * hiDc (w 0) * cLbar) :=
          Eventually.of_forall fun w => mul_nonneg (mul_nonneg (cc_pos hg).le (hiDc_nonneg _))
            (by linarith [cLbar_bounds.1])
        rw [lintegral_indicator cW_meas, ← ofReal_integral_eq_lintegral_ofReal hint hnn,
          int_cW (fun x => cc gam * hiDc x * cLbar), integral_mul_const, integral_const_mul,
          ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le (by norm_num [cU] : (0:ℝ) ≤ cU), int_hiDc]
        congr 1; unfold cdel; ring

lemma lam_atom {gam : ℝ} (hg : 0 ≤ gam) {h : (Fin 2 → ℝ) → ℝ → ℝ} (hp : Prof h)
    {α : Fin 2 → ℝ} (hα : α ∈ cA) (y : ℝ) :
    lam (mdl (Gh gam h)) muF α {y} = 0 := by
  have hφ : Measurable (fun w : Fin 2 → ℝ => paced (mdl (Gh gam h)) muF (w, 0) α) :=
    (paced_meas (mdl (Gh gam h)) muF muF_meas α).comp (measurable_id.prodMk measurable_const)
  have k1 : lam (mdl (Gh gam h)) muF α = ((Gh gam h).map Prod.fst).map
      (fun w : Fin 2 → ℝ => paced (mdl (Gh gam h)) muF (w, 0) α) :=
    (Measure.map_map hφ measurable_fst).symm
  rw [k1, marg_eq hg hp, Measure.map_apply hφ (measurableSet_singleton y)]
  refine (withDensity_absolutelyContinuous _ _) ?_
  have hE : MeasurableSet ((fun w : Fin 2 → ℝ => paced (mdl (Gh gam h)) muF (w, 0) α) ⁻¹' {y}) :=
    hφ (measurableSet_singleton y)
  have hmp := volume_preserving_finTwoArrow ℝ
  have hT : MeasurableSet (MeasurableEquiv.finTwoArrow.symm ⁻¹'
      ((fun w : Fin 2 → ℝ => paced (mdl (Gh gam h)) muF (w, 0) α) ⁻¹' {y})) :=
    MeasurableEquiv.finTwoArrow.symm.measurable hE
  have hEq : ((fun w : Fin 2 → ℝ => paced (mdl (Gh gam h)) muF (w, 0) α) ⁻¹' {y}) =
      MeasurableEquiv.finTwoArrow ⁻¹' (MeasurableEquiv.finTwoArrow.symm ⁻¹'
        ((fun w : Fin 2 → ℝ => paced (mdl (Gh gam h)) muF (w, 0) α) ⁻¹' {y})) := by
    ext w
    have hw : (![w 0, w 1] : Fin 2 → ℝ) = w := by ext i; fin_cases i <;> rfl
    simp [hw]
  rw [hEq, hmp.measure_preimage hT.nullMeasurableSet, Measure.volume_eq_prod,
    Measure.measure_prod_null hT]
  refine Eventually.of_forall fun x => ?_
  have hα1 : 0 < α 1 := by
    have h1 := (cA_mem.1 hα).2.1
    have h2 : (0:ℝ) < cEps := by norm_num [cEps]
    linarith
  have hc : 0 ≤ cm2 * ramp ca1 ca2 x := muF_nonneg ((fun _ => x), 0)
  refine measure_mono_null (t := {(y * (1 + cm2 * ramp ca1 ca2 x) - x * α 0) / α 1}) ?_
    (measure_singleton _)
  intro p hp
  simp only [mem_preimage, mem_singleton_iff] at hp ⊢
  have e0 : (MeasurableEquiv.finTwoArrow.symm (x, p) : Fin 2 → ℝ) 0 = x := by simp
  have e1 : (MeasurableEquiv.finTwoArrow.symm (x, p) : Fin 2 → ℝ) 1 = p := by simp
  have hv : val (mdl (Gh gam h)) (MeasurableEquiv.finTwoArrow.symm (x, p), 0) α =
      x * α 0 + p * α 1 := (mdl_val (Gh gam h) _ α).trans (by dsimp only; rw [e0, e1])
  unfold paced muF at hp
  dsimp only at hp
  rw [hv, e0] at hp
  rw [div_eq_iff (by linarith)] at hp
  rw [eq_div_iff hα1.ne']
  linarith

lemma low_mass {gam : ℝ} (hg : 0 ≤ gam) {h : (Fin 2 → ℝ) → ℝ → ℝ} (hp : Prof h)
    {α : Fin 2 → ℝ} (hα : α ∈ cA) :
    1 - cdel gam ≤ (lam (mdl (Gh gam h)) muF α (Iio cr0)).toReal := by
  haveI := Gh_prob hg hp
  have hφ : Measurable (fun θ : (Fin 2 → ℝ) × ℝ => paced (mdl (Gh gam h)) muF θ α) :=
    paced_meas (mdl (Gh gam h)) muF muF_meas α
  have hs : MeasurableSet ((fun θ : (Fin 2 → ℝ) × ℝ => paced (mdl (Gh gam h)) muF θ α) ⁻¹' Iio cr0) :=
    hφ measurableSet_Iio
  have hsub : ((fun θ : (Fin 2 → ℝ) × ℝ => paced (mdl (Gh gam h)) muF θ α) ⁻¹' Iio cr0)ᶜ ⊆
      (Theta (mdl (Gh gam h)))ᶜ ∪ Prod.fst ⁻¹' {w : Fin 2 → ℝ | ca1 < w 0} := by
    intro θ hθ
    by_contra hc
    simp only [mem_union, mem_compl_iff, not_or, not_not, mem_preimage, mem_setOf_eq,
      not_lt] at hc hθ
    apply hθ
    rw [theta_eq] at hc
    have hc1 : θ ∈ cW ×ˢ cBI := Classical.not_not.1 hc.1
    show val (mdl (Gh gam h)) θ α / (1 + muF θ) < cr0
    rw [muF_zero hc.2, add_zero, div_one]
    refine lt_of_eq_of_lt (mdl_val (Gh gam h) θ α) ?_
    exact low_val_lt (hc1.1 0 (mem_univ _)).1 hc.2 (hc1.1 1 (mem_univ _)).1
      (hc1.1 1 (mem_univ _)).2 hα
  have hm : Gh gam h (Prod.fst ⁻¹' {w : Fin 2 → ℝ | ca1 < w 0}) ≤ ENNReal.ofReal (cdel gam) := by
    rw [← Measure.map_apply measurable_fst
      (measurableSet_lt measurable_const (measurable_pi_apply 0)), marg_eq hg hp]
    exact margM_high hg
  have hc : Gh gam h ((fun θ : (Fin 2 → ℝ) × ℝ => paced (mdl (Gh gam h)) muF θ α) ⁻¹' Iio cr0)ᶜ ≤
      ENNReal.ofReal (cdel gam) := by
    calc _ ≤ Gh gam h ((Theta (mdl (Gh gam h)))ᶜ ∪ Prod.fst ⁻¹' {w : Fin 2 → ℝ | ca1 < w 0}) :=
          measure_mono hsub
      _ ≤ Gh gam h (Theta (mdl (Gh gam h)))ᶜ +
          Gh gam h (Prod.fst ⁻¹' {w : Fin 2 → ℝ | ca1 < w 0}) := measure_union_le _ _
      _ ≤ 0 + ENNReal.ofReal (cdel gam) := by
          rw [Gh_supp gam h hp.meas]; exact add_le_add le_rfl hm
      _ = _ := zero_add _
  have e0 : lam (mdl (Gh gam h)) muF α = (Gh gam h).map (fun θ : (Fin 2 → ℝ) × ℝ => paced (mdl (Gh gam h)) muF θ α) :=
    rfl
  rw [e0, Measure.map_apply hφ measurableSet_Iio]
  have e := prob_compl_eq_one_sub (μ := Gh gam h) hs.compl
  rw [compl_compl] at e
  rw [e, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  have := ENNReal.toReal_le_of_le_ofReal (cdel_nonneg hg) hc
  linarith

lemma spend_hi {gam : ℝ} (hg : 0 ≤ gam) {h : (Fin 2 → ℝ) → ℝ → ℝ} (hp : Prof h)
    (hδ : cdel gam < 1) {θ : (Fin 2 → ℝ) × ℝ} (hθ : θ ∈ cW ×ˢ cBI) (hw : ca2 ≤ θ.1 0) :
    cr0 * (1 - cdel gam) ≤ Spend (mdl (Gh gam h)) muF θ cm2 ∧
      Spend (mdl (Gh gam h)) muF θ cm2 ≤ cr0 + cdel gam := by
  haveI := Gh_prob hg hp
  haveI : IsProbabilityMeasure (mdl (Gh gam h)).G := Gh_prob hg hp
  haveI := cF_prob
  have hw0 := hθ.1 0 (mem_univ _)
  have hw1 := hθ.1 1 (mem_univ _)
  have hU : cU ≤ 1 := by norm_num [cU]
  obtain ⟨hS, hI⟩ := spend_formula (G := Gh gam h) hw0.1.le (hw0.2.le.trans hU) hw1.1.le
    (hw1.2.le.trans hU) (by linarith [cm2_pos] : (-1:ℝ) < cm2)
  have hae : ∀ᵐ α ∂cF, α ∈ cA := by
    rw [ae_iff]; simpa [Set.compl_def] using cF_supp
  have hpt : ∀ α ∈ cA,
      cr0 * (1 - cdel gam) ≤ sig0 (Phi (lam (mdl (Gh gam h)) muF α) 1) cr0
          (val (mdl (Gh gam h)) θ α / (1 + cm2)) *
        Win (lam (mdl (Gh gam h)) muF α) 1 cr0
          (sig0 (Phi (lam (mdl (Gh gam h)) muF α) 1) cr0 (val (mdl (Gh gam h)) θ α / (1 + cm2))) ∧
      sig0 (Phi (lam (mdl (Gh gam h)) muF α) 1) cr0 (val (mdl (Gh gam h)) θ α / (1 + cm2)) *
        Win (lam (mdl (Gh gam h)) muF α) 1 cr0
          (sig0 (Phi (lam (mdl (Gh gam h)) muF α) 1) cr0 (val (mdl (Gh gam h)) θ α / (1 + cm2)))
        ≤ cr0 + cdel gam := by
    intro α hα
    haveI : NullSingletonClass (lam (mdl (Gh gam h)) muF α) := ⟨lam_atom hg hp hα⟩
    haveI := lam_prob (mdl (Gh gam h)) muF muF_meas α
    have hx : cr0 ≤ val (mdl (Gh gam h)) θ α / (1 + cm2) := by
      rw [mdl_val]; exact high_paced_ge hw hw1.1 hα
    have hlo : 1 - cdel gam ≤ ((lam (mdl (Gh gam h)) muF α) (Iio cr0)).toReal ^ 1 := by
      rw [pow_one]; exact low_mass hg hp hα
    obtain ⟨b1, b2⟩ := spend_pt_bounds (lam (mdl (Gh gam h)) muF α) 1 (by norm_num [cr0]) hδ hlo hx
    refine ⟨b1, b2.trans ?_⟩
    have hx1 : val (mdl (Gh gam h)) θ α / (1 + cm2) ≤ 1 := by
      have hA := cA_mem.1 hα
      have hp1 : 0 < 1 + cm2 := by linarith [cm2_pos]
      rw [div_le_one hp1, mdl_val]
      have e1 : θ.1 0 * α 0 ≤ cU * (cK0 + 1) := by
        have : (0:ℝ) ≤ α 0 := by have : (0:ℝ) ≤ cK0 := by norm_num [cK0]
                                 linarith [hA.1.1]
        nlinarith [hA.1.2, hw0.2, hw0.1]
      have e2 : θ.1 1 * α 1 ≤ cU * (2 * cEps) := by
        have : (0:ℝ) ≤ α 1 := by have : (0:ℝ) ≤ cEps := by norm_num [cEps]
                                 linarith [hA.2.1]
        nlinarith [hA.2.2, hw1.2, hw1.1]
      have : cU * (cK0 + 1) + cU * (2 * cEps) ≤ 1 + cm2 := by
        norm_num [cm2, cV0, cOmega, cU, cBmin, cK0, cEps]
      linarith
    have := cdel_nonneg hg
    have hr0 : (0:ℝ) ≤ cr0 := by norm_num [cr0]
    nlinarith
  rw [hS]
  constructor
  · have hc1 : Integrable (fun _ : Fin 2 → ℝ => cr0 * (1 - cdel gam)) cF := integrable_const _
    have hk : ∫ _ : Fin 2 → ℝ, cr0 * (1 - cdel gam) ∂cF = cr0 * (1 - cdel gam) := by simp
    have := integral_mono_ae hc1 hI (hae.mono fun α hα => (hpt α hα).1)
    exact hk.symm.le.trans this
  · have hc1 : Integrable (fun _ : Fin 2 → ℝ => cr0 + cdel gam) cF := integrable_const _
    have hk : ∫ _ : Fin 2 → ℝ, cr0 + cdel gam ∂cF = cr0 + cdel gam := by simp
    have := integral_mono_ae hI hc1 (hae.mono fun α hα => (hpt α hα).2)
    exact this.trans hk.le

end P7e

end CA63

-- ===== part P7f =====
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open ContextualAuctions.RevEquiv

namespace CA63

section P7f

/-! ### P7f: `L`, `J₁` estimates; the corrected profile `hG` is admissible -/

lemma cBU : cBmin ≤ cU := by norm_num [cBmin, cU]

lemma inv_sub_cont {S : ℝ} (hS : cU < S) :
    ContinuousOn (fun B => 1 / (S - B)) (uIcc cBmin cU) := by
  refine ContinuousOn.div continuousOn_const (continuousOn_const.sub continuousOn_id) ?_
  intro B hB
  rw [uIcc_of_le cBU] at hB
  exact (sub_pos.2 (lt_of_le_of_lt hB.2 hS)).ne'

lemma Lf_sub {S S' : ℝ} (hS : cU < S) (hS' : cU < S') :
    |Lf S - Lf S'| ≤ (cU - cBmin) * |S - S'| / ((S - cU) * (S' - cU)) := by
  unfold Lf
  rw [← intervalIntegral.integral_sub ((inv_sub_cont hS).intervalIntegrable)
    ((inv_sub_cont hS').intervalIntegrable)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := cBmin) (b := cU)
    (f := fun B => 1 / (S - B) - 1 / (S' - B)) (C := |S - S'| / ((S - cU) * (S' - cU))) ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 cBU)] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  · intro B hB
    rw [uIoc_of_le cBU] at hB
    have h1 : 0 < S - B := by linarith [hB.2]
    have h2 : 0 < S' - B := by linarith [hB.2]
    have h3 : S - cU ≤ S - B := by linarith [hB.2]
    have h4 : S' - cU ≤ S' - B := by linarith [hB.2]
    rw [Real.norm_eq_abs, div_sub_div _ _ h1.ne' h2.ne', abs_div, abs_mul, abs_of_pos h1,
      abs_of_pos h2]
    have e : 1 * (S' - B) - (S - B) * 1 = -(S - S') := by ring
    rw [e, abs_neg]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos (by linarith) (by linarith))
      (mul_le_mul h3 h4 (by linarith) h1.le)

lemma cZ_hasDerivAt (x : ℝ) : HasDerivAt cZ (deriv cZ x) x :=
  ((cut_contDiff cBmin cU 1 (n := 1)).differentiable one_ne_zero x).hasDerivAt

lemma cZ_deriv_cont : Continuous (deriv cZ) :=
  (cut_contDiff cBmin cU 1 (n := 2)).continuous_deriv (by norm_num)

lemma cZ_lo : cZ cBmin = 0 := by
  have hE := cutE_pos (lo := cBmin) (hi := cU) (by norm_num [cBmin, cU]) 1
  exact cut_zero (by norm_num [cBmin, cU]) 1 (fun h => by linarith [h.1])

lemma cZ_hi : cZ cU = 0 := by
  have hE := cutE_pos (lo := cBmin) (hi := cU) (by norm_num [cBmin, cU]) 1
  exact cut_zero (by norm_num [cBmin, cU]) 1 (fun h => by linarith [h.2])

lemma cZ_one {B : ℝ} (h1 : 1 / 160 ≤ B) (h2 : B ≤ 7 / 800) : cZ B = 1 := by
  have hE : cutE cBmin cU 1 = 1 / 1600 := by norm_num [cutE, cBmin, cU]
  unfold cZ cut
  rw [hE, ramp_one (by norm_num) (by unfold cBmin; linarith),
    ramp_zero (by norm_num) (by unfold cU; linarith)]
  norm_num

lemma J1_eq {S : ℝ} (hS : cU < S) : J1 S = -∫ B in cBmin..cU, cZ B / (S - B) ^ 2 := by
  have hne : ∀ x ∈ uIcc cBmin cU, S - x ≠ 0 := fun x hx => by
    rw [uIcc_of_le cBU] at hx; exact (sub_pos.2 (lt_of_le_of_lt hx.2 hS)).ne'
  have hu : ∀ x ∈ uIcc cBmin cU, HasDerivAt (fun y => (S - y)⁻¹) (-(-1) / (S - x) ^ 2) x :=
    fun x hx => ((hasDerivAt_id' x).const_sub S).inv (hne x hx)
  have hv : ∀ x ∈ uIcc cBmin cU, HasDerivAt cZ (deriv cZ x) x := fun x _ => cZ_hasDerivAt x
  have hu' : IntervalIntegrable (fun x => -(-1) / (S - x) ^ 2) volume cBmin cU :=
    (ContinuousOn.div continuousOn_const ((continuousOn_const.sub continuousOn_id).pow 2)
      (fun x hx => pow_ne_zero 2 (hne x hx))).intervalIntegrable
  have hv' : IntervalIntegrable (deriv cZ) volume cBmin cU := cZ_deriv_cont.intervalIntegrable _ _
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  rw [cZ_lo, cZ_hi, mul_zero, mul_zero, sub_zero, zero_sub] at ibp
  unfold J1
  rw [show (fun B => deriv cZ B / (S - B)) = fun B => (S - B)⁻¹ * deriv cZ B from
    funext fun B => div_eq_inv_mul _ _, ibp]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  ring

lemma J1_le {S : ℝ} (hS : cU < S) (hS' : S ≤ 1 / 40) : J1 S ≤ -4 := by
  rw [J1_eq hS]
  have hcont : ContinuousOn (fun B => cZ B / (S - B) ^ 2) (uIcc cBmin cU) := by
    refine ContinuousOn.div (cut_contDiff cBmin cU 1 (n := 0)).continuous.continuousOn
      ((continuousOn_const.sub continuousOn_id).pow 2) ?_
    intro x hx
    rw [uIcc_of_le cBU] at hx
    exact pow_ne_zero 2 (sub_pos.2 (lt_of_le_of_lt hx.2 hS)).ne'
  have h1 : ∫ B in (1/160:ℝ)..(7/800), cZ B / (S - B) ^ 2 ≤
      ∫ B in cBmin..cU, cZ B / (S - B) ^ 2 := by
    refine intervalIntegral.integral_mono_interval (by norm_num [cBmin]) (by norm_num)
      (by norm_num [cU]) ?_ hcont.intervalIntegrable
    exact Eventually.of_forall fun B => div_nonneg (cut_nonneg 1 B) (sq_nonneg _)
  have h2 : ∫ B in (1/160:ℝ)..(7/800), (1600:ℝ) ≤ ∫ B in (1/160:ℝ)..(7/800), cZ B / (S - B) ^ 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
      (hcont.mono ?_).intervalIntegrable ?_
    · rw [uIcc_of_le (by norm_num), uIcc_of_le cBU]
      exact Icc_subset_Icc (by norm_num [cBmin]) (by norm_num [cU])
    · intro B hB
      have hp : 0 < S - B := by have : B < cU := by unfold cU; linarith [hB.2]
                                linarith
      rw [cZ_one hB.1 hB.2, le_div_iff₀ (by positivity)]
      have : S - B ≤ 1 / 40 := by linarith [hB.1]
      nlinarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at h2
  norm_num at h2
  linarith

/-- the high-zone spend (reference law `Gh gam h0`) -/
noncomputable def Sf (gam : ℝ) (w : Fin 2 → ℝ) : ℝ := Spend (mdl (Gh gam h0)) muF (w, 3 / 400) cm2

/-- the correction coefficient -/
noncomputable def kk (gam : ℝ) (w : Fin 2 → ℝ) : ℝ := (cLbar - Lf (Sf gam w)) / J1 (Sf gam w)

/-- the corrected profile -/
noncomputable def hG (gam : ℝ) (w : Fin 2 → ℝ) (B : ℝ) : ℝ :=
  if ca2 ≤ w 0 then (1 + kk gam w * deriv cZ B) / (Sf gam w - B) else h0 w B

lemma Sf_bounds {gam : ℝ} (hg : 0 ≤ gam) (hδ : cdel gam ≤ 1 / 1000) {w : Fin 2 → ℝ}
    (hw : w ∈ cW) (hw0 : ca2 ≤ w 0) :
    cr0 * (1 - cdel gam) ≤ Sf gam w ∧ Sf gam w ≤ cr0 + cdel gam :=
  spend_hi hg h0_prof (by linarith) (θ := (w, 3 / 400))
    ⟨hw, by constructor <;> norm_num [cBmin, cU]⟩ hw0

lemma Sf_range {gam : ℝ} (hg : 0 ≤ gam) (hδ : cdel gam ≤ 1 / 1000) {w : Fin 2 → ℝ}
    (hw : w ∈ cW) (hw0 : ca2 ≤ w 0) :
    cU + 1 / 200 ≤ Sf gam w ∧ Sf gam w ≤ 1 / 40 ∧ |cr0 - Sf gam w| ≤ cdel gam := by
  obtain ⟨h1, h2⟩ := Sf_bounds hg hδ hw hw0
  have h0 := cdel_nonneg hg
  refine ⟨?_, ?_, ?_⟩
  · unfold cU; unfold cr0 at h1; nlinarith
  · unfold cr0 at h2; linarith
  · rw [abs_le]; unfold cr0 at h1 h2 ⊢; constructor <;> nlinarith

lemma kk_bound {gam : ℝ} (hg : 0 ≤ gam) (hδ : cdel gam ≤ 1 / 1000) {w : Fin 2 → ℝ}
    (hw : w ∈ cW) (hw0 : ca2 ≤ w 0) : |kk gam w| ≤ 25 * cdel gam := by
  obtain ⟨h1, h2, h3⟩ := Sf_range hg hδ hw hw0
  have hU : cU < Sf gam w := by linarith
  have hJ := J1_le hU h2
  have hL := Lf_sub (S := cr0) (S' := Sf gam w) (by norm_num [cr0, cU]) hU
  have hd : cU * 0 + (1 / 200) ≤ Sf gam w - cU := by linarith
  unfold kk
  rw [abs_div, abs_of_neg (by linarith : J1 (Sf gam w) < 0), div_le_iff₀ (by linarith)]
  rw [show cLbar = Lf cr0 from rfl]
  have hfac : (cU - cBmin) * |cr0 - Sf gam w| / ((cr0 - cU) * (Sf gam w - cU)) ≤
      100 * cdel gam := by
    rw [div_le_iff₀ (mul_pos (by norm_num [cr0, cU]) (by linarith))]
    have h0 := cdel_nonneg hg
    have e1 : cU - cBmin = 1 / 200 := by norm_num [cU, cBmin]
    have e2 : cr0 - cU = 1 / 100 := by norm_num [cr0, cU]
    rw [e1, e2]
    nlinarith [abs_nonneg (cr0 - Sf gam w)]
  have h0 := cdel_nonneg hg
  nlinarith

lemma Sf_meas {gam : ℝ} (hg : 0 ≤ gam) : Measurable (Sf gam) := by
  haveI : IsProbabilityMeasure (mdl (Gh gam h0)).G := Gh_prob hg h0_prof
  haveI : IsProbabilityMeasure (mdl (Gh gam h0)).F := cF_prob
  have hm := spend_meas (mdl (Gh gam h0)) muF muF_meas measurable_const cm2
  exact hm.comp (measurable_id.prodMk measurable_const)

lemma ii_meas {F : ℝ → ℝ → ℝ} (hF : Measurable (Function.uncurry F)) :
    Measurable (fun S => ∫ B in cBmin..cU, F S B) := by
  simp_rw [intervalIntegral.integral_of_le cBU]
  exact (hF.stronglyMeasurable.integral_prod_right
    (ν := volume.restrict (Ioc cBmin cU))).measurable

lemma Lf_meas : Measurable Lf :=
  ii_meas (F := fun S B => 1 / (S - B)) (measurable_const.div (measurable_fst.sub measurable_snd))

lemma J1_meas : Measurable J1 :=
  ii_meas (F := fun S B => deriv cZ B / (S - B))
    ((cZ_deriv_cont.measurable.comp measurable_snd).div (measurable_fst.sub measurable_snd))

lemma kk_meas {gam : ℝ} (hg : 0 ≤ gam) : Measurable (kk gam) :=
  (measurable_const.sub (Lf_meas.comp (Sf_meas hg))).div (J1_meas.comp (Sf_meas hg))

lemma hG_prof {gam : ℝ} (hg : 0 ≤ gam) (hδ : cdel gam ≤ 1 / 1000)
    (hk : ∀ w ∈ cW, ca2 ≤ w 0 → ∀ B, |kk gam w * deriv cZ B| ≤ 1) : Prof (hG gam) where
  meas := by
    show Measurable (fun p : (Fin 2 → ℝ) × ℝ => hG gam p.1 p.2)
    unfold hG
    refine Measurable.ite (measurableSet_le measurable_const
      ((measurable_pi_apply 0).comp measurable_fst)) ?_ h0_prof.meas
    exact (measurable_const.add (((kk_meas hg).comp measurable_fst).mul
      (cZ_deriv_cont.measurable.comp measurable_snd))).div
      (((Sf_meas hg).comp measurable_fst).sub measurable_snd)
  nonneg := fun w hw B hB => by
    unfold hG
    split_ifs with h
    · obtain ⟨h1, -, -⟩ := Sf_range hg hδ hw h
      have := (abs_le.1 (hk w hw h B)).1
      exact div_nonneg (by linarith) (by linarith [hB.2])
    · exact h0_prof.nonneg w hw B hB
  int := fun w hw => by
    by_cases h : ca2 ≤ w 0
    · obtain ⟨h1, -, -⟩ := Sf_range hg hδ hw h
      have e : hG gam w = fun B => (1 + kk gam w * deriv cZ B) / (Sf gam w - B) := by
        funext B; unfold hG; rw [if_pos h]
      rw [e]
      refine (ContinuousOn.integrableOn_Icc (μ := volume) ?_).mono_set Ioo_subset_Icc_self
      refine ContinuousOn.div (continuous_const.add (continuous_const.mul cZ_deriv_cont)).continuousOn
        (continuousOn_const.sub continuousOn_id) ?_
      intro B hB; exact (sub_pos.2 (by linarith [hB.2])).ne'
    · have e : hG gam w = h0 w := by funext B; unfold hG; rw [if_neg h]
      rw [e]; exact h0_prof.int w hw
  mass := fun w hw => by
    by_cases h : ca2 ≤ w 0
    · obtain ⟨h1, h2, -⟩ := Sf_range hg hδ hw h
      have hU : cU < Sf gam w := by linarith
      have hJ := J1_le hU h2
      have e : ∀ B, hG gam w B = 1 / (Sf gam w - B) + kk gam w * (deriv cZ B / (Sf gam w - B)) := by
        intro B; unfold hG; rw [if_pos h]; ring
      simp_rw [e]
      show ∫ B in Ioo cBmin cU, _ = _
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le cBU]
      have hi1 := (inv_sub_cont hU).intervalIntegrable (μ := volume)
      have hi2 : IntervalIntegrable (fun B => deriv cZ B / (Sf gam w - B)) volume cBmin cU := by
        refine (ContinuousOn.div cZ_deriv_cont.continuousOn
          (continuousOn_const.sub continuousOn_id) ?_).intervalIntegrable
        intro B hB; rw [uIcc_of_le cBU] at hB
        have hlt : B < Sf gam w := by linarith [hB.2]
        exact (sub_pos.2 hlt).ne'
      rw [intervalIntegral.integral_add hi1 (hi2.const_mul _), intervalIntegral.integral_const_mul]
      show Lf (Sf gam w) + kk gam w * J1 (Sf gam w) = cLbar
      unfold kk
      rw [div_mul_cancel₀ _ (by linarith : J1 (Sf gam w) < 0).ne]
      ring
    · have e : hG gam w = h0 w := by funext B; unfold hG; rw [if_neg h]
      rw [e]; exact h0_prof.mass w hw

end P7f

end CA63

-- ===== part P7g =====
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open ContextualAuctions.RevEquiv

namespace CA63

section P7g

/-! ### P7g: choice of `γ`, spend of the true law, zero spend in the low zone -/

lemma cdel_le {gam : ℝ} (hg : 0 < gam) : cdel gam ≤ 100 / gam := by
  have hL := cLbar_bounds
  have e1 : cU - cBmin = 1 / 200 := by norm_num [cU, cBmin]
  have hpos : 0 < gam * (cU - cBmin) + cLbar := by rw [e1]; nlinarith
  have hU : (0:ℝ) < cU := by norm_num [cU]
  have e : cdel gam = cLbar / (gam * (cU - cBmin) + cLbar) := by
    unfold cdel cc; field_simp
  rw [e, div_le_div_iff₀ hpos hg, e1]
  nlinarith

lemma spend_G {gam : ℝ} (hg : 0 ≤ gam) {h : (Fin 2 → ℝ) → ℝ → ℝ} (hp : Prof h)
    {θ : (Fin 2 → ℝ) × ℝ} (hθ : θ.1 ∈ cW) :
    Spend (mdl (Gh gam h)) muF θ cm2 = Sf gam θ.1 := by
  haveI := Gh_prob hg hp
  haveI := Gh_prob hg h0_prof
  have hw0 := hθ 0 (mem_univ _)
  have hw1 := hθ 1 (mem_univ _)
  have hU : cU ≤ 1 := by norm_num [cU]
  rw [spend_marg (G := Gh gam h) (G' := Gh gam h0)
    ((marg_eq hg hp).trans (marg_eq hg h0_prof).symm) hw0.1.le (hw0.2.le.trans hU) hw1.1.le
    (hw1.2.le.trans hU) (by linarith [cm2_pos] : (-1:ℝ) < cm2)]
  rfl

lemma spend_low {G : Measure ((Fin 2 → ℝ) × ℝ)} [IsProbabilityMeasure G]
    {θ : (Fin 2 → ℝ) × ℝ} (hθ : θ.1 ∈ cW) (hw : θ.1 0 ≤ ca1) :
    Spend (mdl G) muF θ 0 = 0 := by
  have hw0 := hθ 0 (mem_univ _)
  have hw1 := hθ 1 (mem_univ _)
  have hU : cU ≤ 1 := by norm_num [cU]
  obtain ⟨hS, -⟩ := spend_formula (G := G) hw0.1.le (hw0.2.le.trans hU) hw1.1.le
    (hw1.2.le.trans hU) (by norm_num : (-1:ℝ) < 0)
  have hae : ∀ᵐ α ∂cF, α ∈ cA := by
    rw [ae_iff]; simpa [Set.compl_def] using cF_supp
  rw [hS]
  refine integral_eq_zero_of_ae (hae.mono fun α hα => ?_)
  have hx : val (mdl G) θ α / (1 + 0) < cr0 := by
    rw [add_zero, div_one]
    exact lt_of_eq_of_lt (mdl_val G θ α) (low_val_lt hw0.1 hw hw1.1 hw1.2 hα)
  have hs : ∀ Φ : ℝ → ℝ, sig0 Φ cr0 (val (mdl G) θ α / (1 + 0)) = val (mdl G) θ α / (1 + 0) :=
    fun Φ => if_pos hx
  simp only [Pi.zero_apply, hs]
  unfold Win
  rw [if_neg (not_le.2 hx), mul_zero]

end P7g

end CA63

-- ===== part P8a =====
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open ContextualAuctions.RevEquiv

namespace CA63

section P8a

/-! ### P8a: `μ ∈ X₀` (bounded, integrable, total variation `≤ V₀`) -/

noncomputable def tlo : Fin 3 → ℝ := ![0, 0, cBmin]
noncomputable def thi : Fin 3 → ℝ := ![cU, cU, cU]

lemma tlo_le : ∀ i, tlo i ≤ thi i := by
  intro i; fin_cases i <;> norm_num [tlo, thi, cU, cBmin]

lemma box_eq (G : Measure ((Fin 2 → ℝ) × ℝ)) :
    {z : Fin 3 → ℝ | (Fin.init z, z (Fin.last 2)) ∈ Theta (mdl G)} =
      Set.pi univ (fun i => Ioo (tlo i) (thi i)) := by
  ext z
  rw [mem_setOf_eq, theta_eq]
  show (Fin.init z ∈ cW ∧ z (Fin.last 2) ∈ cBI) ↔ _
  simp only [cW, cBI, mem_univ_pi]
  constructor
  · rintro ⟨h1, h2⟩ i
    fin_cases i
    · simpa [Fin.init, tlo, thi] using h1 0
    · simpa [Fin.init, tlo, thi] using h1 1
    · simpa [tlo, thi] using h2
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i
      · simpa [Fin.init, tlo, thi] using h 0
      · simpa [Fin.init, tlo, thi] using h 1
    · simpa [tlo, thi] using h 2

noncomputable def fmu (t : ℝ) : ℝ := cm2 * ramp ca1 ca2 t

lemma fmu_contDiff : ContDiff ℝ 1 fmu := contDiff_const.mul (ramp_contDiff _ _)

lemma fmu_deriv_nonneg (t : ℝ) : 0 ≤ deriv fmu t := by
  have hd : DifferentiableAt ℝ (ramp ca1 ca2) t :=
    (ramp_contDiff ca1 ca2 (n := 1)).differentiable one_ne_zero t
  unfold fmu
  rw [deriv_const_mul cm2 hd]
  exact mul_nonneg cm2_pos.le (ramp_deriv_nonneg zones.2.2.1 t)

lemma fmu_int : ∫ t in Ioo 0 cU, deriv fmu t = cm2 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num [cU] : (0:ℝ) ≤ cU)]
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun x _ => (fmu_contDiff.differentiable one_ne_zero) x)
    ((fmu_contDiff.continuous_deriv le_rfl).intervalIntegrable _ _)]
  unfold fmu
  rw [ramp_one zones.2.2.1 (zones.2.2.2.1.trans zones.2.2.2.2).le, ramp_zero zones.2.2.1 (by linarith [zones.1, zones.2.1])]
  ring

lemma muF_X0 (G : Measure ((Fin 2 → ℝ) × ℝ)) : muF ∈ X0 (mdl G) := by
  refine ⟨⟨⟨muF_meas, fun θ _ => muF_nonneg θ⟩, ?_, fun θ _ => ⟨muF_nonneg θ, ?_⟩⟩, ?_⟩
  · rw [theta_eq]
    have hK : IsCompact ((Set.pi univ (fun _ : Fin 2 => Icc (0:ℝ) cU)) ×ˢ Icc cBmin cU) :=
      (isCompact_univ_pi fun _ => isCompact_Icc).prod isCompact_Icc
    have hfin : volume (cW ×ˢ cBI) ≠ ⊤ :=
      (lt_of_le_of_lt (measure_mono (Set.prod_mono (Set.pi_mono fun _ _ => Ioo_subset_Icc_self)
        Ioo_subset_Icc_self)) hK.measure_lt_top).ne
    refine Measure.integrableOn_of_bounded (M := cm2) hfin muF_meas.aestronglyMeasurable
      (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (muF_nonneg θ)]
    exact muF_le θ
  · rw [mdl_omega]; exact (muF_le θ).trans cm2_le
  · rw [mdl_V0]
    show totVar (fun z : Fin 3 → ℝ => muF (Fin.init z, z (Fin.last 2)))
      {z : Fin 3 → ℝ | (Fin.init z, z (Fin.last 2)) ∈ Theta (mdl G)} ≤ ((cV0 : ℝ) : EReal)
    rw [box_eq]
    refine sSup_le ?_
    rintro v ⟨ψ, hψ, hc, hs, hn, rfl⟩
    refine EReal.coe_le_coe_iff.2 ?_
    have h := tv_first_le tlo thi tlo_le fmu fmu_contDiff fmu_deriv_nonneg ψ hψ hc hs hn
    have e1 : tlo 0 = 0 := by simp [tlo]
    have e2 : thi 0 = cU := by simp [thi]
    have e3 : (thi 1 - tlo 1) * (thi 2 - tlo 2) = cU * (cU - cBmin) := by simp [tlo, thi]
    rw [e1, e2, e3, fmu_int, cm2_eq] at h
    exact h

end P8a

end CA63

-- ===== part P8b =====
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open ContextualAuctions.RevEquiv

namespace CA63

section P8b

/-! ### P8b: the density of the true law against the spend gap -/

lemma dens_hi {gam : ℝ} {θ : (Fin 2 → ℝ) × ℝ} (hθ : θ ∈ cW ×ˢ cBI) (hw : ca2 ≤ θ.1 0)
    (hS : Sf gam θ.1 - θ.2 ≠ 0) :
    (θ.2 - Sf gam θ.1) * gden gam (hG gam) θ =
      -(cc gam * (hiDc (θ.1 0) * (1 + kk gam θ.1 * deriv cZ θ.2))) := by
  have hl : lowDc (θ.1 0) = 0 :=
    lowDc_zero (fun h => by linarith [h.2, zones.2.2.1])
  rw [gden, indicator_of_mem hθ]
  simp only [hG, if_pos hw, hl, mul_zero, zero_add]
  field_simp
  ring

lemma dens_lo {gam : ℝ} {θ : (Fin 2 → ℝ) × ℝ} (hθ : θ ∈ cW ×ˢ cBI) (hw : θ.1 0 < ca2) :
    gden gam (hG gam) θ = cc gam * (gam * lowDc (θ.1 0)) := by
  have hh : hiDc (θ.1 0) = 0 := hiDc_zero (fun h => by linarith [h.1])
  rw [gden, indicator_of_mem hθ, hh, zero_mul, add_zero]

end P8b

end CA63

-- ===== part P8c =====
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open ContextualAuctions.RevEquiv

namespace CA63

section P8c

/-! ### P8c: transport, constants, the calibration field and the ν-side bound -/

noncomputable def tEq : (Fin 3 → ℝ) ≃ᵐ (Fin 2 → ℝ) × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)).trans
    MeasurableEquiv.prodComm

lemma tEq_apply (z : Fin 3 → ℝ) : tEq z = (Fin.init z, z (Fin.last 2)) := by
  refine Prod.ext ?_ rfl
  funext j
  simp [tEq, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.init, Fin.removeNth]
  fin_cases j <;> rfl

lemma tEq_mp : MeasurePreserving tEq volume volume :=
  (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin 2 → ℝ)))).comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2))

/-- the open box in `Fin 3` coordinates -/
def cBox : Set (Fin 3 → ℝ) := Set.pi univ (fun i => Ioo (tlo i) (thi i))

lemma cBox_eq : cBox = tEq ⁻¹' (cW ×ˢ cBI) := by
  have h := box_eq (0 : Measure ((Fin 2 → ℝ) × ℝ))
  rw [theta_eq] at h
  ext z
  simp only [mem_preimage, tEq_apply]
  rw [cBox, ← h]
  rfl

lemma box_int (f : (Fin 2 → ℝ) × ℝ → ℝ) :
    ∫ z in cBox, f (Fin.init z, z (Fin.last 2)) = ∫ θ in cW ×ˢ cBI, f θ := by
  rw [cBox_eq]
  simp_rw [← tEq_apply]
  exact tEq_mp.setIntegral_preimage_emb tEq.measurableEmbedding f _

lemma box_intOn {f : (Fin 2 → ℝ) × ℝ → ℝ} (hf : IntegrableOn f (cW ×ˢ cBI)) :
    IntegrableOn (fun z => f (Fin.init z, z (Fin.last 2))) cBox := by
  rw [cBox_eq]
  have := (tEq_mp.integrableOn_comp_preimage tEq.measurableEmbedding (f := f)
    (s := cW ×ˢ cBI)).2 hf
  simpa only [Function.comp_def, tEq_apply] using this

lemma bdd_cs {f : ℝ → ℝ} (hc : Continuous f) {a b : ℝ} (hs : tsupport f ⊆ Icc a b) :
    ∃ C, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hs)
  exact ⟨C, (norm_nonneg _).trans (hC 0), fun x => by simpa [Real.norm_eq_abs] using hC x⟩

lemma cZ_tsupport : tsupport cZ ⊆ Icc cBmin cU :=
  (cut_tsupport_Ioo (by norm_num [cBmin, cU]) 1).trans Ioo_subset_Icc_self

lemma cZ_contDiff : ContDiff ℝ 1 cZ := cut_contDiff _ _ _

lemma bnd_ramp : ∃ C, 0 ≤ C ∧ ∀ x, |deriv (ramp ca2 ca3) x| ≤ C :=
  bdd_cs ((ramp_deriv_contDiff ca2 ca3 (n := 0)).continuous)
    (ramp_deriv_tsupport zones.2.2.2.1)

lemma bnd_Z : ∃ C, 0 ≤ C ∧ ∀ x, |deriv cZ x| ≤ C :=
  bdd_cs cZ_deriv_cont ((tsupport_deriv_subset (𝕜 := ℝ) (f := cZ)).trans cZ_tsupport)

lemma bnd_eta : ∃ C, 0 ≤ C ∧ ∀ x, |deriv (eta ca0 ca1 ca2 ca3) x| ≤ C :=
  bdd_cs ((eta_contDiff (n := 1)).continuous_deriv le_rfl)
    ((tsupport_deriv_subset (𝕜 := ℝ) (f := eta ca0 ca1 ca2 ca3)).trans (eta_tsupport zones.2.1 zones.2.2.1.le zones.2.2.2.1))

lemma bnd_hiD : ∃ C, 0 ≤ C ∧ ∀ x, |hiDc x| ≤ C :=
  bdd_cs hiDc_cont (hiD_tsupport zones.2.1 zones.2.2.1.le zones.2.2.2.1)

/-- the requirements on the low-zone weight `gam` -/
structure GamOK (gam : ℝ) : Prop where
  big : 200 ≤ gam
  del : cdel gam ≤ 1 / 1000
  k1 : ∀ x, Real.pi / 2 * deriv (ramp ca2 ca3) x * (25 * cdel gam) ≤ 1
  k2 : ∀ B, |deriv cZ B| * (25 * cdel gam) ≤ 1

lemma gam_exists : ∃ gam, GamOK gam := by
  obtain ⟨C1, hC1, h1⟩ := bnd_ramp
  obtain ⟨C2, hC2, h2⟩ := bnd_Z
  set gam : ℝ := 100000 + 5000 * C1 + 2500 * C2 with hgdef
  have hg : 0 < gam := by positivity
  have hd := cdel_le hg
  have hd0 : 0 ≤ cdel gam := cdel_nonneg hg.le
  have hpi : Real.pi / 2 < 2 := by linarith [Real.pi_lt_four]
  have hA : 0 ≤ 5000 * C1 := by positivity
  have hB : 0 ≤ 2500 * C2 := by positivity
  have e1 : 25 * cdel gam * gam ≤ 2500 := by
    have := mul_le_mul_of_nonneg_right hd hg.le
    rw [div_mul_cancel₀ _ hg.ne'] at this; linarith
  refine ⟨gam, ⟨by linarith, ?_, fun x => ?_, fun B => ?_⟩⟩
  · have : 100000 ≤ gam := by linarith
    have h3 : cdel gam * gam ≤ 100 := by linarith
    have h4 : cdel gam * 100000 ≤ cdel gam * gam := mul_le_mul_of_nonneg_left this hd0
    linarith
  · have hx := (abs_le.1 (h1 x)).2
    have hx0 : 0 ≤ deriv (ramp ca2 ca3) x := ramp_deriv_nonneg zones.2.2.2.1 x
    have hgC : 5000 * C1 ≤ gam := by linarith
    have : deriv (ramp ca2 ca3) x * (25 * cdel gam) ≤ 1 / 2 := by
      have := mul_le_mul hx (le_refl (25 * cdel gam)) (by positivity) hC1
      nlinarith
    nlinarith [Real.pi_pos, mul_nonneg hx0 (by positivity : (0:ℝ) ≤ 25 * cdel gam)]
  · have hx := h2 B
    have hgC : 2500 * C2 ≤ gam := by linarith
    have := mul_le_mul hx (le_refl (25 * cdel gam)) (by positivity) hC2
    nlinarith

/-- the bounded profile `k`, extended by zero -/
def kSet : Set (Fin 2 → ℝ) := cW ∩ {w | ca2 ≤ w 0}

lemma kSet_meas : MeasurableSet kSet :=
  cW_meas.inter (measurableSet_le measurable_const (measurable_pi_apply 0))

noncomputable def kfun (gam : ℝ) : (Fin 2 → ℝ) → ℝ := kSet.indicator (kk gam)

lemma kfun_bound {gam : ℝ} (hg : GamOK gam) (w : Fin 2 → ℝ) :
    |kfun gam w| ≤ 25 * cdel gam := by
  unfold kfun
  by_cases hw : w ∈ kSet
  · rw [indicator_of_mem hw]
    exact kk_bound (by linarith [hg.big]) hg.del hw.1 hw.2
  · rw [indicator_of_notMem hw, abs_zero]
    exact mul_nonneg (by norm_num) (cdel_nonneg (by linarith [hg.big]))

lemma kfun_meas {gam : ℝ} (hg : GamOK gam) : Measurable (kfun gam) :=
  (kk_meas (by linarith [hg.big])).indicator kSet_meas

lemma cW_fin : volume cW ≠ ⊤ := by
  rw [cW, volume_pi_pi]
  simp [Real.volume_Ioo]

lemma kfun_int {gam : ℝ} (hg : GamOK gam) : Integrable (kfun gam) := by
  have hz : ∀ w, w ∉ cW → kfun gam w = 0 := fun w hw =>
    indicator_of_notMem (fun h => hw h.1) _
  refine (integrableOn_iff_integrable_of_support_subset (s := cW) ?_).1 ?_
  · intro w hw; by_contra h; exact hw (hz w h)
  · exact Measure.integrableOn_of_bounded (M := 25 * cdel gam) cW_fin
      (kfun_meas hg).aestronglyMeasurable
      (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact kfun_bound hg w)

/-- the calibration field `D` in `Fin 3` coordinates -/
noncomputable def Dz (gam : ℝ) (z : Fin 3 → ℝ) : ℝ :=
  -(deriv (eta ca0 ca1 ca2 ca3) (z 0)) + hiDc (z 0) * kfun gam (Fin.init z) * deriv cZ (z 2)

/-- the same field in type coordinates -/
noncomputable def Dθ (gam : ℝ) (θ : (Fin 2 → ℝ) × ℝ) : ℝ :=
  -(deriv (eta ca0 ca1 ca2 ca3) (θ.1 0)) + hiDc (θ.1 0) * kfun gam θ.1 * deriv cZ θ.2

lemma Dz_eq (gam : ℝ) (z : Fin 3 → ℝ) : Dz gam z = Dθ gam (Fin.init z, z (Fin.last 2)) := rfl

lemma test_fields {gam : ℝ} (hg : GamOK gam) (kj : ℕ → (Fin 2 → ℝ) → ℝ)
    (hkj : ∀ j, ContDiff ℝ 1 (kj j)) (hK : ∀ j w, |kj j w| ≤ 25 * cdel gam) (j : ℕ) :
    let φ := fld (eta ca0 ca1 ca2 ca3) (cut (tlo 1) (thi 1) j) (cut (tlo 2) (thi 2) j) hiDc cZ (kj j)
    ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ cBox ∧
      ∀ z, Real.sqrt (∑ i, (φ z i) ^ 2) ≤ 1 := by
  intro φ
  have h1 : tlo 1 < thi 1 := by norm_num [tlo, thi, cU]
  have h2 : tlo 2 < thi 2 := by simp [tlo, thi, cU, cBmin]; norm_num
  set e2 := min (cutE (tlo 2) (thi 2) j) (cutE (tlo 2) (thi 2) 1)
  have he2 : 0 < e2 := lt_min (cutE_pos h2 j) (cutE_pos h2 1)
  have hcz : cZ = cut (tlo 2) (thi 2) 1 := by simp [cZ, tlo, thi]
  refine ⟨fld_contDiff eta_contDiff (cut_contDiff _ _ _) (cut_contDiff _ _ _)
      (hiD_contDiff (n := 1)) cZ_contDiff (hkj j), ?_⟩
  obtain ⟨hcs, hts⟩ := fld_support (a := eta ca0 ca1 ca2 ca3) (c1 := cut (tlo 1) (thi 1) j)
    (c2 := cut (tlo 2) (thi 2) j) (hh := hiDc) (e := cZ) (kk := kj j)
    ![ca0, tlo 1 + cutE (tlo 1) (thi 1) j, tlo 2 + e2]
    ![ca3, thi 1 - cutE (tlo 1) (thi 1) j, thi 2 - e2] tlo thi
    (fun i => by
      fin_cases i
      · simp [tlo]; exact zones.1
      · simp; exact cutE_pos h1 j
      · simp; exact he2)
    (fun i => by
      fin_cases i
      · simp [thi]; exact zones.2.2.2.2
      · simp; exact cutE_pos h1 j
      · simp; exact he2)
    (fun x hx => eta_zero zones.2.1 zones.2.2.1.le zones.2.2.2.1 (fun h => hx (by
      simp only [Matrix.cons_val_zero]; exact Ioo_subset_Icc_self h)))
    (fun x hx => hiDc_zero (fun h => hx (by
      simp only [Matrix.cons_val_zero]
      exact ⟨by linarith [h.1, zones.1, zones.2.1, zones.2.2.1], h.2.le⟩)))
    (fun x hx => cut_zero h1 j (fun h => hx (by simpa using h)))
    (fun x hx => cut_zero h2 j (fun h => hx (by
      simp only [Matrix.cons_val]
      have m1 := min_le_left (cutE (tlo 2) (thi 2) j) (cutE (tlo 2) (thi 2) 1)
      exact ⟨by linarith [h.1], by linarith [h.2]⟩)))
    (fun x hx => by
      rw [hcz]
      exact cut_zero h2 1 (fun h => hx (by
        simp only [Matrix.cons_val]
        have m1 := min_le_right (cutE (tlo 2) (thi 2) j) (cutE (tlo 2) (thi 2) 1)
        exact ⟨by linarith [h.1], by linarith [h.2]⟩)))
  refine ⟨hcs, hts, fld_norm (fun x => cut_abs_le j x) (fun x => cut_abs_le j x) ?_⟩
  intro x w s
  refine eta_norm_bound zones.2.1 zones.2.2.1.le zones.2.2.2.1 x _ ?_
  have hr0 : 0 ≤ deriv (ramp ca2 ca3) x := ramp_deriv_nonneg zones.2.2.2.1 x
  have hc : |kj j w * cZ s| ≤ 25 * cdel gam := by
    rw [abs_mul]
    calc |kj j w| * |cZ s| ≤ 25 * cdel gam * 1 :=
          mul_le_mul (hK j w) (cut_abs_le 1 s) (abs_nonneg _)
            (mul_nonneg (by norm_num) (cdel_nonneg (by linarith [hg.big])))
      _ = _ := mul_one _
  calc Real.pi / 2 * deriv (ramp ca2 ca3) x * |kj j w * cZ s|
      ≤ Real.pi / 2 * deriv (ramp ca2 ca3) x * (25 * cdel gam) :=
        mul_le_mul_of_nonneg_left hc (mul_nonneg (by positivity) hr0)
    _ ≤ 1 := hg.k1 x

end P8c

end CA63

-- ===== part P8d =====
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open ContextualAuctions.RevEquiv

namespace CA63

section P8d

/-! ### P8d: the ν-side bound and the calibration identity -/

lemma tlo_lt : ∀ i, tlo i < thi i := by
  intro i; fin_cases i <;> simp [tlo, thi, cU, cBmin] <;> norm_num

lemma nu_side {gam : ℝ} (hg : GamOK gam) (G : Measure ((Fin 2 → ℝ) × ℝ))
    {ν : (Fin 2 → ℝ) × ℝ → ℝ} (hν : ν ∈ X0 (mdl G)) :
    ∫ θ in cW ×ˢ cBI, ν θ * Dθ gam θ ≤ cV0 := by
  obtain ⟨kj, hkj, hK, hlim⟩ := smooth_approx (kfun_int hg) (kfun_bound hg)
  obtain ⟨C1, -, hA1⟩ := bnd_eta
  obtain ⟨C2, -, hA2⟩ := bnd_hiD
  obtain ⟨C3, -, hA3⟩ := bnd_Z
  have hint : IntegrableOn ν (cW ×ˢ cBI) := by
    have := hν.1.2.1; rwa [theta_eq] at this
  have hu := box_intOn hint
  have hl := div_tendsto (eta_contDiff (n := 1)) (hiD_contDiff (n := 1)) cZ_contDiff hA1 hA2 hA3
    kj (kfun gam) hkj hK hlim tlo thi tlo_lt _ hu
  have h := approx_le_totVar (fun z => ν (Fin.init z, z (Fin.last 2))) cBox (Dz gam) _
    (fun j => test_fields hg kj hkj hK j) hl
  have hV := hν.2
  rw [mdl_V0] at hV
  have e : Vtheta (mdl G) ν =
      totVar (fun z : Fin 3 → ℝ => ν (Fin.init z, z (Fin.last 2))) cBox := by
    show totVar _ {z : Fin 3 → ℝ | (Fin.init z, z (Fin.last 2)) ∈ Theta (mdl G)} = _
    rw [box_eq]; rfl
  rw [e] at hV
  have h2 := EReal.coe_le_coe_iff.1 (h.trans hV)
  have e2 := box_int (fun θ => ν θ * Dθ gam θ)
  rw [← e2]; exact h2

lemma cBI_fin : volume cBI ≠ ⊤ := by simp [cBI, Real.volume_Ioo]

lemma box_fin : volume (cW ×ˢ cBI) ≠ ⊤ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_ne_top cW_fin cBI_fin

lemma intOn_bdd {f : (Fin 2 → ℝ) × ℝ → ℝ} (hm : AEStronglyMeasurable f volume) {C : ℝ}
    (hC : ∀ θ ∈ cW ×ˢ cBI, |f θ| ≤ C) : IntegrableOn f (cW ×ˢ cBI) :=
  Measure.integrableOn_of_bounded (M := C) box_fin hm
    ((ae_restrict_mem (cW_meas.prod cBI_meas)).mono fun θ hθ => by
      rw [Real.norm_eq_abs]; exact hC θ hθ)

lemma Dθ_meas {gam : ℝ} (hg : GamOK gam) : Measurable (Dθ gam) := by
  have h1 : Measurable (deriv (eta ca0 ca1 ca2 ca3)) :=
    ((eta_contDiff (n := 1)).continuous_deriv le_rfl).measurable
  have h3 : Measurable (deriv cZ) := cZ_deriv_cont.measurable
  unfold Dθ
  exact (h1.comp ((measurable_pi_apply 0).comp measurable_fst)).neg.add
    (((hiDc_cont.measurable.comp ((measurable_pi_apply 0).comp measurable_fst)).mul
      ((kfun_meas hg).comp measurable_fst)).mul (h3.comp measurable_snd))

lemma Dθ_bdd {gam : ℝ} (hg : GamOK gam) : ∃ C, ∀ θ, |Dθ gam θ| ≤ C := by
  obtain ⟨C1, h1, hA1⟩ := bnd_eta
  obtain ⟨C2, h2, hA2⟩ := bnd_hiD
  obtain ⟨C3, h3, hA3⟩ := bnd_Z
  refine ⟨C1 + C2 * (25 * cdel gam) * C3, fun θ => ?_⟩
  have hk := kfun_bound hg θ.1
  have hK0 : 0 ≤ 25 * cdel gam := (abs_nonneg _).trans hk
  unfold Dθ
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_mul, abs_mul]
  gcongr
  · exact hA1 _
  · exact hA2 _
  · exact hA3 _

lemma int_cZ' : ∫ B in cBI, deriv cZ B = 0 := by
  rw [cBI, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le cBU,
    intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (cZ_contDiff.differentiable one_ne_zero) x)
      (cZ_deriv_cont.intervalIntegrable _ _), cZ_hi, cZ_lo, sub_zero]

lemma fmu_deriv_eq (t : ℝ) : deriv fmu t = cm2 * deriv (ramp ca1 ca2) t := by
  have hd : DifferentiableAt ℝ (ramp ca1 ca2) t :=
    (ramp_contDiff ca1 ca2 (n := 1)).differentiable one_ne_zero t
  unfold fmu
  rw [deriv_const_mul cm2 hd]

lemma fmu_eta (t : ℝ) : deriv fmu t * eta ca0 ca1 ca2 ca3 t = deriv fmu t := by
  by_cases ht : t ∈ Ioo ca1 ca2
  · rw [eta_one zones.2.1 zones.2.2.1.le zones.2.2.2.1 ht.1.le ht.2.le, mul_one]
  · rw [fmu_deriv_eq, ramp_deriv_zero zones.2.2.1 ht]; ring

lemma one_dim : ∫ t in Ioo 0 cU, fmu t * -(deriv (eta ca0 ca1 ca2 ca3) t) = cm2 := by
  have hU : (0:ℝ) ≤ cU := by norm_num [cU]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hU]
  simp_rw [mul_neg]
  rw [intervalIntegral.integral_neg]
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := cU)
    (u := fmu) (v := eta ca0 ca1 ca2 ca3) (u' := deriv fmu)
    (v' := deriv (eta ca0 ca1 ca2 ca3))
    (fun x _ => ((fmu_contDiff.differentiable one_ne_zero) x).hasDerivAt)
    (fun x _ => ((eta_contDiff (n := 1)).differentiable one_ne_zero x).hasDerivAt)
    ((fmu_contDiff.continuous_deriv le_rfl).intervalIntegrable _ _)
    (((eta_contDiff (n := 1)).continuous_deriv le_rfl).intervalIntegrable _ _)
  rw [hibp, eta_zero zones.2.1 zones.2.2.1.le zones.2.2.2.1 (x := cU) (fun h => by linarith [h.2, zones.2.2.2.2]),
    eta_zero zones.2.1 zones.2.2.1.le zones.2.2.2.1 (x := 0) (fun h => by linarith [h.1, zones.1])]
  simp_rw [fmu_eta]
  rw [intervalIntegral.integral_of_le hU, integral_Ioc_eq_integral_Ioo, fmu_int]
  ring

lemma muF_mk (w : Fin 2 → ℝ) (B : ℝ) : muF (w, B) = fmu (w 0) := rfl

lemma inner_eq {gam : ℝ} (w : Fin 2 → ℝ) :
    ∫ B in cBI, muF (w, B) * Dθ gam (w, B) =
      (cU - cBmin) * (fmu (w 0) * -(deriv (eta ca0 ca1 ca2 ca3) (w 0))) := by
  have hf : (fun B => muF (w, B) * Dθ gam (w, B)) = fun B =>
      fmu (w 0) * -(deriv (eta ca0 ca1 ca2 ca3) (w 0)) +
        (fmu (w 0) * hiDc (w 0) * kfun gam w) * deriv cZ B := by
    funext B; simp only [muF_mk, Dθ]; ring
  have hZi : IntegrableOn (deriv cZ) cBI :=
    (cZ_deriv_cont.integrableOn_Icc (a := cBmin) (b := cU)).mono_set Ioo_subset_Icc_self
  have hci : IntegrableOn (fun _ : ℝ => fmu (w 0) * -(deriv (eta ca0 ca1 ca2 ca3) (w 0))) cBI :=
    integrableOn_const cBI_fin
  rw [hf, integral_add hci (hZi.const_mul _), integral_const_mul (fmu (w 0) * hiDc (w 0) * kfun gam w), int_cZ', mul_zero, add_zero,
    setIntegral_const, smul_eq_mul, measureReal_def, cBI, Real.volume_Ioo,
    ENNReal.toReal_ofReal (sub_nonneg.mpr cBU)]

lemma outer_eq (g : ℝ → ℝ) : ∫ w in cW, g (w 0) = (∫ t in Ioo 0 cU, g t) * cU := by
  have hpi : (volume.restrict cW : Measure (Fin 2 → ℝ)) =
      Measure.pi (fun _ => volume.restrict (Ioo 0 cU)) := by
    rw [cW, volume_pi, Measure.restrict_pi_pi]
  have hfun : (fun w : Fin 2 → ℝ => g (w 0)) =
      fun w => ∏ i : Fin 2, (![g, fun _ => 1] i) (w i) := by
    funext w; simp [Fin.prod_univ_two]
  rw [hpi, hfun, integral_fintype_prod_eq_prod, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, integral_const,
    smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo, sub_zero]
  rw [ENNReal.toReal_ofReal (by norm_num [cU])]

lemma calib {gam : ℝ} (hg : GamOK gam) : ∫ θ in cW ×ˢ cBI, muF θ * Dθ gam θ = cV0 := by
  obtain ⟨C, hC⟩ := Dθ_bdd hg
  have hI : IntegrableOn (fun θ => muF θ * Dθ gam θ) (cW ×ˢ cBI) :=
    intOn_bdd ((muF_meas.mul (Dθ_meas hg)).aestronglyMeasurable) (C := cm2 * C) fun θ _ => by
      rw [abs_mul, abs_of_nonneg (muF_nonneg θ)]
      exact mul_le_mul (muF_le θ) (hC θ) (abs_nonneg _) cm2_pos.le
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hI
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hI]
  simp_rw [inner_eq]
  rw [integral_const_mul, outer_eq (fun t => fmu t * -(deriv (eta ca0 ca1 ca2 ca3) t)), one_dim]
  rw [← cm2_eq]; ring

end P8d

end CA63

-- ===== part P8e =====
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open ContextualAuctions.RevEquiv

namespace CA63

section P8e

/-! ### P8e: the fixed-point property `μ ∈ C₀*(μ)` -/

variable {gam : ℝ}

lemma hprof (hg : GamOK gam) : Prof (hG gam) := by
  have hg0 : 0 ≤ gam := by linarith [hg.big]
  refine hG_prof hg0 hg.del (fun w hw hw0 B => ?_)
  rw [abs_mul]
  have h1 := kk_bound hg0 hg.del hw hw0
  have h2 := hg.k2 B
  calc |kk gam w| * |deriv cZ B| ≤ 25 * cdel gam * |deriv cZ B| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ 1 := by linarith

/-- the true type law -/
noncomputable abbrev GG (gam : ℝ) : Measure ((Fin 2 → ℝ) × ℝ) := Gh gam (hG gam)

lemma GG_prob (hg : GamOK gam) : IsProbabilityMeasure (GG gam) :=
  Gh_prob (by linarith [hg.big]) (hprof hg)

lemma hatomG (hg : GamOK gam) :
    ∀ᵐ α ∂(mdl (GG gam)).F, ∀ y, lam (mdl (GG gam)) muF α {y} = 0 := by
  have hae : ∀ᵐ α ∂cF, α ∈ cA := by
    rw [ae_iff]; simpa [Set.compl_def] using cF_supp
  filter_upwards [hae] with α hα y
  exact lam_atom (by linarith [hg.big]) (hprof hg) hα y

lemma suppG (hg : GamOK gam) : ∀ᵐ θ ∂(mdl (GG gam)).G, θ ∈ cW ×ˢ cBI := by
  have h0 := Gh_supp gam (hG gam) (hprof hg).meas (GG gam)
  rw [theta_eq] at h0
  have h1 : (mdl (GG gam)).G (cW ×ˢ cBI)ᶜ = 0 := h0
  exact ae_iff.2 h1

lemma subgr (hg : GamOK gam) {θ : (Fin 2 → ℝ) × ℝ} (hθ : θ ∈ cW ×ˢ cBI) {t t' : ℝ}
    (ht : -1 < t) (ht' : -1 < t') :
    qDual (mdl (GG gam)) muF θ t + (t' - t) * (θ.2 - Spend (mdl (GG gam)) muF θ t) ≤
      qDual (mdl (GG gam)) muF θ t' := by
  haveI : IsProbabilityMeasure (mdl (GG gam)).G := GG_prob hg
  haveI : IsProbabilityMeasure (mdl (GG gam)).F := cF_prob
  have hw0 := hθ.1 0 (mem_univ _)
  have hw1 := hθ.1 1 (mem_univ _)
  have hU : cU ≤ 1 := by norm_num [cU]
  exact qDual_subgrad (mdl (GG gam)) muF muF_meas measurable_const
    (fun _ => show (0:ℝ) < cr0 by norm_num [cr0]) (show (2:ℕ) - 1 ≠ 0 by decide) (hatomG hg) θ
    ht ht' (mdl_val_nonneg hw0.1.le hw1.1.le)
    (mdl_val_bound hw0.1.le (hw0.2.le.trans hU) hw1.1.le (hw1.2.le.trans hU))

lemma q_int (hg : GamOK gam) {ν : (Fin 2 → ℝ) × ℝ → ℝ} (hνm : Measurable ν)
    (hν0 : ∀ θ ∈ cW ×ˢ cBI, 0 ≤ ν θ) (hν1 : ∀ θ ∈ cW ×ˢ cBI, ν θ ≤ cOmega / cBmin) :
    Integrable (fun θ : Buyer (mdl (GG gam)) => qDual (mdl (GG gam)) muF θ (ν θ))
      (mdl (GG gam)).G := by
  haveI : IsProbabilityMeasure (mdl (GG gam)).G := GG_prob hg
  haveI : IsProbabilityMeasure (mdl (GG gam)).F := cF_prob
  haveI : IsProbabilityMeasure cF := cF_prob
  let M := mdl (GG gam)
  let V : Buyer M × Context M → ℝ := fun q =>
    (1 + ν q.1) * Vopt (Phi (lam M muF q.2) (M.n - 1)) (M.r q.2) (val M q.1 q.2 / (1 + ν q.1))
  have hVm : Measurable V := by
    have h1 := Vopt_meas M muF muF_meas measurable_const
    have hval := val_meas_joint M
    exact (measurable_const.add (hνm.comp measurable_fst)).mul
      (h1.comp (measurable_snd.prodMk (hval.div (measurable_const.add (hνm.comp measurable_fst)))))
  have hF : StronglyMeasurable (fun θ : Buyer M => ∫ α, V (θ, α) ∂M.F) :=
    hVm.stronglyMeasurable.integral_prod_right'
  have hU : cU ≤ 1 := by norm_num [cU]
  have heq : (fun θ : Buyer M => qDual M muF θ (ν θ)) =ᵐ[M.G]
      fun θ => (∫ α, V (θ, α) ∂M.F) + ν θ * θ.2 := by
    filter_upwards [suppG hg] with θ hθ
    have hw0 := hθ.1 0 (mem_univ _)
    have hw1 := hθ.1 1 (mem_univ _)
    rw [qDual_eq M muF muF_meas measurable_const
      (fun _ => show (0:ℝ) < cr0 by norm_num [cr0]) (show (2:ℕ) - 1 ≠ 0 by decide) (hatomG hg) θ
      (by linarith [hν0 θ hθ]) (mdl_val_nonneg hw0.1.le hw1.1.le)
      (mdl_val_bound hw0.1.le (hw0.2.le.trans hU) hw1.1.le (hw1.2.le.trans hU))]
    rfl
  refine Integrable.congr ?_ heq.symm
  refine Integrable.of_bound (hF.aestronglyMeasurable.add
    ((hνm.mul measurable_snd).aestronglyMeasurable)) (102 + cOmega / cBmin) ?_
  filter_upwards [suppG hg] with θ hθ
  have hw0 := hθ.1 0 (mem_univ _)
  have hw1 := hθ.1 1 (mem_univ _)
  have hn0 := hν0 θ hθ
  have hn1 := hν1 θ hθ
  have hpos : 0 < 1 + ν θ := by linarith
  have hb := mdl_val_bound (G := GG gam) hw0.1.le (hw0.2.le.trans hU) hw1.1.le (hw1.2.le.trans hU)
  have hI : ‖∫ α, V (θ, α) ∂M.F‖ ≤ 102 := by
    have := norm_integral_le_of_norm_le_const (μ := M.F) (f := fun α => V (θ, α)) (C := 102) (by
      filter_upwards [hb] with α hα
      haveI := lam_prob M muF muF_meas α
      have v1 := Vopt_le (lam M muF α) (M.n - 1) (show (0:ℝ) < cr0 by norm_num [cr0])
        (val M θ α / (1 + ν θ))
      have v0 := Vopt_nonneg' (lam M muF α) (M.n - 1) cr0 (val M θ α / (1 + ν θ))
      show ‖(1 + ν θ) * Vopt (Phi (lam M muF α) (M.n - 1)) cr0 (val M θ α / (1 + ν θ))‖ ≤ 102
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpos.le v0)]
      rw [abs_div, abs_of_pos hpos] at v1
      calc (1 + ν θ) * Vopt (Phi (lam M muF α) (M.n - 1)) cr0 (val M θ α / (1 + ν θ))
          ≤ (1 + ν θ) * (|val M θ α| / (1 + ν θ)) := mul_le_mul_of_nonneg_left v1 hpos.le
        _ = |val M θ α| := by field_simp
        _ ≤ 102 := hα)
    rwa [probReal_univ, mul_one] at this
  have hB : |ν θ * θ.2| ≤ cOmega / cBmin := by
    have h2 : 0 < θ.2 := lt_trans (by norm_num [cBmin]) hθ.2.1
    have h3 : θ.2 ≤ 1 := hθ.2.2.le.trans hU
    rw [abs_of_nonneg (mul_nonneg hn0 h2.le)]
    calc ν θ * θ.2 ≤ ν θ * 1 := mul_le_mul_of_nonneg_left h3 hn0
      _ ≤ _ := by linarith
  rw [Real.norm_eq_abs]
  refine (abs_add_le _ _).trans ?_
  rw [Real.norm_eq_abs] at hI
  linarith

lemma pt_ineq (hg : GamOK gam) {ν : (Fin 2 → ℝ) × ℝ → ℝ} (hν0 : ∀ θ ∈ cW ×ˢ cBI, 0 ≤ ν θ)
    {θ : (Fin 2 → ℝ) × ℝ} (hθ : θ ∈ cW ×ˢ cBI) :
    -cc gam * ((ν θ - muF θ) * Dθ gam θ) ≤
      gden gam (hG gam) θ * (qDual (mdl (GG gam)) muF θ (ν θ) -
        qDual (mdl (GG gam)) muF θ (muF θ)) := by
  have hg0 : 0 ≤ gam := by linarith [hg.big]
  haveI : IsProbabilityMeasure (GG gam) := GG_prob hg
  have hc := cc_pos hg0
  have hgn := gden_nonneg hg0 (hprof hg) θ
  have hn := hν0 θ hθ
  have hsub := subgr hg hθ (t := muF θ) (t' := ν θ) (by linarith [muF_nonneg θ]) (by linarith)
  have hD : deriv (eta ca0 ca1 ca2 ca3) (θ.1 0) = lowDc (θ.1 0) - hiDc (θ.1 0) :=
    (etac_hasDerivAt _).deriv
  have hkey : gden gam (hG gam) θ * ((ν θ - muF θ) *
      (θ.2 - Spend (mdl (GG gam)) muF θ (muF θ))) ≤
      gden gam (hG gam) θ * (qDual (mdl (GG gam)) muF θ (ν θ) -
        qDual (mdl (GG gam)) muF θ (muF θ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hgn
  refine le_trans ?_ hkey
  by_cases hw : ca2 ≤ θ.1 0
  · have hm : muF θ = cm2 := by
      show cm2 * ramp ca1 ca2 (θ.1 0) = cm2
      rw [ramp_one zones.2.2.1 hw, mul_one]
    have hS : Spend (mdl (GG gam)) muF θ (muF θ) = Sf gam θ.1 := by
      rw [hm]; exact spend_G hg0 (hprof hg) hθ.1
    obtain ⟨hS1, -, -⟩ := Sf_range hg0 hg.del hθ.1 hw
    have hne : Sf gam θ.1 - θ.2 ≠ 0 := by
      have := hθ.2.2; linarith
    have hdh := dens_hi hθ hw hne
    have hl : lowDc (θ.1 0) = 0 := lowDc_zero (fun h => by linarith [h.2, zones.2.2.1])
    have hk : kfun gam θ.1 = kk gam θ.1 := indicator_of_mem (show θ.1 ∈ kSet from ⟨hθ.1, hw⟩) _
    rw [hS]
    have e1 : gden gam (hG gam) θ * ((ν θ - muF θ) * (θ.2 - Sf gam θ.1)) =
        (ν θ - muF θ) * ((θ.2 - Sf gam θ.1) * gden gam (hG gam) θ) := by ring
    rw [e1, hdh]
    unfold Dθ
    rw [hD, hl, hk]
    apply le_of_eq; ring
  · have hw' : θ.1 0 < ca2 := lt_of_not_ge hw
    have hlo := dens_lo (gam := gam) hθ hw'
    have hh : hiDc (θ.1 0) = 0 := hiDc_zero (fun h => hw h.1.le)
    by_cases hw1 : θ.1 0 ≤ ca1
    · have hm : muF θ = 0 := by
        show cm2 * ramp ca1 ca2 (θ.1 0) = 0
        rw [ramp_zero zones.2.2.1 hw1, mul_zero]
      have hS : Spend (mdl (GG gam)) muF θ (muF θ) = 0 := by
        rw [hm]; exact spend_low hθ.1 hw1
      rw [hS, hm, hlo]
      unfold Dθ
      rw [hD, hh]
      have hL := lowDc_nonneg (θ.1 0)
      have hB : 1 ≤ gam * θ.2 := by
        have h1 := hθ.2.1
        have h2 : (200:ℝ) * (1 / 200) ≤ gam * θ.2 :=
          mul_le_mul hg.big (by simpa [cBmin] using h1.le) (by norm_num) (by linarith)
        linarith
      have hp : 0 ≤ cc gam * ν θ * lowDc (θ.1 0) := mul_nonneg (mul_nonneg hc.le hn) hL
      nlinarith [mul_nonneg hp (sub_nonneg.2 hB)]
    · have hl : lowDc (θ.1 0) = 0 := lowDc_zero (fun h => hw1 h.2.le)
      rw [hlo, hl]
      unfold Dθ
      rw [hD, hl, hh]
      apply le_of_eq; ring

/-- the integrand of `fObj μ ν - fObj μ μ` -/
noncomputable def Fq (gam : ℝ) (ν : (Fin 2 → ℝ) × ℝ → ℝ) (θ : (Fin 2 → ℝ) × ℝ) : ℝ :=
  qDual (mdl (GG gam)) muF θ (ν θ) - qDual (mdl (GG gam)) muF θ (muF θ)

lemma hfix_main (hg : GamOK gam) {ν : (Fin 2 → ℝ) × ℝ → ℝ} (hν : ν ∈ X0 (mdl (GG gam))) :
    fObj (mdl (GG gam)) muF muF ≤ fObj (mdl (GG gam)) muF ν := by
  have hg0 : 0 ≤ gam := by linarith [hg.big]
  have hνX := hν
  obtain ⟨⟨⟨hνm, hν0⟩, hνi, hνb⟩, -⟩ := hν
  rw [theta_eq] at hν0 hνb
  have hνb' : ∀ θ ∈ cW ×ˢ cBI, ν θ ≤ cOmega / cBmin := fun θ hθ => by
    have := (hνb θ hθ).2; rwa [mdl_omega] at this
  have qi1 := q_int hg hνm hν0 hνb'
  have qi0 := q_int hg muF_meas (fun θ _ => muF_nonneg θ) (fun θ _ => (muF_le θ).trans cm2_le)
  have hI : Integrable (Fq gam ν) (GG gam) := qi1.sub qi0
  suffices h : 0 ≤ ∫ θ, Fq gam ν θ ∂(GG gam) by
    unfold fObj
    rw [← sub_nonneg, ← integral_sub qi1 qi0]
    exact h
  set gd := gden gam (hG gam) with hgd
  have hgm : Measurable gd := gden_meas gam (hprof hg).meas
  have hgn : ∀ θ, 0 ≤ gd θ := gden_nonneg hg0 (hprof hg)
  have hf : Measurable (fun θ => ENNReal.ofReal (gd θ)) := ENNReal.measurable_ofReal.comp hgm
  have hlt : ∀ᵐ θ ∂(volume : Measure ((Fin 2 → ℝ) × ℝ)), ENNReal.ofReal (gd θ) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hE : ∫ θ, Fq gam ν θ ∂(GG gam) = ∫ θ, (ENNReal.ofReal (gd θ)).toReal • Fq gam ν θ :=
    integral_withDensity_eq_integral_toReal_smul hf hlt (Fq gam ν)
  have hI2 : Integrable (fun θ => (ENNReal.ofReal (gd θ)).toReal • Fq gam ν θ) :=
    (integrable_withDensity_iff_integrable_smul' hf hlt).1 hI
  simp only [ENNReal.toReal_ofReal (hgn _), smul_eq_mul] at hE hI2
  rw [hE]
  set S := cW ×ˢ cBI with hS
  have hSm : MeasurableSet S := cW_meas.prod cBI_meas
  obtain ⟨C, hC⟩ := Dθ_bdd hg
  have hνD : IntegrableOn (fun θ => ν θ * Dθ gam θ) S :=
    intOn_bdd ((hνm.mul (Dθ_meas hg)).aestronglyMeasurable) (C := cOmega / cBmin * C)
      fun θ hθ => by
        rw [abs_mul, abs_of_nonneg (hν0 θ hθ)]
        exact mul_le_mul (hνb' θ hθ) (hC θ) (abs_nonneg _)
          (le_trans (hν0 θ hθ) (hνb' θ hθ))
  have hmD : IntegrableOn (fun θ => muF θ * Dθ gam θ) S :=
    intOn_bdd ((muF_meas.mul (Dθ_meas hg)).aestronglyMeasurable) (C := cm2 * C) fun θ _ => by
      rw [abs_mul, abs_of_nonneg (muF_nonneg θ)]
      exact mul_le_mul (muF_le θ) (hC θ) (abs_nonneg _) cm2_pos.le
  have hRi : Integrable (S.indicator fun θ => -cc gam * ((ν θ - muF θ) * Dθ gam θ)) := by
    rw [integrable_indicator_iff hSm]
    have := (hνD.sub hmD).const_mul (-cc gam)
    refine this.congr (Eventually.of_forall fun θ => ?_)
    simp only [Pi.sub_apply]; ring
  have hmono : ∫ θ, S.indicator (fun θ => -cc gam * ((ν θ - muF θ) * Dθ gam θ)) θ ≤
      ∫ θ, gd θ * Fq gam ν θ := by
    refine integral_mono hRi hI2 fun θ => ?_
    by_cases hθ : θ ∈ S
    · rw [indicator_of_mem hθ]; exact pt_ineq hg hν0 hθ
    · rw [indicator_of_notMem hθ]
      have : gd θ = 0 := by rw [hgd, gden, indicator_of_notMem hθ]
      rw [this, zero_mul]
  refine le_trans ?_ hmono
  rw [integral_indicator hSm]
  have e : (fun θ => -cc gam * ((ν θ - muF θ) * Dθ gam θ)) =
      fun θ => -cc gam * (ν θ * Dθ gam θ - muF θ * Dθ gam θ) := by
    funext θ; ring
  rw [e, integral_const_mul, integral_sub hνD hmD, calib hg]
  have h1 := nu_side hg (GG gam) hνX
  have h2 := cc_pos hg0
  nlinarith

lemma hfix (hg : GamOK gam) : muF ∈ C0star (mdl (GG gam)) muF :=
  ⟨muF_X0 _, fun ν hν => hfix_main hg hν⟩

end P8e

end CA63

-- ===== part P9 =====
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open ContextualAuctions.RevEquiv

namespace CA63

section P9

/-! ### P9: high-zone buyers overspend their budget under `Ψ^μ` (second price) -/

variable {gam : ℝ}

lemma cdel_pos {gam : ℝ} (hg : 0 ≤ gam) : 0 < cdel gam := by
  unfold cdel
  exact mul_pos (mul_pos (cc_pos hg) (by norm_num [cU])) (by linarith [cLbar_bounds.1])

lemma margK (hg : 0 ≤ gam) : margM gam kSet = ENNReal.ofReal (cdel gam) := by
  rw [margM, withDensity_apply _ kSet_meas, ← lintegral_indicator kSet_meas]
  have hc : Continuous (fun w : Fin 2 → ℝ => cc gam * hiDc (w 0) * cLbar) :=
    (continuous_const.mul (hiDc_cont.comp (continuous_apply 0))).mul continuous_const
  have hK : IsCompact (Set.pi univ (fun _ : Fin 2 => Icc (0:ℝ) cU)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hint : IntegrableOn (fun w : Fin 2 → ℝ => cc gam * hiDc (w 0) * cLbar) cW :=
    (hc.continuousOn.integrableOn_compact hK).mono_set
      (Set.pi_mono (fun _ _ => Ioo_subset_Icc_self))
  have hnn : 0 ≤ᵐ[volume.restrict cW] (fun w : Fin 2 → ℝ => cc gam * hiDc (w 0) * cLbar) :=
    Eventually.of_forall fun w => mul_nonneg (mul_nonneg (cc_pos hg).le (hiDc_nonneg _))
      (by linarith [cLbar_bounds.1])
  have hpt : ∀ w, kSet.indicator (cW.indicator fun w => ENNReal.ofReal
      (cc gam * (gam * lowDc (w 0) * (cU - cBmin) + hiDc (w 0) * cLbar))) w =
      cW.indicator (fun w => ENNReal.ofReal (cc gam * hiDc (w 0) * cLbar)) w := by
    intro w
    by_cases hw : w ∈ cW
    · by_cases h2 : ca2 ≤ w 0
      · rw [indicator_of_mem (show w ∈ kSet from ⟨hw, h2⟩), indicator_of_mem hw,
          indicator_of_mem hw,
          lowDc_zero (fun h => by linarith [h.2, zones.2.2.1])]
        congr 1; ring
      · rw [indicator_of_notMem (fun h => h2 h.2), indicator_of_mem hw,
          hiDc_zero (fun h => h2 h.1.le)]
        simp
    · rw [indicator_of_notMem (fun h => hw h.1), indicator_of_notMem hw]
  simp_rw [hpt]
  rw [lintegral_indicator cW_meas, ← ofReal_integral_eq_lintegral_ofReal hint hnn,
    int_cW (fun x => cc gam * hiDc x * cLbar), integral_mul_const, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num [cU] : (0:ℝ) ≤ cU), int_hiDc]
  congr 1; unfold cdel; ring

lemma EEm_meas (M : Model) [IsProbabilityMeasure M.G] (μ : Buyer M → ℝ) (hμ : Measurable μ)
    (A : Set (Context M)) (hA : MeasurableSet A) (c : ℝ) :
    MeasurableSet (Prod.fst ⁻¹' A ∩
      ⋂ i, {ω : Context M × (Fin (M.n - 1) → Buyer M) | paced M μ (ω.2 i) ω.1 < c}) := by
  refine (measurable_fst hA).inter (MeasurableSet.iInter fun i => ?_)
  have hs : Measurable (fun ω : Context M × (Fin (M.n - 1) → Buyer M) => (ω.2 i, ω.1)) :=
    ((measurable_pi_apply i).comp measurable_snd).prodMk measurable_fst
  have h1 : Measurable (fun ω : Context M × (Fin (M.n - 1) → Buyer M) => paced M μ (ω.2 i) ω.1) :=
    by simpa only [Function.comp_def] using (paced_meas_joint M μ hμ).comp hs
  exact measurableSet_lt h1 measurable_const

/-- the event that every competitor is paced below the reserve -/
def EE (G : Measure ((Fin 2 → ℝ) × ℝ)) :
    Set (Context (mdl G) × (Fin ((mdl G).n - 1) → Buyer (mdl G))) :=
  Prod.fst ⁻¹' cA ∩ ⋂ i, {ω | paced (mdl G) muF (ω.2 i) ω.1 < cr0}

section Gen

variable (G : Measure ((Fin 2 → ℝ) × ℝ)) [IsProbabilityMeasure G]

lemma EE_meas : MeasurableSet (EE G) := by
  haveI : IsProbabilityMeasure (mdl G).G := ‹IsProbabilityMeasure G›
  exact EEm_meas (mdl G) muF muF_meas cA
    (show MeasurableSet (cA : Set (Fin 2 → ℝ)) from measurableSet_Icc) cr0

lemma pay_pt {θ : (Fin 2 → ℝ) × ℝ} (hθ : θ ∈ cW ×ˢ cBI) (hw : ca2 ≤ θ.1 0)
    (ω : Context (mdl G) × (Fin ((mdl G).n - 1) → Buyer (mdl G))) :
    (EE G).indicator (fun _ => cr0) ω ≤
      payStd (mdl G) (spFam _) (Psi (mdl G) (spFam _) muF) (Psi (mdl G) (spFam _) muF θ) ω := by
  have hm : muF θ = cm2 := by
    show cm2 * ramp ca1 ca2 (θ.1 0) = cm2
    rw [ramp_one zones.2.2.1 hw, mul_one]
  by_cases hω : ω ∈ EE G
  · rw [indicator_of_mem hω]
    have hω1 : ω.1 ∈ cA := hω.1
    have hω2 : ∀ i, paced (mdl G) muF (ω.2 i) ω.1 < cr0 := fun i => mem_iInter.1 hω.2 i
    have hb : cr0 ≤ paced (mdl G) muF θ ω.1 := by
      unfold paced
      rw [hm]
      exact le_of_le_of_eq (high_paced_ge hw (hθ.1 1 (mem_univ _)).1 hω1)
        (congrArg (fun v => v / (1 + cm2)) (mdl_val G θ ω.1)).symm
    have e : payStd (mdl G) (spFam _) (Psi (mdl G) (spFam _) muF)
        (Psi (mdl G) (spFam _) muF θ) ω = spPay (mdl G) ω.1
          (paced (mdl G) muF θ ω.1) (fun i => paced (mdl G) muF (ω.2 i) ω.1) := rfl
    have hc : (mdl G).r ω.1 ≤ paced (mdl G) muF θ ω.1 ∧
        ∀ i, paced (mdl G) muF (ω.2 i) ω.1 ≤ paced (mdl G) muF θ ω.1 :=
      ⟨hb, fun i => (hω2 i).le.trans hb⟩
    rw [e]
    unfold spPay
    rw [if_pos hc]
    exact le_max_left cr0 _
  · rw [indicator_of_notMem hω]
    exact spPay_nonneg' _ (fun _ => show (0:ℝ) < cr0 by norm_num [cr0]) _ _ _

lemma PE_ge {δ : ℝ}
    (hlow : ∀ α ∈ cA, 1 - δ ≤ (lam (mdl G) muF α (Iio cr0)).toReal) :
    ENNReal.ofReal (1 - δ) ≤ P (mdl G) (EE G) := by
  haveI : IsProbabilityMeasure (mdl G).G := ‹IsProbabilityMeasure G›
  haveI : IsProbabilityMeasure (mdl G).F := cF_prob
  have hpm := paced_meas_joint (mdl G) muF muF_meas
  have hae : ∀ᵐ α ∂(mdl G).F, α ∈ cA := by
    show ∀ᵐ α ∂cF, α ∈ cA
    rw [ae_iff]; simpa [Set.compl_def] using cF_supp
  haveI : SigmaFinite (Measure.pi fun _ : Fin ((mdl G).n - 1) => (mdl G).G) :=
    Measure.pi.sigmaFinite _
  rw [P, Measure.prod_apply (EE_meas G)]
  calc ENNReal.ofReal (1 - δ) = ∫⁻ α, ENNReal.ofReal (1 - δ) ∂(mdl G).F := by
          rw [lintegral_const, measure_univ, mul_one]
    _ ≤ _ := by
        refine lintegral_mono_ae (hae.mono fun α hα => ?_)
        have hsec : Prod.mk α ⁻¹' EE G = Set.pi univ
            (fun _ => {θ' | paced (mdl G) muF θ' α < cr0}) := by
          ext f
          show (α, f) ∈ EE G ↔ f ∈ Set.pi univ _
          constructor
          · intro h i _; exact Set.mem_iInter.1 h.2 i
          · intro h; exact ⟨hα, Set.mem_iInter.2 fun i => h i (Set.mem_univ i)⟩
        refine le_of_le_of_eq ?_ (congrArg (Measure.pi fun _ : Fin ((mdl G).n - 1) => (mdl G).G)
          hsec).symm
        rw [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have hmeas : Measurable (fun θ' => paced (mdl G) muF θ' α) :=
          by simpa only [Function.comp_def, id_eq] using hpm.comp (measurable_id.prodMk measurable_const)
        have hl : (mdl G).G {θ' | paced (mdl G) muF θ' α < cr0} = lam (mdl G) muF α (Iio cr0) :=
          (Measure.map_apply hmeas measurableSet_Iio).symm
        rw [hl]
        have h1 : ENNReal.ofReal (1 - δ) ≤ lam (mdl G) muF α (Iio cr0) :=
          ENNReal.ofReal_le_of_le_toReal (hlow α hα)
        exact h1.trans (le_of_eq (pow_one _).symm)

lemma pay_gt {δ : ℝ} (hδ : δ ≤ 1 / 1000)
    (hlow : ∀ α ∈ cA, 1 - δ ≤ (lam (mdl G) muF α (Iio cr0)).toReal)
    {θ : (Fin 2 → ℝ) × ℝ} (hθ : θ ∈ cW ×ˢ cBI) (hw : ca2 ≤ θ.1 0)
    (hint : Integrable (payStd (mdl G) (spFam _) (Psi (mdl G) (spFam _) muF)
      (Psi (mdl G) (spFam _) muF θ)) (P (mdl G))) :
    θ.2 < paymentStd (mdl G) (spFam _) (Psi (mdl G) (spFam _) muF)
      (Psi (mdl G) (spFam _) muF θ) := by
  haveI : IsProbabilityMeasure (mdl G).G := ‹IsProbabilityMeasure G›
  haveI : IsProbabilityMeasure (mdl G).F := cF_prob
  haveI : IsProbabilityMeasure (P (mdl G)) := by unfold P; infer_instance
  have hmono := integral_mono ((integrable_const cr0).indicator (EE_meas G)) hint
    (pay_pt G hθ hw)
  rw [integral_indicator_const _ (EE_meas G), smul_eq_mul] at hmono
  have hPr : 1 - δ ≤ (P (mdl G)).real (EE G) := by
    rw [measureReal_def]
    have := ENNReal.toReal_mono (measure_ne_top _ _) (PE_ge G hlow)
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  have hB : θ.2 < cU := hθ.2.2
  have hr : (0:ℝ) ≤ cr0 := by norm_num [cr0]
  have h1 : (1 - δ) * cr0 ≤ (P (mdl G)).real (EE G) * cr0 :=
    mul_le_mul_of_nonneg_right hPr hr
  have h2 : cU < (1 - δ) * cr0 := by
    have e1 : cU = 1 / 100 := rfl
    have e2 : cr0 = 1 / 50 := rfl
    rw [e1, e2]; linarith
  unfold paymentStd
  linarith

end Gen

lemma not_symeq (hg : GamOK gam) :
    ¬ IsSymEq (mdl (GG gam)) (spFam _) (Psi (mdl (GG gam)) (spFam _) muF) := by
  rintro ⟨-, hae⟩
  have hg0 : 0 ≤ gam := by linarith [hg.big]
  have hpos : (mdl (GG gam)).G (Prod.fst ⁻¹' kSet) ≠ 0 := by
    have e : (GG gam) (Prod.fst ⁻¹' kSet) = ENNReal.ofReal (cdel gam) := by
      rw [← Measure.map_apply measurable_fst kSet_meas, marg_eq hg0 (hprof hg), margK hg0]
    show (GG gam) (Prod.fst ⁻¹' kSet) ≠ 0
    rw [e]; exact (ENNReal.ofReal_pos.2 (cdel_pos hg0)).ne'
  obtain ⟨θ, hθK, hθS, hopt⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae ((suppG hg).and hae))
  obtain ⟨⟨-, -, hint⟩, hpay, -⟩ := hopt
  haveI : IsProbabilityMeasure (GG gam) := GG_prob hg
  have := pay_gt (GG gam) hg.del (fun α hα => low_mass hg0 (hprof hg) hα) hθS hθK.2 hint
  linarith

end P9

end CA63

open ContextualAuctions.RevEquiv MeasureTheory Classical CA63 in
theorem solution : ¬ (∀ (M : Model) (hM : M.Standing) (fam : StdFamily M) (hfam : fam.Valid M)
    (μ : Buyer M → ℝ) (hμ : μ ∈ X0 M) (hfix : μ ∈ C0star M μ)
    (hΨ : Measurable (Function.uncurry (Psi M fam μ))),
    IsSymEq M fam (Psi M fam μ) ∧
    ∀ θ ∈ Theta M,
      ∫⁻ ω, ENNReal.ofReal (payStd M fam (Psi M fam μ) (Psi M fam μ θ) ω) ∂P M =
        ∫⁻ ω, ENNReal.ofReal
          (if wins M (beta M μ) (beta M μ θ) ω then beta M μ θ ω.1 else 0) ∂P M) := by
  intro h
  obtain ⟨gam, hg⟩ := gam_exists
  haveI : IsProbabilityMeasure (GG gam) := GG_prob hg
  have hM : (mdl (GG gam)).Standing :=
    mdl_standing (GG gam) (Gh_ac gam (hG gam)) (Gh_supp gam (hG gam) (hprof hg).meas (GG gam))
  have hfam := sp_valid (mdl (GG gam)) measurable_const (fun _ => show (0:ℝ) < cr0 by norm_num [cr0])
  have hΨ : Measurable (Function.uncurry (Psi (mdl (GG gam)) (spFam _) muF)) :=
    paced_meas_joint (mdl (GG gam)) muF muF_meas
  exact not_symeq hg (h (mdl (GG gam)) hM (spFam _) hfam muF (muF_X0 _) (hfix hg) hΨ).1
