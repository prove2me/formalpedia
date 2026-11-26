-- Prove2me | solution 1 for DiagonalizationGeneral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:33.727738+00:00
-- url     : https://prove2.me/submissions/612e0de4-95b1-4bf6-8e8f-996eb8b339b8

import Definitions.Def_Tablet_MetricCurrent1
import Definitions.Def_Tablet_PSFamily
import Definitions.Def_Tablet_LipschitzSeparable
import Definitions.Def_Tablet_CurrentFormAddF
import Definitions.Def_Tablet_CurrentTwoFormEstimate
import Definitions.Def_Tablet_CurrentFormAddPi
import Definitions.Def_Tablet_PiBoundsF
import Definitions.Def_Tablet_PiBoundsPi
import Definitions.Def_Tablet_PsiVanishes
import Definitions.Def_Tablet_CurrentContinuousF
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_DiagonalizationGeneral
import Theorems.Thm_CurrentContinuousF
import Theorems.Thm_CurrentFormAddF
import Theorems.Thm_CurrentFormAddPi
import Theorems.Thm_CurrentTwoFormEstimate
import Theorems.Thm_LipschitzSeparable
import Theorems.Thm_PiBoundsF
import Theorems.Thm_PiBoundsPi
import Theorems.Thm_PsiVanishes


set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal
open scoped NNReal
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (T : MetricCurrent1 E) (F : PSFamily T.toFun)
    (D : Set E) (hDc : D.Countable) (hDne : D.Nonempty) (hDd : Dense D) :
    ∃ om : ℕ → Form1 E,
      ∀ (n : ℕ → ℕ) (γ : ℕ → ℕ → Curve E),
        (∀ l : ℕ, 0 < n l) →
        (∀ l : ℕ, 1 ≤ l → ∀ i < n l, (γ l i).len = (l : ℝ)) →
        (∀ k : ℕ, Tendsto (fun l : ℕ =>
            (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
              ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) (om k))
            atTop (nhds (T.toFun (om k)))) →
        (∀ m : ℕ, 1 ≤ m → ∀ Q : Finset E, Q.Nonempty → (Q : Set E) ⊆ D →
          ∀ ε C : ℚ, 0 < ε → 0 < C →
            Tendsto (fun l : ℕ => (1 / ((n l : ℝ) * l)) *
                ∑ i ∈ Finset.range (n l), psi (m * l) Q (ε : ℝ) (C : ℝ) (γ l i))
              atTop (nhds ((F.massMeasure Set.univ).toReal⁻¹ *
                ∫ c, psi m Q (ε : ℝ) (C : ℝ) c ∂(F.eta 1)))
            ∧ Tendsto (fun l : ℕ => (1 / ((n l : ℝ) * l)) *
                ∑ i ∈ Finset.range (n l), psiTilde (m * l) Q (ε : ℝ) (C : ℝ) (γ l i))
              atTop (nhds ((F.massMeasure Set.univ).toReal⁻¹ *
                ∫ c, psiTilde m Q (ε : ℝ) (C : ℝ) c ∂(F.eta 1)))) →
        ∀ ω : Form1 E, Tendsto (fun l : ℕ =>
            (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
              ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) ω)
            atTop (nhds (T.toFun ω)) := by
-- BODY
  classical
  obtain ⟨P, B, L, hPBL, happrox⟩ := LipschitzSeparable (E := E)
  obtain ⟨om, hom_f, hom_pi⟩ : ∃ om : ℕ → Form1 E,
      (∀ p q : ℕ, (om (Nat.pair p q)).f = P p) ∧ (∀ p q : ℕ, (om (Nat.pair p q)).pi = P q) := by
    refine ⟨fun a =>
      { f := P (Nat.unpair a).1, fBound := B (Nat.unpair a).1,
        f_bounded := (hPBL (Nat.unpair a).1).1, fLip := L (Nat.unpair a).1,
        f_lipschitz := (hPBL (Nat.unpair a).1).2,
        pi := P (Nat.unpair a).2, piLip := L (Nat.unpair a).2,
        pi_lipschitz := (hPBL (Nat.unpair a).2).2 }, ?_, ?_⟩ <;>
      intro p q <;> simp [Nat.unpair_pair]
  refine ⟨om, ?_⟩
  intro n γ hnpos hlen hI hII ω
  -- Step 1: the degenerate branch `F.massMeasure univ = 0`.
  haveI hfinM := F.massMeasure_finite
  haveI hfinEta : IsFiniteMeasure (F.eta 1) := F.finite 1
  by_cases hM0 : (F.massMeasure Set.univ).toReal = 0
  · have hmu0 : F.massMeasure Set.univ = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).mp hM0 with h | h
      · exact h
      · exact absurd h (measure_ne_top _ _)
    have hmm := (F.massMarginal 1 le_rfl (fun _ => (1 : ℝ≥0∞)) measurable_const).1
    simp only [MeasureTheory.lintegral_const, one_mul] at hmm
    have heta : F.eta 1 = 0 := by
      rw [← MeasureTheory.Measure.measure_univ_eq_zero, ← hmm, hmu0]
    have hTω : T.toFun ω = 0 := by
      rw [F.weakLength 1 le_rfl ω, heta]
      simp
    rw [hM0, hTω]
    simp only [zero_div, zero_mul]
    exact tendsto_const_nhds
  have hMpos : 0 < (F.massMeasure Set.univ).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hM0)
  set M : ℝ := (F.massMeasure Set.univ).toReal with hMdef
  have hMne : M ≠ 0 := ne_of_gt hMpos
  -- Step 2: the rational bound `C`.
  set M0 : ℝ := max (max ((ω.fBound : ℝ)) ((ω.fLip : ℝ))) ((ω.piLip : ℝ)) with hM0def
  have hb1 : (ω.fBound : ℝ) ≤ M0 := le_max_of_le_left (le_max_left _ _)
  have hb2 : (ω.fLip : ℝ) ≤ M0 := le_max_of_le_left (le_max_right _ _)
  have hb3 : (ω.piLip : ℝ) ≤ M0 := le_max_right _ _
  have hM0nn : (0 : ℝ) ≤ M0 := le_trans (NNReal.coe_nonneg _) hb1
  set Cq : ℚ := ((⌈M0⌉ : ℤ) : ℚ) + 1 with hCqdef
  have hCqR : ((Cq : ℚ) : ℝ) = ((⌈M0⌉ : ℤ) : ℝ) + 1 := by rw [hCqdef]; push_cast; ring
  have hceil : M0 ≤ ((⌈M0⌉ : ℤ) : ℝ) := Int.le_ceil M0
  have hCpos : (0 : ℝ) < ((Cq : ℚ) : ℝ) := by rw [hCqR]; linarith
  have hCqpos : (0 : ℚ) < Cq := by exact_mod_cast hCpos
  have hfBC : (ω.fBound : ℝ) ≤ ((Cq : ℚ) : ℝ) := by rw [hCqR]; linarith
  have hfLC : (ω.fLip : ℝ) ≤ ((Cq : ℚ) : ℝ) := by rw [hCqR]; linarith
  have hpLC : (ω.piLip : ℝ) ≤ ((Cq : ℚ) : ℝ) := by rw [hCqR]; linarith
  -- reduce to the `ε`-`N` form of the limit
  rw [Metric.tendsto_atTop]
  intro θ' hθ'
  set θ : ℝ := θ' / 4 with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; linarith
  -- Step 3: an admissible index from `PsiVanishes`.
  obtain ⟨m, Q, ε, hm, hQne, hQD, hεpos, hint1, hint2, hsum⟩ :=
    PsiVanishes D hDc hDne hDd ((Cq : ℚ) : ℝ) hCpos 1 (F.eta 1) (F.lengthExactly 1 le_rfl) θ hθpos
  have hεR : (0 : ℝ) < ((ε : ℚ) : ℝ) := by exact_mod_cast hεpos
  -- Step 4: the two approximating subsequences.
  obtain ⟨φf, hφfLip, hφfconv, hφfBd⟩ := happrox ω.f ω.fLip ω.f_lipschitz
  obtain ⟨φp, hφpLip, hφpconv, -⟩ := happrox ω.pi ω.piLip ω.pi_lipschitz
  have hfkB : ∀ k x, |P (φf k) x| ≤ (ω.fBound : ℝ) := hφfBd ω.fBound ω.f_bounded
  set Wk : ℕ → Form1 E := fun k =>
    { f := P (φf k), fBound := ω.fBound, f_bounded := hfkB k,
      fLip := ω.fLip, f_lipschitz := hφfLip k,
      pi := ω.pi, piLip := ω.piLip, pi_lipschitz := ω.pi_lipschitz } with hWkdef
  set Wkj : ℕ → ℕ → Form1 E := fun k j =>
    { f := P (φf k), fBound := ω.fBound, f_bounded := hfkB k,
      fLip := ω.fLip, f_lipschitz := hφfLip k,
      pi := P (φp j), piLip := ω.piLip, pi_lipschitz := hφpLip j } with hWkjdef
  -- Step 5: one good pair `(k, j)`.
  have hTf : Tendsto (fun k => T.toFun (Wk k)) atTop (nhds (T.toFun ω)) :=
    CurrentContinuousF T ω.f ω.fBound ω.f_bounded ω.fLip ω.f_lipschitz ω.pi ω.piLip
      ω.pi_lipschitz (fun k => P (φf k)) (fun _ => ω.fBound) hfkB (fun _ => ω.fLip) hφfLip
      ω.fBound (fun _ => le_rfl) hφfconv
  have hkev : ∀ᶠ k in atTop, (∀ q ∈ Q, |ω.f q - P (φf k) q| ≤ ((ε : ℚ) : ℝ))
      ∧ |T.toFun (Wk k) - T.toFun ω| < θ / 2 := by
    refine Filter.Eventually.and ?_ ?_
    · refine (Finset.eventually_all Q).mpr ?_
      intro q _
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hφfconv q) ((ε : ℚ) : ℝ) hεR
      refine Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
      have h := hN k hk
      rw [Real.dist_eq] at h
      rw [abs_sub_comm]
      exact h.le
    · obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hTf (θ / 2) (by linarith)
      refine Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
      have h := hN k hk
      rwa [Real.dist_eq] at h
  obtain ⟨k, hkQ, hkT⟩ := hkev.exists
  have hTpi : Tendsto (fun j => T.toFun (Wkj k j)) atTop (nhds (T.toFun (Wk k))) :=
    T.continuous_pi (P (φf k)) ω.fBound (hfkB k) ω.fLip (hφfLip k) ω.pi ω.piLip ω.pi_lipschitz
      (fun j => P (φp j)) (fun _ => ω.piLip) hφpLip ω.piLip (fun _ => le_rfl) hφpconv
  have hjev : ∀ᶠ j in atTop, (∀ q ∈ Q, |ω.pi q - P (φp j) q| ≤ ((ε : ℚ) : ℝ))
      ∧ |T.toFun (Wkj k j) - T.toFun (Wk k)| < θ / 2 := by
    refine Filter.Eventually.and ?_ ?_
    · refine (Finset.eventually_all Q).mpr ?_
      intro q _
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hφpconv q) ((ε : ℚ) : ℝ) hεR
      refine Filter.eventually_atTop.mpr ⟨N, fun j hj => ?_⟩
      have h := hN j hj
      rw [Real.dist_eq] at h
      rw [abs_sub_comm]
      exact h.le
    · obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hTpi (θ / 2) (by linarith)
      refine Filter.eventually_atTop.mpr ⟨N, fun j hj => ?_⟩
      have h := hN j hj
      rwa [Real.dist_eq] at h
  obtain ⟨j, hjQ, hjT⟩ := hjev.exists
  have h51 : |T.toFun (Wkj k j) - T.toFun ω| < θ := by
    have htri := abs_sub_le (T.toFun (Wkj k j)) (T.toFun (Wk k)) (T.toFun ω)
    linarith
  -- Step 6: identifying `om (pair (φf k) (φp j))` with `Wkj k j`.
  have homf : (om (Nat.pair (φf k) (φp j))).f = (Wkj k j).f := hom_f _ _
  have hompi : (om (Nat.pair (φf k) (φp j))).pi = (Wkj k j).pi := hom_pi _ _
  have hccEq : ∀ c : Curve E,
      curveCurrent c (om (Nat.pair (φf k) (φp j))) = curveCurrent c (Wkj k j) := by
    intro c
    show (∫ t in (0 : ℝ)..c.len, (om (Nat.pair (φf k) (φp j))).f (c.toFun t)
          * deriv ((om (Nat.pair (φf k) (φp j))).pi ∘ c.toFun) t)
        = ∫ t in (0 : ℝ)..c.len, (Wkj k j).f (c.toFun t) * deriv ((Wkj k j).pi ∘ c.toFun) t
    rw [homf, hompi]
  have hTEq : T.toFun (om (Nat.pair (φf k) (φp j))) = T.toFun (Wkj k j) := by
    have h := T.smul_pi (Wkj k j) (om (Nat.pair (φf k) (φp j))) 1 homf
      (fun x => by rw [hompi]; ring)
    rw [h, one_mul]
  have h61 : Tendsto (fun l : ℕ => M / ((n l : ℝ) * l) *
      ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) (Wkj k j)) atTop
      (nhds (T.toFun (Wkj k j))) := by
    have h := hI (Nat.pair (φf k) (φp j))
    rw [hTEq] at h
    refine h.congr (fun l => ?_)
    congr 1
    exact Finset.sum_congr rfl (fun i _ => hccEq (γ l i))
  -- Steps 7-8: the per-curve estimate, averaged.
  have hstep8 : ∀ l : ℕ, 1 ≤ l →
      |M / ((n l : ℝ) * l) * ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) ω
        - M / ((n l : ℝ) * l) * ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) (Wkj k j)|
      ≤ M * ((1 / ((n l : ℝ) * l)) *
              ∑ i ∈ Finset.range (n l), psiTilde (m * l) Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) (γ l i)
            + (1 / ((n l : ℝ) * l)) *
              ∑ i ∈ Finset.range (n l), psi (m * l) Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) (γ l i)) := by
    intro l hl
    have hml : 1 ≤ m * l := by simpa using Nat.mul_le_mul hm hl
    have hper : ∀ i : ℕ, |curveCurrent (γ l i) ω - curveCurrent (γ l i) (Wkj k j)|
        ≤ psiTilde (m * l) Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) (γ l i)
          + psi (m * l) Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) (γ l i) := by
      intro i
      exact CurrentTwoFormEstimate (γ l i) (m * l) hml Q hQne ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ)
        hεR hCpos ω (Wk k) (Wkj k j) rfl rfl hfBC hfBC hfLC hfLC hpLC hpLC hpLC hkQ hjQ
    have hMnn : (0 : ℝ) ≤ M / ((n l : ℝ) * l) := div_nonneg hMpos.le (by positivity)
    have h1 : |∑ i ∈ Finset.range (n l),
          (curveCurrent (γ l i) ω - curveCurrent (γ l i) (Wkj k j))|
        ≤ ∑ i ∈ Finset.range (n l),
            (psiTilde (m * l) Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) (γ l i)
              + psi (m * l) Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) (γ l i)) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hper i))
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at h1
    calc |M / ((n l : ℝ) * l) * ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) ω
            - M / ((n l : ℝ) * l) * ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) (Wkj k j)|
        = M / ((n l : ℝ) * l) * |(∑ i ∈ Finset.range (n l), curveCurrent (γ l i) ω)
            - ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) (Wkj k j)| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hMnn]
      _ ≤ M / ((n l : ℝ) * l) *
            ((∑ i ∈ Finset.range (n l), psiTilde (m * l) Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) (γ l i))
              + ∑ i ∈ Finset.range (n l), psi (m * l) Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) (γ l i)) :=
          mul_le_mul_of_nonneg_left h1 hMnn
      _ = M * ((1 / ((n l : ℝ) * l)) *
              ∑ i ∈ Finset.range (n l), psiTilde (m * l) Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) (γ l i)
            + (1 / ((n l : ℝ) * l)) *
              ∑ i ∈ Finset.range (n l), psi (m * l) Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) (γ l i)) := by
          ring
  obtain ⟨hIIpsi, hIIpsiT⟩ := hII m hm Q hQne hQD ε Cq hεpos hCqpos
  have hconvSum : Tendsto (fun l : ℕ => M * ((1 / ((n l : ℝ) * l)) *
        ∑ i ∈ Finset.range (n l), psiTilde (m * l) Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) (γ l i)
      + (1 / ((n l : ℝ) * l)) *
        ∑ i ∈ Finset.range (n l), psi (m * l) Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) (γ l i))) atTop
      (nhds (M * (M⁻¹ * (∫ c, psiTilde m Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) c ∂(F.eta 1))
        + M⁻¹ * ∫ c, psi m Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) c ∂(F.eta 1)))) :=
    Filter.Tendsto.const_mul M (hIIpsiT.add hIIpsi)
  have hval : M * (M⁻¹ * (∫ c, psiTilde m Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) c ∂(F.eta 1))
        + M⁻¹ * ∫ c, psi m Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) c ∂(F.eta 1))
      = (∫ c, psi m Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) c ∂(F.eta 1))
        + ∫ c, psiTilde m Q ((ε : ℚ) : ℝ) ((Cq : ℚ) : ℝ) c ∂(F.eta 1) := by
    field_simp
    ring
  rw [hval] at hconvSum
  have hev8 := hconvSum.eventually_lt_const hsum
  have hev9 : ∀ᶠ l : ℕ in atTop,
      |M / ((n l : ℝ) * l) * ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) (Wkj k j)
        - T.toFun (Wkj k j)| < θ := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h61 θ hθpos
    refine Filter.eventually_atTop.mpr ⟨N, fun l hl => ?_⟩
    have h := hN l hl
    rwa [Real.dist_eq] at h
  -- Step 9: assembling.
  have hfinal : ∀ᶠ l : ℕ in atTop,
      dist (M / ((n l : ℝ) * l) * ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) ω)
        (T.toFun ω) < θ' := by
    filter_upwards [hev8, hev9, Filter.eventually_ge_atTop 1] with l h8 h9 hl1
    rw [Real.dist_eq]
    have h8' := hstep8 l hl1
    have ht1 := abs_sub_le (M / ((n l : ℝ) * l) * ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) ω)
      (M / ((n l : ℝ) * l) * ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) (Wkj k j))
      (T.toFun ω)
    have ht2 := abs_sub_le
      (M / ((n l : ℝ) * l) * ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) (Wkj k j))
      (T.toFun (Wkj k j)) (T.toFun ω)
    linarith
  exact Filter.eventually_atTop.mp hfinal
