-- Prove2me | solution 2 for FourExp.transcendence_criterion_continuous
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:19:09.420213+00:00
-- url     : https://prove2.me/submissions/783df646-ec7c-44e2-b1c6-2ee788b0999b

import Mathlib
import Theorems.Thm_FourExp_height_dvd_le
import Theorems.Thm_FourExp_small_irreducible_factor
import Theorems.Thm_FourExp_dvd_of_small_values_at_scale

open Filter Topology
open Polynomial

namespace FourExpCrit

/-- The height of an integer polynomial: the largest absolute value of a coefficient. -/
noncomputable def hgt (Q : ℤ[X]) : ℝ := ((Q.support.sup fun i => (Q.coeff i).natAbs : ℕ) : ℝ)

lemma abs_cast_eq (c : ℤ) : |(c : ℝ)| = ((c.natAbs : ℕ) : ℝ) := by
  rw [Nat.cast_natAbs, Int.cast_abs]

lemma coeff_le_hgt (Q : ℤ[X]) (i : ℕ) : |(Q.coeff i : ℝ)| ≤ hgt Q := by
  by_cases hi : i ∈ Q.support
  · rw [abs_cast_eq]
    unfold hgt
    exact_mod_cast Finset.le_sup (f := fun i => (Q.coeff i).natAbs) hi
  · rw [notMem_support_iff.mp hi]
    simp [hgt]

lemma hgt_le (Q : ℤ[X]) (K : ℝ) (hK : 0 ≤ K) (h : ∀ i, |(Q.coeff i : ℝ)| ≤ K) : hgt Q ≤ K := by
  unfold hgt
  have hs : (Q.support.sup fun i => (Q.coeff i).natAbs) ≤ ⌊K⌋₊ :=
    Finset.sup_le (fun i _ => Nat.le_floor (by rw [← abs_cast_eq]; exact h i))
  exact (Nat.cast_le.mpr hs).trans (Nat.floor_le hK)

lemma one_le_hgt (Q : ℤ[X]) (hQ : Q ≠ 0) : 1 ≤ hgt Q := by
  have hc : Q.coeff Q.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  have h1 : (1 : ℤ) ≤ |Q.coeff Q.natDegree| := Int.one_le_abs hc
  have h2 : (1 : ℝ) ≤ |(Q.coeff Q.natDegree : ℝ)| := by exact_mod_cast h1
  exact h2.trans (coeff_le_hgt Q _)

lemma finite_bounded (D : ℕ) (K : ℝ) :
    {Q : ℤ[X] | Q.natDegree ≤ D ∧ ∀ i, |(Q.coeff i : ℝ)| ≤ K}.Finite := by
  classical
  let S : Finset (Fin (D + 1) → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (-⌈K⌉) ⌈K⌉)
  apply Set.Finite.of_finite_image (f := fun Q : ℤ[X] => fun i : Fin (D + 1) => Q.coeff i)
  · apply (S.finite_toSet).subset
    rintro _ ⟨Q, ⟨_, hK⟩, rfl⟩
    simp only [S, Finset.coe_sort_coe, Fintype.coe_piFinset, Set.mem_pi, Set.mem_univ,
      Finset.coe_Icc, Set.mem_Icc, true_implies]
    intro i
    have h := hK i
    have h1 : (Q.coeff i : ℝ) ≤ K := (le_abs_self _).trans h
    have h2 : -(Q.coeff i : ℝ) ≤ K := (neg_le_abs _).trans h
    have hc := Int.le_ceil K
    constructor
    · have : ((-⌈K⌉ : ℤ) : ℝ) ≤ Q.coeff i := by push_cast; linarith
      exact_mod_cast this
    · have : (Q.coeff i : ℝ) ≤ ((⌈K⌉ : ℤ) : ℝ) := h1.trans hc
      exact_mod_cast this
  · intro Q hQ R hR h
    ext i
    by_cases hi : i ≤ D
    · exact congrFun h ⟨i, Nat.lt_succ_of_le hi⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by have := hQ.1; omega),
        coeff_eq_zero_of_natDegree_lt (by have := hR.1; omega)]

lemma one_le_natDegree {Q : ℤ[X]} (hirr : Irreducible Q) (hprim : Q.IsPrimitive) :
    1 ≤ Q.natDegree := by
  by_contra h
  push_neg at h
  have h0 : Q.natDegree = 0 := by omega
  have hQC := eq_C_of_natDegree_eq_zero h0
  have hu : IsUnit (Q.coeff 0) := hprim _ (by rw [hQC]; simp)
  exact hirr.not_isUnit (by rw [hQC]; exact Polynomial.isUnit_C.mpr hu)

end FourExpCrit

set_option maxHeartbeats 400000 in
open FourExpCrit in
theorem solution
    (α : ℂ) (ε : ℝ) (hε : 0 < ε)
    (σ₁ σ₂ : ℝ → ℝ) (hσ₁ : StrictMono σ₁) (hσ₂ : StrictMono σ₂)
    (hσ₁c : Continuous σ₁) (hσ₂c : Continuous σ₂)
    (hσ₁t : Tendsto σ₁ atTop atTop) (hσ₂t : Tendsto σ₂ atTop atTop)
    (a₁ a₂ : ℝ) (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂)
    (h₂₁ : ∀ x : ℝ, 1 ≤ x → σ₂ x ≤ σ₁ x)
    (hgrowth₁ : ∀ x : ℝ, 1 ≤ x → σ₁ (x + 1) ≤ a₁ * σ₁ x)
    (hgrowth₂ : ∀ x : ℝ, 1 ≤ x → σ₂ (x + 1) ≤ a₂ * σ₂ x)
    (N₀ : ℕ) (P : ℕ → Polynomial ℤ)
    (hP_ne : ∀ N : ℕ, N₀ < N → P N ≠ 0)
    (hP_height : ∀ N : ℕ, N₀ < N → ∀ i : ℕ, |((P N).coeff i : ℝ)| ≤ Real.exp (σ₁ N))
    (hP_deg : ∀ N : ℕ, N₀ < N → ((P N).natDegree : ℝ) ≤ σ₂ N)
    (hP_small : ∀ N : ℕ, N₀ < N →
      ‖Polynomial.aeval α (P N)‖ <
        Real.exp (-(max (10 + ε) ((4 + ε) * (a₁ * a₂)) * σ₁ N * σ₂ N))) :
    IsAlgebraic ℚ α := by
  classical
  by_contra hαalg
  have hα : Transcendental ℚ α := hαalg
  set C : ℝ := max (10 + ε) ((4 + ε) * (a₁ * a₂)) with hCdef
  have hC10 : 10 + ε ≤ C := le_max_left _ _
  have hCa : (4 + ε) * (a₁ * a₂) ≤ C := le_max_right _ _
  have ha₁0 : 0 < a₁ := by linarith
  have ha₂0 : 0 < a₂ := by linarith
  -- where `σ₂ ≥ 1`
  obtain ⟨X₀, hX₀1, hX₀⟩ : ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ x, X₀ ≤ x → 1 ≤ σ₂ x := by
    obtain ⟨X, hX⟩ := eventually_atTop.mp (hσ₂t.eventually_ge_atTop 1)
    exact ⟨max X 1, le_max_right _ _, fun x hx => hX x (le_of_max_le_left hx)⟩
  have hσ₁ge : ∀ x, X₀ ≤ x → 1 ≤ σ₁ x := fun x hx => (hX₀ x hx).trans (h₂₁ x (by linarith))
  -- Step 1: a small irreducible factor of each `P q`
  have step1 : ∀ q : ℕ, N₀ < q → X₀ ≤ (q : ℝ) → ∃ Q : ℤ[X], Q ∣ P q ∧ Irreducible Q ∧
      Q.IsPrimitive ∧ ∃ s : ℕ, 0 < s ∧
        ‖aeval α Q‖ < Real.exp (-((C - 6) * σ₁ q * σ₂ q / s)) ∧
        hgt Q ≤ Real.exp (3 * σ₁ q / s) ∧ (Q.natDegree : ℝ) ≤ σ₂ q / s := by
    intro q hq hqX
    have hPne := hP_ne q hq
    have hcont : (P q).content ≠ 0 := by rwa [Ne, content_eq_zero_iff]
    have hc1 : (1 : ℝ) ≤ |((P q).content : ℝ)| := by exact_mod_cast Int.one_le_abs hcont
    have hdecomp := eq_C_content_mul_primPart (P q)
    have hpH : ∀ i, |((P q).primPart.coeff i : ℝ)| ≤ Real.exp (σ₁ q) := by
      intro i
      have h := hP_height q hq i
      have hci : ((P q).coeff i : ℝ) = ((P q).content : ℝ) * ((P q).primPart.coeff i : ℝ) := by
        conv_lhs => rw [hdecomp]
        simp
      rw [hci, abs_mul] at h
      have : |((P q).primPart.coeff i : ℝ)| ≤ |((P q).content : ℝ)| * |((P q).primPart.coeff i : ℝ)| :=
        le_mul_of_one_le_left (abs_nonneg _) hc1
      linarith
    have hpα : ‖aeval α (P q).primPart‖ ≤ ‖aeval α (P q)‖ := by
      have hev : aeval α (P q) = ((P q).content : ℂ) * aeval α (P q).primPart := by
        conv_lhs => rw [hdecomp]
        simp
      rw [hev, norm_mul]
      have : (1 : ℝ) ≤ ‖((P q).content : ℂ)‖ := by
        rw [Complex.norm_intCast]; exact hc1
      nlinarith [norm_nonneg (aeval α (P q).primPart)]
    have h21q := h₂₁ q (by linarith)
    obtain ⟨Q, hQp, hprim, hirr, s, hs, hQα, hQh, hQd⟩ :=
      FourExp.small_irreducible_factor α hα (P q).primPart (isPrimitive_primPart _)
        (Real.exp (σ₁ q)) (σ₂ q) C hpH (by rw [Real.log_exp]; exact h21q)
        (by rw [natDegree_primPart]; exact hP_deg q hq) (by linarith)
        (by
          rw [← Real.exp_mul]
          refine lt_of_le_of_lt hpα (lt_of_lt_of_eq (hP_small q hq) ?_)
          congr 1
          ring)
    have hs' : (0 : ℝ) < s := by exact_mod_cast hs
    refine ⟨Q, hQp.trans (primPart_dvd _), hirr, hprim, s, hs, ?_, ?_, hQd⟩
    · rw [← Real.exp_mul] at hQα
      convert hQα using 2
      ring
    · apply hgt_le Q _ (Real.exp_pos _).le
      intro i
      refine (hQh i).trans ?_
      rw [← Real.exp_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [mul_one_div, ← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hs'.le
  -- the scale of a polynomial
  let T : ℤ[X] → Set ℝ := fun Q =>
    {x | 1 ≤ x ∧ Real.log (hgt Q) ≤ 3 * σ₁ x ∧ (Q.natDegree : ℝ) ≤ (1 + ε / 2) * σ₂ x}
  have hTclosed : ∀ Q, IsClosed (T Q) := by
    intro Q
    refine (isClosed_le continuous_const continuous_id).inter
      ((isClosed_le continuous_const (continuous_const.mul hσ₁c)).inter
        (isClosed_le continuous_const (continuous_const.mul hσ₂c)))
  have hTbdd : ∀ Q, BddBelow (T Q) := fun Q => ⟨1, fun x hx => hx.1⟩
  -- a factor from step 1 lies in its own scale set at `q`
  have hq_mem : ∀ q : ℕ, N₀ < q → X₀ ≤ (q : ℝ) → ∀ Q : ℤ[X], Q ≠ 0 → ∀ s : ℕ, 0 < s →
      hgt Q ≤ Real.exp (3 * σ₁ q / s) → (Q.natDegree : ℝ) ≤ σ₂ q / s → (q : ℝ) ∈ T Q := by
    intro q hq hqX Q hQ0 s hs hh hd
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hσ₁q := hσ₁ge q hqX
    have hσ₂q := hX₀ q hqX
    refine ⟨by linarith, ?_, ?_⟩
    · have := Real.log_le_log (by linarith [one_le_hgt Q hQ0]) hh
      rw [Real.log_exp] at this
      have : 3 * σ₁ q / s ≤ 3 * σ₁ q := div_le_self (by linarith) hs1
      linarith
    · have : σ₂ q / s ≤ σ₂ q := div_le_self (by linarith) hs1
      nlinarith
  -- the threshold of the resultant step at one scale
  obtain ⟨U, hU⟩ := FourExp.dvd_of_small_values_at_scale α ε hε
  obtain ⟨Z₁, hZ₁⟩ := eventually_atTop.mp (hσ₁t.eventually_ge_atTop U)
  set Zs : ℝ := max (max (X₀ + 1) ((N₀ : ℝ) + 2)) (max Z₁ 2) with hZsdef
  -- Step 2: some factor has scale at least `Zs`
  have step2 : ∃ q : ℕ, N₀ < q ∧ X₀ ≤ (q : ℝ) ∧ ∃ Q : ℤ[X], Q ∣ P q ∧ Irreducible Q ∧
      Q.IsPrimitive ∧ ∃ s : ℕ, 0 < s ∧
        ‖aeval α Q‖ < Real.exp (-((C - 6) * σ₁ q * σ₂ q / s)) ∧
        hgt Q ≤ Real.exp (3 * σ₁ q / s) ∧ (Q.natDegree : ℝ) ≤ σ₂ q / s ∧
        Zs ≤ sInf (T Q) := by
    by_contra hno
    push_neg at hno
    -- every such factor lies in a finite set
    set Dm : ℕ := ⌈(1 + ε / 2) * σ₂ Zs⌉₊ with hDm
    set Km : ℝ := Real.exp (3 * σ₁ Zs) with hKm
    have hfin := finite_bounded Dm Km
    set F : Finset ℤ[X] := (hfin.toFinset).filter (fun Q => Q ≠ 0) with hF
    have hinF : ∀ q : ℕ, N₀ < q → X₀ ≤ (q : ℝ) → ∀ (Q : ℤ[X]) (s : ℕ), Q ∣ P q → Irreducible Q →
        Q.IsPrimitive → 0 < s → ‖aeval α Q‖ < Real.exp (-((C - 6) * σ₁ q * σ₂ q / s)) →
        hgt Q ≤ Real.exp (3 * σ₁ q / s) → (Q.natDegree : ℝ) ≤ σ₂ q / s → Q ∈ F := by
      intro q hq hqX Q s hQP hirr hprim hs hα' hh hd
      have hQ0 : Q ≠ 0 := hirr.ne_zero
      have hz := hno q hq hqX Q hQP hirr hprim s hs hα' hh hd
      have hmem : sInf (T Q) ∈ T Q :=
        (hTclosed Q).csInf_mem ⟨q, hq_mem q hq hqX Q hQ0 s hs hh hd⟩ (hTbdd Q)
      obtain ⟨_, hlh, hdz⟩ := hmem
      simp only [hF, Finset.mem_filter, Set.Finite.mem_toFinset]
      refine ⟨⟨?_, fun i => ?_⟩, hQ0⟩
      · have h1 : (Q.natDegree : ℝ) ≤ (1 + ε / 2) * σ₂ Zs :=
          hdz.trans (mul_le_mul_of_nonneg_left (hσ₂.monotone hz.le) (by positivity))
        exact_mod_cast h1.trans (Nat.le_ceil _)
      · refine (coeff_le_hgt Q i).trans ?_
        have hlog := Real.exp_le_exp.mpr
          (hlh.trans (mul_le_mul_of_nonneg_left (hσ₁.monotone hz.le) (by norm_num)))
        rwa [Real.exp_log (by linarith [one_le_hgt Q hQ0])] at hlog
    -- values at `α` of polynomials in `F` are bounded away from `0`
    have hval : ∀ Q ∈ F, 0 < ‖aeval α Q‖ := by
      intro Q hQ
      have hQ0 : Q ≠ 0 := (Finset.mem_filter.mp hQ).2
      refine norm_pos_iff.mpr (fun h => hα ⟨Q.map (algebraMap ℤ ℚ), ?_, ?_⟩)
      · exact (Polynomial.map_ne_zero_iff (algebraMap ℤ ℚ).injective_int).mpr hQ0
      · rw [aeval_map_algebraMap]; exact h
    have hev : ∀ Λ : ℝ, ∃ q : ℕ, N₀ < q ∧ X₀ ≤ (q : ℝ) ∧ Λ ≤ σ₁ q := by
      intro Λ
      have h1 := (hσ₁t.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop Λ
      have h2 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop X₀
      have h3 := eventually_gt_atTop N₀
      obtain ⟨q, hq3, hq2, hq1⟩ := (h3.and (h2.and h1)).exists
      exact ⟨q, hq3, hq2, hq1⟩
    by_cases hFe : F.Nonempty
    · set m : ℝ := F.inf' hFe (fun Q => ‖aeval α Q‖) with hmdef
      have hm : 0 < m := (Finset.lt_inf'_iff hFe).mpr hval
      have hC6 : 0 < C - 6 := by linarith
      obtain ⟨q, hq, hqX, hqΛ⟩ := hev (-Real.log m / (C - 6))
      obtain ⟨Q, hQP, hirr, hprim, s, hs, hQα, hQh, hQd⟩ := step1 q hq hqX
      have hQF := hinF q hq hqX Q s hQP hirr hprim hs hQα hQh hQd
      have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
      have hδ1 : (1 : ℝ) ≤ Q.natDegree := by exact_mod_cast one_le_natDegree hirr hprim
      have hσ₂s : 1 ≤ σ₂ q / s := hδ1.trans hQd
      have hσ₁q := hσ₁ge q hqX
      have hexp : (C - 6) * σ₁ q * σ₂ q / s ≥ -Real.log m := by
        have h1 : (C - 6) * σ₁ q ≥ -Real.log m := by
          rw [ge_iff_le, mul_comm]
          exact (div_le_iff₀ hC6).mp hqΛ
        have h2 : (C - 6) * σ₁ q * σ₂ q / s = (C - 6) * σ₁ q * (σ₂ q / s) := by ring
        rw [h2]
        have hX : 0 ≤ (C - 6) * σ₁ q := mul_nonneg hC6.le (by linarith)
        have h3 := mul_le_mul_of_nonneg_left hσ₂s hX
        linarith
      have hle : Real.exp (-((C - 6) * σ₁ q * σ₂ q / s)) ≤ m := by
        calc Real.exp (-((C - 6) * σ₁ q * σ₂ q / s)) ≤ Real.exp (Real.log m) :=
              Real.exp_le_exp.mpr (by linarith)
          _ = m := Real.exp_log hm
      have := Finset.inf'_le (fun Q => ‖aeval α Q‖) hQF
      linarith
    · obtain ⟨q, hq, hqX, -⟩ := hev 0
      obtain ⟨Q, hQP, hirr, hprim, s, hs, hQα, hQh, hQd⟩ := step1 q hq hqX
      exact hFe ⟨Q, hinF q hq hqX Q s hQP hirr hprim hs hQα hQh hQd⟩
  -- Step 3: the endgame
  obtain ⟨q, hq, hqX, Q, hQP, hirr, hprim, s, hs, hQα, hQh, hQd, hz⟩ := step2
  have hQ0 : Q ≠ 0 := hirr.ne_zero
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hqT := hq_mem q hq hqX Q hQ0 s hs hQh hQd
  set z : ℝ := sInf (T Q) with hzdef
  have hmem : z ∈ T Q := (hTclosed Q).csInf_mem ⟨q, hqT⟩ (hTbdd Q)
  have hzq : z ≤ q := csInf_le (hTbdd Q) hqT
  have hZs1 : X₀ + 1 ≤ z := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hz
  have hZs2 : (N₀ : ℝ) + 2 ≤ z := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hz
  have hZs3 : Z₁ ≤ z := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hz
  have hZs4 : (2 : ℝ) ≤ z := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hz
  set u : ℝ := σ₁ z with hudef
  set v : ℝ := σ₂ z with hvdef
  have hv1 : 1 ≤ v := hX₀ z (by linarith)
  have hvu : v ≤ u := h₂₁ z (by linarith)
  have huU : U ≤ u := hZ₁ z hZs3
  -- both scale inequalities cannot be strict at `z`
  have hnotboth : ¬ (Real.log (hgt Q) < 3 * u ∧ (Q.natDegree : ℝ) < (1 + ε / 2) * v) := by
    rintro ⟨h1, h2⟩
    have e1 : ∀ᶠ x in 𝓝 z, Real.log (hgt Q) < 3 * σ₁ x :=
      ((continuous_const.mul hσ₁c).tendsto z).eventually_const_lt h1
    have e2 : ∀ᶠ x in 𝓝 z, (Q.natDegree : ℝ) < (1 + ε / 2) * σ₂ x :=
      ((continuous_const.mul hσ₂c).tendsto z).eventually_const_lt h2
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp (e1.and e2)
    set x : ℝ := z - min (η / 2) ((z - 1) / 2) with hxdef
    have hmin1 : min (η / 2) ((z - 1) / 2) ≤ η / 2 := min_le_left _ _
    have hmin2 : min (η / 2) ((z - 1) / 2) ≤ (z - 1) / 2 := min_le_right _ _
    have hminpos : 0 < min (η / 2) ((z - 1) / 2) := lt_min (by linarith) (by linarith)
    have hdist : dist x z < η := by
      rw [Real.dist_eq, hxdef]
      rw [abs_of_nonpos (by linarith)]
      linarith
    obtain ⟨hx1, hx2⟩ := hball hdist
    have hxT : x ∈ T Q := ⟨by linarith, hx1.le, hx2.le⟩
    have := csInf_le (hTbdd Q) hxT
    linarith
  obtain ⟨_, hlh, hdz⟩ := hmem
  -- (3.9)
  have hσ₁q_nonneg : 0 ≤ σ₁ q := by linarith [hσ₁ge q hqX]
  have hσ₂q1 : 1 ≤ σ₂ q := hX₀ q hqX
  have huq : u ≤ σ₁ q := hσ₁.monotone hzq
  have hvq : v ≤ σ₂ q := hσ₂.monotone hzq
  have hlogq : Real.log (hgt Q) ≤ 3 * σ₁ q / s := by
    have := Real.log_le_log (by linarith [one_le_hgt Q hQ0]) hQh
    rwa [Real.log_exp] at this
  have h39 : u * v ≤ σ₁ q * σ₂ q / s := by
    have hs' : (0 : ℝ) < s := by linarith
    rcases not_and_or.mp hnotboth with ha | hb
    · push_neg at ha
      have hu' : u ≤ σ₁ q / s := by
        have : 3 * u ≤ 3 * σ₁ q / s := ha.trans hlogq
        have : 3 * σ₁ q / s = 3 * (σ₁ q / s) := by ring
        linarith
      calc u * v ≤ (σ₁ q / s) * σ₂ q :=
            mul_le_mul hu' hvq (by linarith) (div_nonneg hσ₁q_nonneg hs'.le)
        _ = σ₁ q * σ₂ q / s := by ring
    · push_neg at hb
      have hv' : v ≤ σ₂ q / s := by
        have h1 : v ≤ (1 + ε / 2) * v := by nlinarith
        linarith
      calc u * v ≤ σ₁ q * (σ₂ q / s) := mul_le_mul huq hv' (by linarith) hσ₁q_nonneg
        _ = σ₁ q * σ₂ q / s := by ring
  have huv0 : 0 ≤ u * v := by nlinarith
  have hQsmall : ‖aeval α Q‖ < Real.exp (-((4 + ε) * (u * v))) := by
    refine lt_of_lt_of_le hQα (Real.exp_le_exp.mpr ?_)
    have h1 : (C - 6) * (u * v) ≤ (C - 6) * (σ₁ q * σ₂ q / s) :=
      mul_le_mul_of_nonneg_left h39 (by linarith)
    have h2 : (4 + ε) * (u * v) ≤ (C - 6) * (u * v) := mul_le_mul_of_nonneg_right (by linarith) huv0
    have h3 : (C - 6) * σ₁ q * σ₂ q / s = (C - 6) * (σ₁ q * σ₂ q / s) := by ring
    linarith
  -- the polynomial `P N` with `N = ⌊z⌋₊`
  set N : ℕ := ⌊z⌋₊ with hNdef
  have hN1 : (N : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hN2 : z < (N : ℝ) + 1 := Nat.lt_floor_add_one z
  have hNN₀ : N₀ < N := by
    have : (N₀ : ℝ) < N := by linarith
    exact_mod_cast this
  have hzm1 : X₀ ≤ z - 1 := by linarith
  have hgr₁ : u ≤ a₁ * σ₁ (z - 1) := by
    have := hgrowth₁ (z - 1) (by linarith); simpa using this
  have hgr₂ : v ≤ a₂ * σ₂ (z - 1) := by
    have := hgrowth₂ (z - 1) (by linarith); simpa using this
  have hσ₁m := hσ₁ge (z - 1) hzm1
  have hσ₂m := hX₀ (z - 1) hzm1
  have hNm : z - 1 ≤ N := by linarith
  have hσ₁N : σ₁ (z - 1) ≤ σ₁ N := hσ₁.monotone hNm
  have hσ₂N : σ₂ (z - 1) ≤ σ₂ N := hσ₂.monotone hNm
  have hPsmall : ‖aeval α (P N)‖ < Real.exp (-((4 + ε) * (u * v))) := by
    refine lt_of_lt_of_le (hP_small N hNN₀) (Real.exp_le_exp.mpr ?_)
    have h1 : u * v ≤ (a₁ * a₂) * (σ₁ (z - 1) * σ₂ (z - 1)) := by
      have := mul_le_mul hgr₁ hgr₂ (by linarith) (by positivity)
      linarith
    have h2 : σ₁ (z - 1) * σ₂ (z - 1) ≤ σ₁ N * σ₂ N :=
      mul_le_mul hσ₁N hσ₂N (by linarith) (by linarith)
    have h3 : (4 + ε) * (u * v) ≤ C * (σ₁ N * σ₂ N) := by
      calc (4 + ε) * (u * v) ≤ (4 + ε) * ((a₁ * a₂) * (σ₁ (z - 1) * σ₂ (z - 1))) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = ((4 + ε) * (a₁ * a₂)) * (σ₁ (z - 1) * σ₂ (z - 1)) := by ring
        _ ≤ C * (σ₁ (z - 1) * σ₂ (z - 1)) := mul_le_mul_of_nonneg_right hCa (by positivity)
        _ ≤ C * (σ₁ N * σ₂ N) := mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 : C * σ₁ N * σ₂ N = C * (σ₁ N * σ₂ N) := by ring
    linarith
  have hPne := hP_ne N hNN₀
  have hPH : ∀ i, |((P N).coeff i : ℝ)| ≤ Real.exp u :=
    fun i => (hP_height N hNN₀ i).trans (Real.exp_le_exp.mpr (hσ₁.monotone hN1))
  have hhQ : hgt Q ≤ Real.exp (3 * u) := by
    have := Real.exp_le_exp.mpr hlh
    rwa [Real.exp_log (by linarith [one_le_hgt Q hQ0])] at this
  have hQH : ∀ i, |(Q.coeff i : ℝ)| ≤ Real.exp (3 * u) := fun i => (coeff_le_hgt Q i).trans hhQ
  set d : ℕ := (P N).natDegree with hddef
  set δ : ℕ := Q.natDegree with hδdef
  have hd : (d : ℝ) ≤ v := (hP_deg N hNN₀).trans (hσ₂.monotone hN1)
  -- the resultant step at the scale `(u, v)`
  have hdvd : Q ∣ P N := hU u v huU hv1 hvu (P N) Q hirr hPH hd hQH hdz hPsmall hQsmall
  -- Gel'fond's height bound makes both scale inequalities strict
  have hA1 := FourExp.height_dvd_le (P N) Q hPne hdvd (Real.exp (σ₁ N)) (hP_height N hNN₀)
  have hhgt : hgt Q ≤ Real.exp ((d : ℝ) + σ₁ N) := by
    apply hgt_le Q _ (Real.exp_pos _).le
    intro i
    rw [Real.exp_add]
    exact hA1 i
  have hlogQ : Real.log (hgt Q) ≤ (d : ℝ) + σ₁ N := by
    have := Real.log_le_log (by linarith [one_le_hgt Q hQ0]) hhgt
    rwa [Real.log_exp] at this
  have hdegQ : (δ : ℝ) ≤ d := by exact_mod_cast natDegree_le_of_dvd hdvd hPne
  apply hnotboth
  constructor
  · have : σ₁ N ≤ u := hσ₁.monotone hN1
    linarith
  · have : v < (1 + ε / 2) * v := by nlinarith
    linarith

#print axioms solution
