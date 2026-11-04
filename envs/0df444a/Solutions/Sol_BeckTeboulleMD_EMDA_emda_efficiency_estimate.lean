-- Prove2me | solution 1 for BeckTeboulleMD.EMDA.emda_efficiency_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T02:02:19.062297+00:00
-- url     : https://prove2.me/submissions/084ebf8b-3026-4bc1-8986-ae42bc888b8b

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_emdaStep

set_option autoImplicit false

open MeasureTheory ProbabilityTheory in
/-- Finite Hoeffding lemma: for weights `p` in the simplex and values `|v j| ≤ L`,
`∑ p_j e^{t v_j} ≤ exp (t ∑ p_j v_j + L² t² / 2)`. -/
lemma emda_hoeff {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (v : Fin n → ℝ) (L : ℝ) (hv : ∀ j, |v j| ≤ L) (t : ℝ) :
    ∑ j, p j * Real.exp (t * v j) ≤ Real.exp (t * ∑ j, p j * v j + L ^ 2 * t ^ 2 / 2) := by
  set μ : Measure (Fin n) := ∑ j, ENNReal.ofReal (p j) • Measure.dirac j with hμ
  have hfin : ∀ j, IsFiniteMeasure (ENNReal.ofReal (p j) • Measure.dirac j) := fun j => by
    constructor; simp
  have hint : ∀ φ : Fin n → ℝ, ∫ ω, φ ω ∂μ = ∑ j, p j * φ j := by
    intro φ
    rw [hμ, integral_finsetSum_measure (fun j _ => by haveI := hfin j; exact Integrable.of_finite)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp0 j), smul_eq_mul]
  haveI : IsProbabilityMeasure μ := by
    constructor
    rw [hμ, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hp0 j), hp1, ENNReal.ofReal_one]
  have hb : ∀ᵐ ω ∂μ, v ω ∈ Set.Icc (-L) L :=
    Filter.Eventually.of_forall (fun ω => abs_le.mp (hv ω))
  have h := (hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := v)
    (Measurable.of_discrete).aemeasurable hb).mgf_le t
  simp only [mgf] at h
  rw [hint] at h
  have hm : μ[v] = ∑ j, p j * v j := hint v
  rw [hm] at h
  have hc : (((‖L - -L‖₊ / 2) ^ 2 : NNReal) : ℝ) = L ^ 2 := by
    push_cast
    rw [Real.norm_eq_abs, sub_neg_eq_add, div_pow, sq_abs]
    ring
  rw [hc] at h
  set m := ∑ j, p j * v j
  have hsplit : ∑ j, p j * Real.exp (t * (v j - m))
      = (∑ j, p j * Real.exp (t * v j)) * Real.exp (-(t * m)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_sub, sub_eq_add_neg, Real.exp_add]
    ring
  rw [hsplit] at h
  have he : 0 < Real.exp (t * m) := Real.exp_pos _
  calc ∑ j, p j * Real.exp (t * v j)
      = ((∑ j, p j * Real.exp (t * v j)) * Real.exp (-(t * m))) * Real.exp (t * m) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ Real.exp (L ^ 2 * t ^ 2 / 2) * Real.exp (t * m) :=
        mul_le_mul_of_nonneg_right h he.le
    _ = Real.exp (t * m + L ^ 2 * t ^ 2 / 2) := by
        rw [← Real.exp_add, add_comm]

/-- Hoeffding for a vector of oscillation at most `2L` (shift-invariant form). -/
lemma emda_hoeff_osc {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (g : Fin n → ℝ) (L : ℝ) (hosc : ∀ i j, g i - g j ≤ 2 * L) (t : ℝ) :
    ∑ j, p j * Real.exp (-t * g j) ≤ Real.exp (-t * ∑ j, p j * g j + L ^ 2 * t ^ 2 / 2) := by
  rcases isEmpty_or_nonempty (Fin n) with hE | hne
  · simp at hp1
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
  set c := g i0 - L with hc
  have hv : ∀ j, |g j - c| ≤ L := by
    intro j
    rw [abs_le]
    have h1 := hi0 j (Finset.mem_univ _)
    have h2 := hosc i0 j
    constructor <;> linarith
  have h : ∑ j, p j * Real.exp (-t * (g j - c)) ≤
      Real.exp (-t * ∑ j, p j * (g j - c) + L ^ 2 * (-t) ^ 2 / 2) :=
    emda_hoeff p hp0 hp1 (fun j => g j - c) L hv (-t)
  have e1 : ∑ j, p j * Real.exp (-t * g j) =
      (∑ j, p j * Real.exp (-t * (g j - c))) * Real.exp (-t * c) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  have e2 : ∑ j, p j * (g j - c) = ∑ j, p j * g j - c := by
    have : ∀ j, p j * (g j - c) = p j * g j - p j * c := fun j => by ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
  rw [e1]
  calc (∑ j, p j * Real.exp (-t * (g j - c))) * Real.exp (-t * c)
      ≤ Real.exp (-t * ∑ j, p j * (g j - c) + L ^ 2 * (-t) ^ 2 / 2) * Real.exp (-t * c) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = Real.exp (-t * ∑ j, p j * g j + L ^ 2 * t ^ 2 / 2) := by
        rw [← Real.exp_add, e2]
        congr 1
        ring

open BeckTeboulleMD.EMDA in
lemma emda_step_pos {n : ℕ} [Nonempty (Fin n)] (t : ℝ) (q w : Fin n → ℝ)
    (hq : ∀ j, 0 < q j) :
    (∀ j, 0 < emdaStep t q w j) ∧ ∑ j, emdaStep t q w j = 1 := by
  have hZ : 0 < ∑ i, q i * Real.exp (-t * w i) :=
    Finset.sum_pos (fun i _ => mul_pos (hq i) (Real.exp_pos _)) Finset.univ_nonempty
  refine ⟨fun j => div_pos (mul_pos (hq j) (Real.exp_pos _)) hZ, ?_⟩
  unfold emdaStep
  rw [← Finset.sum_div]
  exact div_self hZ.ne'

open BeckTeboulleMD.EMDA in
/-- One mirror step: the entropic potential `∑ u_j log q_j` absorbs the linear gain. -/
lemma emda_one_step {n : ℕ} [Nonempty (Fin n)] (q u w : Fin n → ℝ) (hq : ∀ j, 0 < q j)
    (hq1 : ∑ j, q j = 1) (hu1 : ∑ j, u j = 1) (L : ℝ) (hosc : ∀ i j, w i - w j ≤ 2 * L)
    (t : ℝ) :
    t * (∑ j, q j * w j - ∑ j, u j * w j) ≤
      ∑ j, u j * Real.log (emdaStep t q w j) - ∑ j, u j * Real.log (q j) +
        L ^ 2 * t ^ 2 / 2 := by
  set Z := ∑ i, q i * Real.exp (-t * w i) with hZdef
  have hZ : 0 < Z :=
    Finset.sum_pos (fun i _ => mul_pos (hq i) (Real.exp_pos _)) Finset.univ_nonempty
  have hlog : ∀ j, Real.log (emdaStep t q w j) = Real.log (q j) - t * w j - Real.log Z := by
    intro j
    show Real.log (q j * Real.exp (-t * w j) / Z) = _
    rw [Real.log_div (mul_pos (hq j) (Real.exp_pos _)).ne' hZ.ne',
      Real.log_mul (hq j).ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hdiff : ∑ j, u j * Real.log (emdaStep t q w j) - ∑ j, u j * Real.log (q j)
      = -(t * ∑ j, u j * w j) - Real.log Z := by
    simp_rw [hlog]
    rw [← Finset.sum_sub_distrib]
    have e : ∀ j, u j * (Real.log (q j) - t * w j - Real.log Z) - u j * Real.log (q j)
        = -(t * (u j * w j)) - u j * Real.log Z := fun j => by ring
    simp_rw [e]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hu1, Finset.sum_neg_distrib,
      ← Finset.mul_sum]
    ring
  have hH := emda_hoeff_osc q (fun j => (hq j).le) hq1 w L hosc t
  have hlZ : Real.log Z ≤ -t * ∑ j, q j * w j + L ^ 2 * t ^ 2 / 2 := by
    rw [Real.log_le_iff_le_exp hZ]
    exact hH
  rw [hdiff]
  have e1 : t * (∑ j, q j * w j - ∑ j, u j * w j) =
      t * ∑ j, q j * w j - t * ∑ j, u j * w j := by ring
  have e2 : -t * ∑ j, q j * w j = -(t * ∑ j, q j * w j) := by ring
  rw [e1]
  rw [e2] at hlZ
  linarith

/-- A subgradient (relative to the simplex) at a point with positive coordinates of an
`L`-Lipschitz (w.r.t. `‖·‖₁`) function has oscillation at most `2L`. -/
lemma emda_osc {n : ℕ} (f : (Fin n → ℝ) → ℝ) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ x ∈ stdSimplex ℝ (Fin n), ∀ y ∈ stdSimplex ℝ (Fin n),
      |f x - f y| ≤ L * ∑ i, |x i - y i|)
    (q g : Fin n → ℝ) (hq : ∀ j, 0 < q j) (hq1 : ∑ j, q j = 1)
    (hg : ∀ y ∈ stdSimplex ℝ (Fin n), f q + ∑ i, g i * (y i - q i) ≤ f y) :
    ∀ i j, g i - g j ≤ 2 * L := by
  intro i j
  by_cases hij : i = j
  · subst hij; simp only [sub_self]; linarith
  set y : Fin n → ℝ := fun m =>
    q m + q j * ((if m = i then 1 else 0) - (if m = j then 1 else 0)) with hy
  have hsI : ∑ m : Fin n, (if m = i then (1:ℝ) else 0) = 1 := by simp
  have hsJ : ∑ m : Fin n, (if m = j then (1:ℝ) else 0) = 1 := by simp
  have hymem : y ∈ stdSimplex ℝ (Fin n) := by
    refine ⟨fun m => ?_, ?_⟩
    · simp only [hy]
      by_cases hmj : m = j
      · subst hmj
        rw [if_neg (Ne.symm hij), if_pos rfl]
        linarith
      · rw [if_neg hmj]
        have := hq m
        have := hq j
        split_ifs <;> nlinarith
    · simp only [hy]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hsI, hsJ, hq1]
      ring
  have hlin : ∑ m, g m * (y m - q m) = q j * (g i - g j) := by
    have e : ∀ m, g m * (y m - q m) =
        q j * (if m = i then g m else 0) - q j * (if m = j then g m else 0) := by
      intro m
      simp only [hy]
      split_ifs <;> ring
    simp_rw [e]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have habs : ∑ m, |y m - q m| = 2 * q j := by
    have e : ∀ m, |y m - q m| =
        q j * (if m = i then 1 else 0) + q j * (if m = j then 1 else 0) := by
      intro m
      have hqj := hq j
      simp only [hy]
      by_cases hmi : m = i
      · subst hmi
        rw [if_pos rfl, if_neg hij]
        simp only [add_sub_cancel_left, sub_zero, mul_one, mul_zero, add_zero]
        exact abs_of_pos hqj
      · by_cases hmj : m = j
        · subst hmj
          rw [if_neg hmi, if_pos rfl]
          simp only [add_sub_cancel_left, zero_sub, mul_neg, mul_one, mul_zero, zero_add,
            abs_neg]
          exact abs_of_pos hqj
        · rw [if_neg hmi, if_neg hmj]
          simp
    simp_rw [e]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsI, hsJ]
    ring
  have h1 := hg y hymem
  have h2 := hL y hymem q ⟨fun m => (hq m).le, hq1⟩
  rw [hlin] at h1
  rw [habs] at h2
  have h3 : f y - f q ≤ L * (2 * q j) := le_trans (le_abs_self _) h2
  have h4 : q j * (g i - g j) ≤ q j * (2 * L) := by nlinarith
  exact le_of_mul_le_mul_left h4 (hq j)

open BeckTeboulleMD.EMDA in
theorem solution {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ (stdSimplex ℝ (Fin n)) f) (L : ℝ)
    (hL : ∀ x ∈ stdSimplex ℝ (Fin n), ∀ y ∈ stdSimplex ℝ (Fin n),
      |f x - f y| ≤ L * ∑ i, |x i - y i|)
    (k : ℕ) (hk : 1 ≤ k) (x : ℕ → Fin n → ℝ) (g : ℕ → Fin n → ℝ)
    (hx1 : x 1 = fun _ => (n : ℝ)⁻¹)
    (hg : ∀ s ∈ Finset.Ico 1 k, ∀ y ∈ stdSimplex ℝ (Fin n),
      f (x s) + ∑ i, g s i * (y i - x s i) ≤ f y)
    (hstep : ∀ s ∈ Finset.Ico 1 k,
      x (s + 1) = emdaStep (Real.sqrt (2 * Real.log n) / (L * Real.sqrt k)) (x s) (g s))
    (u : Fin n → ℝ) (hu : u ∈ stdSimplex ℝ (Fin n)) :
    (Finset.Icc 1 k).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hk⟩⟩ (fun s => f (x s)) - f u ≤
      Real.sqrt (2 * Real.log n) * L / Real.sqrt k := by
  obtain ⟨hu0, hu1⟩ := hu
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hu1
    · exact h
  have hnR : (0:ℝ) < n := by exact_mod_cast hn1
  haveI : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
  have hx1mem : x 1 ∈ stdSimplex ℝ (Fin n) := by
    refine ⟨fun j => by rw [hx1]; positivity, ?_⟩
    rw [hx1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  set M := (Finset.Icc 1 k).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hk⟩⟩ (fun s => f (x s))
    with hMdef
  have hMs : ∀ s, 1 ≤ s → s ≤ k → M ≤ f (x s) := fun s h1 h2 =>
    Finset.inf'_le (fun s => f (x s)) (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hlip1 := hL (x 1) hx1mem u ⟨hu0, hu1⟩
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have hn : n = 1 := by omega
    subst hn
    have hx : x 1 = u := by
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simp only [Fin.sum_univ_one] at hu1
      rw [hx1, hu1]; norm_num
    have hR : Real.sqrt (2 * Real.log ((1:ℕ):ℝ)) * L / Real.sqrt k = 0 := by
      simp
    rw [hR]
    have := hMs 1 le_rfl hk
    rw [hx] at this
    linarith
  -- L ≥ 0 from two distinct vertices
  have hL0 : 0 ≤ L := by
    set i0 : Fin n := ⟨0, by omega⟩
    set i1 : Fin n := ⟨1, by omega⟩
    have hne : i0 ≠ i1 := by
      intro h; have := congrArg Fin.val h; simp [i0, i1] at this
    have h := hL _ (single_mem_stdSimplex ℝ i0) _ (single_mem_stdSimplex ℝ i1)
    have hS : 1 ≤ ∑ j, |(Pi.single i0 (1:ℝ) : Fin n → ℝ) j - (Pi.single i1 (1:ℝ) : Fin n → ℝ) j| := by
      have := Finset.single_le_sum (f := fun j =>
        |(Pi.single i0 (1:ℝ) : Fin n → ℝ) j - (Pi.single i1 (1:ℝ) : Fin n → ℝ) j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i0)
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne hne, sub_zero, abs_one] at this
      exact this
    by_contra hneg
    push Not at hneg
    have := abs_nonneg (f (Pi.single i0 1) - f (Pi.single i1 1))
    nlinarith
  rcases hL0.eq_or_lt with hLz | hLpos
  · subst hLz
    have hR : Real.sqrt (2 * Real.log n) * (0:ℝ) / Real.sqrt k = 0 := by simp
    rw [hR]
    rw [zero_mul] at hlip1
    have := hMs 1 le_rfl hk
    have := le_abs_self (f (x 1) - f u)
    linarith
  -- main case: n ≥ 2, L > 0
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkR
  have hsl : 0 < Real.sqrt (2 * Real.log n) := Real.sqrt_pos.mpr (by positivity)
  set t := Real.sqrt (2 * Real.log n) / (L * Real.sqrt k) with ht
  set R := Real.sqrt (2 * Real.log n) * L / Real.sqrt k with hR
  have htpos : 0 < t := by rw [ht]; positivity
  have hsl2 : Real.sqrt (2 * Real.log n) * Real.sqrt (2 * Real.log n) = 2 * Real.log n :=
    Real.mul_self_sqrt (by positivity)
  have hsk2 : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hkR.le
  have ht2 : (k:ℝ) * (L ^ 2 * t ^ 2 / 2) = Real.log n := by
    rw [ht]; field_simp; nlinarith [hsl2, hsk2]
  have htR : t * (k * R) = 2 * Real.log n := by
    rw [ht, hR]; field_simp; nlinarith [hsl2, hsk2]
  have inv : ∀ s, 1 ≤ s → s ≤ k → (∀ j, 0 < x s j) ∧ ∑ j, x s j = 1 := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => intro _; exact ⟨fun j => by rw [hx1]; positivity, hx1mem.2⟩
    | succ s hs ih =>
      intro hsk'
      obtain ⟨hpos, -⟩ := ih (by omega)
      rw [hstep s (Finset.mem_Ico.mpr ⟨hs, by omega⟩)]
      exact emda_step_pos _ _ _ hpos
  have step : ∀ s, 1 ≤ s → s < k →
      t * (f (x s) - f u) ≤ ∑ j, u j * Real.log (x (s + 1) j) -
        ∑ j, u j * Real.log (x s j) + L ^ 2 * t ^ 2 / 2 := by
    intro s hs hsk'
    obtain ⟨hpos, hsum⟩ := inv s hs hsk'.le
    have hsI : s ∈ Finset.Ico 1 k := Finset.mem_Ico.mpr ⟨hs, hsk'⟩
    have hsub := hg s hsI u ⟨hu0, hu1⟩
    have hosc := emda_osc f L hL0 hL (x s) (g s) hpos hsum (hg s hsI)
    have h1 := emda_one_step (x s) u (g s) hpos hsum hu1 L hosc t
    rw [← hstep s hsI] at h1
    have hlin : f (x s) - f u ≤ ∑ j, x s j * g s j - ∑ j, u j * g s j := by
      have e : ∑ j, g s j * (u j - x s j) = ∑ j, u j * g s j - ∑ j, x s j * g s j := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun j _ => by ring)
      linarith
    have hm := mul_le_mul_of_nonneg_left hlin htpos.le
    linarith
  have tele : ∀ m : ℕ, m + 1 ≤ k → t * ∑ i ∈ Finset.range m, (f (x (i + 1)) - f u)
      ≤ ∑ j, u j * Real.log (x (m + 1) j) - ∑ j, u j * Real.log (x 1 j) +
        m * (L ^ 2 * t ^ 2 / 2) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [Finset.sum_range_succ, mul_add]
      have h1 := step (m + 1) (by omega) (by omega)
      have h2 := ih (by omega)
      push_cast
      linarith
  have hT := tele (k - 1) (by omega)
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at hT
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk, Nat.cast_one]
  rw [hcast] at hT
  -- virtual last step at x k
  obtain ⟨hposk, hsumk⟩ := inv k hk le_rfl
  have hmemk : x k ∈ stdSimplex ℝ (Fin n) := ⟨fun j => (hposk j).le, hsumk⟩
  set w : Fin n → ℝ := fun j => if u j ≤ x k j then L else -L with hw
  have hoscw : ∀ i j, w i - w j ≤ 2 * L := by
    intro i j
    simp only [hw]
    split_ifs <;> linarith
  have hlast := emda_one_step (x k) u w hposk hsumk hu1 L hoscw t
  have hwlin : f (x k) - f u ≤ ∑ j, x k j * w j - ∑ j, u j * w j := by
    have h := hL (x k) hmemk u ⟨hu0, hu1⟩
    have e : ∑ j, x k j * w j - ∑ j, u j * w j = L * ∑ j, |x k j - u j| := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hw]
      split_ifs with hj
      · rw [abs_of_nonneg (by linarith)]; ring
      · rw [abs_of_neg (by push Not at hj; linarith)]; ring
    rw [e]
    exact le_trans (le_abs_self _) h
  obtain ⟨hposv, hsumv⟩ := emda_step_pos t (x k) w hposk
  have hΨv : ∑ j, u j * Real.log (emdaStep t (x k) w j) ≤ 0 := by
    refine Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hu0 j) ?_)
    refine Real.log_nonpos (hposv j).le ?_
    rw [← hsumv]
    exact Finset.single_le_sum (f := fun i => emdaStep t (x k) w i)
      (fun i _ => (hposv i).le) (Finset.mem_univ j)
  have hΨ1 : ∑ j, u j * Real.log (x 1 j) = -Real.log n := by
    rw [hx1]
    simp only []
    rw [← Finset.sum_mul, hu1, one_mul, Real.log_inv]
  have hsumM : ((k:ℝ) - 1) * (M - f u) ≤ ∑ i ∈ Finset.range (k - 1), (f (x (i + 1)) - f u) := by
    have := Finset.card_nsmul_le_sum (Finset.range (k - 1)) (fun i => f (x (i + 1)) - f u)
      (M - f u) (fun i hi => by
        have hi' := Finset.mem_range.mp hi
        have := hMs (i + 1) (by omega) (by omega)
        show M - f u ≤ f (x (i + 1)) - f u
        linarith)
    rw [Finset.card_range, nsmul_eq_mul, hcast] at this
    exact this
  have hMk := hMs k hk le_rfl
  by_contra hcon
  push Not at hcon
  have hk1R : (0:ℝ) ≤ (k:ℝ) - 1 := by
    have : (1:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have a1 := mul_le_mul_of_nonneg_left hsumM htpos.le
  have a2 := mul_le_mul_of_nonneg_left (show M - f u ≤ f (x k) - f u by linarith) htpos.le
  have a3 := mul_le_mul_of_nonneg_left hwlin htpos.le
  have a4 : t * (k * R) < t * (k * (M - f u)) :=
    mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hcon hkR) htpos
  have e : t * (((k:ℝ) - 1) * (M - f u)) + t * (M - f u) = t * (k * (M - f u)) := by ring
  have e2 : ((k:ℝ) - 1) * (L ^ 2 * t ^ 2 / 2) + L ^ 2 * t ^ 2 / 2 =
      (k:ℝ) * (L ^ 2 * t ^ 2 / 2) := by ring
  linarith
