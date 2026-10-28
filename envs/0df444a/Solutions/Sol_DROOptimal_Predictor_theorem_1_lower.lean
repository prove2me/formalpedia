-- Prove2me | solution 1 for DROOptimal.Predictor.theorem_1_lower
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T18:10:12.970915+00:00
-- url     : https://prove2.me/submissions/90170675-d559-424c-99bf-1ddc15d604e7

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting

set_option autoImplicit false

open Filter Topology

namespace DRO1LAux

open DROOptimal.Predictor

lemma relEntropy_of_pos {d : ℕ} (Q P : Δ d)
    (hP : ∀ i, 0 < (P : Fin d → ℝ) i) :
    relEntropy Q P =
      ((∑ i, (Q : Fin d → ℝ) i * Real.log ((Q : Fin d → ℝ) i / (P : Fin d → ℝ) i) : ℝ) : EReal) := by
  unfold relEntropy
  rw [if_pos (fun i h => absurd h (hP i).ne')]

lemma sum_comp_count {d T : ℕ} (ω : Fin T → Fin d) (h : Fin d → ℝ) :
    ∑ t, h (ω t) = ∑ i, ((Finset.univ.filter (fun t => ω t = i)).card : ℝ) * h i := by
  rw [← Finset.sum_fiberwise Finset.univ ω (fun t => h (ω t))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : ∀ t ∈ Finset.univ.filter (fun t => ω t = i), h (ω t) = h i :=
    fun t ht => by rw [(Finset.mem_filter.1 ht).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]

lemma emp_nonneg {d T : ℕ} (ω : Fin T → Fin d) (i : Fin d) : 0 ≤ empiricalVec ω i := by
  unfold empiricalVec; positivity

lemma emp_sum_one {d T : ℕ} (hT : 0 < T) (ω : Fin T → Fin d) : ∑ i, empiricalVec ω i = 1 := by
  have h := sum_comp_count ω (fun _ => (1:ℝ))
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  unfold empiricalVec
  rw [← Finset.sum_div, ← h]
  exact div_self (by exact_mod_cast hT.ne')

/-- The count of state `a` in the path `ω`. -/
noncomputable def cnt {d T : ℕ} (ω : Fin T → Fin d) (a : Fin d) : ℝ :=
  ((Finset.univ.filter (fun t => ω t = a)).card : ℝ)

lemma cnt_eq {d T : ℕ} (ω : Fin T → Fin d) (a : Fin d) :
    cnt ω a = ∑ t, (if ω t = a then (1:ℝ) else 0) := by
  unfold cnt; rw [Finset.sum_boole]

lemma sum_prod {d T : ℕ} (f : Fin T → Fin d → ℝ) :
    ∑ ω : Fin T → Fin d, ∏ t, f t (ω t) = ∏ t, ∑ i, f t i := by
  rw [Finset.prod_univ_sum (fun _ => Finset.univ), Fintype.piFinset_univ]

lemma mass_one {d T : ℕ} (q : Fin d → ℝ) (hq1 : ∑ i, q i = 1) :
    ∑ ω : Fin T → Fin d, ∏ t, q (ω t) = 1 := by
  rw [sum_prod (fun _ i => q i)]; simp [hq1]

lemma coord_le_one {d : ℕ} (q : Fin d → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (a : Fin d) : q a ≤ 1 := by
  rw [← hq1]; exact Finset.single_le_sum (fun i _ => hq0 i) (Finset.mem_univ a)

lemma mgf_le {d T : ℕ} (q : Fin d → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (a : Fin d) (l : ℝ) (hl : |l| ≤ 1) :
    ∑ ω : Fin T → Fin d, (∏ t, q (ω t)) * Real.exp (l * cnt ω a)
      ≤ Real.exp (T * (q a * l + l ^ 2)) := by
  have h1 : ∀ ω : Fin T → Fin d, (∏ t, q (ω t)) * Real.exp (l * cnt ω a)
      = ∏ t, (q (ω t) * Real.exp (l * if ω t = a then 1 else 0)) := by
    intro ω
    rw [Finset.prod_mul_distrib, cnt_eq, Finset.mul_sum, Real.exp_sum]
  simp_rw [h1]
  rw [sum_prod (fun _ i => q i * Real.exp (l * if i = a then 1 else 0))]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hs : ∑ i, q i * Real.exp (l * if i = a then 1 else 0) = 1 + q a * (Real.exp l - 1) := by
    have : ∀ i, q i * Real.exp (l * if i = a then 1 else 0)
        = q i + (if i = a then q a * (Real.exp l - 1) else 0) := by
      intro i
      split_ifs with h
      · subst h; rw [mul_one]; ring
      · simp
    simp_rw [this]
    rw [Finset.sum_add_distrib, hq1, Finset.sum_ite_eq']
    simp
  rw [hs]
  have qa1 := coord_le_one q hq0 hq1 a
  have e1 := Real.abs_exp_sub_one_sub_id_le hl
  have e2 : Real.exp l - 1 ≤ l + l ^ 2 := by
    have := (abs_le.1 e1).2; linarith
  have e3 : q a * (Real.exp l - 1) ≤ q a * l + l ^ 2 := by
    have := mul_le_mul_of_nonneg_left e2 (hq0 a)
    have h4 : q a * l ^ 2 ≤ l ^ 2 := by
      have := mul_le_mul_of_nonneg_right qa1 (sq_nonneg l); linarith
    nlinarith
  have hb : 1 + q a * (Real.exp l - 1) ≤ Real.exp (q a * l + l ^ 2) := by
    have := Real.add_one_le_exp (q a * l + l ^ 2); linarith
  have h0 : 0 ≤ 1 + q a * (Real.exp l - 1) := by
    have h5 : 1 + q a * (Real.exp l - 1) = (1 - q a) + q a * Real.exp l := by ring
    rw [h5]
    have := mul_nonneg (hq0 a) (Real.exp_pos l).le
    linarith
  calc (1 + q a * (Real.exp l - 1)) ^ T ≤ (Real.exp (q a * l + l ^ 2)) ^ T :=
        pow_le_pow_left₀ h0 hb T
    _ = Real.exp (T * (q a * l + l ^ 2)) := by rw [← Real.exp_nat_mul]

lemma tail_le {d T : ℕ} (q : Fin d → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (a : Fin d) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∑ ω : Fin T → Fin d,
        (∏ t, q (ω t)) * (if (T : ℝ) * δ ≤ |cnt ω a - T * q a| then (1:ℝ) else 0)
      ≤ 2 * Real.exp (-(T * (δ ^ 2 / 4))) := by
  have hl : |δ / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hl' : |-(δ / 2)| ≤ 1 := by rwa [abs_neg]
  set A : ℝ := Real.exp (-((δ / 2) * (T * q a + T * δ))) with hA
  set B : ℝ := Real.exp ((δ / 2) * (T * q a - T * δ)) with hB
  have pt : ∀ ω : Fin T → Fin d,
      (if (T : ℝ) * δ ≤ |cnt ω a - T * q a| then (1:ℝ) else 0)
        ≤ A * Real.exp ((δ / 2) * cnt ω a) + B * Real.exp (-(δ / 2) * cnt ω a) := by
    intro ω
    have pA : 0 ≤ A * Real.exp ((δ / 2) * cnt ω a) := by positivity
    have pB : 0 ≤ B * Real.exp (-(δ / 2) * cnt ω a) := by positivity
    split_ifs with h
    · rcases le_abs'.1 h with h' | h'
      · have : 1 ≤ B * Real.exp (-(δ / 2) * cnt ω a) := by
          rw [hB, ← Real.exp_add]
          apply Real.one_le_exp
          have : 0 ≤ (δ / 2) * (-(T * δ) - (cnt ω a - T * q a)) :=
            mul_nonneg (by linarith) (by linarith)
          nlinarith
        linarith
      · have : 1 ≤ A * Real.exp ((δ / 2) * cnt ω a) := by
          rw [hA, ← Real.exp_add]
          apply Real.one_le_exp
          have : 0 ≤ (δ / 2) * ((cnt ω a - T * q a) - T * δ) :=
            mul_nonneg (by linarith) (by linarith)
          nlinarith
        linarith
    · linarith
  have hw : ∀ ω : Fin T → Fin d, 0 ≤ ∏ t, q (ω t) :=
    fun ω => Finset.prod_nonneg (fun t _ => hq0 _)
  calc ∑ ω : Fin T → Fin d,
        (∏ t, q (ω t)) * (if (T : ℝ) * δ ≤ |cnt ω a - T * q a| then (1:ℝ) else 0)
      ≤ ∑ ω : Fin T → Fin d, (∏ t, q (ω t)) *
          (A * Real.exp ((δ / 2) * cnt ω a) + B * Real.exp (-(δ / 2) * cnt ω a)) :=
        Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (pt ω) (hw ω))
    _ = A * ∑ ω : Fin T → Fin d, (∏ t, q (ω t)) * Real.exp ((δ / 2) * cnt ω a)
        + B * ∑ ω : Fin T → Fin d, (∏ t, q (ω t)) * Real.exp (-(δ / 2) * cnt ω a) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun ω _ => ?_)
        ring
    _ ≤ A * Real.exp (T * (q a * (δ / 2) + (δ / 2) ^ 2))
        + B * Real.exp (T * (q a * (-(δ / 2)) + (-(δ / 2)) ^ 2)) := by
        gcongr
        · exact mgf_le q hq0 hq1 a _ hl
        · exact mgf_le q hq0 hq1 a _ hl'
    _ = 2 * Real.exp (-(T * (δ ^ 2 / 4))) := by
        rw [hA, hB, ← Real.exp_add, ← Real.exp_add]
        have e1 : -((δ / 2) * (T * q a + T * δ)) + T * (q a * (δ / 2) + (δ / 2) ^ 2)
            = -(T * (δ ^ 2 / 4)) := by ring
        have e2 : (δ / 2) * (T * q a - T * δ) + T * (q a * (-(δ / 2)) + (-(δ / 2)) ^ 2)
            = -(T * (δ ^ 2 / 4)) := by ring
        rw [e1, e2]; ring

lemma prod_ge {d T : ℕ} (p q : Fin d → ℝ) (hp : ∀ i, 0 < p i) (hq0 : ∀ i, 0 ≤ q i)
    (ω : Fin T → Fin d) :
    (∏ t, q (ω t)) * Real.exp (-(∑ i, cnt ω i * Real.log (q i / p i))) ≤ ∏ t, p (ω t) := by
  have key : ∀ i, q i * Real.exp (-(Real.log (q i / p i))) ≤ p i := by
    intro i
    rcases (hq0 i).eq_or_lt with h | h
    · rw [← h]; simp [(hp i).le]
    · rw [Real.exp_neg, Real.exp_log (div_pos h (hp i)), inv_div]
      have : q i * (p i / q i) = p i := by field_simp
      rw [this]
  have hs : ∑ i, cnt ω i * Real.log (q i / p i) = ∑ t, Real.log (q (ω t) / p (ω t)) := by
    rw [sum_comp_count ω (fun i => Real.log (q i / p i))]; rfl
  rw [hs, ← Finset.sum_neg_distrib, Real.exp_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun t _ => mul_nonneg (hq0 _) (Real.exp_pos _).le)
    (fun t _ => key _)

end DRO1LAux

open DROOptimal.Predictor in
theorem solution {d : ℕ} (ℙ : Δ d) (hℙ : ∀ i, 0 < (ℙ : Fin d → ℝ) i) (D : Set (Δ d))
    (hD : MeasurableSet D) (s : ℝ)
    (hs : (⨅ ℙ' ∈ interior D, relEntropy ℙ' ℙ) < (s : EReal)) :
    ∀ᶠ T : ℕ in Filter.atTop, Real.exp (-(s * (T : ℝ))) ≤ empProb ℙ T D := by
  classical
  obtain ⟨Q, hQD, hQs⟩ : ∃ Q ∈ interior D, relEntropy Q ℙ < (s : EReal) := by
    rw [iInf_lt_iff] at hs
    obtain ⟨Q, hQ⟩ := hs
    rw [iInf_lt_iff] at hQ
    obtain ⟨hQD, hQs⟩ := hQ
    exact ⟨Q, hQD, hQs⟩
  set p : Fin d → ℝ := (ℙ : Fin d → ℝ) with hp_def
  set q : Fin d → ℝ := (Q : Fin d → ℝ) with hq_def
  have hq0 : ∀ i, 0 ≤ q i := fun i => Q.2.1 i
  have hq1 : ∑ i, q i = 1 := Q.2.2
  set I : ℝ := ∑ i, q i * Real.log (q i / p i) with hI_def
  have hIs : I < s := by
    rw [DRO1LAux.relEntropy_of_pos Q ℙ hℙ] at hQs; exact_mod_cast hQs
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, Metric.ball Q ε ⊆ D :=
    Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hQD)
  set ℓ : Fin d → ℝ := fun i => Real.log (q i / p i) with hℓ_def
  set M : ℝ := ∑ i, |ℓ i| with hM_def
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hsI : 0 < s - I := by linarith
  set δ : ℝ := min 1 (min (ε / 2) ((s - I) / (2 * (M + 1)))) with hδ_def
  have hcpos : 0 < (s - I) / (2 * (M + 1)) := by positivity
  have hδ : 0 < δ := by
    simp only [hδ_def, lt_min_iff]; exact ⟨one_pos, by linarith, hcpos⟩
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ < ε := by
    have : δ ≤ ε / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hδM : δ * M < (s - I) / 2 := by
    have h1 : δ ≤ (s - I) / (2 * (M + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 : δ * M ≤ (s - I) / (2 * (M + 1)) * M := mul_le_mul_of_nonneg_right h1 hM
    have h3 : (s - I) / (2 * (M + 1)) * M < (s - I) / (2 * (M + 1)) * (M + 1) := by
      nlinarith
    have h4 : (s - I) / (2 * (M + 1)) * (M + 1) = (s - I) / 2 := by
      field_simp
    linarith
  set g : ℝ := s - I - δ * M with hg_def
  have hg : 0 < g := by simp only [hg_def]; linarith
  set c : ℝ := δ ^ 2 / 4 with hc_def
  have hc : 0 < c := by positivity
  -- the key bound
  have bound : ∀ T : ℕ, 0 < T →
      Real.exp (-(T * (I + δ * M))) * (1 - 2 * d * Real.exp (-(T * c))) ≤ empProb ℙ T D := by
    intro T hT
    have hTr : (0:ℝ) < T := by exact_mod_cast hT
    let good : (Fin T → Fin d) → Prop := fun ω => ∀ a, |DRO1LAux.cnt ω a - T * q a| < T * δ
    let w : (Fin T → Fin d) → ℝ := fun ω => ∏ t, q (ω t)
    have hw : ∀ ω, 0 ≤ w ω := fun ω => Finset.prod_nonneg (fun t _ => hq0 _)
    -- good paths have empirical vector in D
    have hgoodD : ∀ ω, good ω → EmpiricalIn ω D := by
      intro ω hω
      have hmem : empiricalVec ω ∈ stdSimplex ℝ (Fin d) :=
        ⟨fun i => DRO1LAux.emp_nonneg ω i, DRO1LAux.emp_sum_one hT ω⟩
      refine ⟨hmem, hball ?_⟩
      rw [Metric.mem_ball, Subtype.dist_eq, dist_pi_lt_iff hε]
      intro i
      rw [Real.dist_eq]
      have e : empiricalVec ω i - q i = (DRO1LAux.cnt ω i - T * q i) / T := by
        unfold empiricalVec DRO1LAux.cnt; field_simp
      show |empiricalVec ω i - (Q : Fin d → ℝ) i| < ε
      rw [← hq_def, e, abs_div, abs_of_pos hTr, div_lt_iff₀ hTr]
      have := hω i
      nlinarith
    -- exponent bound on good paths
    have hexp : ∀ ω, good ω →
        ∑ i, DRO1LAux.cnt ω i * Real.log (q i / p i) ≤ T * (I + δ * M) := by
      intro ω hω
      have h1 : ∀ i, DRO1LAux.cnt ω i * ℓ i ≤ T * (q i * ℓ i) + T * δ * |ℓ i| := by
        intro i
        have h2 : (DRO1LAux.cnt ω i - T * q i) * ℓ i ≤ T * δ * |ℓ i| := by
          calc (DRO1LAux.cnt ω i - T * q i) * ℓ i
              ≤ |(DRO1LAux.cnt ω i - T * q i) * ℓ i| := le_abs_self _
            _ = |DRO1LAux.cnt ω i - T * q i| * |ℓ i| := abs_mul _ _
            _ ≤ T * δ * |ℓ i| := mul_le_mul_of_nonneg_right (hω i).le (abs_nonneg _)
        nlinarith
      calc ∑ i, DRO1LAux.cnt ω i * Real.log (q i / p i)
          = ∑ i, DRO1LAux.cnt ω i * ℓ i := rfl
        _ ≤ ∑ i, (T * (q i * ℓ i) + T * δ * |ℓ i|) := Finset.sum_le_sum (fun i _ => h1 i)
        _ = T * (I + δ * M) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          simp only [hI_def, hM_def, hℓ_def]; ring
    -- mass of good paths
    have hgood_mass : 1 - 2 * d * Real.exp (-(T * c)) ≤ ∑ ω, (if good ω then w ω else 0) := by
      have pt : ∀ ω, w ω - ∑ a, w ω *
          (if (T : ℝ) * δ ≤ |DRO1LAux.cnt ω a - T * q a| then (1:ℝ) else 0)
          ≤ (if good ω then w ω else 0) := by
        intro ω
        by_cases hω : good ω
        · rw [if_pos hω]
          have : ∀ a, w ω * (if (T : ℝ) * δ ≤ |DRO1LAux.cnt ω a - T * q a| then (1:ℝ) else 0)
              = 0 := by
            intro a; rw [if_neg (not_le.2 (hω a))]; ring
          simp [this]
        · rw [if_neg hω]
          simp only [good, not_forall, not_lt] at hω
          obtain ⟨a, ha⟩ := hω
          have : w ω * (if (T : ℝ) * δ ≤ |DRO1LAux.cnt ω a - T * q a| then (1:ℝ) else 0)
              ≤ ∑ a, w ω *
                (if (T : ℝ) * δ ≤ |DRO1LAux.cnt ω a - T * q a| then (1:ℝ) else 0) :=
            Finset.single_le_sum (f := fun a => w ω *
                (if (T : ℝ) * δ ≤ |DRO1LAux.cnt ω a - T * q a| then (1:ℝ) else 0))
              (fun b _ => mul_nonneg (hw ω) (by split_ifs <;> norm_num)) (Finset.mem_univ a)
          rw [if_pos ha, mul_one] at this
          linarith
      have htail : ∀ a, ∑ ω : Fin T → Fin d, w ω *
          (if (T : ℝ) * δ ≤ |DRO1LAux.cnt ω a - T * q a| then (1:ℝ) else 0)
          ≤ 2 * Real.exp (-(T * c)) := fun a => DRO1LAux.tail_le q hq0 hq1 a δ hδ hδ1
      calc 1 - 2 * d * Real.exp (-(T * c))
          = ∑ ω, w ω - ∑ a : Fin d, 2 * Real.exp (-(T * c)) := by
            rw [DRO1LAux.mass_one q hq1]; simp; ring
        _ ≤ ∑ ω, w ω - ∑ a : Fin d, ∑ ω : Fin T → Fin d, w ω *
            (if (T : ℝ) * δ ≤ |DRO1LAux.cnt ω a - T * q a| then (1:ℝ) else 0) := by
            have := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => htail a)
            linarith
        _ = ∑ ω, (w ω - ∑ a, w ω *
            (if (T : ℝ) * δ ≤ |DRO1LAux.cnt ω a - T * q a| then (1:ℝ) else 0)) := by
            rw [Finset.sum_sub_distrib, Finset.sum_comm]
        _ ≤ ∑ ω, (if good ω then w ω else 0) := Finset.sum_le_sum (fun ω _ => pt ω)
    -- assemble
    have hpt : ∀ ω, (if good ω then w ω else 0) * Real.exp (-(T * (I + δ * M)))
        ≤ (if EmpiricalIn ω D then ∏ t, (ℙ : Fin d → ℝ) (ω t) else 0) := by
      intro ω
      by_cases hω : good ω
      · rw [if_pos hω, if_pos (hgoodD ω hω)]
        calc w ω * Real.exp (-(T * (I + δ * M)))
            ≤ w ω * Real.exp (-(∑ i, DRO1LAux.cnt ω i * Real.log (q i / p i))) := by
              apply mul_le_mul_of_nonneg_left _ (hw ω)
              apply Real.exp_le_exp.2
              have := hexp ω hω; linarith
          _ ≤ ∏ t, p (ω t) := DRO1LAux.prod_ge p q hℙ hq0 ω
      · rw [if_neg hω, zero_mul]
        split_ifs
        · exact Finset.prod_nonneg (fun t _ => (hℙ _).le)
        · exact le_refl _
    calc Real.exp (-(T * (I + δ * M))) * (1 - 2 * d * Real.exp (-(T * c)))
        ≤ Real.exp (-(T * (I + δ * M))) * ∑ ω, (if good ω then w ω else 0) :=
          mul_le_mul_of_nonneg_left hgood_mass (Real.exp_pos _).le
      _ = ∑ ω, (if good ω then w ω else 0) * Real.exp (-(T * (I + δ * M))) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun ω _ => ?_); ring
      _ ≤ ∑ ω, (if EmpiricalIn ω D then ∏ t, (ℙ : Fin d → ℝ) (ω t) else 0) :=
          Finset.sum_le_sum (fun ω _ => hpt ω)
      _ = empProb ℙ T D := rfl
  -- eventually
  refine Filter.eventually_atTop.2 ⟨Nat.ceil (1 / g + 4 * d / c) + 1, fun T hT => ?_⟩
  have hT1 : (Nat.ceil (1 / g + 4 * d / c) : ℝ) + 1 ≤ T := by exact_mod_cast hT
  have hceil := Nat.le_ceil (1 / g + 4 * d / c)
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hgc1 : 0 ≤ 1 / g := by positivity
  have hgc2 : 0 ≤ 4 * d / c := by positivity
  set x : ℝ := (T : ℝ) with hx
  have hTpos : 0 < T := by
    have : (0:ℝ) < T := by linarith [Nat.cast_nonneg (α := ℝ) (Nat.ceil (1 / g + 4 * d / c))]
    exact_mod_cast this
  have hxg : 1 ≤ x * g := by
    have h1 : 1 / g ≤ x := by linarith
    have h2 : 1 / g * g = 1 := by field_simp
    have := mul_le_mul_of_nonneg_right h1 hg.le
    linarith
  have hxc : 4 * d ≤ x * c := by
    have h1 : 4 * d / c ≤ x := by linarith
    have h2 : 4 * d / c * c = 4 * d := by field_simp
    have := mul_le_mul_of_nonneg_right h1 hc.le
    linarith
  have hE1 : 2 * d * Real.exp (-(x * c)) ≤ 1 / 2 := by
    have e : Real.exp (-(x * c)) * Real.exp (x * c) = 1 := by rw [← Real.exp_add]; simp
    have hge : 4 * d + 1 ≤ Real.exp (x * c) := by
      have := Real.add_one_le_exp (x * c); linarith
    have hpos := Real.exp_pos (-(x * c))
    have := mul_le_mul_of_nonneg_left hge hpos.le
    nlinarith
  have hE2 : Real.exp (-(x * g)) ≤ 1 / 2 := by
    have e : Real.exp (-(x * g)) * Real.exp (x * g) = 1 := by rw [← Real.exp_add]; simp
    have hge : 2 ≤ Real.exp (x * g) := by
      have := Real.add_one_le_exp (x * g); linarith
    have hpos := Real.exp_pos (-(x * g))
    have := mul_le_mul_of_nonneg_left hge hpos.le
    nlinarith
  have hsplit : Real.exp (-(s * x)) = Real.exp (-(x * (I + δ * M))) * Real.exp (-(x * g)) := by
    rw [← Real.exp_add]; congr 1; simp only [hg_def]; ring
  calc Real.exp (-(s * (T : ℝ))) = Real.exp (-(s * x)) := rfl
    _ = Real.exp (-(x * (I + δ * M))) * Real.exp (-(x * g)) := hsplit
    _ ≤ Real.exp (-(x * (I + δ * M))) * (1 - 2 * d * Real.exp (-(x * c))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        linarith
    _ ≤ empProb ℙ T D := bound T hTpos
