-- Prove2me | solution 1 for BauerleRiederMDP.MeanRisk.theorem_4_7_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T08:47:52.613211+00:00
-- url     : https://prove2.me/submissions/cb9ece72-d81c-4623-b1de-421f98a612e0

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket
import Definitions.Def_BauerleRiederMDP_MeanRisk_valueMR
import Definitions.Def_BauerleRiederMDP_MeanRisk_IsOptimalMR

set_option autoImplicit false

open MeasureTheory

namespace P8c40

/-! Draft for BauerleRiederMDP.MeanRisk.theorem_4_7_3 (8c40cfb2). Plan: scratch/decomp/8c40cfb2.plan.md.
Duality route: Z := (1+λ*)ρ - λ*, ρ = dQ/dP, 0 ≤ Z ≤ (1-γ)⁻¹ ⇔ λ* ≤ both terms of the min. -/

/-- E. The threshold `γ₂`: `λ₁ ≤ λ₂ ↔ γ₂ ≤ γ`. -/
lemma lam_le_iff (p q γ : ℝ) (N : ℕ) (hN : 1 ≤ N) (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1)
    (hγ1 : γ < 1) :
    q ^ N / (p ^ N - q ^ N) ≤ ((1 - p) ^ N * (1 - γ)⁻¹ - (1 - q) ^ N) / ((1 - q) ^ N - (1 - p) ^ N) ↔
      p ^ N * ((1 - q) ^ N - (1 - p) ^ N) / ((p * (1 - q)) ^ N - (q * (1 - p)) ^ N) ≤ γ := by
  have hN0 : N ≠ 0 := by omega
  have ha : q ^ N < p ^ N := pow_lt_pow_left₀ hqp hq0.le hN0
  have hb : 0 < q ^ N := pow_pos hq0 N
  have he : 0 < (1 - p) ^ N := pow_pos (by linarith) N
  have hc : (1 - p) ^ N < (1 - q) ^ N := pow_lt_pow_left₀ (by linarith) (by linarith) hN0
  have hpq : q * (1 - p) < p * (1 - q) := by nlinarith
  have hD : 0 < (p * (1 - q)) ^ N - (q * (1 - p)) ^ N := by
    have := pow_lt_pow_left₀ hpq (by nlinarith) hN0
    linarith
  have ht : 0 < 1 - γ := by linarith
  have hL : ((1 - p) ^ N * (1 - γ)⁻¹ - (1 - q) ^ N) / ((1 - q) ^ N - (1 - p) ^ N) =
      ((1 - p) ^ N - (1 - q) ^ N * (1 - γ)) / ((1 - γ) * ((1 - q) ^ N - (1 - p) ^ N)) := by
    field_simp
  rw [hL, div_le_div_iff₀ (by linarith) (by nlinarith), div_le_iff₀ hD, mul_pow, mul_pow]
  constructor <;> intro h <;> nlinarith

section freeze
open MDPFinance.MeanVariance

/-- Affine policies `x ↦ κ (c + x)`: `X_k + c = (x + c) ∏ (1 + κ R)`. -/
lemma tw_affine {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) (κ c : ℝ) :
    ∀ (k n : ℕ) (x : ℝ) (ω : Ω),
      M.terminalWealth (fun _ x => κ * (c + x)) k n x ω + c =
        (x + c) * ∏ j ∈ Finset.range k, (1 + κ * M.R (n + j + 1) ω) := by
  intro k
  induction k with
  | zero => intro n x ω; simp [MeanRiskMarket.terminalWealth]
  | succ k ih =>
    intro n x ω
    rw [MeanRiskMarket.terminalWealth, ih, Finset.prod_range_succ']
    have e : ∀ j, n + 1 + j + 1 = n + (j + 1) + 1 := fun j => by omega
    simp only [e, add_zero]
    ring

/-- `P(R_1 = … = R_N = v) = r^N` from independence. -/
lemma prob_all {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) (v r : ℝ) (hr : 0 ≤ r)
    (hv : ∀ n, 1 ≤ n → n ≤ M.N → M.measIP {ω | M.R n ω = v} = ENNReal.ofReal r) :
    M.measIP {ω | ∀ j < M.N, M.R (j + 1) ω = v} = ENNReal.ofReal (r ^ M.N) := by
  have hset : {ω | ∀ j < M.N, M.R (j + 1) ω = v} =
      ⋂ i ∈ (Finset.univ : Finset (Fin M.N)), M.R (i.val + 1) ⁻¹' {v} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_univ, Set.mem_preimage,
      Set.mem_singleton_iff, forall_const]
    exact ⟨fun h i => h i.val i.isLt, fun h j hj => h ⟨j, hj⟩⟩
  have h := M.hR_indep.measure_inter_preimage_eq_mul Finset.univ (sets := fun _ => ({v} : Set ℝ))
    (fun i _ => measurableSet_singleton v)
  rw [hset]
  refine h.trans ?_
  have hc : ∀ i : Fin M.N, M.measIP (M.R (i.val + 1) ⁻¹' {v}) = ENNReal.ofReal r :=
    fun i => hv _ (by omega) (by have := i.isLt; omega)
  simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow hr]

/-- Each `R_n` is a.s. `u - 1` or `d - 1`. -/
lemma ae_two {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) (n : ℕ) (h1 : 1 ≤ n)
    (h2 : n ≤ M.N) : ∀ᵐ ω ∂M.measIP, M.R n ω = M.u - 1 ∨ M.R n ω = M.d - 1 := by
  haveI := M.isProb
  have hm := M.hR_meas n h1 h2
  have hA : MeasurableSet {ω | M.R n ω = M.u - 1} := hm (measurableSet_singleton _)
  have hB : MeasurableSet {ω | M.R n ω = M.d - 1} := hm (measurableSet_singleton _)
  have hdisj : Disjoint {ω | M.R n ω = M.u - 1} {ω | M.R n ω = M.d - 1} := by
    rw [Set.disjoint_left]
    intro ω h h'
    simp only [Set.mem_setOf_eq] at h h'
    have := M.hd_lt_one
    have := M.hone_lt_u
    linarith
  have hU : M.measIP ({ω | M.R n ω = M.u - 1} ∪ {ω | M.R n ω = M.d - 1}) = 1 := by
    rw [measure_union hdisj hB, (M.hR_law n h1 h2).1, (M.hR_law n h1 h2).2,
      ← ENNReal.ofReal_add M.hp_mem.1.le (by linarith [M.hp_mem.2])]
    simp
  rw [ae_iff]
  have e : {ω | ¬ (M.R n ω = M.u - 1 ∨ M.R n ω = M.d - 1)} =
      ({ω | M.R n ω = M.u - 1} ∪ {ω | M.R n ω = M.d - 1})ᶜ := by
    ext ω; simp
  rw [e, measure_compl (hA.union hB) (measure_ne_top _ _), hU]
  simp

lemma ae_all_two {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) :
    ∀ᵐ ω ∂M.measIP, ∀ j : ℕ, j < M.N → M.R (j + 1) ω = M.u - 1 ∨ M.R (j + 1) ω = M.d - 1 := by
  rw [ae_all_iff]
  intro j
  by_cases hj : j < M.N
  · filter_upwards [ae_two M (j + 1) (by omega) (by omega)] with ω h _
    exact h
  · exact ae_of_all _ (fun ω h => absurd h hj)

/-- Freeze policies: a.s. `X_N = -c + 1{all R = w} (x₀ + c) s^N` when `1 + κ v = 0`, `1 + κ w = s`. -/
lemma freeze_ae {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω)
    (κ c v w s : ℝ) (hv : 1 + κ * v = 0) (hw : 1 + κ * w = s)
    (hvw : ∀ᵐ ω ∂M.measIP, ∀ j : ℕ, j < M.N → M.R (j + 1) ω = v ∨ M.R (j + 1) ω = w) :
    ∀ᵐ ω ∂M.measIP, M.terminalWealth (fun _ x => κ * (c + x)) M.N 0 M.x0 ω =
      -c + (if ∀ j < M.N, M.R (j + 1) ω = w then (M.x0 + c) * s ^ M.N else 0) := by
  filter_upwards [hvw] with ω hω
  have h := tw_affine M κ c M.N 0 M.x0 ω
  simp only [zero_add] at h
  split_ifs with hall
  · have hp : ∏ j ∈ Finset.range M.N, (1 + κ * M.R (j + 1) ω) = s ^ M.N := by
      rw [Finset.prod_eq_pow_card (b := s)
        (fun j hj => by rw [hall j (Finset.mem_range.1 hj), hw]), Finset.card_range]
    rw [hp] at h
    linarith
  · push Not at hall
    obtain ⟨j, hj, hne⟩ := hall
    have hp : ∏ j ∈ Finset.range M.N, (1 + κ * M.R (j + 1) ω) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_range.2 hj) ?_
      rcases hω j hj with h' | h'
      · rw [h', hv]
      · exact absurd h' hne
    rw [hp, mul_zero] at h
    linarith

/-- The down-freeze factor: `1 + (1-d)⁻¹ (u-1) = q⁻¹`. -/
lemma factor_D {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) :
    1 + (1 - M.d)⁻¹ * (M.u - 1) = M.q⁻¹ := by
  have h1 : 1 - M.d ≠ 0 := by linarith [M.hd_lt_one]
  have h2 : M.u - M.d ≠ 0 := by linarith [M.hd_lt_one, M.hone_lt_u]
  rw [MeanRiskMarket.q, inv_div]
  field_simp
  ring

/-- The up-freeze factor: `1 + (1-u)⁻¹ (d-1) = (1-q)⁻¹`. -/
lemma factor_C {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) :
    1 + (1 - M.u)⁻¹ * (M.d - 1) = (1 - M.q)⁻¹ := by
  have h1 : 1 - M.u ≠ 0 := by linarith [M.hone_lt_u]
  have h2 : M.u - M.d ≠ 0 := by linarith [M.hd_lt_one, M.hone_lt_u]
  have h3 : 1 - (1 - M.d) / (M.u - M.d) = (M.u - 1) / (M.u - M.d) := by field_simp; ring
  rw [MeanRiskMarket.q, h3, inv_div]
  have h4 : M.u - 1 ≠ 0 := by linarith [M.hone_lt_u]
  field_simp
  ring

end freeze

section twopoint
open BauerleRiederMDP.MeanRisk

/-- VaR of a two-point risk `X = -c + K 1_A` (a.s.), `K > 0`. -/
lemma var_two {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (c K : ℝ) (hK : 0 < K) (A : Set Ω) (hA : MeasurableSet A)
    (hX : ∀ᵐ ω ∂P, X ω = -c + A.indicator (fun _ => K) ω) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    VaR P u X = if u ≤ P.real A then c - K else c := by
  have hset : ∀ x : ℝ, P.real {ω | x + X ω < 0} =
      if x < c - K then 1 else if x < c then 1 - P.real A else 0 := by
    intro x
    have hcongr : {ω | x + X ω < 0} =ᵐ[P] {ω | x + (-c + A.indicator (fun _ => K) ω) < 0} := by
      filter_upwards [hX] with ω hω
      show (x + X ω < 0) = (x + (-c + A.indicator (fun _ => K) ω) < 0)
      rw [hω]
    rw [measureReal_congr hcongr]
    split_ifs with h1 h2
    · have e : {ω | x + (-c + A.indicator (fun _ => K) ω) < 0} = Set.univ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        have : A.indicator (fun _ => K) ω ≤ K := by
          by_cases hω : ω ∈ A <;> simp [hω, hK.le]
        linarith
      rw [e]; simp
    · have e : {ω | x + (-c + A.indicator (fun _ => K) ω) < 0} = Aᶜ := by
        ext ω
        by_cases hω : ω ∈ A <;> simp [hω] <;> linarith
      rw [e, measureReal_compl hA]; simp
    · have e : {ω | x + (-c + A.indicator (fun _ => K) ω) < 0} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        have : 0 ≤ A.indicator (fun _ => K) ω := by
          by_cases hω : ω ∈ A <;> simp [hω, hK.le]
        linarith
      rw [e]; simp
  unfold VaR
  simp_rw [hset]
  split_ifs with hu
  · have e : {x : ℝ | (if x < c - K then (1:ℝ) else if x < c then 1 - P.real A else 0) ≤ 1 - u}
        = Set.Ici (c - K) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_Ici]
      constructor
      · intro h
        by_contra hx
        push Not at hx
        rw [if_pos hx] at h
        linarith
      · intro hx
        rw [if_neg (not_lt.2 hx)]
        split_ifs <;> linarith
    rw [e, csInf_Ici]
  · push Not at hu
    have e : {x : ℝ | (if x < c - K then (1:ℝ) else if x < c then 1 - P.real A else 0) ≤ 1 - u}
        = Set.Ici c := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_Ici]
      constructor
      · intro h
        by_contra hx
        push Not at hx
        split_ifs at h with h1 <;> linarith
      · intro hx
        rw [if_neg (by linarith), if_neg (not_lt.2 hx)]
        linarith
    rw [e, csInf_Ici]

/-- Quantile AVaR of a two-point risk `X = -c + K 1_A` (a.s.), `K > 0`, `P(A) < 1`. -/
lemma avar_two {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (c K γ : ℝ) (hK : 0 < K) (A : Set Ω) (hA : MeasurableSet A)
    (hX : ∀ᵐ ω ∂P, X ω = -c + A.indicator (fun _ => K) ω) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (ha1 : P.real A < 1) :
    AVaR P γ X = c - K * max (P.real A - γ) 0 / (1 - γ) := by
  have hfun : ∀ u ∈ Set.Ioo γ 1,
      VaR P u X = c - (Set.Iic (P.real A)).indicator (fun _ => K) u := by
    intro u hu
    rw [var_two P X c K hK A hA hX u (by linarith [hu.1]) hu.2]
    by_cases h : u ≤ P.real A
    · rw [if_pos h, Set.indicator_of_mem (show u ∈ Set.Iic (P.real A) from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show u ∉ Set.Iic (P.real A) from h)]
      ring
  unfold AVaR
  rw [setIntegral_congr_fun measurableSet_Ioo hfun]
  have hfin : volume (Set.Ioo γ 1) ≠ ⊤ := measure_Ioo_lt_top.ne
  have hc : IntegrableOn (fun _ : ℝ => c) (Set.Ioo γ 1) := integrableOn_const hfin
  have hk : IntegrableOn (fun _ : ℝ => K) (Set.Ioo γ 1) := integrableOn_const hfin
  rw [integral_sub hc (hk.indicator measurableSet_Iic), setIntegral_const,
    setIntegral_indicator measurableSet_Iic, setIntegral_const]
  have hI : Set.Ioo γ 1 ∩ Set.Iic (P.real A) = Set.Ioc γ (P.real A) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, by linarith⟩, h3⟩
  have ht : 1 - γ ≠ 0 := by linarith
  rw [hI, Real.volume_real_Ioo_of_le hγ1.le, measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal', smul_eq_mul, smul_eq_mul]
  field_simp

end twopoint

section laws
open MDPFinance.MeanVariance

lemma meas_all {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) (v : ℝ) :
    MeasurableSet {ω | ∀ j < M.N, M.R (j + 1) ω = v} := by
  have hset : {ω | ∀ j < M.N, M.R (j + 1) ω = v} = ⋂ i : Fin M.N, M.R (i.val + 1) ⁻¹' {v} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h i => h i.val i.isLt, fun h j hj => h ⟨j, hj⟩⟩
  rw [hset]
  exact MeasurableSet.iInter (fun i => M.hR_meas _ (by omega) (by have := i.isLt; omega)
    (measurableSet_singleton v))

/-- Down-freeze policy (child D): a.s. two-point, up-path probability `p^N`. -/
lemma D_law {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) (c : ℝ) :
    M.measIP.real {ω | ∀ j < M.N, M.R (j + 1) ω = M.u - 1} = M.p ^ M.N ∧
    ∀ᵐ ω ∂M.measIP, M.terminalWealth (fun _ x => (1 - M.d)⁻¹ * (c + x)) M.N 0 M.x0 ω =
      -c + {ω | ∀ j < M.N, M.R (j + 1) ω = M.u - 1}.indicator
        (fun _ => (M.x0 + c) * M.q⁻¹ ^ M.N) ω := by
  have h1 : 1 - M.d ≠ 0 := by linarith [M.hd_lt_one]
  constructor
  · rw [measureReal_def, prob_all M (M.u - 1) M.p M.hp_mem.1.le (fun n a b => (M.hR_law n a b).1),
      ENNReal.toReal_ofReal (pow_nonneg M.hp_mem.1.le _)]
  · have hv : 1 + (1 - M.d)⁻¹ * (M.d - 1) = 0 := by
      rw [show M.d - 1 = -(1 - M.d) by ring, mul_neg, inv_mul_cancel₀ h1]; ring
    have hvw : ∀ᵐ ω ∂M.measIP, ∀ j : ℕ, j < M.N →
        M.R (j + 1) ω = M.d - 1 ∨ M.R (j + 1) ω = M.u - 1 := by
      filter_upwards [ae_all_two M] with ω h j hj
      exact (h j hj).symm
    filter_upwards [freeze_ae M _ c _ _ _ hv (factor_D M) hvw] with ω h
    rw [h]
    by_cases hP : ∀ j < M.N, M.R (j + 1) ω = M.u - 1 <;> simp [Set.indicator_apply, hP]

/-- Up-freeze policy (child C): a.s. two-point, down-path probability `(1-p)^N`. -/
lemma C_law {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) (c : ℝ) :
    M.measIP.real {ω | ∀ j < M.N, M.R (j + 1) ω = M.d - 1} = (1 - M.p) ^ M.N ∧
    ∀ᵐ ω ∂M.measIP, M.terminalWealth (fun _ x => (1 - M.u)⁻¹ * (c + x)) M.N 0 M.x0 ω =
      -c + {ω | ∀ j < M.N, M.R (j + 1) ω = M.d - 1}.indicator
        (fun _ => (M.x0 + c) * (1 - M.q)⁻¹ ^ M.N) ω := by
  have h1 : 1 - M.u ≠ 0 := by linarith [M.hone_lt_u]
  have hp1 : 0 ≤ 1 - M.p := by linarith [M.hp_mem.2]
  constructor
  · rw [measureReal_def, prob_all M (M.d - 1) (1 - M.p) hp1 (fun n a b => (M.hR_law n a b).2),
      ENNReal.toReal_ofReal (pow_nonneg hp1 _)]
  · have hv : 1 + (1 - M.u)⁻¹ * (M.u - 1) = 0 := by
      rw [show M.u - 1 = -(1 - M.u) by ring, mul_neg, inv_mul_cancel₀ h1]; ring
    filter_upwards [freeze_ae M _ c _ _ _ hv (factor_C M) (ae_all_two M)] with ω h
    rw [h]
    by_cases hP : ∀ j < M.N, M.R (j + 1) ω = M.d - 1 <;> simp [Set.indicator_apply, hP]

/-- Mean of a two-point risk. -/
lemma mean_two {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (c K : ℝ) (A : Set Ω) (hA : MeasurableSet A)
    (hX : ∀ᵐ ω ∂P, X ω = -c + A.indicator (fun _ => K) ω) :
    ∫ ω, X ω ∂P = -c + P.real A * K := by
  rw [integral_congr_ae hX, integral_add (integrable_const _)
    ((integrable_const K).indicator hA), integral_const, integral_indicator_const K hA]
  simp

end laws

section attain
open MDPFinance.MeanVariance

/-- `(1 - x^N)/(1 - x)^N` is increasing on `(0,1)`. -/
lemma mono_f (x y : ℝ) (N : ℕ) (hN : 1 ≤ N) (hx0 : 0 < x) (hxy : x < y) (hy1 : y < 1) :
    (1 - x ^ N) * (1 - y) ^ N ≤ (1 - y ^ N) * (1 - x) ^ N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [← mul_neg_geom_sum x, ← mul_neg_geom_sum y, pow_succ, pow_succ]
  have hs : ∑ i ∈ Finset.range (n + 1), x ^ i ≤ ∑ i ∈ Finset.range (n + 1), y ^ i :=
    Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ hx0.le hxy.le i)
  have hp : (1 - y) ^ n ≤ (1 - x) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
  have h0 : 0 ≤ ∑ i ∈ Finset.range (n + 1), x ^ i :=
    Finset.sum_nonneg (fun i _ => pow_nonneg hx0.le i)
  have h1 : 0 ≤ (1 - y) ^ n := pow_nonneg (by linarith) n
  have h2 := mul_le_mul hs hp h1 (h0.trans hs)
  have hxy' : 0 ≤ (1 - x) * (1 - y) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h2 hxy']

lemma q_pos {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) : 0 < M.q :=
  div_pos (by linarith [M.hd_lt_one]) (by linarith [M.hd_lt_one, M.hone_lt_u])

lemma q_lt_one {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) : M.q < 1 := by
  rw [MeanRiskMarket.q, div_lt_one (by linarith [M.hd_lt_one, M.hone_lt_u])]
  linarith [M.hone_lt_u]

/-- `p^N ≤ γ₂`. -/
lemma pN_le_γ2 (p q : ℝ) (N : ℕ) (hN : 1 ≤ N) (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) :
    p ^ N ≤ p ^ N * ((1 - q) ^ N - (1 - p) ^ N) / ((p * (1 - q)) ^ N - (q * (1 - p)) ^ N) := by
  have hN0 : N ≠ 0 := by omega
  have hpq : q * (1 - p) < p * (1 - q) := by nlinarith
  have hD : 0 < (p * (1 - q)) ^ N - (q * (1 - p)) ^ N := by
    have := pow_lt_pow_left₀ hpq (by nlinarith) hN0
    linarith
  rw [le_div_iff₀ hD, mul_pow, mul_pow]
  have hm := mono_f q p N hN hq0 hqp hp1
  nlinarith [mul_le_mul_of_nonneg_left hm (pow_pos (hq0.trans hqp) N).le]

/-- `γ₂ ≤ 1 - (1-p)^N`. -/
lemma γ2_le (p q : ℝ) (N : ℕ) (hN : 1 ≤ N) (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) :
    p ^ N * ((1 - q) ^ N - (1 - p) ^ N) / ((p * (1 - q)) ^ N - (q * (1 - p)) ^ N) ≤
      1 - (1 - p) ^ N := by
  have hN0 : N ≠ 0 := by omega
  have hpq : q * (1 - p) < p * (1 - q) := by nlinarith
  have hD : 0 < (p * (1 - q)) ^ N - (q * (1 - p)) ^ N := by
    have := pow_lt_pow_left₀ hpq (by nlinarith) hN0
    linarith
  rw [div_le_iff₀ hD, mul_pow, mul_pow]
  have hm := mono_f (1 - p) (1 - q) N hN (by linarith) (by linarith) (by linarith)
  simp only [sub_sub_cancel] at hm
  have he : 0 ≤ (1 - p) ^ N := pow_nonneg (by linarith) N
  nlinarith [mul_le_mul_of_nonneg_left hm he]

/-- Attainment by the down-freeze policy `x ↦ (c+x)/(1-d)` (case `γ ≥ γ₂`). -/
lemma att_D {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) (hN : 1 ≤ M.N)
    (hpq : M.q < M.p) (c : ℝ)
    (hc : c = (M.μ - M.x0) * (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N)) - M.x0)
    (hγ : M.p ^ M.N * ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N) /
      ((M.p * (1 - M.q)) ^ M.N - (M.q * (1 - M.p)) ^ M.N) ≤ M.γ) :
    M.IsAdmissible 0 (fun _ x => (1 - M.d)⁻¹ * (c + x)) ∧
    M.meanXN (fun _ x => (1 - M.d)⁻¹ * (c + x)) = M.μ ∧
    BauerleRiederMDP.MeanRisk.AVaR M.measIP M.γ (M.terminalWealth (fun _ x => (1 - M.d)⁻¹ * (c + x)) M.N 0 M.x0) = c := by
  haveI := M.isProb
  have hq0 := q_pos M
  have hp0 := M.hp_mem.1
  have hp1 := M.hp_mem.2
  have hN0 : M.N ≠ 0 := by omega
  have hqN : 0 < M.q ^ M.N := pow_pos hq0 _
  have hpqN : M.q ^ M.N < M.p ^ M.N := pow_lt_pow_left₀ hpq hq0.le hN0
  have hpN1 : M.p ^ M.N < 1 := pow_lt_one₀ hp0.le hp1 hN0
  have hD : M.p ^ M.N - M.q ^ M.N ≠ 0 := by linarith
  obtain ⟨hPA, hX⟩ := D_law M c
  have hK : 0 < (M.x0 + c) * M.q⁻¹ ^ M.N := by
    have e : M.x0 + c = (M.μ - M.x0) * (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N)) := by rw [hc]; ring
    rw [e]
    have := M.hx0μ
    exact mul_pos (mul_pos (by linarith) (div_pos hqN (by linarith))) (pow_pos (inv_pos.2 hq0) _)
  refine ⟨fun k _ _ => by fun_prop, ?_, ?_⟩
  · unfold MeanRiskMarket.meanXN
    rw [mean_two _ _ c _ _ (meas_all M _) hX, hPA, inv_pow, hc]
    have : M.q ^ M.N ≠ 0 := hqN.ne'
    field_simp
    ring
  · rw [avar_two _ _ c _ M.γ hK _ (meas_all M _) hX M.hγ.1 M.hγ.2 (by rw [hPA]; exact hpN1), hPA,
      max_eq_right (by linarith [pN_le_γ2 M.p M.q M.N hN hq0 hpq hp1])]
    simp

/-- The up-freeze policy `x ↦ (c+x)/(1-u)` with `x₀ + c < 0`, `γ ≤ 1 - (1-p)^N`. -/
lemma att_C {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) (c : ℝ)
    (hneg : M.x0 + c < 0) (hγ : M.γ ≤ 1 - (1 - M.p) ^ M.N) :
    M.IsAdmissible 0 (fun _ x => (1 - M.u)⁻¹ * (c + x)) ∧
    M.meanXN (fun _ x => (1 - M.u)⁻¹ * (c + x)) =
      -c + (1 - M.p) ^ M.N * ((M.x0 + c) * (1 - M.q)⁻¹ ^ M.N) ∧
    BauerleRiederMDP.MeanRisk.AVaR M.measIP M.γ (M.terminalWealth (fun _ x => (1 - M.u)⁻¹ * (c + x)) M.N 0 M.x0) =
      c - (1 - M.p) ^ M.N * ((M.x0 + c) * (1 - M.q)⁻¹ ^ M.N) / (1 - M.γ) := by
  haveI := M.isProb
  obtain ⟨hPB, hX⟩ := C_law M c
  set B := {ω | ∀ j < M.N, M.R (j + 1) ω = M.d - 1} with hBdef
  set K := (M.x0 + c) * (1 - M.q)⁻¹ ^ M.N with hKdef
  have hB : MeasurableSet B := meas_all M _
  have hK : K < 0 :=
    mul_neg_of_neg_of_pos hneg (pow_pos (inv_pos.2 (by linarith [q_lt_one M])) _)
  have he : 0 < (1 - M.p) ^ M.N := pow_pos (by linarith [M.hp_mem.2]) _
  refine ⟨fun k _ _ => by fun_prop, ?_, ?_⟩
  · unfold MeanRiskMarket.meanXN
    rw [mean_two _ _ c _ _ hB hX, hPB]
  · have hX' : ∀ᵐ ω ∂M.measIP, M.terminalWealth (fun _ x => (1 - M.u)⁻¹ * (c + x)) M.N 0 M.x0 ω =
        -(c - K) + Bᶜ.indicator (fun _ => -K) ω := by
      filter_upwards [hX] with ω h
      rw [h]
      by_cases hω : ω ∈ B
      · rw [Set.indicator_of_mem hω, Set.indicator_of_notMem (show ω ∉ Bᶜ from fun h' => h' hω)]
        ring
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_mem (show ω ∈ Bᶜ from hω)]
        ring
    have hPc : M.measIP.real Bᶜ = 1 - (1 - M.p) ^ M.N := by
      rw [measureReal_compl hB, hPB]; simp
    rw [avar_two _ _ (c - K) (-K) M.γ (by linarith) Bᶜ hB.compl hX' M.hγ.1 M.hγ.2
      (by rw [hPc]; linarith), hPc, max_eq_left (by linarith)]
    have ht : 1 - M.γ ≠ 0 := by linarith [M.hγ.2]
    field_simp
    ring

/-- Attainment by the up-freeze policy (case `γ ≤ γ₂`): AVaR `= (μ - x₀) λ₂ - x₀`. -/
lemma att_C2 {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) (hN : 1 ≤ M.N)
    (hpq : M.q < M.p) (c : ℝ)
    (hc : c = (M.x0 - M.μ) * ((1 - M.q) ^ M.N / ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N)) - M.x0)
    (hγ : M.γ ≤ M.p ^ M.N * ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N) /
      ((M.p * (1 - M.q)) ^ M.N - (M.q * (1 - M.p)) ^ M.N)) :
    M.IsAdmissible 0 (fun _ x => (1 - M.u)⁻¹ * (c + x)) ∧
    M.meanXN (fun _ x => (1 - M.u)⁻¹ * (c + x)) = M.μ ∧
    BauerleRiederMDP.MeanRisk.AVaR M.measIP M.γ (M.terminalWealth (fun _ x => (1 - M.u)⁻¹ * (c + x)) M.N 0 M.x0) =
      (M.μ - M.x0) * (((1 - M.p) ^ M.N * (1 - M.γ)⁻¹ - (1 - M.q) ^ M.N) /
        ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N)) - M.x0 := by
  have hq0 := q_pos M
  have hq1 := q_lt_one M
  have hp1 := M.hp_mem.2
  have hN0 : M.N ≠ 0 := by omega
  have hce : (1 - M.p) ^ M.N < (1 - M.q) ^ M.N :=
    pow_lt_pow_left₀ (by linarith) (by linarith) hN0
  have he : 0 < (1 - M.p) ^ M.N := pow_pos (by linarith) _
  have hc' : 0 < (1 - M.q) ^ M.N := pow_pos (by linarith) _
  have hx := M.hx0μ
  have hneg : M.x0 + c < 0 := by
    rw [hc]
    have : 0 < (1 - M.q) ^ M.N / ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N) := div_pos hc' (by linarith)
    nlinarith
  obtain ⟨h1, h2, h3⟩ := att_C M c hneg (hγ.trans (γ2_le M.p M.q M.N hN hq0 hpq hp1))
  have hD : (1 - M.q) ^ M.N - (1 - M.p) ^ M.N ≠ 0 := by linarith
  have ht : 1 - M.γ ≠ 0 := by linarith [M.hγ.2]
  refine ⟨h1, ?_, ?_⟩
  · rw [h2, inv_pow, hc]
    field_simp
    ring
  · rw [h3, inv_pow, hc]
    field_simp
    ring

end attain

section dual
open BauerleRiederMDP.MeanRisk Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma F_anti (X : Ω → ℝ) {x y : ℝ} (h : x ≤ y) :
    P.real {ω | y + X ω < 0} ≤ P.real {ω | x + X ω < 0} :=
  measureReal_mono (fun ω (hω : y + X ω < 0) => show x + X ω < 0 by linarith)

lemma F_top (X : Ω → ℝ) (C : ℝ) (hC : ∀ᵐ ω ∂P, |X ω| ≤ C) :
    P.real {ω | C + X ω < 0} = 0 := by
  have h0 : P {ω | C + X ω < 0} = 0 := by
    refine measure_mono_null (fun ω (hω : C + X ω < 0) => ?_) (ae_iff.1 hC)
    show ¬ |X ω| ≤ C
    intro h
    have := neg_abs_le (X ω)
    linarith
  rw [measureReal_def, h0]; simp

lemma F_bot (X : Ω → ℝ) (hX : Measurable X) (C : ℝ) (hC : ∀ᵐ ω ∂P, |X ω| ≤ C) {x : ℝ}
    (hx : x < -C) : P.real {ω | x + X ω < 0} = 1 := by
  have hS : MeasurableSet {ω | x + X ω < 0} := measurableSet_lt (by fun_prop) measurable_const
  have h1 : P {ω | x + X ω < 0} = 1 := by
    refine (prob_compl_eq_zero_iff hS).1 (measure_mono_null (fun ω hω => ?_) (ae_iff.1 hC))
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hω
    show ¬ |X ω| ≤ C
    intro h
    have := le_abs_self (X ω)
    linarith
  rw [measureReal_def, h1]; simp

/-- Right-continuity of `x ↦ P(x + X < 0)`. -/
lemma F_rc (X : Ω → ℝ) (x r : ℝ) (hr : 0 ≤ r)
    (h : ∀ y, x < y → P.real {ω | y + X ω < 0} ≤ r) : P.real {ω | x + X ω < 0} ≤ r := by
  let s : ℕ → Set Ω := fun n => {ω | x + 1 / ((n : ℝ) + 1) + X ω < 0}
  have hm : Monotone s := by
    intro m n hmn ω (hω : x + 1 / ((m : ℝ) + 1) + X ω < 0)
    show x + 1 / ((n : ℝ) + 1) + X ω < 0
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by have : (m : ℝ) ≤ n := by exact_mod_cast hmn
                                                   linarith)
    linarith
  have hU : (⋃ n, s n) = {ω | x + X ω < 0} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, s]
    constructor
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hω
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ) (show 0 < -(x + X ω) by linarith)
      exact ⟨n, by linarith⟩
  have hb : ∀ n, P (s n) ≤ ENNReal.ofReal r := fun n =>
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hr).2
      (h _ (by have : 0 < 1 / ((n : ℝ) + 1) := by positivity
               linarith))
  have hlim := tendsto_measure_iUnion_atTop (μ := P) hm
  rw [hU] at hlim
  exact ENNReal.toReal_le_of_le_ofReal hr (le_of_tendsto' hlim hb)

/-- Galois connection for the quantile `VaR`. -/
lemma var_le_iff (X : Ω → ℝ) (hX : Measurable X) (C : ℝ) (hC : ∀ᵐ ω ∂P, |X ω| ≤ C)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (x : ℝ) :
    VaR P u X ≤ x ↔ P.real {ω | x + X ω < 0} ≤ 1 - u := by
  have hne : ({y : ℝ | P.real {ω | y + X ω < 0} ≤ 1 - u}).Nonempty :=
    ⟨C, by
      show P.real {ω | C + X ω < 0} ≤ 1 - u
      rw [F_top P X C hC]; linarith⟩
  have hbdd : BddBelow {y : ℝ | P.real {ω | y + X ω < 0} ≤ 1 - u} := by
    refine ⟨-C, fun y hy => ?_⟩
    have hy' : P.real {ω | y + X ω < 0} ≤ 1 - u := hy
    by_contra hlt
    push Not at hlt
    rw [F_bot P X hX C hC hlt] at hy'
    linarith
  unfold VaR
  constructor
  · intro hle
    refine F_rc P X x (1 - u) (by linarith) (fun y hy => ?_)
    obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt hne (lt_of_le_of_lt hle hy)
    exact (F_anti P X hzy.le).trans hz
  · intro hx
    exact csInf_le hbdd hx

lemma var_bounds (X : Ω → ℝ) (hX : Measurable X) (C : ℝ) (hC : ∀ᵐ ω ∂P, |X ω| ≤ C)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) : -C ≤ VaR P u X ∧ VaR P u X ≤ C := by
  constructor
  · by_contra hlt
    push Not at hlt
    obtain ⟨y, h1, h2⟩ := exists_between hlt
    have := (var_le_iff P X hX C hC u hu0 hu1 y).1 h1.le
    rw [F_bot P X hX C hC h2] at this
    linarith
  · rw [var_le_iff P X hX C hC u hu0 hu1, F_top P X C hC]; linarith

lemma var_mono (X : Ω → ℝ) (hX : Measurable X) (C : ℝ) (hC : ∀ᵐ ω ∂P, |X ω| ≤ C)
    (γ : ℝ) (hγ0 : 0 < γ) : MonotoneOn (fun u => VaR P u X) (Set.Icc γ 1) := by
  intro u1 h1 u2 h2 h12
  show VaR P u1 X ≤ VaR P u2 X
  rw [var_le_iff P X hX C hC u1 (by linarith [h1.1]) h1.2]
  have := (var_le_iff P X hX C hC u2 (by linarith [h2.1]) h2.2 (VaR P u2 X)).1 le_rfl
  linarith

/-- Example C.2.2 b) at the minimiser `b = VaR_γ`, for a.s. bounded measurable `X`. -/
lemma avar_rep (X : Ω → ℝ) (hX : Measurable X) (C : ℝ) (hC : ∀ᵐ ω ∂P, |X ω| ≤ C)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    AVaR P γ X = VaR P γ X + (1 - γ)⁻¹ * ∫ ω, max (-(X ω + VaR P γ X)) 0 ∂P := by
  set b := VaR P γ X with hbdef
  have hbF : P.real {ω | b + X ω < 0} ≤ 1 - γ :=
    (var_le_iff P X hX C hC γ hγ0 hγ1.le b).1 le_rfl
  have hint : IntegrableOn (fun u => VaR P u X) (Set.Ioo γ 1) :=
    ((var_mono P X hX C hC γ hγ0).integrableOn_isCompact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  have hfin : volume (Set.Ioo γ 1) ≠ ⊤ := measure_Ioo_lt_top.ne
  have hbI : IntegrableOn (fun _ : ℝ => b) (Set.Ioo γ 1) := integrableOn_const hfin
  have hXi : Integrable X P :=
    Integrable.of_bound hX.aestronglyMeasurable C (by
      filter_upwards [hC] with ω h
      simpa [Real.norm_eq_abs] using h)
  have hYi : Integrable (fun ω => max (-(X ω + b)) 0) P :=
    (hXi.add (integrable_const b)).neg.pos_part
  -- layer cake on both sides
  have hL : ∫ u in Set.Ioo γ 1, (VaR P u X - b) =
      ∫ s in Set.Ioi 0, (volume.restrict (Set.Ioo γ 1)).real {u | s < VaR P u X - b} := by
    refine Integrable.integral_eq_integral_meas_lt (hint.sub hbI) ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall (fun u hu => ?_))
    show (0 : ℝ) ≤ VaR P u X - b
    have := var_mono P X hX C hC γ hγ0 ⟨le_rfl, hγ1.le⟩ ⟨hu.1.le, hu.2.le⟩ hu.1.le
    simp only at this
    linarith
  have hR : ∫ ω, max (-(X ω + b)) 0 ∂P =
      ∫ s in Set.Ioi 0, P.real {ω | s < max (-(X ω + b)) 0} :=
    Integrable.integral_eq_integral_meas_lt hYi (Eventually.of_forall (fun ω => le_max_right _ _))
  have hEq : ∫ u in Set.Ioo γ 1, (VaR P u X - b) = ∫ ω, max (-(X ω + b)) 0 ∂P := by
    rw [hL, hR]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s (hs : 0 < s) => ?_)
    have hPs0 : 0 ≤ P.real {ω | b + s + X ω < 0} := measureReal_nonneg
    have hPs1 : P.real {ω | b + s + X ω < 0} ≤ 1 - γ :=
      (F_anti P X (by linarith : b ≤ b + s)).trans hbF
    have hset1 : {u | s < VaR P u X - b} ∩ Set.Ioo γ 1 =
        Set.Ioo (1 - P.real {ω | b + s + X ω < 0}) 1 := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ioo]
      constructor
      · rintro ⟨h, hu1, hu2⟩
        refine ⟨?_, hu2⟩
        by_contra hc
        push Not at hc
        have := (var_le_iff P X hX C hC u (by linarith) hu2.le (b + s)).2 (by linarith)
        linarith
      · rintro ⟨hu1, hu2⟩
        refine ⟨?_, by linarith, hu2⟩
        by_contra hc
        push Not at hc
        have := (var_le_iff P X hX C hC u (by linarith) hu2.le (b + s)).1 (by linarith)
        linarith
    have hset2 : {ω | s < max (-(X ω + b)) 0} = {ω | b + s + X ω < 0} := by
      ext ω
      simp only [Set.mem_setOf_eq, lt_max_iff]
      constructor
      · rintro (h | h) <;> linarith
      · intro h; left; linarith
    rw [measureReal_restrict_apply' measurableSet_Ioo, hset1, hset2,
      Real.volume_real_Ioo_of_le (by linarith)]
    ring
  unfold AVaR
  have h1 : ∫ u in Set.Ioo γ 1, (VaR P u X - b) =
      (∫ u in Set.Ioo γ 1, VaR P u X) - ∫ u in Set.Ioo γ 1, b := integral_sub hint hbI
  have h2 : ∫ u in Set.Ioo γ 1, b = (1 - γ) * b := by
    rw [setIntegral_const, Real.volume_real_Ioo_of_le hγ1.le, smul_eq_mul]
  have h3 : ∫ u in Set.Ioo γ 1, VaR P u X = (1 - γ) * b + ∫ ω, max (-(X ω + b)) 0 ∂P := by
    linarith
  rw [h3]
  have ht : 1 - γ ≠ 0 := by linarith
  field_simp

/-- Dual lower bound: `AVaR_γ(X) ≥ -E[Z X]` for `0 ≤ Z ≤ (1-γ)⁻¹`, `E Z = 1`. -/
lemma avar_ge_dual (X Z : Ω → ℝ) (hX : Measurable X) (C : ℝ) (hC : ∀ᵐ ω ∂P, |X ω| ≤ C)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hZi : Integrable Z P) (hZ0 : ∀ᵐ ω ∂P, 0 ≤ Z ω)
    (hZ1 : ∀ᵐ ω ∂P, Z ω ≤ (1 - γ)⁻¹) (hZ : ∫ ω, Z ω ∂P = 1) :
    -∫ ω, Z ω * X ω ∂P ≤ AVaR P γ X := by
  rw [avar_rep P X hX C hC γ hγ0 hγ1]
  set b := VaR P γ X
  have hXi : Integrable X P :=
    Integrable.of_bound hX.aestronglyMeasurable C (by
      filter_upwards [hC] with ω h
      simpa [Real.norm_eq_abs] using h)
  have hYi : Integrable (fun ω => max (-(X ω + b)) 0) P :=
    (hXi.add (integrable_const b)).neg.pos_part
  have hZX : Integrable (fun ω => Z ω * X ω) P :=
    Integrable.of_bound (hZi.1.mul hX.aestronglyMeasurable) ((1 - γ)⁻¹ * C) (by
      filter_upwards [hC, hZ0, hZ1] with ω h h0 h1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
      exact mul_le_mul h1 h (abs_nonneg _) (by positivity))
  have hmono : ∫ ω, -(Z ω * X ω) ∂P ≤
      ∫ ω, ((1 - γ)⁻¹ * max (-(X ω + b)) 0 + b * Z ω) ∂P := by
    refine integral_mono_ae hZX.neg ((hYi.const_mul _).add (hZi.const_mul b)) ?_
    filter_upwards [hZ0, hZ1] with ω h0 h1
    have e1 := mul_le_mul_of_nonneg_left (le_max_left (-(X ω + b)) 0) h0
    have e2 := mul_le_mul_of_nonneg_right h1 (le_max_right (-(X ω + b)) 0)
    nlinarith
  rw [integral_neg, integral_add (hYi.const_mul _) (hZi.const_mul b), integral_const_mul,
    integral_const_mul, hZ] at hmono
  linarith

end dual

lemma lam_ge_iff (p q γ : ℝ) (N : ℕ) (hN : 1 ≤ N) (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1)
    (hγ1 : γ < 1) :
    ((1 - p) ^ N * (1 - γ)⁻¹ - (1 - q) ^ N) / ((1 - q) ^ N - (1 - p) ^ N) ≤ q ^ N / (p ^ N - q ^ N) ↔
      γ ≤ p ^ N * ((1 - q) ^ N - (1 - p) ^ N) / ((p * (1 - q)) ^ N - (q * (1 - p)) ^ N) := by
  have hN0 : N ≠ 0 := by omega
  have ha : q ^ N < p ^ N := pow_lt_pow_left₀ hqp hq0.le hN0
  have hb : 0 < q ^ N := pow_pos hq0 N
  have he : 0 < (1 - p) ^ N := pow_pos (by linarith) N
  have hc : (1 - p) ^ N < (1 - q) ^ N := pow_lt_pow_left₀ (by linarith) (by linarith) hN0
  have hpq : q * (1 - p) < p * (1 - q) := by nlinarith
  have hD : 0 < (p * (1 - q)) ^ N - (q * (1 - p)) ^ N := by
    have := pow_lt_pow_left₀ hpq (by nlinarith) hN0
    linarith
  have ht : 0 < 1 - γ := by linarith
  have hL : ((1 - p) ^ N * (1 - γ)⁻¹ - (1 - q) ^ N) / ((1 - q) ^ N - (1 - p) ^ N) =
      ((1 - p) ^ N - (1 - q) ^ N * (1 - γ)) / ((1 - γ) * ((1 - q) ^ N - (1 - p) ^ N)) := by
    field_simp
  rw [hL, div_le_div_iff₀ (by nlinarith) (by linarith), le_div_iff₀ hD, mul_pow, mul_pow]
  constructor <;> intro h <;> nlinarith

lemma lam2_nonneg (p q γ : ℝ) (N : ℕ) (hq1 : q < 1) (hqp : q < p) (hp1 : p < 1) (hγ1 : γ < 1) (hN : 1 ≤ N)
    (h : 1 - ((1 - p) / (1 - q)) ^ N ≤ γ) :
    0 ≤ ((1 - p) ^ N * (1 - γ)⁻¹ - (1 - q) ^ N) / ((1 - q) ^ N - (1 - p) ^ N) := by
  have hN0 : N ≠ 0 := by omega
  have hc : 0 < (1 - q) ^ N := pow_pos (by linarith) N
  have hce : (1 - p) ^ N < (1 - q) ^ N := pow_lt_pow_left₀ (by linarith) (by linarith) hN0
  have ht : 0 < 1 - γ := by linarith
  rw [div_pow] at h
  have h' : 1 - γ ≤ (1 - p) ^ N / (1 - q) ^ N := by linarith
  rw [le_div_iff₀ hc] at h'
  have h'' : (1 - q) ^ N ≤ (1 - p) ^ N * (1 - γ)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ ht]; linarith
  exact div_nonneg (by linarith) (by linarith)

section mart
open MDPFinance.MeanVariance ProbabilityTheory

/-- One-step density factor of the martingale measure. -/
noncomputable def rf {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) (v : ℝ) : ℝ :=
  if v = M.u - 1 then M.q / M.p else (1 - M.q) / (1 - M.p)

/-- `ρ_m = ∏_{j<m} rf(R_{j+1})`, the density of the martingale measure on `σ(R_1..R_m)`. -/
noncomputable def rhoM {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) (m : ℕ) (ω : Ω) : ℝ :=
  ∏ j ∈ Finset.range m, rf M (M.R (j + 1) ω)

/-- `σ(R_{i+1})`. -/
noncomputable def mR {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) (i : Fin M.N) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap (M.R (i.val + 1)) inferInstance

/-- `σ(R_1, …, R_m)`. -/
noncomputable def FF {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) (m : ℕ) :
    MeasurableSpace Ω :=
  ⨆ i ∈ {i : Fin M.N | i.val < m}, mR M i

open Classical in
/-- Finite support of `X_m` along the binomial tree. -/
noncomputable def SS {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω) (π : ℕ → ℝ → ℝ) :
    ℕ → Finset ℝ
  | 0 => {M.x0}
  | m + 1 => (SS M π m).biUnion (fun x => {x + π m x * (M.u - 1), x + π m x * (M.d - 1)})

variable {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω)

lemma measurable_rf : Measurable (rf M) := by
  unfold rf
  exact Measurable.ite (measurableSet_singleton (M.u - 1) : MeasurableSet {v : ℝ | v = M.u - 1})
    measurable_const measurable_const

lemma rf_bounds (hpq : M.q < M.p) (v : ℝ) :
    M.q / M.p ≤ rf M v ∧ rf M v ≤ (1 - M.q) / (1 - M.p) := by
  have hp0 := M.hp_mem.1
  have hp1 := M.hp_mem.2
  have hle : M.q / M.p ≤ (1 - M.q) / (1 - M.p) := by
    rw [div_le_div_iff₀ hp0 (by linarith)]; nlinarith
  unfold rf
  split_ifs
  · exact ⟨le_rfl, hle⟩
  · exact ⟨hle, le_rfl⟩

lemma rho_bounds (hpq : M.q < M.p) (m : ℕ) (ω : Ω) :
    (M.q / M.p) ^ m ≤ rhoM M m ω ∧ rhoM M m ω ≤ ((1 - M.q) / (1 - M.p)) ^ m := by
  have h0 : 0 ≤ M.q / M.p := div_nonneg (q_pos M).le M.hp_mem.1.le
  induction m with
  | zero => simp [rhoM]
  | succ m ih =>
    have hr := rf_bounds M hpq (M.R (m + 1) ω)
    simp only [rhoM, Finset.prod_range_succ, pow_succ] at ih ⊢
    exact ⟨mul_le_mul ih.1 hr.1 h0 ((pow_nonneg h0 m).trans ih.1),
      mul_le_mul ih.2 hr.2 (h0.trans hr.1) ((pow_nonneg h0 m).trans (ih.1.trans ih.2))⟩

/-- Forward recursion of the terminal wealth. -/
lemma tw_succ (π : ℕ → ℝ → ℝ) : ∀ (k n : ℕ) (x : ℝ) (ω : Ω),
    M.terminalWealth π (k + 1) n x ω =
      M.terminalWealth π k n x ω + π (n + k) (M.terminalWealth π k n x ω) * M.R (n + k + 1) ω := by
  intro k
  induction k with
  | zero => intro n x ω; simp [MeanRiskMarket.terminalWealth]
  | succ k ih =>
    intro n x ω
    have h1 : M.terminalWealth π (k + 1 + 1) n x ω =
        M.terminalWealth π (k + 1) (n + 1) (x + π n x * M.R (n + 1) ω) ω := rfl
    have h2 : M.terminalWealth π (k + 1) n x ω =
        M.terminalWealth π k (n + 1) (x + π n x * M.R (n + 1) ω) ω := rfl
    rw [h1, h2, ih]
    have e : n + 1 + k = n + (k + 1) := by omega
    rw [e]

lemma FF_mono (m : ℕ) : FF M m ≤ FF M (m + 1) :=
  biSup_mono (fun i (hi : i.val < m) => show i.val < m + 1 by omega)

lemma FF_le (m : ℕ) : FF M m ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le (fun i _ => (M.hR_meas _ (by omega) (by have := i.isLt; omega)).comap_le)

lemma R_meas_FF (j m : ℕ) (hj : j < m) (hjN : j < M.N) : Measurable[FF M m] (M.R (j + 1)) :=
  Measurable.mono (comap_measurable (M.R (j + 1)))
    (le_iSup₂ (f := fun (i : Fin M.N) (_ : i ∈ {i : Fin M.N | i.val < m}) => mR M i)
      ⟨j, hjN⟩ hj) le_rfl

lemma indep_FF (m : ℕ) (hm : m < M.N) {f g : Ω → ℝ} (hf : Measurable[FF M m] f)
    (hg : Measurable[mR M ⟨m, hm⟩] g) : IndepFun f g M.measIP := by
  have hI : iIndep (mR M) M.measIP :=
    (iIndepFun_iff_iIndep (fun _ => (inferInstance : MeasurableSpace ℝ))
      (fun n : Fin M.N => M.R (n.val + 1)) M.measIP).1 M.hR_indep
  have hle : ∀ i, mR M i ≤ ‹MeasurableSpace Ω› :=
    fun i => (M.hR_meas _ (by omega) (by have := i.isLt; omega)).comap_le
  have hdis : Disjoint {i : Fin M.N | i.val < m} ({⟨m, hm⟩} : Set (Fin M.N)) := by
    rw [Set.disjoint_left]
    intro i hi hi'
    rw [Set.mem_singleton_iff] at hi'
    subst hi'
    exact lt_irrefl m hi
  have H := indep_iSup_of_disjoint hle hI hdis
  have hT : mR M ⟨m, hm⟩ ≤ ⨆ i ∈ ({⟨m, hm⟩} : Set (Fin M.N)), mR M i :=
    le_iSup₂ (f := fun (i : Fin M.N) (_ : i ∈ ({⟨m, hm⟩} : Set (Fin M.N))) => mR M i) ⟨m, hm⟩ rfl
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left (indep_of_indep_of_le_right H (hg.comap_le.trans hT)) hf.comap_le

lemma meas_FF (π : ℕ → ℝ → ℝ) (hπ : M.IsAdmissible 0 π) :
    ∀ m, m ≤ M.N → Measurable[FF M m] (fun ω => M.terminalWealth π m 0 M.x0 ω) ∧
      Measurable[FF M m] (rhoM M m) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · show Measurable[FF M 0] (fun _ => M.x0)
      exact measurable_const
    · have e : rhoM M 0 = fun _ => 1 := by funext ω; simp [rhoM]
      rw [e]
      exact measurable_const
  | succ m ih =>
    intro hm
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hR := R_meas_FF M m (m + 1) (by omega) (by omega)
    have h1' := h1.mono (FF_mono M m) le_rfl
    have h2' := h2.mono (FF_mono M m) le_rfl
    refine ⟨?_, ?_⟩
    · have e : (fun ω => M.terminalWealth π (m + 1) 0 M.x0 ω) = fun ω =>
          M.terminalWealth π m 0 M.x0 ω + π m (M.terminalWealth π m 0 M.x0 ω) * M.R (m + 1) ω := by
        funext ω; rw [tw_succ]; simp only [zero_add]
      rw [e]
      exact h1'.add (((hπ m (Nat.zero_le m) (by omega)).comp h1').mul hR)
    · have e : rhoM M (m + 1) = fun ω => rhoM M m ω * rf M (M.R (m + 1) ω) := by
        funext ω; simp only [rhoM, Finset.prod_range_succ]
      rw [e]
      exact h2'.mul ((measurable_rf M).comp hR)

lemma fin_ae (π : ℕ → ℝ → ℝ) :
    ∀ᵐ ω ∂M.measIP, ∀ m, m ≤ M.N → M.terminalWealth π m 0 M.x0 ω ∈ SS M π m := by
  filter_upwards [ae_all_two M] with ω hω
  intro m
  induction m with
  | zero => intro _; simp [SS, MeanRiskMarket.terminalWealth]
  | succ m ih =>
    intro hm
    have h := ih (by omega)
    rw [tw_succ]
    simp only [zero_add, SS, Finset.mem_biUnion]
    refine ⟨_, h, ?_⟩
    rcases hω m (by omega) with h' | h' <;> simp [h']

lemma abd_mul {P : Measure Ω} {f g : Ω → ℝ} {A B : ℝ}
    (hf : ∀ᵐ ω ∂P, |f ω| ≤ A) (hg : ∀ᵐ ω ∂P, |g ω| ≤ B) :
    ∀ᵐ ω ∂P, |f ω * g ω| ≤ A * B := by
  filter_upwards [hf, hg] with ω h1 h2
  rw [abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

lemma int_bdd {P : Measure Ω} [IsFiniteMeasure P] {f : Ω → ℝ} {A : ℝ}
    (hm : Measurable f) (hf : ∀ᵐ ω ∂P, |f ω| ≤ A) : Integrable f P :=
  Integrable.of_bound hm.aestronglyMeasurable A (by
    filter_upwards [hf] with ω h
    simpa [Real.norm_eq_abs] using h)

lemma int_fun_R (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ M.N) (g : ℝ → ℝ) :
    ∫ ω, g (M.R n ω) ∂M.measIP = g (M.u - 1) * M.p + g (M.d - 1) * (1 - M.p) := by
  haveI := M.isProb
  have hA : MeasurableSet {ω | M.R n ω = M.u - 1} := M.hR_meas n h1 h2 (measurableSet_singleton _)
  have hB : MeasurableSet {ω | M.R n ω = M.d - 1} := M.hR_meas n h1 h2 (measurableSet_singleton _)
  have hne : M.u - 1 ≠ M.d - 1 := by intro h; linarith [M.hd_lt_one, M.hone_lt_u]
  have hae : ∀ᵐ ω ∂M.measIP, g (M.R n ω) =
      {ω | M.R n ω = M.u - 1}.indicator (fun _ => g (M.u - 1)) ω +
        {ω | M.R n ω = M.d - 1}.indicator (fun _ => g (M.d - 1)) ω := by
    filter_upwards [ae_two M n h1 h2] with ω h
    rcases h with h | h
    · have hb : ω ∉ {ω | M.R n ω = M.d - 1} := by
        show ¬ (M.R n ω = M.d - 1); rw [h]; exact hne
      rw [Set.indicator_of_mem (show ω ∈ {ω | M.R n ω = M.u - 1} from h),
        Set.indicator_of_notMem hb, h, add_zero]
    · have ha : ω ∉ {ω | M.R n ω = M.u - 1} := by
        show ¬ (M.R n ω = M.u - 1); rw [h]; exact hne.symm
      rw [Set.indicator_of_mem (show ω ∈ {ω | M.R n ω = M.d - 1} from h),
        Set.indicator_of_notMem ha, h, zero_add]
  rw [integral_congr_ae hae, integral_add ((integrable_const _).indicator hA)
    ((integrable_const _).indicator hB), integral_indicator_const _ hA, integral_indicator_const _ hB]
  have pA : M.measIP.real {ω | M.R n ω = M.u - 1} = M.p := by
    rw [measureReal_def, (M.hR_law n h1 h2).1, ENNReal.toReal_ofReal M.hp_mem.1.le]
  have pB : M.measIP.real {ω | M.R n ω = M.d - 1} = 1 - M.p := by
    rw [measureReal_def, (M.hR_law n h1 h2).2, ENNReal.toReal_ofReal (by linarith [M.hp_mem.2])]
  rw [pA, pB, smul_eq_mul, smul_eq_mul]
  ring

/-- Child B: `𝔼[ρ_m X_m] = x₀` and `𝔼 ρ_m = 1` (pricing under the martingale measure). -/
lemma integ (hpq : M.q < M.p) (π : ℕ → ℝ → ℝ) (hπ : M.IsAdmissible 0 π) : ∀ m, m ≤ M.N →
    ∫ ω, rhoM M m ω * M.terminalWealth π m 0 M.x0 ω ∂M.measIP = M.x0 ∧
      ∫ ω, rhoM M m ω ∂M.measIP = 1 := by
  haveI := M.isProb
  have hp0 := M.hp_mem.1
  have hp1 := M.hp_mem.2
  have hp1' : 1 - M.p ≠ 0 := by linarith
  have hne : M.d - 1 ≠ M.u - 1 := by intro h; linarith [M.hd_lt_one, M.hone_lt_u]
  intro m
  induction m with
  | zero => intro _; simp [rhoM, MeanRiskMarket.terminalWealth]
  | succ m ih =>
    intro hm
    have hmN : m < M.N := by omega
    obtain ⟨i1, i2⟩ := ih (by omega)
    obtain ⟨mX, mρ⟩ := meas_FF M π hπ m (by omega)
    have hRm : Measurable[mR M ⟨m, hmN⟩] (M.R (m + 1)) := comap_measurable _
    have hV : Measurable[mR M ⟨m, hmN⟩] (fun ω => rf M (M.R (m + 1) ω)) :=
      (measurable_rf M).comp hRm
    have hU : Measurable[mR M ⟨m, hmN⟩] (fun ω => rf M (M.R (m + 1) ω) * M.R (m + 1) ω) :=
      hV.mul hRm
    have hY : Measurable[FF M m] (fun ω => rhoM M m ω * M.terminalWealth π m 0 M.x0 ω) :=
      mρ.mul mX
    have hW : Measurable[FF M m] (fun ω => rhoM M m ω * π m (M.terminalWealth π m 0 M.x0 ω)) :=
      mρ.mul ((hπ m (Nat.zero_le m) hmN).comp mX)
    have amb : ∀ {f : Ω → ℝ}, Measurable[FF M m] f → Measurable f :=
      fun hf => hf.mono (FF_le M m) le_rfl
    have amb' : ∀ {f : Ω → ℝ}, Measurable[mR M ⟨m, hmN⟩] f → Measurable f :=
      fun hf => hf.mono (M.hR_meas (m + 1) (by omega) (by omega)).comap_le le_rfl
    have EV : ∫ ω, rf M (M.R (m + 1) ω) ∂M.measIP = 1 := by
      rw [show (∫ ω, rf M (M.R (m + 1) ω) ∂M.measIP) = _ from
        int_fun_R M (m + 1) (by omega) (by omega) (rf M)]
      unfold rf
      rw [if_pos rfl, if_neg hne, div_mul_cancel₀ _ hp0.ne', div_mul_cancel₀ _ hp1']
      ring
    have EU : ∫ ω, rf M (M.R (m + 1) ω) * M.R (m + 1) ω ∂M.measIP = 0 := by
      rw [show (∫ ω, rf M (M.R (m + 1) ω) * M.R (m + 1) ω ∂M.measIP) = _ from
        int_fun_R M (m + 1) (by omega) (by omega) (fun v => rf M v * v)]
      unfold rf
      rw [if_pos rfl, if_neg hne]
      have hq : M.q * (M.u - M.d) = 1 - M.d := by
        unfold MeanRiskMarket.q
        have : M.u - M.d ≠ 0 := by linarith [M.hd_lt_one, M.hone_lt_u]
        field_simp
      have e1 : M.q / M.p * (M.u - 1) * M.p = M.q * (M.u - 1) := by field_simp
      have e2 : (1 - M.q) / (1 - M.p) * (M.d - 1) * (1 - M.p) = (1 - M.q) * (M.d - 1) := by
        field_simp
      rw [e1, e2]
      linear_combination hq
    have e : ∀ ω, rhoM M (m + 1) ω * M.terminalWealth π (m + 1) 0 M.x0 ω =
        (rhoM M m ω * M.terminalWealth π m 0 M.x0 ω) * rf M (M.R (m + 1) ω) +
        (rhoM M m ω * π m (M.terminalWealth π m 0 M.x0 ω)) *
          (rf M (M.R (m + 1) ω) * M.R (m + 1) ω) := by
      intro ω
      rw [tw_succ]
      simp only [rhoM, Finset.prod_range_succ, zero_add]
      ring
    have eρ : ∀ ω, rhoM M (m + 1) ω = rhoM M m ω * rf M (M.R (m + 1) ω) := by
      intro ω; simp only [rhoM, Finset.prod_range_succ]
    have hfin := fin_ae M π
    have bX : ∀ᵐ ω ∂M.measIP, |M.terminalWealth π m 0 M.x0 ω| ≤ ∑ s ∈ SS M π m, |s| := by
      filter_upwards [hfin] with ω h
      exact Finset.single_le_sum (f := fun s => |s|) (fun s _ => abs_nonneg s) (h m (by omega))
    have bP : ∀ᵐ ω ∂M.measIP, |π m (M.terminalWealth π m 0 M.x0 ω)| ≤
        ∑ s ∈ SS M π m, |π m s| := by
      filter_upwards [hfin] with ω h
      exact Finset.single_le_sum (f := fun s => |π m s|) (fun s _ => abs_nonneg _) (h m (by omega))
    have bρ : ∀ᵐ ω ∂M.measIP, |rhoM M m ω| ≤ ((1 - M.q) / (1 - M.p)) ^ m :=
      ae_of_all _ (fun ω => by
        have h := rho_bounds M hpq m ω
        have h0 : 0 ≤ (M.q / M.p) ^ m := pow_nonneg (div_nonneg (q_pos M).le hp0.le) m
        rw [abs_of_nonneg (h0.trans h.1)]; exact h.2)
    have bV : ∀ᵐ ω ∂M.measIP, |rf M (M.R (m + 1) ω)| ≤ (1 - M.q) / (1 - M.p) :=
      ae_of_all _ (fun ω => by
        have h := rf_bounds M hpq (M.R (m + 1) ω)
        rw [abs_of_nonneg ((div_nonneg (q_pos M).le hp0.le).trans h.1)]; exact h.2)
    have bR : ∀ᵐ ω ∂M.measIP, |M.R (m + 1) ω| ≤ |M.u - 1| + |M.d - 1| := by
      filter_upwards [ae_two M (m + 1) (by omega) (by omega)] with ω h
      rcases h with h | h <;> rw [h] <;> linarith [abs_nonneg (M.u - 1), abs_nonneg (M.d - 1)]
    have iYV : Integrable (fun ω => rhoM M m ω * M.terminalWealth π m 0 M.x0 ω *
        rf M (M.R (m + 1) ω)) M.measIP :=
      int_bdd ((amb hY).mul (amb' hV)) (abd_mul (abd_mul bρ bX) bV)
    have iWU : Integrable (fun ω => rhoM M m ω * π m (M.terminalWealth π m 0 M.x0 ω) *
        (rf M (M.R (m + 1) ω) * M.R (m + 1) ω)) M.measIP :=
      int_bdd ((amb hW).mul (amb' hU)) (abd_mul (abd_mul bρ bP) (abd_mul bV bR))
    refine ⟨?_, ?_⟩
    · rw [integral_congr_ae (ae_of_all _ e), integral_add iYV iWU,
        (indep_FF M m hmN hY hV).integral_fun_mul_eq_mul_integral (amb hY).aestronglyMeasurable
          (amb' hV).aestronglyMeasurable,
        (indep_FF M m hmN hW hU).integral_fun_mul_eq_mul_integral (amb hW).aestronglyMeasurable
          (amb' hU).aestronglyMeasurable, i1, EV, EU]
      ring
    · rw [integral_congr_ae (ae_of_all _ eρ),
        (indep_FF M m hmN mρ hV).integral_fun_mul_eq_mul_integral (amb mρ).aestronglyMeasurable
          (amb' hV).aestronglyMeasurable, i2, EV]
      ring

/-- Lower bound: `AVaR_γ(X_N) ≥ (μ - x₀) λ - x₀` for `0 ≤ λ ≤ λ₁, λ₂` and every feasible policy. -/
lemma LB (hpq : M.q < M.p) (hN : 1 ≤ M.N) (π : ℕ → ℝ → ℝ) (hπ : M.IsAdmissible 0 π)
    (hμ : M.μ ≤ M.meanXN π) (lam : ℝ) (h0 : 0 ≤ lam)
    (h1 : lam ≤ M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N))
    (h2 : lam ≤ ((1 - M.p) ^ M.N * (1 - M.γ)⁻¹ - (1 - M.q) ^ M.N) /
      ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N)) :
    (M.μ - M.x0) * lam - M.x0 ≤
      BauerleRiederMDP.MeanRisk.AVaR M.measIP M.γ (M.terminalWealth π M.N 0 M.x0) := by
  haveI := M.isProb
  have hp0 := M.hp_mem.1
  have hp1 := M.hp_mem.2
  have hq0 := q_pos M
  have hN0 : M.N ≠ 0 := by omega
  have hγ0 := M.hγ.1
  have hγ1 := M.hγ.2
  obtain ⟨mX, mρ⟩ := meas_FF M π hπ M.N le_rfl
  have mX' : Measurable (M.terminalWealth π M.N 0 M.x0) := mX.mono (FF_le M M.N) le_rfl
  have mρ' : Measurable (rhoM M M.N) := mρ.mono (FF_le M M.N) le_rfl
  obtain ⟨iρX, iρ⟩ := integ M hpq π hπ M.N le_rfl
  have bX : ∀ᵐ ω ∂M.measIP, |M.terminalWealth π M.N 0 M.x0 ω| ≤ ∑ s ∈ SS M π M.N, |s| := by
    filter_upwards [fin_ae M π] with ω h
    exact Finset.single_le_sum (f := fun s => |s|) (fun s _ => abs_nonneg s) (h M.N le_rfl)
  have bρ : ∀ᵐ ω ∂M.measIP, |rhoM M M.N ω| ≤ ((1 - M.q) / (1 - M.p)) ^ M.N :=
    ae_of_all _ (fun ω => by
      have h := rho_bounds M hpq M.N ω
      have h0 : 0 ≤ (M.q / M.p) ^ M.N := pow_nonneg (div_nonneg hq0.le hp0.le) _
      rw [abs_of_nonneg (h0.trans h.1)]; exact h.2)
  have iX : Integrable (M.terminalWealth π M.N 0 M.x0) M.measIP := int_bdd mX' bX
  have iρ' : Integrable (rhoM M M.N) M.measIP := int_bdd mρ' bρ
  have iρX' : Integrable (fun ω => rhoM M M.N ω * M.terminalWealth π M.N 0 M.x0 ω) M.measIP :=
    int_bdd (mρ'.mul mX') (abd_mul bρ bX)
  have hpN : 0 < M.p ^ M.N := pow_pos hp0 _
  have hab : M.q ^ M.N < M.p ^ M.N := pow_lt_pow_left₀ hpq hq0.le hN0
  have he : 0 < (1 - M.p) ^ M.N := pow_pos (by linarith) _
  have hce : (1 - M.p) ^ M.N < (1 - M.q) ^ M.N :=
    pow_lt_pow_left₀ (by linarith) (by linarith) hN0
  have ht : 0 < 1 - M.γ := by linarith
  have h1' : lam * (M.p ^ M.N - M.q ^ M.N) ≤ M.q ^ M.N := (le_div_iff₀ (by linarith)).1 h1
  have h2' : lam * ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N) ≤
      (1 - M.p) ^ M.N * (1 - M.γ)⁻¹ - (1 - M.q) ^ M.N := (le_div_iff₀ (by linarith)).1 h2
  have hZ0 : ∀ᵐ ω ∂M.measIP, 0 ≤ (1 + lam) * rhoM M M.N ω - lam := ae_of_all _ (fun ω => by
    have hb := (rho_bounds M hpq M.N ω).1
    rw [div_pow, div_le_iff₀ hpN] at hb
    nlinarith [mul_le_mul_of_nonneg_left hb (by linarith : (0:ℝ) ≤ 1 + lam)])
  have hZ1 : ∀ᵐ ω ∂M.measIP, (1 + lam) * rhoM M M.N ω - lam ≤ (1 - M.γ)⁻¹ :=
    ae_of_all _ (fun ω => by
      have hb := (rho_bounds M hpq M.N ω).2
      rw [div_pow, le_div_iff₀ he] at hb
      have hti : 0 < (1 - M.γ)⁻¹ := inv_pos.2 ht
      nlinarith [mul_le_mul_of_nonneg_left hb (by linarith : (0:ℝ) ≤ 1 + lam)])
  have hZi : Integrable (fun ω => (1 + lam) * rhoM M M.N ω - lam) M.measIP :=
    (iρ'.const_mul _).sub (integrable_const _)
  have hZ : ∫ ω, ((1 + lam) * rhoM M M.N ω - lam) ∂M.measIP = 1 := by
    rw [integral_sub (iρ'.const_mul _) (integrable_const _), integral_const_mul, iρ, integral_const]
    simp
  have hd : -∫ ω, ((1 + lam) * rhoM M M.N ω - lam) * M.terminalWealth π M.N 0 M.x0 ω ∂M.measIP ≤
      BauerleRiederMDP.MeanRisk.AVaR M.measIP M.γ (M.terminalWealth π M.N 0 M.x0) :=
    avar_ge_dual M.measIP (M.terminalWealth π M.N 0 M.x0) (fun ω => (1 + lam) * rhoM M M.N ω - lam)
      mX' _ bX M.γ hγ0 hγ1 hZi hZ0 hZ1 hZ
  have hZX : ∫ ω, ((1 + lam) * rhoM M M.N ω - lam) * M.terminalWealth π M.N 0 M.x0 ω ∂M.measIP =
      (1 + lam) * M.x0 - lam * M.meanXN π := by
    have e : ∀ ω, ((1 + lam) * rhoM M M.N ω - lam) * M.terminalWealth π M.N 0 M.x0 ω =
        (1 + lam) * (rhoM M M.N ω * M.terminalWealth π M.N 0 M.x0 ω) -
          lam * M.terminalWealth π M.N 0 M.x0 ω := fun ω => by ring
    rw [integral_congr_ae (ae_of_all _ e), integral_sub (iρX'.const_mul _) (iX.const_mul _),
      integral_const_mul, integral_const_mul, iρX]
    rfl
  rw [hZX] at hd
  nlinarith [mul_le_mul_of_nonneg_left hμ h0]

/-- The `−∞` case `γ < γ₁`: up-freeze policies with `c → −∞`. -/
lemma bot_case (hpq : M.q < M.p) (hN : 1 ≤ M.N)
    (hγ : M.γ < 1 - ((1 - M.p) / (1 - M.q)) ^ M.N) (L : ℝ) :
    ∃ π, (M.IsAdmissible 0 π ∧ M.μ ≤ M.meanXN π) ∧
      BauerleRiederMDP.MeanRisk.AVaR M.measIP M.γ (M.terminalWealth π M.N 0 M.x0) < L := by
  have hp1 := M.hp_mem.2
  have hq1 := q_lt_one M
  have hγ0 := M.hγ.1
  have hγ1 := M.hγ.2
  have ht : 0 < 1 - M.γ := by linarith
  have he : 0 < (1 - M.p) ^ M.N := pow_pos (by linarith) _
  have hc' : 0 < (1 - M.q) ^ M.N := pow_pos (by linarith) _
  have hc1 : (1 - M.q) ^ M.N ≤ 1 := pow_le_one₀ (by linarith) (by linarith [q_pos M])
  rw [div_pow] at hγ
  set κ := (1 - M.p) ^ M.N / (1 - M.q) ^ M.N with hκ
  have heκ : (1 - M.p) ^ M.N ≤ κ := le_div_self he.le hc' hc1
  have conv : ∀ c : ℝ, (1 - M.p) ^ M.N * ((M.x0 + c) * (1 - M.q)⁻¹ ^ M.N) = κ * (M.x0 + c) :=
    fun c => by rw [hκ, inv_pow, div_eq_mul_inv]; ring
  have hκ1 : κ < 1 := by linarith
  have hκt : κ < 1 - M.γ := by linarith
  have hδ : 0 < 1 - κ / (1 - M.γ) := by rw [sub_pos, div_lt_one ht]; exact hκt
  obtain ⟨H, hH1, hH2, hH3⟩ : ∃ H : ℝ, M.x0 + 1 ≤ H ∧ (M.μ - κ * M.x0) / (1 - κ) ≤ H ∧
      (-L - κ * M.x0 / (1 - M.γ)) / (1 - κ / (1 - M.γ)) < H :=
    ⟨max (max (M.x0 + 1) ((M.μ - κ * M.x0) / (1 - κ)))
        ((-L - κ * M.x0 / (1 - M.γ)) / (1 - κ / (1 - M.γ)) + 1),
      le_trans (le_max_left _ _) (le_max_left _ _), le_trans (le_max_right _ _) (le_max_left _ _),
      lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)⟩
  rw [div_le_iff₀ (by linarith)] at hH2
  rw [div_lt_iff₀ hδ] at hH3
  obtain ⟨hadm, hmean, havar⟩ := att_C M (-H) (by linarith) (by linarith)
  refine ⟨_, ⟨hadm, ?_⟩, ?_⟩
  · rw [hmean, conv]; nlinarith
  · rw [havar, conv]
    have e3 : κ * (M.x0 + -H) / (1 - M.γ) = κ / (1 - M.γ) * M.x0 - κ / (1 - M.γ) * H := by ring
    have e4 : κ * M.x0 / (1 - M.γ) = κ / (1 - M.γ) * M.x0 := by ring
    rw [e3]
    rw [e4] at hH3
    nlinarith

end mart

end P8c40

open P8c40 in
open BauerleRiederMDP.MeanRisk in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (M : MDPFinance.MeanVariance.MeanRiskMarket Ω)
    (hd : 0 < M.d) (hN : 1 ≤ M.N) (hpq : M.q < M.p) (γ1 γ2 lamstar : ℝ)
    (hγ1 : γ1 = 1 - ((1 - M.p) / (1 - M.q)) ^ M.N)
    (hγ2 : γ2 = M.p ^ M.N * ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N) /
      ((M.p * (1 - M.q)) ^ M.N - (M.q * (1 - M.p)) ^ M.N))
    (hlamstar : lamstar = min (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N))
      (((1 - M.p) ^ M.N * (1 - M.γ)⁻¹ - (1 - M.q) ^ M.N) /
        ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N))) :
    (γ1 ≤ M.γ → valueMR M = (((M.μ - M.x0) * lamstar - M.x0 : ℝ) : EReal)) ∧
      (M.γ < γ1 → valueMR M = ⊥) ∧
      (γ2 ≤ M.γ → IsOptimalMR M (fun _ x =>
        (1 - M.d)⁻¹ * ((M.μ - M.x0) * (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N)) - M.x0 + x))) ∧
      (γ1 ≤ M.γ → M.γ ≤ γ2 → IsOptimalMR M (fun _ x =>
        (1 - M.u)⁻¹ * ((M.x0 - M.μ) * ((1 - M.q) ^ M.N / ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N)) -
          M.x0 + x))) := by
  subst hγ1 hγ2 hlamstar
  have hq0 := q_pos M
  have hq1 := q_lt_one M
  have hp1 := M.hp_mem.2
  have hγ1' := M.hγ.2
  have hN0 : M.N ≠ 0 := by omega
  have hl1 : 0 < M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N) :=
    div_pos (pow_pos hq0 _) (by linarith [pow_lt_pow_left₀ hpq hq0.le hN0])
  have kle := lam_le_iff M.p M.q M.γ M.N hN hq0 hpq hp1 hγ1'
  have kge := lam_ge_iff M.p M.q M.γ M.N hN hq0 hpq hp1 hγ1'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hγ
    have l2 := lam2_nonneg M.p M.q M.γ M.N hq1 hpq hp1 hγ1' hN hγ
    unfold valueMR
    apply le_antisymm
    · by_cases hg : M.p ^ M.N * ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N) /
          ((M.p * (1 - M.q)) ^ M.N - (M.q * (1 - M.p)) ^ M.N) ≤ M.γ
      · obtain ⟨hadm, hmean, havar⟩ := att_D M hN hpq _ rfl hg
        refine le_trans (iInf₂_le _ ⟨hadm, hmean.ge⟩) ?_
        rw [havar, min_eq_left (kle.2 hg)]
      · push Not at hg
        obtain ⟨hadm, hmean, havar⟩ := att_C2 M hN hpq _ rfl hg.le
        refine le_trans (iInf₂_le _ ⟨hadm, hmean.ge⟩) ?_
        rw [havar, min_eq_right (kge.2 hg.le)]
    · exact le_iInf₂ (fun π hπ => EReal.coe_le_coe_iff.2 (LB M hpq hN π hπ.1 hπ.2 _
        (le_min hl1.le l2) (min_le_left _ _) (min_le_right _ _)))
  · intro hγ
    rw [EReal.eq_bot_iff_forall_lt]
    intro L
    obtain ⟨π, hπ, hlt⟩ := bot_case M hpq hN hγ L
    unfold valueMR
    exact lt_of_le_of_lt (iInf₂_le π hπ) (EReal.coe_lt_coe_iff.2 hlt)
  · intro hγ
    obtain ⟨hadm, hmean, havar⟩ := att_D M hN hpq _ rfl hγ
    unfold IsOptimalMR
    refine ⟨hadm, hmean.ge, fun π hπ hμ => ?_⟩
    rw [havar]
    exact LB M hpq hN π hπ hμ _ hl1.le le_rfl (kle.2 hγ)
  · intro hγ hγ'
    obtain ⟨hadm, hmean, havar⟩ := att_C2 M hN hpq _ rfl hγ'
    unfold IsOptimalMR
    refine ⟨hadm, hmean.ge, fun π hπ hμ => ?_⟩
    rw [havar]
    exact LB M hpq hN π hπ hμ _ (lam2_nonneg M.p M.q M.γ M.N hq1 hpq hp1 hγ1' hN hγ) (kge.2 hγ') le_rfl
