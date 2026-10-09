-- Prove2me | solution 1 for DataDrivenRO.FwdBwd.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T14:25:34.722747+00:00
-- url     : https://prove2.me/submissions/262f7611-d86b-42a5-83dc-d0db929ab151

import Mathlib
import Definitions.Def_DataDrivenRO_FwdBwd_Setting

set_option autoImplicit false

open MeasureTheory

namespace P2a39d195

open DataDrivenRO.FwdBwd

/-! ## Part 1: the Chen–Sim–Sun Chernoff bound -/

lemma integrable_exp_of_bdd (Q : Measure ℝ) [IsProbabilityMeasure Q] (hQ : HasBoundedSupport Q)
    (a : ℝ) : Integrable (fun t => Real.exp (a * t)) Q := by
  obtain ⟨R, hR⟩ := hQ
  have hae : ∀ᵐ t ∂Q, t ∈ Set.Icc (-R) R := mem_ae_iff.2 hR
  refine Integrable.of_bound
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    (Real.exp (|a| * |R|)) ?_
  filter_upwards [hae] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  have h1 : |t| ≤ |R| := (abs_le.2 ⟨ht.1, ht.2⟩).trans (le_abs_self R)
  calc a * t ≤ |a * t| := le_abs_self _
    _ = |a| * |t| := abs_mul a t
    _ ≤ |a| * |R| := mul_le_mul_of_nonneg_left h1 (abs_nonneg a)

lemma log_aux (a σ y L : ℝ) (hy : 0 < y) (h : a / y + 2 / y ^ 2 * L ≤ σ ^ 2) :
    L ≤ σ ^ 2 * y ^ 2 / 2 - a * y / 2 := by
  have hy0 : y ≠ 0 := hy.ne'
  have e : a / y + 2 / y ^ 2 * L = (2 / y ^ 2) * (a * y / 2 + L) := by
    field_simp
  rw [e] at h
  have h2 : a * y / 2 + L ≤ σ ^ 2 * y ^ 2 / 2 := by
    calc a * y / 2 + L = (y ^ 2 / 2) * ((2 / y ^ 2) * (a * y / 2 + L)) := by
          field_simp
      _ ≤ (y ^ 2 / 2) * σ ^ 2 := mul_le_mul_of_nonneg_left h (by positivity)
      _ = σ ^ 2 * y ^ 2 / 2 := by ring
  linarith

lemma mgf_coord_le (Q : Measure ℝ) [IsProbabilityMeasure Q] (hQ : HasBoundedSupport Q)
    (σf σb : ℝ) (hf : FwdDevLe Q σf) (hb : BwdDevLe Q σb) (x : ℝ) (hx : 0 < x) (w : ℝ) :
    ∫ t, Real.exp (x * (t * w)) ∂Q ≤
      Real.exp (x * ((∫ t, t ∂Q) * w) +
        x ^ 2 * (if w < 0 then σb ^ 2 * w ^ 2 else σf ^ 2 * w ^ 2) / 2) := by
  rcases lt_trichotomy w 0 with hw | hw | hw
  · have hy : 0 < -x * w := by nlinarith
    have h := hb (-x * w) hy
    have hint := integrable_exp_of_bdd Q hQ (-(-x * w))
    have heq : (fun t => Real.exp (x * (t * w))) = fun t => Real.exp (-(-x * w) * t) := by
      funext t; congr 1; ring
    rw [heq]
    have hpos : 0 < ∫ t, Real.exp (-(-x * w) * t) ∂Q := integral_exp_pos hint
    rw [← Real.exp_log hpos]
    apply Real.exp_le_exp.2
    simp only [hw, if_true]
    have h2 := log_aux _ _ _ _ hy h
    nlinarith [h2]
  · subst hw
    simp
  · have hy : 0 < x * w := by positivity
    have h := hf (x * w) hy
    have hint := integrable_exp_of_bdd Q hQ (x * w)
    have heq : (fun t => Real.exp (x * (t * w))) = fun t => Real.exp ((x * w) * t) := by
      funext t; congr 1; ring
    rw [heq]
    have hpos : 0 < ∫ t, Real.exp ((x * w) * t) ∂Q := integral_exp_pos hint
    rw [← Real.exp_log hpos]
    apply Real.exp_le_exp.2
    have hnw : ¬ w < 0 := not_lt.2 hw.le
    simp only [hnw, if_false]
    have h2 := log_aux _ _ _ _ hy h
    nlinarith [h2]

lemma tail_le {d : ℕ} (Q : Fin d → Measure ℝ) [∀ i, IsProbabilityMeasure (Q i)]
    (hQ : ∀ i, HasBoundedSupport (Q i)) (σf σb : Fin d → ℝ)
    (hf : ∀ i, FwdDevLe (Q i) (σf i)) (hb : ∀ i, BwdDevLe (Q i) (σb i))
    (x : ℝ) (hx : 0 < x) (v : Fin d → ℝ) (c : ℝ) :
    (Measure.pi Q).real {u | c ≤ u ⬝ᵥ v} ≤
      Real.exp (-x * c + ∑ i, (x * ((∫ t, t ∂(Q i)) * v i) +
        x ^ 2 * (if v i < 0 then σb i ^ 2 * v i ^ 2 else σf i ^ 2 * v i ^ 2) / 2)) := by
  have hprod : ∀ u : Fin d → ℝ, Real.exp (x * (u ⬝ᵥ v)) = ∏ i, Real.exp (x * (u i * v i)) := by
    intro u; rw [dotProduct, Finset.mul_sum, Real.exp_sum]
  have hint : Integrable (fun u : Fin d → ℝ => Real.exp (x * (u ⬝ᵥ v))) (Measure.pi Q) := by
    simp_rw [hprod]
    refine Integrable.fintype_prod (f := fun i t => Real.exp (x * (t * v i))) (fun i => ?_)
    have e : (fun t : ℝ => Real.exp (x * (t * v i))) = fun t => Real.exp ((x * v i) * t) := by
      funext t; congr 1; ring
    rw [e]
    exact integrable_exp_of_bdd (Q i) (hQ i) (x * v i)
  have hch := ProbabilityTheory.measure_ge_le_exp_mul_mgf (X := fun u : Fin d → ℝ => u ⬝ᵥ v)
    (μ := Measure.pi Q) c hx.le hint
  have hmgf : ProbabilityTheory.mgf (fun u : Fin d → ℝ => u ⬝ᵥ v) (Measure.pi Q) x =
      ∏ i, ∫ t, Real.exp (x * (t * v i)) ∂(Q i) := by
    rw [ProbabilityTheory.mgf]
    show ∫ u, Real.exp (x * (u ⬝ᵥ v)) ∂(Measure.pi Q) = _
    simp_rw [hprod]
    exact integral_fintype_prod_eq_prod (fun i t => Real.exp (x * (t * v i)))
  rw [hmgf] at hch
  refine hch.trans ?_
  rw [Real.exp_add, Real.exp_sum]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Finset.prod_le_prod
  · intro i _; exact integral_nonneg (fun t => (Real.exp_pos _).le)
  · intro i _; exact mgf_coord_le (Q i) (hQ i) (σf i) (σb i) (hf i) (hb i) x hx (v i)

lemma dot_continuous {d : ℕ} (v : Fin d → ℝ) : Continuous fun u : Fin d → ℝ => u ⬝ᵥ v := by
  show Continuous fun u : Fin d → ℝ => ∑ i, u i * v i
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).mul continuous_const)

lemma css {d : ℕ} (Q : Fin d → Measure ℝ) [∀ i, IsProbabilityMeasure (Q i)]
    (hQ : ∀ i, HasBoundedSupport (Q i)) (σf σb : Fin d → ℝ)
    (hf : ∀ i, FwdDevLe (Q i) (σf i)) (hb : ∀ i, BwdDevLe (Q i) (σb i))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v : Fin d → ℝ) :
    VaR (Measure.pi Q) ε v ≤ cssBound (fun i => ∫ t, t ∂(Q i)) σf σb ε v := by
  set P := Measure.pi Q with hP
  set L := Real.log (1 / ε) with hL
  have hLpos : 0 < L := by
    have : 1 < 1 / ε := by rw [lt_div_iff₀ hε0]; linarith
    exact Real.log_pos this
  have hexpL : Real.exp (-L) = ε := by
    rw [hL, one_div, Real.log_inv, neg_neg, Real.exp_log hε0]
  set m := ∑ i, (∫ t, t ∂(Q i)) * v i with hm
  set S := ∑ i, (if v i < 0 then σb i ^ 2 * v i ^ 2 else σf i ^ 2 * v i ^ 2) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity)
  have hcss : cssBound (fun i => ∫ t, t ∂(Q i)) σf σb ε v = m + Real.sqrt (2 * L * S) := rfl
  rw [hcss]
  have hmeasX : Measurable fun u : Fin d → ℝ => u ⬝ᵥ v := (dot_continuous v).measurable
  -- membership for every c' above the bound
  have hmem : ∀ c', m + Real.sqrt (2 * L * S) < c' →
      ENNReal.ofReal (1 - ε) ≤ P {u | u ⬝ᵥ v ≤ c'} := by
    intro c' hc'
    set D := c' - m with hD
    have ha0 := Real.sqrt_nonneg (2 * L * S)
    have hDpos : 0 < D := by linarith
    have hsq : Real.sqrt (2 * L * S) ^ 2 = 2 * L * S := Real.sq_sqrt (by positivity)
    have hD2 : 2 * L * S ≤ D ^ 2 := by nlinarith
    set x := 2 * L / D with hx
    have hxpos : 0 < x := by positivity
    have ht := tail_le Q hQ σf σb hf hb x hxpos v c'
    have hsum : ∑ i, (x * ((∫ t, t ∂(Q i)) * v i) +
        x ^ 2 * (if v i < 0 then σb i ^ 2 * v i ^ 2 else σf i ^ 2 * v i ^ 2) / 2) =
        x * m + x ^ 2 * S / 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum]
    rw [hsum] at ht
    have hexp : -x * c' + (x * m + x ^ 2 * S / 2) ≤ -L := by
      have e : -x * c' + (x * m + x ^ 2 * S / 2) = -2 * L + L * ((2 * L * S) / D ^ 2) := by
        rw [hx]; field_simp; ring
      rw [e]
      have : (2 * L * S) / D ^ 2 ≤ 1 := (div_le_one (by positivity)).2 hD2
      nlinarith
    have htail : P.real {u | c' ≤ u ⬝ᵥ v} ≤ ε := by
      calc P.real {u | c' ≤ u ⬝ᵥ v} ≤ _ := ht
        _ ≤ Real.exp (-L) := Real.exp_le_exp.2 hexp
        _ = ε := hexpL
    have hmeasS : MeasurableSet {u : Fin d → ℝ | c' ≤ u ⬝ᵥ v} :=
      measurableSet_le measurable_const hmeasX
    have hcompl := probReal_compl_eq_one_sub (μ := P) hmeasS
    have hsub : {u : Fin d → ℝ | c' ≤ u ⬝ᵥ v}ᶜ ⊆ {u | u ⬝ᵥ v ≤ c'} := by
      intro u hu
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hu
      exact hu.le
    have hmono : P.real {u : Fin d → ℝ | c' ≤ u ⬝ᵥ v}ᶜ ≤ P.real {u | u ⬝ᵥ v ≤ c'} :=
      measureReal_mono hsub (measure_ne_top _ _)
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    change 1 - ε ≤ P.real {u | u ⬝ᵥ v ≤ c'}
    linarith
  -- bounded below
  have hbdd : BddBelow {y : ℝ | ENNReal.ofReal (1 - ε) ≤ P {u | u ⬝ᵥ v ≤ y}} := by
    set s : ℕ → Set (Fin d → ℝ) := fun n => {u | u ⬝ᵥ v ≤ -(n : ℝ)} with hs
    have hsm : ∀ n, NullMeasurableSet (s n) P := fun n =>
      (measurableSet_le hmeasX measurable_const).nullMeasurableSet
    have hanti : Antitone s := by
      intro a b hab u hu
      simp only [hs, Set.mem_setOf_eq] at hu ⊢
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    have hinter : (⋂ n, s n) = ∅ := by
      ext u
      simp only [hs, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_forall, not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-(u ⬝ᵥ v))
      exact ⟨n, by linarith⟩
    have htend := tendsto_measure_iInter_atTop (μ := P) hsm hanti ⟨0, measure_ne_top _ _⟩
    rw [hinter, measure_empty] at htend
    have hpos : (0 : ENNReal) < ENNReal.ofReal (1 - ε) := ENNReal.ofReal_pos.2 (by linarith)
    obtain ⟨n, hn⟩ := ((tendsto_order.1 htend).2 _ hpos).exists
    refine ⟨-(n : ℝ), fun y hy => ?_⟩
    by_contra hlt
    push_neg at hlt
    have hsub : {u : Fin d → ℝ | u ⬝ᵥ v ≤ y} ⊆ s n := by
      intro u hu
      simp only [hs, Set.mem_setOf_eq] at hu ⊢
      linarith
    have := (hy.trans (measure_mono hsub)).trans_lt hn
    exact lt_irrefl _ this
  unfold VaR MultistageStochastic.valueAtRisk
  exact le_of_forall_gt_imp_ge_of_dense fun c' hc' => csInf_le hbdd (hmem c' hc')

/-! ## Part 2: the support function of `UFB` -/

lemma logpos (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) : 0 < Real.log (1 / ε) := by
  have : 1 < 1 / ε := by rw [lt_div_iff₀ hε0]; linarith
  exact Real.log_pos this

lemma css_le_fb {d : ℕ} (mb mf sf sb μ : Fin d → ℝ) (hμ1 : ∀ i, mb i ≤ μ i) (hμ2 : ∀ i, μ i ≤ mf i)
    (ε : ℝ) (v : Fin d → ℝ) :
    cssBound μ sf sb ε v ≤ fbValue mb mf sf sb ε v := by
  simp only [cssBound, fbValue]
  apply add_le_add
  · refine Finset.sum_le_sum (fun i _ => ?_)
    by_cases h : 0 ≤ v i
    · simp only [h, if_true]; exact mul_le_mul_of_nonneg_right (hμ2 i) h
    · simp only [h, if_false]
      exact mul_le_mul_of_nonpos_right (hμ1 i) (le_of_lt (lt_of_not_ge h))
  · apply le_of_eq
    congr 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : 0 ≤ v i
    · have : ¬ v i < 0 := not_lt.mpr h
      simp only [h, this, if_true, if_false]
    · have : v i < 0 := lt_of_not_ge h
      simp only [h, this, if_true, if_false]

lemma dot_le_fb {d : ℕ} (mb mf sf sb : Fin d → ℝ) (hsf : ∀ i, 0 < sf i) (hsb : ∀ i, 0 < sb i)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v u : Fin d → ℝ) (hu : u ∈ UFB mb mf sf sb ε) :
    ∑ j, u j * v j ≤ fbValue mb mf sf sb ε v := by
  obtain ⟨y₁, y₂, y₃, h2, h3, hbox, hq, rfl⟩ := hu
  have hL := logpos ε hε0 hε1
  set a : Fin d → ℝ := fun j => if 0 ≤ v j then sf j * v j else -(sb j * v j) with ha
  set b : Fin d → ℝ := fun j => if 0 ≤ v j then y₂ j / sf j else y₃ j / sb j with hb
  have hsplit : ∀ j, (y₁ + y₂ - y₃) j * v j ≤
      (if 0 ≤ v j then mf j * v j else mb j * v j) + a j * b j := by
    intro j
    have h2j : 0 ≤ y₂ j := h2 j
    have h3j : 0 ≤ y₃ j := h3 j
    obtain ⟨hb1, hb2⟩ := hbox j
    simp only [Pi.add_apply, Pi.sub_apply, ha, hb]
    by_cases h : 0 ≤ v j
    · simp only [h, if_true]
      have e : sf j * v j * (y₂ j / sf j) = y₂ j * v j := by
        field_simp [(hsf j).ne']
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right hb2 h, mul_nonneg h3j h]
    · simp only [h, if_false]
      have hv : v j < 0 := lt_of_not_ge h
      have e : -(sb j * v j) * (y₃ j / sb j) = -(y₃ j * v j) := by
        field_simp [(hsb j).ne']
      rw [e]
      nlinarith [mul_le_mul_of_nonpos_right hb1 hv.le, mul_nonneg h2j (neg_nonneg.2 hv.le)]
  have hA : ∑ j, a j ^ 2 = ∑ j, (if 0 ≤ v j then sf j ^ 2 * v j ^ 2 else sb j ^ 2 * v j ^ 2) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : 0 ≤ v j <;> simp only [ha, h, if_true, if_false] <;> ring
  have hB : ∑ j, b j ^ 2 ≤ 2 * Real.log (1 / ε) := by
    have hterm : ∀ j, b j ^ 2 ≤ 2 * (y₂ j ^ 2 / (2 * sf j ^ 2) + y₃ j ^ 2 / (2 * sb j ^ 2)) := by
      intro j
      have e : 2 * (y₂ j ^ 2 / (2 * sf j ^ 2) + y₃ j ^ 2 / (2 * sb j ^ 2)) =
          (y₂ j / sf j) ^ 2 + (y₃ j / sb j) ^ 2 := by
        have := (hsf j).ne'
        have := (hsb j).ne'
        field_simp
      rw [e]
      by_cases h : 0 ≤ v j
      · simp only [hb, h, if_true]; nlinarith [sq_nonneg (y₃ j / sb j)]
      · simp only [hb, h, if_false]; nlinarith [sq_nonneg (y₂ j / sf j)]
    calc ∑ j, b j ^ 2 ≤ ∑ j, 2 * (y₂ j ^ 2 / (2 * sf j ^ 2) + y₃ j ^ 2 / (2 * sb j ^ 2)) :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = 2 * ∑ j, (y₂ j ^ 2 / (2 * sf j ^ 2) + y₃ j ^ 2 / (2 * sb j ^ 2)) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * Real.log (1 / ε) := by linarith
  have hS0 : 0 ≤ ∑ j, (if 0 ≤ v j then sf j ^ 2 * v j ^ 2 else sb j ^ 2 * v j ^ 2) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
  have hab : ∑ j, a j * b j ≤ Real.sqrt (2 * Real.log (1 / ε) *
      ∑ j, (if 0 ≤ v j then sf j ^ 2 * v j ^ 2 else sb j ^ 2 * v j ^ 2)) := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    calc (∑ j, a j * b j) ^ 2 ≤ (∑ j, a j ^ 2) * (∑ j, b j ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (∑ j, a j ^ 2) * (2 * Real.log (1 / ε)) :=
          mul_le_mul_of_nonneg_left hB (Finset.sum_nonneg (fun j _ => sq_nonneg _))
      _ = _ := by rw [hA]; ring
  calc ∑ j, (y₁ + y₂ - y₃) j * v j ≤
        ∑ j, ((if 0 ≤ v j then mf j * v j else mb j * v j) + a j * b j) :=
        Finset.sum_le_sum (fun j _ => hsplit j)
    _ = ∑ j, (if 0 ≤ v j then mf j * v j else mb j * v j) + ∑ j, a j * b j :=
        Finset.sum_add_distrib
    _ ≤ fbValue mb mf sf sb ε v := by
        unfold fbValue
        linarith [hab]

lemma attain {d : ℕ} (mb mf sf sb : Fin d → ℝ) (hm : ∀ i, mb i ≤ mf i)
    (hsf : ∀ i, 0 < sf i) (hsb : ∀ i, 0 < sb i) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : Fin d → ℝ) :
    ∃ u ∈ UFB mb mf sf sb ε, ∑ j, u j * v j = fbValue mb mf sf sb ε v := by
  have hLpos := logpos ε hε0 hε1
  by_cases hv : v = 0
  · subst hv
    refine ⟨mf, ⟨mf, 0, 0, le_rfl, le_rfl, fun i => ⟨hm i, le_rfl⟩, ?_, by simp⟩, ?_⟩
    · simp only [Pi.zero_apply]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero,
        Finset.sum_const_zero]
      exact hLpos.le
    · simp [fbValue]
  · set S := ∑ i, (if 0 ≤ v i then sf i ^ 2 * v i ^ 2 else sb i ^ 2 * v i ^ 2) with hS
    set L := Real.log (1 / ε) with hL
    have hSpos : 0 < S := by
      obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hv (funext hc)
      have hvj : 0 < v j ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj))
      refine Finset.sum_pos' (fun i _ => by split_ifs <;> positivity) ⟨j, Finset.mem_univ _, ?_⟩
      split_ifs
      · exact mul_pos (pow_pos (hsf j) 2) hvj
      · exact mul_pos (pow_pos (hsb j) 2) hvj
    set lam := Real.sqrt (S / (2 * L)) with hlam
    have hlampos : 0 < lam := Real.sqrt_pos.2 (by positivity)
    have hlam2 : lam ^ 2 = S / (2 * L) := Real.sq_sqrt (by positivity)
    refine ⟨(fun j => if 0 ≤ v j then mf j else mb j) +
        (fun j => if 0 ≤ v j then v j * sf j ^ 2 / lam else 0) -
        (fun j => if 0 ≤ v j then 0 else -(v j * sb j ^ 2 / lam)),
      ⟨_, _, _, ?_, ?_, ?_, ?_, rfl⟩, ?_⟩
    · intro j
      simp only [Pi.zero_apply]
      split_ifs with h
      · exact div_nonneg (mul_nonneg h (sq_nonneg _)) hlampos.le
      · exact le_rfl
    · intro j
      simp only [Pi.zero_apply]
      split_ifs with h
      · exact le_rfl
      · have hv' : v j < 0 := lt_of_not_ge h
        rw [← neg_div]
        exact div_nonneg (by nlinarith [sq_nonneg (sb j), pow_pos (hsb j) 2]) hlampos.le
    · intro j
      split_ifs with h
      · exact ⟨hm j, le_rfl⟩
      · exact ⟨le_rfl, hm j⟩
    · have hterm : ∀ j, ((if 0 ≤ v j then v j * sf j ^ 2 / lam else 0) ^ 2 / (2 * sf j ^ 2) +
          (if 0 ≤ v j then 0 else -(v j * sb j ^ 2 / lam)) ^ 2 / (2 * sb j ^ 2)) =
          (if 0 ≤ v j then sf j ^ 2 * v j ^ 2 else sb j ^ 2 * v j ^ 2) / (2 * lam ^ 2) := by
        intro j
        have := (hsf j).ne'
        have := (hsb j).ne'
        have := hlampos.ne'
        split_ifs with h
        · field_simp
          ring
        · field_simp
          ring
      rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_div, ← hS, hlam2]
      apply le_of_eq
      field_simp
      exact hL
    · have hterm : ∀ j, ((fun j => if 0 ≤ v j then mf j else mb j) +
          (fun j => if 0 ≤ v j then v j * sf j ^ 2 / lam else 0) -
          (fun j => if 0 ≤ v j then 0 else -(v j * sb j ^ 2 / lam))) j * v j =
          (if 0 ≤ v j then mf j * v j else mb j * v j) +
          (if 0 ≤ v j then sf j ^ 2 * v j ^ 2 else sb j ^ 2 * v j ^ 2) / lam := by
        intro j
        have := hlampos.ne'
        simp only [Pi.add_apply, Pi.sub_apply]
        split_ifs with h
        · field_simp
          ring
        · field_simp
          ring
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, ← Finset.sum_div,
        ← hS]
      unfold fbValue
      rw [← hS, ← hL]
      congr 1
      symm
      rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (div_pos hSpos hlampos),
        show S / lam * (S / lam) = S ^ 2 / lam ^ 2 by ring, hlam2]
      field_simp

lemma support_eq {d : ℕ} (mb mf sf sb : Fin d → ℝ) (hm : ∀ i, mb i ≤ mf i)
    (hsf : ∀ i, 0 < sf i) (hsb : ∀ i, 0 < sb i) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : Fin d → ℝ) :
    RobustMDP.Shared.supportFunction (UFB mb mf sf sb ε) v = fbValue mb mf sf sb ε v := by
  unfold RobustMDP.Shared.supportFunction
  apply IsGreatest.csSup_eq
  obtain ⟨u, hu, hval⟩ := attain mb mf sf sb hm hsf hsb ε hε0 hε1 v
  refine ⟨⟨u, hu, hval⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact dot_le_fb mb mf sf sb hsf hsb ε hε0 hε1 v w hw

/-! ## Part 3: `UFB` is nonempty, convex and compact -/

lemma ufb_convex {d : ℕ} (mb mf sf sb : Fin d → ℝ) (hsf : ∀ i, 0 < sf i) (hsb : ∀ i, 0 < sb i)
    (ε : ℝ) : Convex ℝ (UFB mb mf sf sb ε) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨p₁, p₂, p₃, hp2, hp3, hpb, hpq, rfl⟩ := hx
  obtain ⟨q₁, q₂, q₃, hq2, hq3, hqb, hqq, rfl⟩ := hy
  have key : ∀ (p q c : ℝ), 0 < c → (a * p + b * q) ^ 2 / c ≤ a * (p ^ 2 / c) + b * (q ^ 2 / c) := by
    intro p q c hc
    rw [show a * (p ^ 2 / c) + b * (q ^ 2 / c) = (a * p ^ 2 + b * q ^ 2) / c by ring]
    apply div_le_div_of_nonneg_right _ hc.le
    have e : a * p ^ 2 + b * q ^ 2 - (a * p + b * q) ^ 2 = a * b * (p - q) ^ 2 := by
      have hb' : b = 1 - a := by linarith
      subst hb'
      ring
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p - q))]
  refine ⟨a • p₁ + b • q₁, a • p₂ + b • q₂, a • p₃ + b • q₃, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact add_nonneg (mul_nonneg ha (hp2 i)) (mul_nonneg hb (hq2 i))
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact add_nonneg (mul_nonneg ha (hp3 i)) (mul_nonneg hb (hq3 i))
  · intro i
    obtain ⟨h1, h2⟩ := hpb i
    obtain ⟨h3, h4⟩ := hqb i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e1 : mb i = a * mb i + b * mb i := by rw [← add_mul, hab, one_mul]
    have e2 : mf i = a * mf i + b * mf i := by rw [← add_mul, hab, one_mul]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h3 hb]
    · nlinarith [mul_le_mul_of_nonneg_left h2 ha, mul_le_mul_of_nonneg_left h4 hb]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc ∑ i, ((a * p₂ i + b * q₂ i) ^ 2 / (2 * sf i ^ 2) +
            (a * p₃ i + b * q₃ i) ^ 2 / (2 * sb i ^ 2))
        ≤ ∑ i, (a * (p₂ i ^ 2 / (2 * sf i ^ 2)) + b * (q₂ i ^ 2 / (2 * sf i ^ 2)) +
            (a * (p₃ i ^ 2 / (2 * sb i ^ 2)) + b * (q₃ i ^ 2 / (2 * sb i ^ 2)))) :=
          Finset.sum_le_sum (fun i _ => add_le_add (key _ _ _ (by have := hsf i; positivity))
            (key _ _ _ (by have := hsb i; positivity)))
      _ = a * ∑ i, (p₂ i ^ 2 / (2 * sf i ^ 2) + p₃ i ^ 2 / (2 * sb i ^ 2)) +
          b * ∑ i, (q₂ i ^ 2 / (2 * sf i ^ 2) + q₃ i ^ 2 / (2 * sb i ^ 2)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ Real.log (1 / ε) := by
          have e3 : Real.log (1 / ε) = a * Real.log (1 / ε) + b * Real.log (1 / ε) := by
            rw [← add_mul, hab, one_mul]
          nlinarith [mul_le_mul_of_nonneg_left hpq ha, mul_le_mul_of_nonneg_left hqq hb]
  · ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

lemma ufb_compact {d : ℕ} (mb mf sf sb : Fin d → ℝ) (hsf : ∀ i, 0 < sf i) (hsb : ∀ i, 0 < sb i)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) : IsCompact (UFB mb mf sf sb ε) := by
  have hL := logpos ε hε0 hε1
  set K : Set ((Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ)) :=
    {y | 0 ≤ y.2.1 ∧ 0 ≤ y.2.2 ∧ (∀ i, mb i ≤ y.1 i ∧ y.1 i ≤ mf i) ∧
      ∑ i, (y.2.1 i ^ 2 / (2 * sf i ^ 2) + y.2.2 i ^ 2 / (2 * sb i ^ 2)) ≤ Real.log (1 / ε)}
    with hK
  have hUK : UFB mb mf sf sb ε =
      (fun y : (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) => y.1 + y.2.1 - y.2.2) '' K := by
    ext u
    constructor
    · rintro ⟨y₁, y₂, y₃, h2, h3, hb, hs, rfl⟩
      exact ⟨(y₁, y₂, y₃), ⟨h2, h3, hb, hs⟩, rfl⟩
    · rintro ⟨⟨y₁, y₂, y₃⟩, ⟨h2, h3, hb, hs⟩, rfl⟩
      exact ⟨y₁, y₂, y₃, h2, h3, hb, hs, rfl⟩
  have hKc : IsClosed K := by
    have c1 : Continuous fun y : (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) => y.2.1 := by fun_prop
    have c2 : Continuous fun y : (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) => y.2.2 := by fun_prop
    have c3 : Continuous fun y : (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) =>
        ∑ i, (y.2.1 i ^ 2 / (2 * sf i ^ 2) + y.2.2 i ^ 2 / (2 * sb i ^ 2)) := by fun_prop
    rw [hK]
    simp only [Set.setOf_and, Set.setOf_forall]
    refine (isClosed_le continuous_const c1).inter ((isClosed_le continuous_const c2).inter
      (IsClosed.inter ?_ (isClosed_le c3 continuous_const)))
    refine isClosed_iInter fun i => IsClosed.inter (isClosed_le continuous_const ?_)
      (isClosed_le ?_ continuous_const)
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply i).comp continuous_fst
  set B₂ : Fin d → ℝ := fun i => 1 + 2 * sf i ^ 2 * Real.log (1 / ε) with hB₂
  set B₃ : Fin d → ℝ := fun i => 1 + 2 * sb i ^ 2 * Real.log (1 / ε) with hB₃
  have hbox : K ⊆ Set.Icc mb mf ×ˢ (Set.Icc 0 B₂ ×ˢ Set.Icc 0 B₃) := by
    rintro ⟨y₁, y₂, y₃⟩ ⟨h2, h3, hb, hs⟩
    have hterm : ∀ i, y₂ i ^ 2 / (2 * sf i ^ 2) + y₃ i ^ 2 / (2 * sb i ^ 2) ≤ Real.log (1 / ε) :=
      fun i => (Finset.single_le_sum
        (f := fun i => y₂ i ^ 2 / (2 * sf i ^ 2) + y₃ i ^ 2 / (2 * sb i ^ 2))
        (fun j _ => by positivity) (Finset.mem_univ i)).trans hs
    refine ⟨⟨fun i => (hb i).1, fun i => (hb i).2⟩, ⟨h2, fun i => ?_⟩, ⟨h3, fun i => ?_⟩⟩
    · have h := hterm i
      have h0 := div_nonneg (sq_nonneg (y₃ i)) (by positivity : (0 : ℝ) ≤ 2 * sb i ^ 2)
      have hp : y₂ i ^ 2 / (2 * sf i ^ 2) ≤ Real.log (1 / ε) := by linarith
      rw [div_le_iff₀ (by have := hsf i; positivity)] at hp
      show y₂ i ≤ 1 + 2 * sf i ^ 2 * Real.log (1 / ε)
      nlinarith [sq_nonneg (y₂ i - 1)]
    · have h := hterm i
      have h0 := div_nonneg (sq_nonneg (y₂ i)) (by positivity : (0 : ℝ) ≤ 2 * sf i ^ 2)
      have hp : y₃ i ^ 2 / (2 * sb i ^ 2) ≤ Real.log (1 / ε) := by linarith
      rw [div_le_iff₀ (by have := hsb i; positivity)] at hp
      show y₃ i ≤ 1 + 2 * sb i ^ 2 * Real.log (1 / ε)
      nlinarith [sq_nonneg (y₃ i - 1)]
  have hcomp : IsCompact (Set.Icc mb mf ×ˢ (Set.Icc (0 : Fin d → ℝ) B₂ ×ˢ Set.Icc 0 B₃)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  rw [hUK]
  exact (hcomp.of_isClosed_subset hKc hbox).image (by fun_prop)

end P2a39d195

open DataDrivenRO.FwdBwd MeasureTheory in
theorem solution {d : ℕ} (mb mf sf sb : Fin d → ℝ) (hm : ∀ i, mb i ≤ mf i)
    (hsf : ∀ i, 0 < sf i) (hsb : ∀ i, 0 < sb i) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∀ (Q : Fin d → Measure ℝ) [∀ i, IsProbabilityMeasure (Q i)], Admissible mb mf sf sb Q →
        ∀ v, VaR (Measure.pi Q) ε v ≤ fbValue mb mf sf sb ε v) ∧
    (∀ v, RobustMDP.Shared.supportFunction (UFB mb mf sf sb ε) v = fbValue mb mf sf sb ε v) ∧
    ((UFB mb mf sf sb ε).Nonempty ∧ Convex ℝ (UFB mb mf sf sb ε) ∧
      IsCompact (UFB mb mf sf sb ε)) := by
  refine ⟨?_, fun v => P2a39d195.support_eq mb mf sf sb hm hsf hsb ε hε0 hε1 v, ?_,
    P2a39d195.ufb_convex mb mf sf sb hsf hsb ε, P2a39d195.ufb_compact mb mf sf sb hsf hsb ε hε0 hε1⟩
  · intro Q _ hQ v
    exact (P2a39d195.css Q hQ.bdd sf sb hQ.fwd hQ.bwd ε hε0 hε1 v).trans
      (P2a39d195.css_le_fb mb mf sf sb _ hQ.mean_ge hQ.mean_le ε v)
  · obtain ⟨u, hu, -⟩ := P2a39d195.attain mb mf sf sb hm hsf hsb ε hε0 hε1 0
    exact ⟨u, hu⟩
