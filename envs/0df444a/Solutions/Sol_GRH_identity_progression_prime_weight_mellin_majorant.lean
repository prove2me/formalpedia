-- Prove2me | solution 1 for GRH.identity_progression_prime_weight_mellin_majorant
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T01:46:36.610419+00:00
-- url     : https://prove2.me/submissions/d89f72dc-0aa4-4fe2-87ad-fddac297329c

import Theorems.Thm_GRH_identity_progression_mangoldt_series_detects_all_dirichlet_zeros
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp

open Complex MeasureTheory Filter Finset ArithmeticFunction GRH.SplitPrimeLower GRH.OneSidedMoebius

private noncomputable abbrev K := Real.log 4 + 4

private theorem Wpos (q n : ℕ) : 0 ≤ mangoldtWeight q n :=
  sum_nonneg fun i _ => vonMangoldt.residueClass_nonneg (1:ZMod q) i

private theorem Wbound (q : ℕ) {x : ℝ} (hx : 0 ≤ x) : mangoldtWeight q ⌊x⌋₊ ≤ K*x := by
  apply le_trans _ (Chebyshev.psi_le_const_mul_self hx)
  unfold mangoldtWeight Chebyshev.psi
  rw [show Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ from Icc_succ_left_eq_Ioc 0 _]
  exact sum_le_sum fun i _ => vonMangoldt.residueClass_le (1:ZMod q) i

private theorem Wmeas (q : ℕ) : Measurable (fun x : ℝ => mangoldtWeight q ⌊x⌋₊) :=
  (measurable_of_countable (mangoldtWeight q)).comp Nat.measurable_floor

private theorem Wcoe (q n : ℕ) : (mangoldtWeight q n : ℂ) =
    ∑ i ∈ Icc 1 n, (vonMangoldt.residueClass (1:ZMod q) i : ℂ) := by
  unfold mangoldtWeight
  push_cast
  rfl

private theorem Wint (q : ℕ) {s : ℂ} (hs : 1<s.re) :
    IntegrableOn (fun x : ℝ => (mangoldtWeight q ⌊x⌋₊:ℂ)*(x:ℂ)^(-s-1)) (Set.Ioi 1) := by
  have hi : IntegrableOn (fun x : ℝ => K*x^(-s.re)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  refine hi.mono' (((Complex.measurable_ofReal.comp (Wmeas q)).mul
    (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Wpos ..),
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  rw [show (-s-1).re = -s.re+(-1) by simp [sub_eq_add_neg],Real.rpow_add hx0,Real.rpow_neg_one]
  calc
    _ ≤ (K*x)*(x^(-s.re)*x⁻¹) := mul_le_mul_of_nonneg_right (Wbound q hx0.le) (by positivity)
    _ = _ := by field_simp

private theorem Wseries (q : ℕ) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n => (vonMangoldt.residueClass (1:ZMod q) n:ℂ)) s =
      s * transform (fun x => mangoldtWeight q ⌊x⌋₊) s := by
  let f : ℕ → ℂ := fun n => (vonMangoldt.residueClass (1:ZMod q) n:ℂ)
  have hO : Asymptotics.IsBigO atTop (fun n => ∑ i ∈ Icc 1 n, f i)
      (fun n : ℕ => (n:ℝ)^(1:ℝ)) := by
    refine Asymptotics.IsBigO.of_bound K (Eventually.of_forall fun n => ?_)
    simp only [f,← Wcoe,Complex.norm_real,Real.norm_eq_abs,Real.rpow_one,
      abs_of_nonneg (Wpos ..),abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) n)]
    simpa using Wbound q (x:=(n:ℝ)) (by positivity)
  have summ : LSeriesSummable f s := LSeriesSummable_of_abscissaOfAbsConv_lt_re
    ((vonMangoldt.abscissaOfAbsConv_residueClass_le_one (1:ZMod q)).trans_lt (by exact_mod_cast hs))
  have he := LSeries_eq_mul_integral f zero_le_one hs summ hO
  simpa only [transform,Wcoe,neg_add_rev,sub_eq_add_neg,add_comm (-1:ℂ) (-s),f] using he

private theorem powIntegral (u : ℝ) {s : ℂ} (hs : u<s.re) :
    (∫ x : ℝ in Set.Ioi 1, (x:ℂ)^((u:ℂ)-s-1)) = 1/(s-u) := by
  rw [integral_Ioi_cpow_of_lt (by simp;linarith) zero_lt_one]
  simp only [ofReal_one,one_cpow,show (u:ℂ)-s-1+1 = -(s-u) by ring,neg_div_neg_eq]

theorem solution (q : ℕ) [NeZero q] (D θ : ℝ) (hD : 0≤D) (hθ : θ<1) :
    Measurable (primeMajorant q D θ) ∧
    (∀ σ : ℝ, 1<σ → IntegrableOn (fun x : ℝ => primeMajorant q D θ x*x^(-σ-1)) (Set.Ioi 1)) ∧
    ∀ s : ℂ, 1<s.re → transform (primeMajorant q D θ) s =
      (D:ℂ)/(s-θ) - (logDeriv (regularProduct q) s+1)/s := by
  have hm : Measurable (primeMajorant q D θ) :=
    ((measurable_const.mul (measurable_id.pow_const θ)).add (measurable_const.mul (Wmeas q))).sub measurable_id
  refine ⟨hm,?_,?_⟩
  · intro σ hσ
    have hi : IntegrableOn (fun x : ℝ => (D+(q.totient:ℝ)*K+1)*x^(-σ)) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
    refine hi.mono' ((hm.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hx
    have hx0 := zero_lt_one.trans hx1
    have hp : x^θ ≤ x := by simpa using Real.rpow_le_rpow_of_exponent_le hx1.le hθ.le
    have hmaj : |primeMajorant q D θ x| ≤ (D+(q.totient:ℝ)*K+1)*x := by
      unfold primeMajorant
      apply (abs_sub _ _).trans
      rw [abs_of_nonneg (show 0 ≤ D*x^θ+(q.totient:ℝ)*mangoldtWeight q ⌊x⌋₊ by
        positivity [Wpos q ⌊x⌋₊]),abs_of_pos hx0]
      nlinarith only [mul_le_mul_of_nonneg_left hp hD,mul_le_mul_of_nonneg_left
        (Wbound q hx0.le) (Nat.cast_nonneg (α:=ℝ) q.totient)]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    rw [show -σ-1 = -σ+(-1) by ring,Real.rpow_add hx0,Real.rpow_neg_one]
    calc
      _ ≤ ((D+(q.totient:ℝ)*K+1)*x)*(x^(-σ)*x⁻¹) := mul_le_mul_of_nonneg_right hmaj (by positivity)
      _ = _ := by field_simp
  · intro s hs
    have hθs := hθ.trans hs
    have hI (u : ℝ) (hu : u<s.re) :
        IntegrableOn (fun x : ℝ => (x:ℂ)^((u:ℂ)-s-1)) (Set.Ioi 1) :=
      integrableOn_Ioi_cpow_of_lt (by simp;linarith) zero_lt_one
    have hpt : ∀ x ∈ Set.Ioi (1:ℝ), (primeMajorant q D θ x:ℂ)*(x:ℂ)^(-s-1) =
        (D:ℂ)*(x:ℂ)^((θ:ℂ)-s-1) + (q.totient:ℂ)*((mangoldtWeight q ⌊x⌋₊:ℂ)*(x:ℂ)^(-s-1)) -
        (x:ℂ)^(((1:ℝ):ℂ)-s-1) := by
      intro x hx
      have hx0 : 0 < x := zero_lt_one.trans hx
      have hxc : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
      rw [primeMajorant,ofReal_sub,ofReal_add,ofReal_mul,ofReal_mul,ofReal_natCast,ofReal_cpow hx0.le,
        show (θ:ℂ)-s-1 = θ+(-s-1) by ring,cpow_add _ _ hxc,ofReal_one,
        show (1:ℂ)-s-1 = 1+(-s-1) by ring,cpow_add _ _ hxc,Complex.cpow_one]
      ring
    have hsum : IntegrableOn (fun x : ℝ => (D:ℂ)*(x:ℂ)^((θ:ℂ)-s-1) +
        (q.totient:ℂ)*((mangoldtWeight q ⌊x⌋₊:ℂ)*(x:ℂ)^(-s-1))) (Set.Ioi 1) :=
      ((hI θ hθs).const_mul (D:ℂ)).add ((Wint q hs).const_mul (q.totient:ℂ))
    unfold transform
    rw [setIntegral_congr_fun measurableSet_Ioi hpt,integral_sub hsum (hI 1 hs),
      integral_add ((hI θ hθs).const_mul (D:ℂ)) ((Wint q hs).const_mul (q.totient:ℂ)),
      integral_const_mul,integral_const_mul,powIntegral θ hθs,powIntegral 1 hs,ofReal_one]
    change (D:ℂ)*(1/(s-θ)) + (q.totient:ℂ)*transform (fun x => mangoldtWeight q ⌊x⌋₊) s - 1/(s-1) = _
    have e := (GRH.identity_progression_mangoldt_series_detects_all_dirichlet_zeros q).2.2.2 s hs
    rw [Wseries q hs] at e
    have hs0 : s≠0 := fun h => by simp [h] at hs;linarith
    have hs1 : s-1≠0 := sub_ne_zero.mpr fun h => by simp [h] at hs
    linear_combination (norm := (field_simp; ring)) e / s
