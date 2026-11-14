-- Prove2me | solution 1 for BosonicLearn.husimi_fourier
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T20:22:49.988662+00:00
-- url     : https://prove2.me/submissions/4ccc0fd2-c2a3-47ca-b3f3-9081aeb3120f

import Mathlib
import Definitions.Def_BosonicLearn_husimiQ
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Theorems.Thm_BosonicLearn_coherent_weyl_integral
import Theorems.Thm_BosonicLearn_displacementMatrix_unitary
import Theorems.Thm_BosonicLearn_effect_trace_pairing

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity NuclearExpansion)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (oscillatorCharacteristic
  OscillatorCharacteristicSummable oscillatorWeylKernel)
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory Filter
open scoped ENNReal Topology

open BosonicLearn

noncomputable section

/-! ### Products of series over multi-indices -/

/-- `PP α`: a product over the finite type `α` of absolutely convergent series over `ℕ` is an
absolutely convergent series over the multi-indices `α → ℕ`, with sum the product of the sums. -/
private def PP (α : Type) [Fintype α] : Prop :=
  ∀ (f : α → ℕ → ℂ) (s : α → ℂ),
      (∀ i, Summable fun k => ‖f i k‖) → (∀ i, HasSum (f i) (s i)) →
      Summable (fun w : α → ℕ => ‖∏ i, f i (w i)‖) ∧
      HasSum (fun w : α → ℕ => ∏ i, f i (w i)) (∏ i, s i)

private lemma PP_equiv (α β : Type) [Fintype α] [Fintype β] (e : α ≃ β) (ih : PP α) : PP β := by
  intro f s hn hs
  obtain ⟨h1, h2⟩ := ih (fun i => f (e i)) (fun i => s (e i)) (fun i => hn (e i))
    (fun i => hs (e i))
  let E : (β → ℕ) ≃ (α → ℕ) := Equiv.arrowCongr e.symm (Equiv.refl ℕ)
  have hE : ∀ w : β → ℕ, ∏ i, f (e i) (E w i) = ∏ j, f j (w j) := by
    intro w
    exact Equiv.prod_comp e (fun j => f j (w j))
  have hsE : ∏ i, s (e i) = ∏ j, s j := Equiv.prod_comp e s
  refine ⟨?_, ?_⟩
  · have := (Equiv.summable_iff E).mpr h1
    have hfun : ((fun w : α → ℕ => ‖∏ i, f (e i) (w i)‖) ∘ E) =
        fun w : β → ℕ => ‖∏ j, f j (w j)‖ := by
      funext w
      show ‖∏ i, f (e i) (E w i)‖ = _
      rw [hE]
    rw [hfun] at this
    exact this
  · have := (Equiv.hasSum_iff E).mpr h2
    have hfun : ((fun w : α → ℕ => ∏ i, f (e i) (w i)) ∘ E) =
        fun w : β → ℕ => ∏ j, f j (w j) := by
      funext w
      show ∏ i, f (e i) (E w i) = _
      rw [hE]
    rw [hfun, hsE] at this
    exact this

private lemma PP_empty : PP PEmpty := by
  intro f s _ _
  have h := hasSum_unique (fun w : PEmpty → ℕ => ∏ i, f i (w i))
  have hn := hasSum_unique (fun w : PEmpty → ℕ => ‖∏ i, f i (w i)‖)
  refine ⟨hn.summable, ?_⟩
  convert h using 1
  simp

private lemma PP_option (α : Type) [Fintype α] (ih : PP α) : PP (Option α) := by
  intro f s hn hs
  obtain ⟨h1, h2⟩ := ih (fun i => f (some i)) (fun i => s (some i)) (fun i => hn (some i))
    (fun i => hs (some i))
  let E : (Option α → ℕ) ≃ ℕ × (α → ℕ) := Equiv.piOptionEquivProd (β := fun _ => ℕ)
  have hmulN : Summable fun x : ℕ × (α → ℕ) => ‖f none x.1 * ∏ i, f (some i) (x.2 i)‖ :=
    Summable.mul_norm (f := f none) (g := fun w : α → ℕ => ∏ i, f (some i) (w i)) (hn none) h1
  have hmulS : Summable fun x : ℕ × (α → ℕ) => f none x.1 * ∏ i, f (some i) (x.2 i) :=
    hmulN.of_norm
  have hmul : HasSum (fun x : ℕ × (α → ℕ) => f none x.1 * ∏ i, f (some i) (x.2 i))
      (s none * ∏ i, s (some i)) :=
    HasSum.mul (f := f none) (g := fun w : α → ℕ => ∏ i, f (some i) (w i)) (hs none) h2 hmulS
  have hEw : ∀ w : Option α → ℕ, E w = (w none, fun i => w (some i)) := fun w => rfl
  refine ⟨?_, ?_⟩
  · have h3 := (Equiv.summable_iff E).mpr hmulN
    have hfun : ((fun x : ℕ × (α → ℕ) => ‖f none x.1 * ∏ i, f (some i) (x.2 i)‖) ∘ E) =
        fun w : Option α → ℕ => ‖∏ j, f j (w j)‖ := by
      funext w
      rw [Function.comp_apply, hEw, Fintype.prod_option (fun j => f j (w j))]
    rw [hfun] at h3
    exact h3
  · have h3 := (Equiv.hasSum_iff E).mpr hmul
    have hfun : ((fun x : ℕ × (α → ℕ) => f none x.1 * ∏ i, f (some i) (x.2 i)) ∘ E) =
        fun w : Option α → ℕ => ∏ j, f j (w j) := by
      funext w
      rw [Function.comp_apply, hEw, Fintype.prod_option (fun j => f j (w j))]
    rw [hfun, ← Fintype.prod_option s] at h3
    exact h3

private lemma hasSum_pi_prod (I : Type) [Fintype I] : PP I := by
  refine Fintype.induction_empty_option (P := fun (α : Type) [Fintype α] => PP α) ?_ ?_ ?_ I
  · intro α β _ e ih
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    exact PP_equiv α β e ih
  · exact PP_empty
  · intro α _ ih
    exact PP_option α ih

/-! ### The coherent vector as an element of `ℓ²` -/

private lemma fac_norm_sq (E : ℝ) (w : ℂ) (k : ℕ) :
    ‖((E : ℝ) : ℂ) * w ^ k / ((Real.sqrt 2 : ℂ) ^ k * (Real.sqrt (Nat.factorial k) : ℂ))‖ ^ 2 =
      E ^ 2 * ((‖w‖ ^ 2 / 2) ^ k / (Nat.factorial k : ℝ)) := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hk : (Real.sqrt (Nat.factorial k)) ^ 2 = (Nat.factorial k : ℝ) :=
    Real.sq_sqrt (by positivity)
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow, mul_pow, mul_pow, Real.norm_eq_abs, sq_abs,
    ← pow_mul, ← pow_mul, mul_comm k 2, pow_mul, pow_mul, h2, hk, div_pow]
  have hf : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  field_simp

private lemma coherent_sq_summable {n : ℕ} (β : Fin n ⊕ Fin n → ℝ) :
    Summable fun m : Occupation (Fin n) => ‖coherentVector β m‖ ^ 2 := by
  let fac : Fin n → ℕ → ℂ := fun j k =>
    ((Real.exp (-(β (Sum.inl j) ^ 2 + β (Sum.inr j) ^ 2) / 4) : ℝ) : ℂ) *
      ((β (Sum.inl j) : ℂ) + Complex.I * (β (Sum.inr j) : ℂ)) ^ k /
        ((Real.sqrt 2 : ℂ) ^ k * (Real.sqrt (Nat.factorial k) : ℂ))
  have hn : ∀ j, Summable fun k => ‖(((‖fac j k‖ ^ 2 : ℝ)) : ℂ)‖ := by
    intro j
    have h := (Real.summable_pow_div_factorial
      (‖(β (Sum.inl j) : ℂ) + Complex.I * (β (Sum.inr j) : ℂ)‖ ^ 2 / 2)).mul_left
        ((Real.exp (-(β (Sum.inl j) ^ 2 + β (Sum.inr j) ^ 2) / 4)) ^ 2)
    refine h.congr fun k => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact (fac_norm_sq _ _ k).symm
  have key := (hasSum_pi_prod (Fin n) (fun j k => (((‖fac j k‖ ^ 2 : ℝ)) : ℂ))
    (fun j => ∑' k, (((‖fac j k‖ ^ 2 : ℝ)) : ℂ)) hn (fun j => (hn j).of_norm.hasSum)).1
  refine key.congr fun m => ?_
  rw [norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_norm]
  rw [Finset.prod_pow, ← norm_prod]
  rfl

private lemma coherent_memℓp {n : ℕ} (β : Fin n ⊕ Fin n → ℝ) :
    Memℓp (coherentVector β) 2 := by
  refine memℓp_gen ?_
  have h := coherent_sq_summable β
  simpa using h

/-- The conjugate coherent vector `u ↦ conj c(β)_u` as an element of `ℓ²`. -/
private def dv {n : ℕ} (β : Fin n ⊕ Fin n → ℝ) : Hilbert (Occupation (Fin n)) :=
  ⟨fun u => star (coherentVector β u), (coherent_memℓp β).star_mem⟩

private lemma dv_apply {n : ℕ} (β : Fin n ⊕ Fin n → ℝ) (u : Occupation (Fin n)) :
    dv β u = star (coherentVector β u) := rfl

private lemma coherent_measurable {n : ℕ} (u : Occupation (Fin n)) :
    Measurable fun β : Fin n ⊕ Fin n → ℝ => coherentVector β u := by
  unfold coherentVector
  fun_prop

/-- The transform `S z (β) = ∑_u c(β)_u z_u = ⟪conj c(β), z⟫`. -/
private def S {n : ℕ} (z : Hilbert (Occupation (Fin n))) (β : Fin n ⊕ Fin n → ℝ) : ℂ :=
  inner ℂ (dv β) z

private lemma S_hasSum {n : ℕ} (z : Hilbert (Occupation (Fin n))) (β : Fin n ⊕ Fin n → ℝ) :
    HasSum (fun u => coherentVector β u * z u) (S z β) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) (dv β) z
  unfold S
  simpa [dv_apply, mul_comm] using h

private lemma S_measurable {n : ℕ} (z : Hilbert (Occupation (Fin n))) : Measurable (S z) := by
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset (Occupation (Fin n))))
    (f := fun F β => ∑ u ∈ F, coherentVector β u * z u) (fun F => ?_) ?_
  · exact Finset.measurable_sum _ fun u _ => (coherent_measurable u).mul_const _
  · rw [tendsto_pi_nhds]
    intro β
    exact S_hasSum z β

/-! ### Resolution of the identity and the Bessel inequality -/

/-- Resolution of the identity by coherent states (`coherent_weyl_integral` at `t = 0`). -/
private lemma cwi_zero {n : ℕ} (u v : Occupation (Fin n)) :
    Integrable (fun β : Fin n ⊕ Fin n → ℝ => coherentVector β v * star (coherentVector β u)) ∧
    ∫ β : Fin n ⊕ Fin n → ℝ, coherentVector β v * star (coherentVector β u) =
      if v = u then (((2 * Real.pi) ^ n : ℝ) : ℂ) else 0 := by
  obtain ⟨h1, h2⟩ := coherent_weyl_integral (0 : Fin n ⊕ Fin n → ℝ) u v
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul, ite_self] at h1 h2
  have hW : oscillatorWeylKernel (fun _ : Fin n × Fin 2 => (0 : ℝ)) v u =
      if v = u then 1 else 0 := by
    unfold oscillatorWeylKernel
    simp only [Complex.ofReal_zero, neg_zero, mul_zero, add_zero, zero_div]
    simp_rw [(displacementMatrix_unitary 0 _ _).2.1]
    by_cases h : v = u
    · subst h
      simp
    · rw [if_neg h]
      obtain ⟨j, hj⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
  refine ⟨h1, ?_⟩
  rw [h2, hW]
  split_ifs <;> simp

private lemma lp_sum_sq_le {I : Type} (l : Hilbert I) (G : Finset I) :
    ∑ u ∈ G, ‖l u‖ ^ 2 ≤ ‖l‖ ^ 2 := by
  have h := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) l G
  simpa using h

/-- Finite Bessel identity. -/
private lemma bessel_fin {n : ℕ} (F : Finset (Occupation (Fin n))) (z : Occupation (Fin n) → ℂ) :
    Integrable (fun β : Fin n ⊕ Fin n → ℝ => ‖∑ v ∈ F, coherentVector β v * z v‖ ^ 2) ∧
    ∫ β : Fin n ⊕ Fin n → ℝ, ‖∑ v ∈ F, coherentVector β v * z v‖ ^ 2 =
      (2 * Real.pi) ^ n * ∑ v ∈ F, ‖z v‖ ^ 2 := by
  have hexp : ∀ β : Fin n ⊕ Fin n → ℝ, ((‖∑ v ∈ F, coherentVector β v * z v‖ ^ 2 : ℝ) : ℂ) =
      ∑ v ∈ F, ∑ u ∈ F,
        (z v * star (z u)) * (coherentVector β v * star (coherentVector β u)) := by
    intro β
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
    rw [map_mul, ← starRingEnd_apply, ← starRingEnd_apply]
    ring
  have hint : Integrable (fun β : Fin n ⊕ Fin n → ℝ => ∑ v ∈ F, ∑ u ∈ F,
      (z v * star (z u)) * (coherentVector β v * star (coherentVector β u))) :=
    integrable_finsetSum _ fun v _ => integrable_finsetSum _ fun u _ =>
      (cwi_zero u v).1.const_mul _
  have hintC : Integrable (fun β : Fin n ⊕ Fin n → ℝ =>
      ((‖∑ v ∈ F, coherentVector β v * z v‖ ^ 2 : ℝ) : ℂ)) := by
    simp_rw [hexp]
    exact hint
  have hintR : Integrable (fun β : Fin n ⊕ Fin n → ℝ =>
      ‖∑ v ∈ F, coherentVector β v * z v‖ ^ 2) := by
    exact hintC.re.congr (ae_of_all _ fun β => Complex.ofReal_re _)
  refine ⟨hintR, ?_⟩
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun v _ => integrable_finsetSum _ fun u _ =>
    (cwi_zero u v).1.const_mul _)]
  have h1 : ∀ v ∈ F, ∫ β : Fin n ⊕ Fin n → ℝ, ∑ u ∈ F,
      (z v * star (z u)) * (coherentVector β v * star (coherentVector β u)) =
      (((2 * Real.pi) ^ n : ℝ) : ℂ) * ((‖z v‖ ^ 2 : ℝ) : ℂ) := by
    intro v hv
    rw [integral_finsetSum _ (fun u _ => (cwi_zero u v).1.const_mul _)]
    simp_rw [integral_const_mul, (cwi_zero _ v).2, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq, if_pos hv, Complex.ofReal_pow ‖z v‖ 2, ← Complex.mul_conj',
      ← starRingEnd_apply]
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  push_cast
  rfl

private lemma S_sq_lintegral_le {n : ℕ} (z : Hilbert (Occupation (Fin n))) :
    ∫⁻ β : Fin n ⊕ Fin n → ℝ, ‖S z β‖ₑ ^ 2 ≤ ENNReal.ofReal ((2 * Real.pi) ^ n * ‖z‖ ^ 2) := by
  have hlim : ∀ β : Fin n ⊕ Fin n → ℝ, ‖S z β‖ₑ ^ 2 =
      liminf (fun F : Finset (Occupation (Fin n)) =>
        ‖∑ u ∈ F, coherentVector β u * z u‖ₑ ^ 2) atTop := by
    intro β
    have h : Tendsto (fun F : Finset (Occupation (Fin n)) =>
        ‖∑ u ∈ F, coherentVector β u * z u‖ₑ ^ 2) atTop (𝓝 (‖S z β‖ₑ ^ 2)) :=
      (((ENNReal.continuous_pow 2).comp continuous_enorm).tendsto _).comp (S_hasSum z β)
    exact h.liminf_eq.symm
  simp_rw [hlim]
  refine (lintegral_liminf_le (fun F => ?_)).trans ?_
  · exact (Finset.measurable_sum _ fun u _ => (coherent_measurable u).mul_const _).enorm.pow_const 2
  · refine liminf_le_of_frequently_le' (Eventually.frequently (Eventually.of_forall fun F => ?_))
    have hb := bessel_fin F (fun u => z u)
    have heq : ∫⁻ β : Fin n ⊕ Fin n → ℝ, ‖∑ u ∈ F, coherentVector β u * z u‖ₑ ^ 2 =
        ENNReal.ofReal (∫ β : Fin n ⊕ Fin n → ℝ, ‖∑ u ∈ F, coherentVector β u * z u‖ ^ 2) := by
      rw [ofReal_integral_eq_lintegral_ofReal hb.1 (ae_of_all _ fun _ => sq_nonneg _)]
      refine lintegral_congr fun β => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [heq, hb.2]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (lp_sum_sq_le z F) (by positivity))

private lemma S_sq_integrable {n : ℕ} (z : Hilbert (Occupation (Fin n))) :
    Integrable (fun β : Fin n ⊕ Fin n → ℝ => ‖S z β‖ ^ 2) ∧
    ∫ β : Fin n ⊕ Fin n → ℝ, ‖S z β‖ ^ 2 ≤ (2 * Real.pi) ^ n * ‖z‖ ^ 2 := by
  have hle := S_sq_lintegral_le z
  have hmeas : Measurable (fun β : Fin n ⊕ Fin n → ℝ => ‖S z β‖ ^ 2) :=
    (S_measurable z).norm.pow_const 2
  have heq : ∫⁻ β : Fin n ⊕ Fin n → ℝ, ENNReal.ofReal (‖S z β‖ ^ 2) =
      ∫⁻ β : Fin n ⊕ Fin n → ℝ, ‖S z β‖ₑ ^ 2 := by
    refine lintegral_congr fun β => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hnn : 0 ≤ᵐ[volume] (fun β : Fin n ⊕ Fin n → ℝ => ‖S z β‖ ^ 2) :=
    ae_of_all _ fun _ => sq_nonneg _
  refine ⟨⟨hmeas.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn, heq]
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable, heq]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle

/-- The Fourier phase `e^{i t·β}`. -/
private def phase {n : ℕ} (t β : Fin n ⊕ Fin n → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((∑ a, t a * β a : ℝ) : ℂ))

private lemma phase_norm {n : ℕ} (t β : Fin n ⊕ Fin n → ℝ) : ‖phase t β‖ = 1 := by
  rw [phase, mul_comm, Complex.norm_exp_ofReal_mul_I]

private lemma phase_zero {n : ℕ} (β : Fin n ⊕ Fin n → ℝ) : phase 0 β = 1 := by
  simp [phase]

private lemma phase_measurable {n : ℕ} (t : Fin n ⊕ Fin n → ℝ) : Measurable (phase t) := by
  unfold phase
  fun_prop

private lemma phS_memLp {n : ℕ} (t : Fin n ⊕ Fin n → ℝ) (z : Hilbert (Occupation (Fin n))) :
    MemLp (fun β : Fin n ⊕ Fin n → ℝ => phase t β * S z β) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm
    ((phase_measurable t).mul (S_measurable z)).aestronglyMeasurable).mpr ?_
  simpa [norm_mul, phase_norm] using (S_sq_integrable z).1

/-! ### The bounded operator with matrix `e^{-|t|²/4} W(t)ᵀ` -/

private lemma S_add {n : ℕ} (z w : Hilbert (Occupation (Fin n))) (β : Fin n ⊕ Fin n → ℝ) :
    S (z + w) β = S z β + S w β := inner_add_right _ _ _

private lemma S_smul {n : ℕ} (a : ℂ) (z : Hilbert (Occupation (Fin n))) (β : Fin n ⊕ Fin n → ℝ) :
    S (a • z) β = a * S z β := inner_smul_right _ _ _

private lemma S_single {n : ℕ} (v : Occupation (Fin n)) (β : Fin n ⊕ Fin n → ℝ) :
    S (lp.single 2 v (1 : ℂ)) β = coherentVector β v := by
  unfold S
  rw [lp.inner_single_right]
  simp [dv_apply]

/-- `z ↦ e^{it·β} S z(β)` as a linear map into `L²(ℝ²ⁿ)`. -/
private def SLlin {n : ℕ} (t : Fin n ⊕ Fin n → ℝ) :
    Hilbert (Occupation (Fin n)) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (Fin n ⊕ Fin n → ℝ)) where
  toFun z := (phS_memLp t z).toLp _
  map_add' z w := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun β => ?_)
    simp [S_add, mul_add]
  map_smul' a z := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun β => ?_)
    simp [S_smul]
    ring

private lemma inner_SLlin {n : ℕ} (s t : Fin n ⊕ Fin n → ℝ) (w z : Hilbert (Occupation (Fin n))) :
    inner ℂ (SLlin s w) (SLlin t z) =
      ∫ β : Fin n ⊕ Fin n → ℝ, star (phase s β * S w β) * (phase t β * S z β) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (phS_memLp s w), MemLp.coeFn_toLp (phS_memLp t z)]
    with β h1 h2
  have e1 : (SLlin s w : (Fin n ⊕ Fin n → ℝ) → ℂ) β = phase s β * S w β := h1
  have e2 : (SLlin t z : (Fin n ⊕ Fin n → ℝ) → ℂ) β = phase t β * S z β := h2
  rw [e1, e2]
  simp [mul_comm]

private lemma SLlin_norm_le {n : ℕ} (t : Fin n ⊕ Fin n → ℝ) (z : Hilbert (Occupation (Fin n))) :
    ‖SLlin t z‖ ≤ Real.sqrt ((2 * Real.pi) ^ n) * ‖z‖ := by
  have h1 : ‖SLlin t z‖ ^ 2 = ∫ β : Fin n ⊕ Fin n → ℝ, ‖S z β‖ ^ 2 := by
    have h := norm_sq_eq_re_inner (𝕜 := ℂ) (SLlin t z)
    rw [h, inner_SLlin]
    have h2 : ∀ β : Fin n ⊕ Fin n → ℝ, star (phase t β * S z β) * (phase t β * S z β) =
        ((‖S z β‖ ^ 2 : ℝ) : ℂ) := by
      intro β
      rw [← starRingEnd_apply, Complex.conj_mul', norm_mul, phase_norm, one_mul]
      push_cast
      rfl
    simp_rw [h2]
    rw [integral_complex_ofReal]
    exact Complex.ofReal_re _
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [h1, mul_pow, Real.sq_sqrt (by positivity)]
  exact (S_sq_integrable z).2

private def SL {n : ℕ} (t : Fin n ⊕ Fin n → ℝ) :
    Hilbert (Occupation (Fin n)) →L[ℂ] Lp ℂ 2 (volume : Measure (Fin n ⊕ Fin n → ℝ)) :=
  (SLlin t).mkContinuous (Real.sqrt ((2 * Real.pi) ^ n)) (fun z => SLlin_norm_le t z)

/-- The operator `(2π)^{-n} S† M_t S`. -/
private def Fop {n : ℕ} (t : Fin n ⊕ Fin n → ℝ) :
    Hilbert (Occupation (Fin n)) →L[ℂ] Hilbert (Occupation (Fin n)) :=
  ((((2 * Real.pi) ^ (-(n : ℝ)) : ℝ)) : ℂ) • ((ContinuousLinearMap.adjoint (SL 0)).comp (SL t))

private lemma inner_Fop {n : ℕ} (t : Fin n ⊕ Fin n → ℝ) (w z : Hilbert (Occupation (Fin n))) :
    inner ℂ w (Fop t z) = ((((2 * Real.pi) ^ (-(n : ℝ)) : ℝ)) : ℂ) *
      ∫ β : Fin n ⊕ Fin n → ℝ, phase t β * (S z β * star (S w β)) := by
  unfold Fop
  rw [FunLike.coe_smul, Pi.smul_apply, inner_smul_right,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  congr 1
  show inner ℂ (SLlin 0 w) (SLlin t z) = _
  rw [inner_SLlin]
  refine integral_congr_ae (ae_of_all _ fun β => ?_)
  simp only [phase_zero, one_mul]
  ring

/-- The interleaved copy of `t`. -/
private def xiOf {n : ℕ} (t : Fin n ⊕ Fin n → ℝ) : Fin n × Fin 2 → ℝ :=
  fun a => if a.2 = 0 then t (Sum.inl a.1) else t (Sum.inr a.1)

private lemma Fop_entry {n : ℕ} (t : Fin n ⊕ Fin n → ℝ) (u v : Occupation (Fin n)) :
    inner ℂ (lp.single 2 u (1 : ℂ) : Hilbert (Occupation (Fin n))) (Fop t (lp.single 2 v (1 : ℂ))) =
      ((Real.exp (-(∑ a, t a ^ 2) / 4) : ℝ) : ℂ) * oscillatorWeylKernel (xiOf t) v u := by
  rw [inner_Fop]
  simp_rw [S_single]
  have h := (coherent_weyl_integral t u v).2
  have h2 : ∫ β : Fin n ⊕ Fin n → ℝ, phase t β * (coherentVector β v * star (coherentVector β u)) =
      (((2 * Real.pi) ^ n * Real.exp (-(∑ a, t a ^ 2) / 4) : ℝ) : ℂ) *
        oscillatorWeylKernel (xiOf t) v u := by
    unfold xiOf
    rw [← h]
    refine integral_congr_ae (ae_of_all _ fun β => ?_)
    simp only [phase]
    ring
  rw [h2, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, inv_mul_cancel_left₀ (by positivity)]

/-- A bounded operator on `ℓ²` acts through its matrix. -/
private lemma clm_apply_hasSum {I : Type} [DecidableEq I] (F : Hilbert I →L[ℂ] Hilbert I)
    (z : Hilbert I) (i : I) :
    HasSum (fun j => inner ℂ (lp.single 2 i (1 : ℂ) : Hilbert I) (F (lp.single 2 j (1 : ℂ))) * z j)
      (F z i) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) (ContinuousLinearMap.adjoint F (lp.single 2 i (1 : ℂ))) z
  rw [ContinuousLinearMap.adjoint_inner_left, lp.inner_single_left] at h
  have e : ∀ j, inner ℂ (lp.single 2 i (1 : ℂ) : Hilbert I) (F (lp.single 2 j (1 : ℂ))) * z j =
      inner ℂ ((ContinuousLinearMap.adjoint F (lp.single 2 i (1 : ℂ)) : Hilbert I) j) (z j) := by
    intro j
    rw [← ContinuousLinearMap.adjoint_inner_left, lp.inner_single_right]
    simp [mul_comm]
  have e2 : inner ℂ (1 : ℂ) (F z i) = F z i := by simp
  rw [e2] at h
  simp_rw [e]
  exact h

/-! ### Nuclear expansions -/

private lemma nuc_hasSum {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) (i j : I) :
    HasSum (fun k => e.left k i * star (e.right k j)) (X i j) := by
  have hsum : Summable (fun k => e.left k i * star (e.right k j)) := by
    refine Summable.of_norm_bounded e.summable fun k => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) _ _)
      (lp.norm_apply_le_norm (by norm_num) _ _) (norm_nonneg _) (norm_nonneg _)
  rw [e.coefficients i j]
  exact hsum.hasSum

/-- Nuclear expansion of the transposed array. -/
private def nucT {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    NuclearExpansion (fun i j => X j i : Matrix I I ℂ) where
  left k := star (e.right k)
  right k := star (e.left k)
  summable := by
    simpa [norm_star, mul_comm] using e.summable
  coefficients i j := by
    rw [e.coefficients j i]
    refine tsum_congr fun k => ?_
    simp [lp.star_apply, mul_comm]

/-- The quadratic form of a nuclear array on a vector of `ℓ²` is the limit of its finite
sections. -/
private lemma nuclear_form_tendsto {I : Type} [DecidableEq I] {X : Matrix I I ℂ}
    (e : NuclearExpansion X) (x : Hilbert I) :
    Tendsto (fun s : Finset I => ∑ i ∈ s, ∑ j ∈ s, star (x i) * X i j * x j) atTop
      (𝓝 (∑' k, inner ℂ x (e.left k) * inner ℂ (e.right k) x)) := by
  let xs : Finset I → Hilbert I := fun s => ∑ i ∈ s, lp.single 2 i (x i)
  have hxs : Tendsto xs atTop (𝓝 x) := lp.hasSum_single (by norm_num) x
  have hin1 : ∀ (s : Finset I) (y : Hilbert I),
      inner ℂ (xs s) y = ∑ i ∈ s, star (x i) * y i := by
    intro s y
    simp only [xs]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lp.inner_single_left]
    simp [mul_comm]
  have hin2 : ∀ (s : Finset I) (y : Hilbert I),
      inner ℂ y (xs s) = ∑ i ∈ s, star (y i) * x i := by
    intro s y
    rw [← inner_conj_symm, hin1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  have key : ∀ s : Finset I, ∑ i ∈ s, ∑ j ∈ s, star (x i) * X i j * x j =
      ∑' k, inner ℂ (xs s) (e.left k) * inner ℂ (e.right k) (xs s) := by
    intro s
    have h1 : ∀ i j, HasSum (fun k => star (x i) * (e.left k i * star (e.right k j)) * x j)
        (star (x i) * X i j * x j) :=
      fun i j => ((nuc_hasSum e i j).mul_left _).mul_right _
    have h2 : HasSum
        (fun k => ∑ i ∈ s, ∑ j ∈ s, star (x i) * (e.left k i * star (e.right k j)) * x j)
        (∑ i ∈ s, ∑ j ∈ s, star (x i) * X i j * x j) :=
      hasSum_sum fun i _ => hasSum_sum fun j _ => h1 i j
    rw [← h2.tsum_eq]
    refine tsum_congr fun k => ?_
    rw [hin1, hin2, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [key]
  have hbd : ∀ᶠ s in atTop, ‖xs s‖ ≤ ‖x‖ + 1 :=
    (hxs.norm.eventually (gt_mem_nhds (lt_add_one ‖x‖))).mono fun s hs => hs.le
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun k => (‖x‖ + 1) ^ 2 * (‖e.left k‖ * ‖e.right k‖)) (e.summable.mul_left _)
    (fun k => ?_) ?_
  · exact (hxs.inner tendsto_const_nhds).mul (tendsto_const_nhds.inner hxs)
  · filter_upwards [hbd] with s hs k
    rw [norm_mul]
    calc ‖inner ℂ (xs s) (e.left k)‖ * ‖inner ℂ (e.right k) (xs s)‖
        ≤ (‖xs s‖ * ‖e.left k‖) * (‖e.right k‖ * ‖xs s‖) :=
          mul_le_mul (norm_inner_le_norm _ _) (norm_inner_le_norm _ _) (norm_nonneg _)
            (by positivity)
      _ ≤ ((‖x‖ + 1) * ‖e.left k‖) * (‖e.right k‖ * (‖x‖ + 1)) := by gcongr
      _ = (‖x‖ + 1) ^ 2 * (‖e.left k‖ * ‖e.right k‖) := by ring

/-! ### The Husimi function through the nuclear expansion -/

private lemma husimi_expansion {n : ℕ} {ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ}
    (e : NuclearExpansion ρ) (β : Fin n ⊕ Fin n → ℝ) :
    Summable (fun k => S ((nucT e).left k) β * star (S ((nucT e).right k) β)) ∧
    ∑' u, ∑' v, star (coherentVector β u) * ρ u v * coherentVector β v =
      ∑' k, S ((nucT e).left k) β * star (S ((nucT e).right k) β) := by
  let F : Hilbert (Occupation (Fin n)) →L[ℂ] Hilbert (Occupation (Fin n)) :=
    (innerSL ℂ (dv β)).smulRight (dv β)
  have hFz : ∀ z, F z = S z β • dv β := fun z => rfl
  have hF : ∀ (z : Hilbert (Occupation (Fin n))) (u : Occupation (Fin n)),
      HasSum (fun v => (star (coherentVector β u) * coherentVector β v) * z v) (F z u) := by
    intro z u
    have h := (S_hasSum z β).mul_left (star (coherentVector β u))
    have e1 : F z u = star (coherentVector β u) * S z β := by
      rw [hFz]
      simp [dv_apply, mul_comm]
    rw [e1]
    simpa [mul_assoc] using h
  obtain ⟨_, _, h3, h4⟩ := effect_trace_pairing
    (fun u v => star (coherentVector β u) * coherentVector β v) F hF (fun i j => ρ j i) (nucT e)
  have e2 : ∀ k, inner ℂ ((nucT e).right k) (F ((nucT e).left k)) =
      S ((nucT e).left k) β * star (S ((nucT e).right k) β) := by
    intro k
    rw [hFz, inner_smul_right]
    congr 1
    unfold S
    rw [← inner_conj_symm]
    rfl
  simp_rw [e2] at h3 h4
  refine ⟨h3, ?_⟩
  rw [← h4]
  refine tsum_congr fun u => tsum_congr fun v => ?_
  ring

private lemma husimi_form_nonneg {n : ℕ} (ρ : State (Occupation (Fin n)))
    (e : NuclearExpansion ρ.coefficients) (β : Fin n ⊕ Fin n → ℝ) :
    (∑' k, S ((nucT e).left k) β * star (S ((nucT e).right k) β)).im = 0 ∧
    0 ≤ (∑' k, S ((nucT e).left k) β * star (S ((nucT e).right k) β)).re := by
  have h : Tendsto (fun s : Finset (Occupation (Fin n)) =>
      ∑ i ∈ s, ∑ j ∈ s, star (dv β i) * ρ.coefficients j i * dv β j) atTop
      (𝓝 (∑' k, inner ℂ (dv β) ((nucT e).left k) * inner ℂ ((nucT e).right k) (dv β))) :=
    nuclear_form_tendsto (nucT e) (dv β)
  have hform : ∀ s : Finset (Occupation (Fin n)),
      ∑ i ∈ s, ∑ j ∈ s, star (dv β i) * ρ.coefficients j i * dv β j =
      ∑ i ∈ s, ∑ j ∈ s, star (coherentVector β i) * ρ.coefficients i j * coherentVector β j := by
    intro s
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [dv_apply, star_star]
    ring
  have hlim : (∑' k, inner ℂ (dv β) ((nucT e).left k) * inner ℂ ((nucT e).right k) (dv β)) =
      ∑' k, S ((nucT e).left k) β * star (S ((nucT e).right k) β) := by
    refine tsum_congr fun k => ?_
    unfold S
    rw [← inner_conj_symm ((nucT e).right k)]
    rfl
  simp_rw [hform] at h
  rw [hlim] at h
  have hq := fun s => ρ.density.2.1 s (coherentVector β)
  refine ⟨?_, ?_⟩
  · have h1 := (Complex.continuous_im.tendsto _).comp h
    refine tendsto_nhds_unique h1 ?_
    have h0 : (Complex.im ∘ fun s : Finset (Occupation (Fin n)) =>
        ∑ i ∈ s, ∑ j ∈ s, star (coherentVector β i) * ρ.coefficients i j * coherentVector β j) =
        fun _ => 0 := funext fun s => (hq s).1
    rw [h0]
    exact tendsto_const_nhds
  · have h1 := (Complex.continuous_re.tendsto _).comp h
    exact ge_of_tendsto' h1 fun s => (hq s).2

/-! ### Integrability of the terms and of the series -/

private lemma S_memLp {n : ℕ} (z : Hilbert (Occupation (Fin n))) :
    MemLp (S z) 2 (volume : Measure (Fin n ⊕ Fin n → ℝ)) :=
  (memLp_two_iff_integrable_sq_norm (S_measurable z).aestronglyMeasurable).mpr
    (S_sq_integrable z).1

private lemma term_measurable {n : ℕ} (t : Fin n ⊕ Fin n → ℝ)
    (z w : Hilbert (Occupation (Fin n))) :
    Measurable (fun β : Fin n ⊕ Fin n → ℝ => phase t β * (S z β * star (S w β))) :=
  (phase_measurable t).mul ((S_measurable z).mul (continuous_star.measurable.comp (S_measurable w)))

private lemma term_norm {n : ℕ} (t : Fin n ⊕ Fin n → ℝ) (z w : Hilbert (Occupation (Fin n)))
    (β : Fin n ⊕ Fin n → ℝ) :
    ‖phase t β * (S z β * star (S w β))‖ = ‖S z β‖ * ‖S w β‖ := by
  rw [norm_mul, phase_norm, one_mul, norm_mul, norm_star]

private lemma term_integrable {n : ℕ} (t : Fin n ⊕ Fin n → ℝ)
    (z w : Hilbert (Occupation (Fin n))) :
    Integrable (fun β : Fin n ⊕ Fin n → ℝ => phase t β * (S z β * star (S w β))) := by
  refine Integrable.mono' ((S_sq_integrable z).1.add (S_sq_integrable w).1)
    (term_measurable t z w).aestronglyMeasurable (ae_of_all _ fun β => ?_)
  rw [term_norm]
  show _ ≤ ‖S z β‖ ^ 2 + ‖S w β‖ ^ 2
  nlinarith [sq_nonneg (‖S z β‖ - ‖S w β‖), norm_nonneg (S z β), norm_nonneg (S w β)]

private lemma term_norm_integral_le {n : ℕ} (t : Fin n ⊕ Fin n → ℝ)
    (z w : Hilbert (Occupation (Fin n))) :
    ∫ β : Fin n ⊕ Fin n → ℝ, ‖phase t β * (S z β * star (S w β))‖ ≤
      (2 * Real.pi) ^ n * (‖z‖ * ‖w‖) := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := (volume : Measure (Fin n ⊕ Fin n → ℝ)))
    Real.HolderConjugate.two_two (f := S z) (g := S w)
    (by simpa using S_memLp z) (by simpa using S_memLp w)
  simp_rw [term_norm]
  refine h.trans ?_
  have hz := (S_sq_integrable z).2
  have hw := (S_sq_integrable w).2
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have hc : (0 : ℝ) ≤ (2 * Real.pi) ^ n := by positivity
  calc √(∫ β : Fin n ⊕ Fin n → ℝ, ‖S z β‖ ^ 2) * √(∫ β : Fin n ⊕ Fin n → ℝ, ‖S w β‖ ^ 2)
      ≤ √((2 * Real.pi) ^ n * ‖z‖ ^ 2) * √((2 * Real.pi) ^ n * ‖w‖ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt hz) (Real.sqrt_le_sqrt hw) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = (2 * Real.pi) ^ n * (‖z‖ * ‖w‖) := by
        rw [Real.sqrt_mul hc, Real.sqrt_mul hc, Real.sqrt_sq (norm_nonneg _),
          Real.sqrt_sq (norm_nonneg _)]
        have := Real.mul_self_sqrt hc
        calc √((2 * Real.pi) ^ n) * ‖z‖ * (√((2 * Real.pi) ^ n) * ‖w‖)
            = (√((2 * Real.pi) ^ n) * √((2 * Real.pi) ^ n)) * (‖z‖ * ‖w‖) := by ring
          _ = (2 * Real.pi) ^ n * (‖z‖ * ‖w‖) := by rw [this]

private lemma series_measurable {α : Type} [MeasurableSpace α] {F : ℕ → α → ℂ}
    (hmeas : ∀ k, Measurable (F k)) (hsum : ∀ a, Summable (fun k => F k a)) :
    Measurable (fun a => ∑' k, F k a) := by
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset ℕ))
    (f := fun s a => ∑ k ∈ s, F k a) (fun s => Finset.measurable_sum _ fun k _ => hmeas k) ?_
  rw [tendsto_pi_nhds]
  exact fun a => (hsum a).hasSum

private lemma series_integrable {α : Type} [MeasurableSpace α] {μ : Measure α} {F : ℕ → α → ℂ}
    (hmeas : ∀ k, Measurable (F k)) (hsum : ∀ a, Summable (fun k => F k a))
    (hF_int : ∀ k, Integrable (F k) μ) (hF_sum : Summable fun k => ∫ a, ‖F k a‖ ∂μ) :
    Integrable (fun a => ∑' k, F k a) μ := by
  refine ⟨(series_measurable hmeas hsum).aestronglyMeasurable, ?_⟩
  have h3 : ∀ k, ∫⁻ a, ‖F k a‖ₑ ∂μ = ENNReal.ofReal (∫ a, ‖F k a‖ ∂μ) := fun k => by
    rw [ofReal_integral_eq_lintegral_ofReal (hF_int k).norm (ae_of_all _ fun _ => norm_nonneg _)]
    refine lintegral_congr fun a => ?_
    rw [ofReal_norm]
  show ∫⁻ a, ‖∑' k, F k a‖ₑ ∂μ < ∞
  calc ∫⁻ a, ‖∑' k, F k a‖ₑ ∂μ ≤ ∫⁻ a, ∑' k, ‖F k a‖ₑ ∂μ :=
        lintegral_mono fun a => enorm_tsum_le_tsum_enorm
    _ = ∑' k, ∫⁻ a, ‖F k a‖ₑ ∂μ := lintegral_tsum fun k => (hmeas k).enorm.aemeasurable
    _ = ∑' k, ENNReal.ofReal (∫ a, ‖F k a‖ ∂μ) := by simp_rw [h3]
    _ < ∞ := hF_sum.tsum_ofReal_lt_top

/-! ### The characteristic function through the nuclear expansion -/

private lemma char_pairing {n : ℕ} {ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ}
    (e : NuclearExpansion ρ) (t : Fin n ⊕ Fin n → ℝ) :
    (∀ u, Summable fun v => ρ u v * oscillatorWeylKernel (xiOf t) v u) ∧
    Summable (fun u => ∑' v, ρ u v * oscillatorWeylKernel (xiOf t) v u) ∧
    ((Real.exp (-(∑ a, t a ^ 2) / 4) : ℝ) : ℂ) *
        ∑' u, ∑' v, ρ u v * oscillatorWeylKernel (xiOf t) v u =
      ∑' k, inner ℂ ((nucT e).right k) (Fop t ((nucT e).left k)) := by
  set a : ℂ := ((Real.exp (-(∑ a, t a ^ 2) / 4) : ℝ) : ℂ) with ha
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact_mod_cast (Real.exp_pos _).ne'
  have hF : ∀ (z : Hilbert (Occupation (Fin n))) (u : Occupation (Fin n)),
      HasSum (fun v => (a * oscillatorWeylKernel (xiOf t) v u) * z v) (Fop t z u) := by
    intro z u
    have h := clm_apply_hasSum (Fop t) z u
    simp_rw [Fop_entry] at h
    exact h
  obtain ⟨h1, h2, _, h4⟩ := effect_trace_pairing
    (fun u v => a * oscillatorWeylKernel (xiOf t) v u) (Fop t) hF (fun i j => ρ j i) (nucT e)
  have e1 : ∀ u v, a * oscillatorWeylKernel (xiOf t) v u * ρ u v =
      a * (ρ u v * oscillatorWeylKernel (xiOf t) v u) := fun u v => by ring
  have e2 : ∀ u, ∑' v, a * (ρ u v * oscillatorWeylKernel (xiOf t) v u) =
      a * ∑' v, ρ u v * oscillatorWeylKernel (xiOf t) v u := fun u => tsum_mul_left
  simp only [e1] at h1 h2 h4
  simp only [e2] at h2 h4
  rw [tsum_mul_left] at h4
  exact ⟨fun u => (summable_mul_left_iff ha0).mp (h1 u), (summable_mul_left_iff ha0).mp h2, h4⟩

/-! ### The theorem -/

theorem solution {n : ℕ} (ρ : State (Occupation (Fin n))) :
    OscillatorCharacteristicSummable ρ.coefficients ∧
    (∀ β : Fin n ⊕ Fin n → ℝ, 0 ≤ husimiQ ρ.coefficients β) ∧
    Measurable (husimiQ ρ.coefficients) ∧
    Integrable (husimiQ ρ.coefficients) ∧
    ∀ t : Fin n ⊕ Fin n → ℝ,
      ∫ β : Fin n ⊕ Fin n → ℝ, Complex.exp (Complex.I * ((∑ a, t a * β a : ℝ) : ℂ)) *
          ((husimiQ ρ.coefficients β : ℝ) : ℂ) =
        ((Real.exp (-(∑ a, t a ^ 2) / 4) : ℝ) : ℂ) *
          oscillatorCharacteristic ρ.coefficients
            (fun a : Fin n × Fin 2 => if a.2 = 0 then t (Sum.inl a.1) else t (Sum.inr a.1)) := by
  obtain ⟨e⟩ := ρ.density.1
  have hGsum : ∀ β : Fin n ⊕ Fin n → ℝ,
      Summable (fun k => S ((nucT e).left k) β * star (S ((nucT e).right k) β)) :=
    fun β => (husimi_expansion e β).1
  have hQ : ∀ β : Fin n ⊕ Fin n → ℝ, husimiQ ρ.coefficients β =
      (2 * Real.pi) ^ (-(n : ℝ)) *
        (∑' k, S ((nucT e).left k) β * star (S ((nucT e).right k) β)).re := by
    intro β
    unfold husimiQ
    rw [(husimi_expansion e β).2]
  have hQfun : husimiQ ρ.coefficients = fun β : Fin n ⊕ Fin n → ℝ =>
      (2 * Real.pi) ^ (-(n : ℝ)) *
        (∑' k, S ((nucT e).left k) β * star (S ((nucT e).right k) β)).re := funext hQ
  have hpos := fun β : Fin n ⊕ Fin n → ℝ => husimi_form_nonneg ρ e β
  have hsumI : ∀ t : Fin n ⊕ Fin n → ℝ, Summable fun k =>
      ∫ β : Fin n ⊕ Fin n → ℝ,
        ‖phase t β * (S ((nucT e).left k) β * star (S ((nucT e).right k) β))‖ := by
    intro t
    exact Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _)
      (fun k => term_norm_integral_le t _ _) ((nucT e).summable.mul_left _)
  have h0 : ∀ k, (fun β : Fin n ⊕ Fin n → ℝ =>
      phase 0 β * (S ((nucT e).left k) β * star (S ((nucT e).right k) β))) =
      fun β => S ((nucT e).left k) β * star (S ((nucT e).right k) β) :=
    fun k => funext fun β => by rw [phase_zero, one_mul]
  have hmeasT : ∀ k, Measurable (fun β : Fin n ⊕ Fin n → ℝ =>
      S ((nucT e).left k) β * star (S ((nucT e).right k) β)) := fun k => by
    rw [← h0 k]
    exact term_measurable 0 _ _
  have hGmeas : Measurable (fun β : Fin n ⊕ Fin n → ℝ =>
      ∑' k, S ((nucT e).left k) β * star (S ((nucT e).right k) β)) :=
    series_measurable hmeasT hGsum
  have hGint : Integrable (fun β : Fin n ⊕ Fin n → ℝ =>
      ∑' k, S ((nucT e).left k) β * star (S ((nucT e).right k) β)) := by
    refine series_integrable hmeasT hGsum (fun k => ?_) ?_
    · rw [← h0 k]
      exact term_integrable 0 _ _
    · have h := hsumI 0
      simp_rw [phase_zero, one_mul] at h
      exact h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ξ
    have hξ : xiOf (Sum.elim (fun j => ξ (j, 0)) (fun j => ξ (j, 1))) = ξ := by
      funext ⟨j, b⟩
      fin_cases b <;> simp [xiOf]
    obtain ⟨h1, h2, _⟩ := char_pairing e (Sum.elim (fun j => ξ (j, 0)) (fun j => ξ (j, 1)))
    rw [hξ] at h1 h2
    exact ⟨h1, h2⟩
  · intro β
    rw [hQ]
    exact mul_nonneg (by positivity) (hpos β).2
  · rw [hQfun]
    exact (Complex.measurable_re.comp hGmeas).const_mul _
  · rw [hQfun]
    exact hGint.re.const_mul _
  · intro t
    have hptw : ∀ β : Fin n ⊕ Fin n → ℝ,
        Complex.exp (Complex.I * ((∑ a, t a * β a : ℝ) : ℂ)) *
          ((husimiQ ρ.coefficients β : ℝ) : ℂ) =
        (((2 * Real.pi) ^ (-(n : ℝ)) : ℝ) : ℂ) *
          ∑' k, phase t β * (S ((nucT e).left k) β * star (S ((nucT e).right k) β)) := by
      intro β
      have hre : (((∑' k, S ((nucT e).left k) β * star (S ((nucT e).right k) β)).re : ℝ) : ℂ) =
          ∑' k, S ((nucT e).left k) β * star (S ((nucT e).right k) β) :=
        Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im]; exact (hpos β).1.symm)
      rw [hQ, Complex.ofReal_mul, hre, tsum_mul_left]
      show phase t β * _ = _
      ring
    simp_rw [hptw]
    rw [integral_const_mul, ← integral_tsum_of_summable_integral_norm
      (fun k => term_integrable t _ _) (hsumI t), ← tsum_mul_left]
    simp_rw [← inner_Fop]
    rw [← (char_pairing e t).2.2]
    rfl

end
