-- Prove2me | solution 1 for BosonicLearn.fugacity_renyi2_tensorPow
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-14T02:16:23.926988+00:00
-- url     : https://prove2.me/submissions/be3ac0ae-f872-494d-907b-b2ad6b2d3efd

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Theorems.Thm_BosonicLearn_gammaFock_basic
import Theorems.Thm_BosonicLearn_gammaFock_mul
import Theorems.Thm_BosonicLearn_gammaFock_trace_psd
import Theorems.Thm_BosonicLearn_fugacityCoeff_isDensity
import Theorems.Thm_BosonicLearn_isDensity_prod
import Theorems.Thm_BosonicLearn_isDensity_reindex
import Theorems.Thm_BosonicLearn_isDensity_of_posSemidef

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

open BosonicLearn

noncomputable section

/-! ### Generic facts on sums over product index sets -/

/-- A finite product of nonnegative convergent series is the series over `Jᴺ` of the products. -/
private lemma hasSum_pi_prod_of_nonneg {J : Type} (N : ℕ) : ∀ (f : Fin N → J → ℝ) (a : Fin N → ℝ),
    (∀ i k, 0 ≤ f i k) → (∀ i, HasSum (f i) (a i)) →
    HasSum (fun u : Fin N → J => ∏ i, f i (u i)) (∏ i, a i) := by
  induction N with
  | zero =>
    intro f a _ _
    simp
  | succ N ih =>
    intro f a hf0 hf
    have ih' := ih (fun i => f i.succ) (fun i => a i.succ)
      (fun i k => hf0 i.succ k) (fun i => hf i.succ)
    have hsum : Summable (fun p : J × (Fin N → J) => f 0 p.1 * ∏ i : Fin N, f i.succ (p.2 i)) :=
      Summable.mul_of_nonneg (f := f 0) (g := fun u : Fin N → J => ∏ i : Fin N, f i.succ (u i))
        (hf 0).summable ih'.summable (fun k => hf0 0 k)
        (fun u => Finset.prod_nonneg fun i _ => hf0 i.succ (u i))
    have hmul : HasSum (fun p : J × (Fin N → J) => f 0 p.1 * ∏ i : Fin N, f i.succ (p.2 i))
        (a 0 * ∏ i : Fin N, a i.succ) :=
      HasSum.mul (f := f 0) (g := fun u : Fin N → J => ∏ i : Fin N, f i.succ (u i)) (hf 0) ih' hsum
    rw [Fin.prod_univ_succ]
    rw [← (Fin.consEquiv fun _ : Fin (N + 1) => J).hasSum_iff]
    refine hmul.congr_fun fun p => ?_
    simp [Fin.prod_univ_succ, Fin.consEquiv]

/-- `N` independent copies of a nonnegative convergent series. -/
private lemma hasSum_pi_pow_of_nonneg {J : Type} (N : ℕ) (f : J → ℝ) (a : ℝ) (hf0 : ∀ k, 0 ≤ f k)
    (hf : HasSum f a) : HasSum (fun u : Fin N → J => ∏ t, f (u t)) (a ^ N) := by
  have h := hasSum_pi_prod_of_nonneg N (fun _ => f) (fun _ => a) (fun _ => hf0) (fun _ => hf)
  simpa using h

/-- A nonnegative double series with convergent rows and convergent row sums. -/
private lemma hasSum_prod_of_nonneg {α β : Type} (f : α × β → ℝ) (g : α → ℝ) (a : ℝ)
    (hf0 : ∀ p, 0 ≤ f p) (hrow : ∀ x, HasSum (fun y => f (x, y)) (g x)) (hg : HasSum g a) :
    HasSum f a := by
  have hsum : Summable f := by
    rw [summable_prod_of_nonneg hf0]
    refine ⟨fun x => (hrow x).summable, ?_⟩
    have : (fun x => ∑' y, f (x, y)) = g := funext fun x => (hrow x).tsum_eq
    rw [this]
    exact hg.summable
  have h1 := hsum.hasSum.prod_fiberwise hrow
  rw [← h1.unique hg]
  exact hsum.hasSum

/-- `N` independent copies of a nonnegative double series, indexed by pairs of sequences. -/
private lemma hasSum_pair_pow {J : Type} (N : ℕ) (f : J × J → ℝ) (a : ℝ) (hf0 : ∀ k, 0 ≤ f k)
    (hf : HasSum f a) :
    HasSum (fun x : (Fin N → J) × (Fin N → J) => ∏ t, f (x.1 t, x.2 t)) (a ^ N) := by
  have h := hasSum_pi_pow_of_nonneg N f a hf0 hf
  rw [← (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => J) (fun _ => J)).symm.hasSum_iff] at h
  exact h

/-! ### Density of tensor powers -/

private lemma tensorPow_apply {a : Type} (N : ℕ) (M : Matrix a a ℂ) (x y : Fin N → a) :
    WildeQIT.Schumacher.tensorPow N M x y = ∏ i, M (x i) (y i) := rfl

private lemma isDensity_tensorPow_zero {a : Type} (M : Matrix a a ℂ) :
    IsDensity (WildeQIT.Schumacher.tensorPow 0 M) := by
  have hX : ∀ x y : Fin 0 → a, WildeQIT.Schumacher.tensorPow 0 M x y = 1 := by
    intro x y
    rw [tensorPow_apply]
    simp
  refine isDensity_of_posSemidef _ ?_ ?_ ?_
  · intro s z
    have h : ∑ i ∈ s, ∑ j ∈ s, star (z i) * WildeQIT.Schumacher.tensorPow 0 M i j * z j =
        star (∑ i ∈ s, z i) * ∑ i ∈ s, z i := by
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hX, mul_one]
    rw [h]
    have h2 : star (∑ i ∈ s, z i) * ∑ i ∈ s, z i = ((Complex.normSq (∑ i ∈ s, z i) : ℝ) : ℂ) := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj]
    rw [h2]
    exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact Complex.normSq_nonneg _⟩
  · exact (hasSum_fintype _).summable
  · rw [tsum_fintype]
    simp [hX]

private lemma isDensity_tensorPow {a : Type} (M : Matrix a a ℂ) (hM : IsDensity M) (N : ℕ) :
    IsDensity (WildeQIT.Schumacher.tensorPow N M) := by
  induction N with
  | zero => exact isDensity_tensorPow_zero M
  | succ N ih =>
    have h := isDensity_reindex (Fin.consEquiv fun _ : Fin (N + 1) => a) (isDensity_prod hM ih)
    have heq : (fun i j : Fin (N + 1) → a =>
        (fun p q : a × (Fin N → a) => M p.1 q.1 * WildeQIT.Schumacher.tensorPow N M p.2 q.2)
          ((Fin.consEquiv fun _ : Fin (N + 1) => a).symm i)
          ((Fin.consEquiv fun _ : Fin (N + 1) => a).symm j)) =
        WildeQIT.Schumacher.tensorPow (N + 1) M := by
      funext x y
      simp [tensorPow_apply, Fin.prod_univ_succ, Fin.consEquiv, Fin.tail]
    rw [heq] at h
    exact h

/-! ### One copy -/

/-- The photon-number sector `N`: occupation vectors of total `N`. -/
private def sec (n N : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (N + 1)).filter (fun w => ∑ i, w i = N)

private lemma mem_sec {n N : ℕ} (w : Fin n → ℕ) : w ∈ sec n N ↔ ∑ i, w i = N := by
  unfold sec
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun k => ?_, h⟩⟩
  rw [Finset.mem_range, ← h]
  have h2 : w k ≤ ∑ i, w i :=
    Finset.single_le_sum (f := fun i => w i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  omega

private lemma gammaFock_mul_sec {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    gammaFock (A * B) u v = ∑ w ∈ sec n (∑ i, u i), gammaFock A u w * gammaFock B w v :=
  gammaFock_mul A B u v

private lemma gammaFock_herm {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (hS : Sᴴ = S)
    (u v : Fin n → ℕ) : gammaFock S u v = star (gammaFock S v u) := by
  have h := (gammaFock_basic S u v).2.1
  rwa [hS] at h

/-- Homogeneity: `Γ(cR)` is `c^m Γ(R)` on the `m`-photon sector. -/
private lemma gammaFock_smul {n : ℕ} (c : ℂ) (R : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    gammaFock (c • R) u v = c ^ (∑ i, u i) * gammaFock R u v := by
  have hterm : ∀ M ∈ (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin n =>
        Finset.range (u i + 1)).filter (fun M => (∀ i, ∑ j, M i j = u i) ∧ ∀ j, ∑ i, M i j = v j),
      ∏ i, ∏ j, (c • R) i j ^ (M i j) / (Nat.factorial (M i j) : ℂ) =
        c ^ (∑ i, u i) * ∏ i, ∏ j, R i j ^ (M i j) / (Nat.factorial (M i j) : ℂ) := by
    intro M hM
    rw [Finset.mem_filter] at hM
    have hrow := hM.2.1
    have h1 : ∀ i j, (c • R) i j ^ M i j / (Nat.factorial (M i j) : ℂ) =
        c ^ M i j * (R i j ^ M i j / (Nat.factorial (M i j) : ℂ)) := by
      intro i j
      rw [Matrix.smul_apply, smul_eq_mul, mul_pow, mul_div_assoc]
    simp only [h1, Finset.prod_mul_distrib]
    congr 1
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_pow_eq_pow_sum, hrow i]
  unfold gammaFock
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, mul_left_comm]

private lemma norm_sq_of_im_zero (d : ℂ) (hd : d.im = 0) : ‖d‖ ^ 2 = d.re ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, hd]
  ring

private lemma inv_re_of_im_zero (d : ℂ) (hd : d.im = 0) : (d⁻¹).re = (d.re)⁻¹ := by
  rw [Complex.inv_re, Complex.normSq_apply, hd, mul_zero, add_zero]
  by_cases h : d.re = 0
  · simp [h]
  · field_simp

private lemma fugacityCoeff_apply {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    fugacityCoeff R u v = (1 - R).det * gammaFock R u v := rfl

/-- The one-copy summand in terms of `Γ(r₀⁻¹R)` and `Γ(R)`. -/
private lemma one_copy_term {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hRH : Rᴴ = R)
    (hdim : (1 - R).det.im = 0) (r₀ : ℝ) (h0 : 0 < r₀) (h1 : r₀ < 1) (u v : Fin n → ℕ) :
    ‖fugacityCoeff R u v‖ ^ 2 /
        Real.sqrt (((1 - r₀) ^ n * r₀ ^ (∑ i, u i)) * ((1 - r₀) ^ n * r₀ ^ (∑ i, v i))) =
      (1 - R).det.re ^ 2 / (1 - r₀) ^ n *
        (gammaFock (((r₀⁻¹ : ℝ) : ℂ) • R) u v * gammaFock R v u).re := by
  have h1r : 0 < 1 - r₀ := by linarith
  by_cases huv : ∑ i, u i = ∑ i, v i
  · have hsqrt : Real.sqrt (((1 - r₀) ^ n * r₀ ^ (∑ i, u i)) * ((1 - r₀) ^ n * r₀ ^ (∑ i, v i))) =
        (1 - r₀) ^ n * r₀ ^ (∑ i, u i) := by
      rw [← huv]
      exact Real.sqrt_mul_self (by positivity)
    rw [hsqrt, gammaFock_smul, gammaFock_herm R hRH v u, fugacityCoeff_apply, norm_mul, mul_pow,
      norm_sq_of_im_zero _ hdim]
    have hre : (((r₀⁻¹ : ℝ) : ℂ) ^ (∑ i, u i) * gammaFock R u v * star (gammaFock R u v)).re =
        (r₀⁻¹) ^ (∑ i, u i) * ‖gammaFock R u v‖ ^ 2 := by
      rw [mul_assoc, Complex.star_def, Complex.mul_conj, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
        Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hre, inv_pow]
    field_simp
  · have hz1 : gammaFock R u v = 0 := (gammaFock_basic R u v).1 huv
    have hz2 : gammaFock (((r₀⁻¹ : ℝ) : ℂ) • R) u v = 0 := (gammaFock_basic _ u v).1 huv
    rw [fugacityCoeff_apply, hz1, hz2]
    simp

/-- Summing the one-copy summand over the second index. -/
private lemma one_copy_row {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (K : ℝ) (u : Fin n → ℕ) :
    HasSum (fun v : Fin n → ℕ => K * (gammaFock (c • R) u v * gammaFock R v u).re)
      (K * (gammaFock (c • (R * R)) u u).re) := by
  have hmul : gammaFock (c • (R * R)) u u =
      ∑ v ∈ sec n (∑ i, u i), gammaFock (c • R) u v * gammaFock R v u := by
    rw [← Matrix.smul_mul, gammaFock_mul_sec]
  rw [hmul, Complex.re_sum, Finset.mul_sum]
  refine hasSum_sum_of_ne_finset_zero fun v hv => ?_
  have hne : ∑ i, u i ≠ ∑ i, v i := fun h => hv ((mem_sec v).mpr h.symm)
  rw [(gammaFock_basic (c • R) u v).1 hne]
  simp

private lemma scaled_sq_facts {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef) (r₀ : ℝ)
    (h0 : 0 < r₀)
    (hR2 : (((r₀ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R * R).PosDef) :
    (((r₀⁻¹ : ℝ) : ℂ) • (R * R)).PosSemidef ∧ (1 - ((r₀⁻¹ : ℝ) : ℂ) • (R * R)).PosDef := by
  have hc : (0 : ℂ) < ((r₀⁻¹ : ℝ) : ℂ) := Complex.zero_lt_real.mpr (inv_pos.mpr h0)
  constructor
  · have h : (R * R).PosSemidef := by
      have := Matrix.posSemidef_conjTranspose_mul_self R
      rwa [hR.1.eq] at this
    exact h.smul hc.le
  · have h : (1 : Matrix (Fin n) (Fin n) ℂ) - ((r₀⁻¹ : ℝ) : ℂ) • (R * R) =
        ((r₀⁻¹ : ℝ) : ℂ) • (((r₀ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R * R) := by
      rw [smul_sub, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ h0.ne', Complex.ofReal_one,
        one_smul]
    rw [h]
    exact hR2.smul hc

/-- The one-copy Rényi-2 overlap. -/
private lemma one_copy_hasSum {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) (r₀ : ℝ) (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hR2 : (((r₀ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R * R).PosDef) :
    0 < (1 - ((r₀⁻¹ : ℝ) : ℂ) • (R * R)).det.re ∧
    HasSum (fun p : (Fin n → ℕ) × (Fin n → ℕ) =>
        ‖fugacityCoeff R p.1 p.2‖ ^ 2 /
          Real.sqrt (((1 - r₀) ^ n * r₀ ^ (∑ i, p.1 i)) * ((1 - r₀) ^ n * r₀ ^ (∑ i, p.2 i))))
      ((1 - R).det.re ^ 2 / ((1 - r₀) ^ n * (1 - ((r₀⁻¹ : ℝ) : ℂ) • (R * R)).det.re)) := by
  obtain ⟨hpsd, hpd⟩ := scaled_sq_facts R hR r₀ h0 hR2
  obtain ⟨hDpos, hDim, hDsum⟩ := gammaFock_trace_psd _ hpsd hpd
  obtain ⟨hdpos, hdim, -⟩ := gammaFock_trace_psd R hR hR1
  have h1r : 0 < 1 - r₀ := by linarith
  refine ⟨hDpos, ?_⟩
  refine hasSum_prod_of_nonneg _ (fun u => (1 - R).det.re ^ 2 / (1 - r₀) ^ n *
    (gammaFock (((r₀⁻¹ : ℝ) : ℂ) • (R * R)) u u).re) _ (fun p => by positivity) (fun u => ?_) ?_
  · have h := one_copy_row R ((r₀⁻¹ : ℝ) : ℂ) ((1 - R).det.re ^ 2 / (1 - r₀) ^ n) u
    refine h.congr_fun fun v => ?_
    exact one_copy_term R hR.1.eq hdim r₀ h0 h1 u v
  · have h := (Complex.hasSum_re hDsum).mul_left ((1 - R).det.re ^ 2 / (1 - r₀) ^ n)
    have hval : (1 - R).det.re ^ 2 / (1 - r₀) ^ n * ((1 - ((r₀⁻¹ : ℝ) : ℂ) • (R * R)).det)⁻¹.re =
        (1 - R).det.re ^ 2 / ((1 - r₀) ^ n * (1 - ((r₀⁻¹ : ℝ) : ℂ) • (R * R)).det.re) := by
      rw [inv_re_of_im_zero _ hDim]
      field_simp
    rw [← hval]
    exact h

/-- The thermal weights `p₀(u) = (1 - r₀)ⁿ r₀^{|u|}` sum to one. -/
private lemma thermal_hasSum (n : ℕ) (r₀ : ℝ) (h0 : 0 < r₀) (h1 : r₀ < 1) :
    HasSum (fun u : Fin n → ℕ => (1 - r₀) ^ n * r₀ ^ (∑ i, u i)) 1 := by
  have h1r : 0 < 1 - r₀ := by linarith
  have hgeo : HasSum (fun k : ℕ => (1 - r₀) * r₀ ^ k) 1 := by
    have h := (hasSum_geometric_of_lt_one h0.le h1).mul_left (1 - r₀)
    rwa [mul_inv_cancel₀ h1r.ne'] at h
  have h := hasSum_pi_prod_of_nonneg n (fun _ k => (1 - r₀) * r₀ ^ k) (fun _ => 1)
    (fun _ k => by positivity) (fun _ => hgeo)
  simp only [Finset.prod_const_one] at h
  refine h.congr_fun fun u => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum]

theorem solution {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) (r₀ : ℝ) (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hR2 : (((r₀ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R * R).PosDef) (N : ℕ) :
    IsDensity (WildeQIT.Schumacher.tensorPow N (fugacityCoeff R)) ∧
    HasSum (fun x : Fin N → Occupation (Fin n) => ∏ t, ((1 - r₀) ^ n * r₀ ^ (∑ i, x t i))) 1 ∧
    0 < (1 - ((r₀⁻¹ : ℝ) : ℂ) • (R * R)).det.re ∧
    HasSum (fun x : (Fin N → Occupation (Fin n)) × (Fin N → Occupation (Fin n)) =>
        ‖WildeQIT.Schumacher.tensorPow N (fugacityCoeff R) x.1 x.2‖ ^ 2 /
          Real.sqrt ((∏ t, ((1 - r₀) ^ n * r₀ ^ (∑ i, x.1 t i))) *
            ∏ t, ((1 - r₀) ^ n * r₀ ^ (∑ i, x.2 t i))))
      (((1 - R).det.re ^ 2 /
        ((1 - r₀) ^ n * (1 - ((r₀⁻¹ : ℝ) : ℂ) • (R * R)).det.re)) ^ N) := by
  obtain ⟨hDpos, hone⟩ := one_copy_hasSum R hR hR1 r₀ h0 h1 hR2
  have h1r : 0 < 1 - r₀ := by linarith
  refine ⟨isDensity_tensorPow _ (fugacityCoeff_isDensity R hR hR1) N, ?_, hDpos, ?_⟩
  · have h := hasSum_pi_pow_of_nonneg N _ 1 (fun u => by positivity) (thermal_hasSum n r₀ h0 h1)
    simpa using h
  · have h := hasSum_pair_pow N _ _ (fun p => by positivity) hone
    refine h.congr_fun fun x => ?_
    rw [tensorPow_apply, norm_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
      Real.sqrt_prod _ (fun t _ => by positivity), Finset.prod_div_distrib]
