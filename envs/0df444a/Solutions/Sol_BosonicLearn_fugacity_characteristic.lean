-- Prove2me | solution 1 for BosonicLearn.fugacity_characteristic
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T19:45:00.549721+00:00
-- url     : https://prove2.me/submissions/d61f7ab6-8ac1-420b-ae9e-ad296f56d657

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Theorems.Thm_BosonicLearn_gammaFock_basic
import Theorems.Thm_BosonicLearn_gammaFock_mul
import Theorems.Thm_BosonicLearn_gammaFock_weyl
import Theorems.Thm_BosonicLearn_displacementMatrix_unitary
import Theorems.Thm_BosonicLearn_thermal_characteristic

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (oscillatorCharacteristic
  OscillatorCharacteristicSummable oscillatorWeylKernel)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open scoped Matrix ComplexOrder

open BosonicLearn

noncomputable section

/-! ### `Γ` of a diagonal matrix -/

/-- The index set of `gammaFock`: matrices `M ∈ ℕ^{n×n}` with row sums `u` and column sums `v`. -/
private def gS {n : ℕ} (u v : Fin n → ℕ) : Finset (Fin n → Fin n → ℕ) :=
  (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin n => Finset.range (u i + 1)).filter
    (fun M => (∀ i, ∑ j, M i j = u i) ∧ ∀ j, ∑ i, M i j = v j)

/-- The box constraint is automatic. -/
private lemma mem_gS {n : ℕ} (u v : Fin n → ℕ) (M : Fin n → Fin n → ℕ) :
    M ∈ gS u v ↔ (∀ i, ∑ j, M i j = u i) ∧ ∀ j, ∑ i, M i j = v j := by
  unfold gS
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i j => ?_, h⟩
    have h1 : M i j ≤ ∑ j, M i j :=
      Finset.single_le_sum (f := fun j => M i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [h.1 i] at h1
    omega

/-- The combinatorial sum in `gammaFock`. -/
private def gSum {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) : ℂ :=
  ∑ M ∈ gS u v, ∏ i, ∏ j, R i j ^ (M i j) / (Nat.factorial (M i j) : ℂ)

private lemma gammaFock_eq {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    gammaFock R u v =
      (Real.sqrt ((∏ i, (Nat.factorial (u i) : ℝ)) * ∏ j, (Nat.factorial (v j) : ℝ)) : ℂ) *
        gSum R u v := rfl

/-- For diagonal `R`, an off-diagonal nonzero entry of `M` kills the term. -/
private lemma term_diagonal_eq_zero {n : ℕ} (c : Fin n → ℂ) (M : Fin n → Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) (h : M i j ≠ 0) :
    ∏ i, ∏ j, (Matrix.diagonal c) i j ^ (M i j) / (Nat.factorial (M i j) : ℂ) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
  rw [Matrix.diagonal_apply_ne c hij, zero_pow h, zero_div]

/-- A matrix with vanishing off-diagonal entries and row sums `u` is `diag u`. -/
private lemma diag_of_offdiag_zero {n : ℕ} (u : Fin n → ℕ) (M : Fin n → Fin n → ℕ)
    (hrow : ∀ i, ∑ j, M i j = u i) (hoff : ∀ i j, i ≠ j → M i j = 0) (i : Fin n) :
    M i i = u i := by
  rw [← hrow i]
  exact (Finset.sum_eq_single i (fun j _ hji => hoff i j (Ne.symm hji))
    (fun h => absurd (Finset.mem_univ i) h)).symm

private lemma diag_of_offdiag_zero' {n : ℕ} (v : Fin n → ℕ) (M : Fin n → Fin n → ℕ)
    (hcol : ∀ j, ∑ i, M i j = v j) (hoff : ∀ i j, i ≠ j → M i j = 0) (j : Fin n) :
    M j j = v j := by
  rw [← hcol j]
  exact (Finset.sum_eq_single j (fun i _ hij => hoff i j hij)
    (fun h => absurd (Finset.mem_univ j) h)).symm

private lemma gSum_diagonal_ne {n : ℕ} (c : Fin n → ℂ) (u v : Fin n → ℕ) (huv : u ≠ v) :
    gSum (Matrix.diagonal c) u v = 0 := by
  unfold gSum
  refine Finset.sum_eq_zero fun M hM => ?_
  rw [mem_gS] at hM
  by_cases hoff : ∀ i j, i ≠ j → M i j = 0
  · exfalso
    apply huv
    funext i
    rw [← diag_of_offdiag_zero u M hM.1 hoff i, diag_of_offdiag_zero' v M hM.2 hoff i]
  · push Not at hoff
    obtain ⟨i, j, hij, hne⟩ := hoff
    exact term_diagonal_eq_zero c M i j hij hne

private lemma gSum_diagonal_self {n : ℕ} (c : Fin n → ℂ) (u : Fin n → ℕ) :
    gSum (Matrix.diagonal c) u u = ∏ i, (c i ^ u i / (Nat.factorial (u i) : ℂ)) := by
  unfold gSum
  rw [Finset.sum_eq_single (fun i j => if i = j then u i else 0)]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · intro M hM hne
    rw [mem_gS] at hM
    by_cases hoff : ∀ i j, i ≠ j → M i j = 0
    · exfalso
      apply hne
      funext i j
      by_cases hij : i = j
      · subst hij
        simp [diag_of_offdiag_zero u M hM.1 hoff i]
      · simp [hij, hoff i j hij]
    · push Not at hoff
      obtain ⟨i, j, hij, hne'⟩ := hoff
      exact term_diagonal_eq_zero c M i j hij hne'
  · intro h
    exfalso
    apply h
    rw [mem_gS]
    constructor
    · intro i
      simp
    · intro j
      simp

/-- `Γ(diag c)` is diagonal with entries `∏ cᵢ^{uᵢ}`. -/
private lemma gammaFock_diagonal {n : ℕ} (c : Fin n → ℂ) (u v : Fin n → ℕ) :
    gammaFock (Matrix.diagonal c) u v = if u = v then ∏ i, c i ^ u i else 0 := by
  by_cases huv : u = v
  · subst huv
    rw [if_pos rfl, gammaFock_eq, gSum_diagonal_self]
    have hpos : (0 : ℝ) ≤ ∏ i, (Nat.factorial (u i) : ℝ) :=
      Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
    rw [Real.sqrt_mul_self hpos]
    push_cast
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have : ((Nat.factorial (u i) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  · rw [if_neg huv, gammaFock_eq, gSum_diagonal_ne c u v huv, mul_zero]

/-! ### Photon-number sectors -/

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

private lemma card_sec_le (n N : ℕ) : (sec n N).card ≤ (N + 1) ^ n := by
  unfold sec
  refine (Finset.card_filter_le _ _).trans ?_
  simp

private lemma gammaFock_mul_sec {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    gammaFock (A * B) u v = ∑ w ∈ sec n (∑ i, u i), gammaFock A u w * gammaFock B w v :=
  gammaFock_mul A B u v

/-- Spectral form of `Γ(U diag(c) Uᴴ)`. -/
private lemma gammaFock_spectral {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ)
    (u v : Fin n → ℕ) :
    gammaFock (U * Matrix.diagonal c * Uᴴ) u v =
      ∑ w ∈ sec n (∑ i, u i), gammaFock U u w * (∏ i, c i ^ w i) * gammaFock Uᴴ w v := by
  rw [gammaFock_mul_sec]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [gammaFock_mul_sec, Finset.sum_eq_single w]
  · rw [gammaFock_diagonal, if_pos rfl]
  · intro w' _ hne
    rw [gammaFock_diagonal, if_neg hne, mul_zero]
  · intro h
    exact absurd hw h

/-- The multimode Weyl kernel `∏ⱼ D(ζⱼ)_{vⱼ uⱼ}`. -/
private def Wk {n : ℕ} (ζ : Fin n → ℂ) (v u : Fin n → ℕ) : ℂ :=
  ∏ j, displacementMatrix (ζ j) (v j) (u j)

/-- **Sector identity.** The trace of `Γ(U diag(c) Uᴴ) W(ζ)` over a photon-number sector equals the trace of
`Γ(diag c) W(Uᴴζ)` over the same sector. -/
private lemma sector_identity {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU1 : Uᴴ * U = 1)
    (c : Fin n → ℂ) (ζ : Fin n → ℂ) (N : ℕ) :
    ∑ u ∈ sec n N, ∑ v ∈ sec n N, gammaFock (U * Matrix.diagonal c * Uᴴ) u v * Wk ζ v u =
      ∑ w ∈ sec n N, (∏ i, c i ^ w i) * Wk (Uᴴ *ᵥ ζ) w w := by
  have hL : ∀ u ∈ sec n N, ∀ v, gammaFock (U * Matrix.diagonal c * Uᴴ) u v * Wk ζ v u =
      ∑ w ∈ sec n N, gammaFock U u w * (∏ i, c i ^ w i) * gammaFock Uᴴ w v * Wk ζ v u := by
    intro u hu v
    rw [gammaFock_spectral, (mem_sec u).mp hu, Finset.sum_mul]
  have hRw : ∀ w ∈ sec n N, Wk (Uᴴ *ᵥ ζ) w w =
      ∑ v ∈ sec n N, ∑ u ∈ sec n N, gammaFock Uᴴ w v * Wk ζ v u * gammaFock U u w := by
    intro w hw
    have h := gammaFock_weyl U hU1 ζ w w
    rw [(mem_sec w).mp hw] at h
    exact h.symm
  calc ∑ u ∈ sec n N, ∑ v ∈ sec n N, gammaFock (U * Matrix.diagonal c * Uᴴ) u v * Wk ζ v u
      = ∑ u ∈ sec n N, ∑ v ∈ sec n N, ∑ w ∈ sec n N,
          gammaFock U u w * (∏ i, c i ^ w i) * gammaFock Uᴴ w v * Wk ζ v u :=
        Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v _ => hL u hu v
    _ = ∑ v ∈ sec n N, ∑ u ∈ sec n N, ∑ w ∈ sec n N,
          gammaFock U u w * (∏ i, c i ^ w i) * gammaFock Uᴴ w v * Wk ζ v u := Finset.sum_comm
    _ = ∑ v ∈ sec n N, ∑ w ∈ sec n N, ∑ u ∈ sec n N,
          gammaFock U u w * (∏ i, c i ^ w i) * gammaFock Uᴴ w v * Wk ζ v u :=
        Finset.sum_congr rfl fun v _ => Finset.sum_comm
    _ = ∑ w ∈ sec n N, ∑ v ∈ sec n N, ∑ u ∈ sec n N,
          gammaFock U u w * (∏ i, c i ^ w i) * gammaFock Uᴴ w v * Wk ζ v u := Finset.sum_comm
    _ = ∑ w ∈ sec n N, (∏ i, c i ^ w i) * Wk (Uᴴ *ᵥ ζ) w w := by
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [hRw w hw, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        ring

/-! ### Norm bounds -/

private lemma disp_norm_le_one (z : ℂ) (m k : ℕ) : ‖displacementMatrix z m k‖ ≤ 1 := by
  have h := (displacementMatrix_unitary z k k).2.2.1
  rw [if_pos rfl] at h
  have h2 : HasSum (fun j : ℕ => ‖displacementMatrix z j k‖ ^ 2) 1 := by
    have h3 := Complex.hasSum_re h
    rw [Complex.one_re] at h3
    refine h3.congr_fun fun j => ?_
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have h4 : ‖displacementMatrix z m k‖ ^ 2 ≤ 1 := le_hasSum h2 m (fun j _ => sq_nonneg _)
  exact (sq_le_one_iff₀ (norm_nonneg _)).mp h4

private lemma Wk_norm_le_one {n : ℕ} (ζ : Fin n → ℂ) (v u : Fin n → ℕ) : ‖Wk ζ v u‖ ≤ 1 := by
  unfold Wk
  rw [norm_prod]
  exact Finset.prod_le_one (fun j _ => norm_nonneg _) (fun j _ => disp_norm_le_one _ _ _)

/-- Entries of `Γ(U)` are bounded by one for a (co)isometry `U`. -/
private lemma gammaFock_norm_le_one {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU2 : U * Uᴴ = 1)
    (u w : Fin n → ℕ) : ‖gammaFock U u w‖ ≤ 1 := by
  by_cases hw : ∑ i, u i = ∑ i, w i
  · have h := gammaFock_mul_sec U Uᴴ u u
    rw [hU2, (gammaFock_basic 1 u u).2.2, if_pos rfl] at h
    have h2 : (1 : ℝ) = ∑ w' ∈ sec n (∑ i, u i), ‖gammaFock U u w'‖ ^ 2 := by
      have h3 := congrArg Complex.re h
      rw [Complex.one_re, Complex.re_sum] at h3
      rw [h3]
      refine Finset.sum_congr rfl fun w' _ => ?_
      rw [(gammaFock_basic U w' u).2.1, Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq]
    have h4 : ‖gammaFock U u w‖ ^ 2 ≤ 1 := by
      rw [h2]
      exact Finset.single_le_sum (f := fun w' => ‖gammaFock U u w'‖ ^ 2)
        (fun w' _ => sq_nonneg _) ((mem_sec w).mpr hw.symm)
    exact (sq_le_one_iff₀ (norm_nonneg _)).mp h4
  · rw [(gammaFock_basic U u w).1 hw, norm_zero]
    exact zero_le_one

private lemma gammaFock_spectral_norm_le {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (d : Fin n → ℝ) (hd0 : ∀ i, 0 ≤ d i) (r : ℝ)
    (hr0 : 0 ≤ r) (hr : ∀ i, d i ≤ r) (N : ℕ) (u v : Fin n → ℕ) (hu : ∑ i, u i = N) :
    ‖gammaFock (U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) u v‖ ≤
      ((sec n N).card : ℝ) * r ^ N := by
  rw [gammaFock_spectral, hu]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ w ∈ sec n N,
      ‖gammaFock U u w * (∏ i, ((d i : ℂ)) ^ w i) * gammaFock Uᴴ w v‖ ≤ r ^ N := by
    intro w hw
    rw [norm_mul, norm_mul]
    have h1 := gammaFock_norm_le_one U hU2 u w
    have h2 := gammaFock_norm_le_one Uᴴ
      (by rw [Matrix.conjTranspose_conjTranspose]; exact hU1) w v
    have h3 : ‖∏ i, ((d i : ℂ)) ^ w i‖ ≤ r ^ N := by
      rw [norm_prod, ← (mem_sec w).mp hw, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd0 i)]
      exact pow_le_pow_left₀ (hd0 i) (hr i) _
    have hr0' : 0 ≤ r ^ N := pow_nonneg hr0 N
    calc ‖gammaFock U u w‖ * ‖∏ i, ((d i : ℂ)) ^ w i‖ * ‖gammaFock Uᴴ w v‖
        ≤ 1 * r ^ N * 1 := by
          refine mul_le_mul (mul_le_mul h1 h3 (norm_nonneg _) zero_le_one) h2 (norm_nonneg _) ?_
          positivity
      _ = r ^ N := by ring
  calc ∑ w ∈ sec n N, ‖gammaFock U u w * (∏ i, ((d i : ℂ)) ^ w i) * gammaFock Uᴴ w v‖
      ≤ ∑ _w ∈ sec n N, r ^ N := Finset.sum_le_sum hterm
    _ = ((sec n N).card : ℝ) * r ^ N := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Crude absolute bound for the sector sums of the diagonal of `ρ W`. -/
private lemma sector_sum_norm_le {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (d : Fin n → ℝ) (hd0 : ∀ i, 0 ≤ d i) (r : ℝ)
    (hr0 : 0 ≤ r) (hr : ∀ i, d i ≤ r) (c : ℂ) (ζ : Fin n → ℂ) (N : ℕ) :
    ∑ u ∈ sec n N, ‖∑ v ∈ sec n N,
        c * gammaFock (U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) u v * Wk ζ v u‖ ≤
      ‖c‖ * (((N + 1 : ℕ) : ℝ) ^ n) ^ 3 * r ^ N := by
  have hcard : ((sec n N).card : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ n := by
    exact_mod_cast card_sec_le n N
  have hr0' : 0 ≤ r ^ N := pow_nonneg hr0 N
  have hterm : ∀ u ∈ sec n N, ‖∑ v ∈ sec n N,
      c * gammaFock (U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) u v * Wk ζ v u‖ ≤
      ((sec n N).card : ℝ) * (‖c‖ * (((sec n N).card : ℝ) * r ^ N)) := by
    intro u hu
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ v ∈ sec n N,
        ‖c * gammaFock (U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) u v * Wk ζ v u‖ ≤
        ‖c‖ * (((sec n N).card : ℝ) * r ^ N) := by
      intro v _
      rw [norm_mul, norm_mul]
      have h2 := gammaFock_spectral_norm_le U hU1 hU2 d hd0 r hr0 hr N u v ((mem_sec u).mp hu)
      have h3 := Wk_norm_le_one ζ v u
      calc ‖c‖ * ‖gammaFock (U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) u v‖ * ‖Wk ζ v u‖
          ≤ ‖c‖ * (((sec n N).card : ℝ) * r ^ N) * 1 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) h3 (norm_nonneg _) ?_
            positivity
        _ = ‖c‖ * (((sec n N).card : ℝ) * r ^ N) := mul_one _
    calc ∑ v ∈ sec n N,
          ‖c * gammaFock (U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) u v * Wk ζ v u‖
        ≤ ∑ _v ∈ sec n N, ‖c‖ * (((sec n N).card : ℝ) * r ^ N) := Finset.sum_le_sum h1
      _ = ((sec n N).card : ℝ) * (‖c‖ * (((sec n N).card : ℝ) * r ^ N)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  calc ∑ u ∈ sec n N, ‖∑ v ∈ sec n N,
        c * gammaFock (U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) u v * Wk ζ v u‖
      ≤ ∑ _u ∈ sec n N, ((sec n N).card : ℝ) * (‖c‖ * (((sec n N).card : ℝ) * r ^ N)) :=
        Finset.sum_le_sum hterm
    _ = ‖c‖ * ((sec n N).card : ℝ) ^ 3 * r ^ N := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ‖c‖ * (((N + 1 : ℕ) : ℝ) ^ n) ^ 3 * r ^ N := by
        have h3 : ((sec n N).card : ℝ) ^ 3 ≤ (((N + 1 : ℕ) : ℝ) ^ n) ^ 3 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 3
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) hr0'

private lemma summable_majorant (C : ℝ) (k : ℕ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun N : ℕ => C * (((N + 1 : ℕ) : ℝ) ^ k) ^ 3 * r ^ N) := by
  have hr : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
  have h0 : Summable (fun N : ℕ => ((N : ℕ) : ℝ) ^ (k * 3) * r ^ N) :=
    summable_pow_mul_geometric_of_norm_lt_one (k * 3) hr
  have h1 : Summable (fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ (k * 3) * r ^ (N + 1)) :=
    (summable_nat_add_iff (f := fun N : ℕ => ((N : ℕ) : ℝ) ^ (k * 3) * r ^ N) 1).mpr h0
  have h2 : Summable (fun N : ℕ => (C * r⁻¹) * (((N + 1 : ℕ) : ℝ) ^ (k * 3) * r ^ (N + 1))) :=
    h1.mul_left (C * r⁻¹)
  refine h2.congr fun N => ?_
  have hrne : r ≠ 0 := hr0.ne'
  rw [pow_succ r N, ← pow_mul]
  field_simp

private lemma exists_bound {n : ℕ} (d : Fin n → ℝ) (hd1 : ∀ i, d i < 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ i, d i ≤ r := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1 / 2, by norm_num, by norm_num, fun i => (h.false i).elim⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_max d
    refine ⟨max (d i₀) (1 / 2), lt_max_of_lt_right (by norm_num),
      max_lt (hd1 i₀) (by norm_num), fun i => (hi₀ i).trans (le_max_left _ _)⟩

/-! ### Summation by photon-number sectors -/

private lemma sec_pairwiseDisjoint (n : ℕ) (s : Set ℕ) : s.PairwiseDisjoint (sec n) := by
  intro N _ N' _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro u hu hu'
  exact hne (((mem_sec u).mp hu).symm.trans ((mem_sec u).mp hu'))

/-- A non-negative family whose sector sums are dominated by a summable sequence is summable. -/
private lemma summable_of_sector_le {n : ℕ} (f : (Fin n → ℕ) → ℝ) (hf : ∀ u, 0 ≤ f u)
    (b : ℕ → ℝ) (hb : Summable b) (h : ∀ N, ∑ u ∈ sec n N, f u ≤ b N) : Summable f := by
  have hb0 : ∀ N, 0 ≤ b N := fun N => (Finset.sum_nonneg fun u _ => hf u).trans (h N)
  refine summable_of_sum_le (c := ∑' N, b N) hf fun s => ?_
  set M := s.sup (fun u => ∑ i, u i) with hM
  have hsub : s ⊆ (Finset.range (M + 1)).biUnion (sec n) := by
    intro u hu
    rw [Finset.mem_biUnion]
    refine ⟨∑ i, u i, ?_, (mem_sec u).mpr rfl⟩
    rw [Finset.mem_range]
    have : ∑ i, u i ≤ M := Finset.le_sup (f := fun u : Fin n → ℕ => ∑ i, u i) hu
    omega
  calc ∑ u ∈ s, f u ≤ ∑ u ∈ (Finset.range (M + 1)).biUnion (sec n), f u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun u _ _ => hf u
    _ = ∑ N ∈ Finset.range (M + 1), ∑ u ∈ sec n N, f u :=
        Finset.sum_biUnion (sec_pairwiseDisjoint n _)
    _ ≤ ∑ N ∈ Finset.range (M + 1), b N := Finset.sum_le_sum fun N _ => h N
    _ ≤ ∑' N, b N := sum_le_hasSum _ (fun N _ => hb0 N) hb.hasSum

/-- Two summable families with the same sector sums have the same sum. -/
private lemma hasSum_of_sector_eq {n : ℕ} (f g : (Fin n → ℕ) → ℂ) (hf : Summable f) {a : ℂ}
    (hg : HasSum g a) (h : ∀ N, ∑ u ∈ sec n N, f u = ∑ u ∈ sec n N, g u) : HasSum f a := by
  let B : ℕ → Finset (Fin n → ℕ) := fun M => (Finset.range (M + 1)).biUnion (sec n)
  have hmono : Monotone B := by
    intro M M' hMM' u hu
    simp only [B, Finset.mem_biUnion, Finset.mem_range] at hu ⊢
    obtain ⟨N, hN, huN⟩ := hu
    exact ⟨N, by omega, huN⟩
  have hcov : ∀ u : Fin n → ℕ, ∃ M, u ∈ B M := fun u => ⟨∑ i, u i, by
    simp only [B, Finset.mem_biUnion, Finset.mem_range]
    exact ⟨∑ i, u i, by omega, (mem_sec u).mpr rfl⟩⟩
  have hB : Filter.Tendsto B Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_finset_of_monotone hmono hcov
  have hsum : ∀ (φ : (Fin n → ℕ) → ℂ) (M : ℕ),
      ∑ u ∈ B M, φ u = ∑ N ∈ Finset.range (M + 1), ∑ u ∈ sec n N, φ u :=
    fun φ M => Finset.sum_biUnion (sec_pairwiseDisjoint n _)
  have hf' : Filter.Tendsto (fun s : Finset (Fin n → ℕ) => ∑ u ∈ s, f u) Filter.atTop
      (nhds (∑' u, f u)) := hf.hasSum
  have hg' : Filter.Tendsto (fun s : Finset (Fin n → ℕ) => ∑ u ∈ s, g u) Filter.atTop
      (nhds a) := hg
  have h1 : Filter.Tendsto (fun M => ∑ u ∈ B M, f u) Filter.atTop (nhds (∑' u, f u)) :=
    hf'.comp hB
  have h2 : Filter.Tendsto (fun M => ∑ u ∈ B M, g u) Filter.atTop (nhds a) :=
    hg'.comp hB
  have h3 : (fun M => ∑ u ∈ B M, f u) = fun M => ∑ u ∈ B M, g u := funext fun M => by
    rw [hsum, hsum]
    exact Finset.sum_congr rfl fun N _ => h N
  rw [h3] at h1
  have h4 := tendsto_nhds_unique h1 h2
  rw [← h4]
  exact hf.hasSum

/-! ### Products of series -/

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

/-- The Weyl characteristic function of the product thermal state `Γ(diag d)` (unnormalized). -/
private lemma product_side {n : ℕ} (d : Fin n → ℝ) (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i < 1)
    (z : Fin n → ℂ) :
    HasSum (fun w : Fin n → ℕ => (∏ i, (d i : ℂ) ^ w i) * Wk z w w)
      (∏ j, (((1 - d j)⁻¹ *
        Real.exp (-(Complex.normSq (z j)) * (1 + d j) / (2 * (1 - d j))) : ℝ) : ℂ)) := by
  have key := (hasSum_pi_prod (Fin n)
    (fun j m => (d j : ℂ) ^ m * displacementMatrix (z j) m m)
    (fun j => (((1 - d j)⁻¹ *
        Real.exp (-(Complex.normSq (z j)) * (1 + d j) / (2 * (1 - d j))) : ℝ) : ℂ))
    (fun j => (thermal_characteristic (d j) (hd0 j) (hd1 j) (z j)).1)
    (fun j => (thermal_characteristic (d j) (hd0 j) (hd1 j) (z j)).2)).2
  refine key.congr_fun fun w => ?_
  unfold Wk
  rw [Finset.prod_mul_distrib]

/-! ### Spectral data and the Cayley transform -/

private lemma conj_one_sub {n : ℕ} (U D : Matrix (Fin n) (Fin n) ℂ) (hU1 : Uᴴ * U = 1) :
    Uᴴ * (1 - U * D * Uᴴ) * U = 1 - D := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU1]
  have h : Uᴴ * (U * D * Uᴴ) * U = (Uᴴ * U) * D * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
  rw [h, hU1, Matrix.one_mul, Matrix.mul_one]

private lemma one_sub_conj {n : ℕ} (U D : Matrix (Fin n) (Fin n) ℂ) (hU2 : U * Uᴴ = 1) :
    1 - U * D * Uᴴ = U * (1 - D) * Uᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU2]

private lemma one_add_conj {n : ℕ} (U D : Matrix (Fin n) (Fin n) ℂ) (hU2 : U * Uᴴ = 1) :
    1 + U * D * Uᴴ = U * (1 + D) * Uᴴ := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU2]

private lemma conj_mul_conj {n : ℕ} (U A B : Matrix (Fin n) (Fin n) ℂ) (hU1 : Uᴴ * U = 1) :
    (U * A * Uᴴ) * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
  calc (U * A * Uᴴ) * (U * B * Uᴴ) = U * A * (Uᴴ * U) * B * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = U * (A * B) * Uᴴ := by
        rw [hU1, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

private lemma one_sub_diagonal {n : ℕ} (d : Fin n → ℝ) :
    (1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.diagonal (fun i => (d i : ℂ)) =
      Matrix.diagonal (fun i => ((1 - d i : ℝ) : ℂ)) := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  congr 1
  funext i
  simp

private lemma one_add_diagonal {n : ℕ} (d : Fin n → ℝ) :
    (1 : Matrix (Fin n) (Fin n) ℂ) + Matrix.diagonal (fun i => (d i : ℂ)) =
      Matrix.diagonal (fun i => ((1 + d i : ℝ) : ℂ)) := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_add]
  congr 1
  funext i
  simp

/-- Unitary diagonalization `R = U diag(d) Uᴴ` with `0 ≤ dᵢ < 1`. -/
private lemma spectral_data {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      R = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ ∧ (∀ i, 0 ≤ d i) ∧ (∀ i, d i < 1) := by
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix (Fin n) (Fin n) ℂ,
      U = (hR.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hU1 : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hUdef]
    exact Unitary.coe_star_mul_self _
  have hU2 : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hUdef]
    exact Unitary.coe_mul_star_self _
  have hspec : R = U * Matrix.diagonal (fun i => ((hR.1.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have h := hR.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hUdef, ← Matrix.star_eq_conjTranspose]
    exact h
  refine ⟨U, hR.1.eigenvalues, hU1, hU2, hspec, hR.eigenvalues_nonneg, ?_⟩
  have hD := conj_one_sub U (Matrix.diagonal (fun i => ((hR.1.eigenvalues i : ℝ) : ℂ))) hU1
  rw [← hspec, one_sub_diagonal] at hD
  have hpd : (Uᴴ * (1 - R) * U).PosDef :=
    hR1.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit
      (IsUnit.of_mul_eq_one _ hU2))
  rw [hD, Matrix.posDef_diagonal_iff] at hpd
  intro i
  have h := hpd i
  rw [Complex.zero_lt_real] at h
  linarith

/-- `(1 + R)(1 - R)⁻¹` in the eigenbasis of `R`. -/
private lemma cayley_spectral {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (hd1 : ∀ i, d i < 1) :
    (1 + U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) *
        (1 - U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ)⁻¹ =
      U * Matrix.diagonal (fun i => (((1 + d i) / (1 - d i) : ℝ) : ℂ)) * Uᴴ := by
  have hinv : (1 - U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ)⁻¹ =
      U * Matrix.diagonal (fun i => (((1 - d i)⁻¹ : ℝ) : ℂ)) * Uᴴ := by
    apply Matrix.inv_eq_right_inv
    rw [one_sub_conj U _ hU2, one_sub_diagonal, conj_mul_conj U _ _ hU1,
      Matrix.diagonal_mul_diagonal]
    have h1 : (fun i => ((1 - d i : ℝ) : ℂ) * (((1 - d i)⁻¹ : ℝ) : ℂ)) = fun _ => (1 : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (by linarith [hd1 i]), Complex.ofReal_one]
    rw [h1, Matrix.diagonal_one, Matrix.mul_one, hU2]
  rw [hinv, one_add_conj U _ hU2, one_add_diagonal, conj_mul_conj U _ _ hU1,
    Matrix.diagonal_mul_diagonal]
  congr 3
  funext i
  rw [← Complex.ofReal_mul, div_eq_mul_inv]

/-- Quadratic form of `U diag(e) Uᴴ`. -/
private lemma quad_form_spectral {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → ℂ)
    (ζ : Fin n → ℂ) :
    ∑ j, ∑ k, star (ζ j) * (U * Matrix.diagonal e * Uᴴ) j k * ζ k =
      ∑ i, e i * (Complex.normSq ((Uᴴ *ᵥ ζ) i) : ℂ) := by
  have h1 : ∑ j, ∑ k, star (ζ j) * (U * Matrix.diagonal e * Uᴴ) j k * ζ k =
      star ζ ⬝ᵥ ((U * Matrix.diagonal e * Uᴴ) *ᵥ ζ) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  have h2 : star ζ ᵥ* U = star (Uᴴ *ᵥ ζ) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, h2]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

private lemma exponent_identity {n : ℕ} (R U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hspec : R = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) (hd1 : ∀ i, d i < 1)
    (ζ : Fin n → ℂ) :
    ∏ j, ((Real.exp (-(Complex.normSq ((Uᴴ *ᵥ ζ) j)) * (1 + d j) / (2 * (1 - d j))) : ℝ) : ℂ) =
      Complex.exp (-(1 / 2 : ℂ) *
        ∑ j, ∑ k, star (ζ j) * ((1 + R) * (1 - R)⁻¹) j k * ζ k) := by
  rw [hspec, cayley_spectral U d hU1 hU2 hd1, quad_form_spectral, Finset.mul_sum,
    Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Complex.ofReal_exp]
  congr 1
  have hne : (1 : ℂ) - (d j : ℂ) ≠ 0 := by
    have h : (1 : ℝ) - d j ≠ 0 := by linarith [hd1 j]
    exact_mod_cast h
  push_cast
  field_simp

/-! ### The main computation -/

private lemma fug_apply {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    fugacityCoeff R u v = (1 - R).det * gammaFock R u v := rfl

private lemma core {n : ℕ} (R U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hspec : R = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i < 1) (ζ : Fin n → ℂ) :
    (∀ u : Fin n → ℕ, Summable (fun v : Fin n → ℕ => fugacityCoeff R u v * Wk ζ v u)) ∧
    HasSum (fun u : Fin n → ℕ => ∑' v : Fin n → ℕ, fugacityCoeff R u v * Wk ζ v u)
      (∏ j, ((Real.exp (-(Complex.normSq ((Uᴴ *ᵥ ζ) j)) * (1 + d j) / (2 * (1 - d j))) : ℝ)
        : ℂ)) := by
  have hdet : (1 - R).det = ((∏ i, (1 - d i) : ℝ) : ℂ) := by
    rw [hspec, one_sub_conj U _ hU2, one_sub_diagonal, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal, mul_right_comm, ← Matrix.det_mul, hU2, Matrix.det_one, one_mul,
      Complex.ofReal_prod]
  have hzero : ∀ u v : Fin n → ℕ, v ∉ sec n (∑ i, u i) →
      fugacityCoeff R u v * Wk ζ v u = 0 := by
    intro u v hv
    have hne : ∑ i, u i ≠ ∑ i, v i := fun h => hv ((mem_sec v).mpr h.symm)
    rw [fug_apply, (gammaFock_basic R u v).1 hne, mul_zero, zero_mul]
  have hF : ∀ u : Fin n → ℕ, ∑' v : Fin n → ℕ, fugacityCoeff R u v * Wk ζ v u =
      ∑ v ∈ sec n (∑ i, u i), (1 - R).det * gammaFock R u v * Wk ζ v u :=
    fun u => tsum_eq_sum (hzero u)
  refine ⟨fun u => summable_of_ne_finset_zero (hzero u), ?_⟩
  rw [show (fun u : Fin n → ℕ => ∑' v : Fin n → ℕ, fugacityCoeff R u v * Wk ζ v u) =
      fun u : Fin n → ℕ => ∑ v ∈ sec n (∑ i, u i), (1 - R).det * gammaFock R u v * Wk ζ v u
    from funext hF]
  obtain ⟨r, hr0, hr1, hr⟩ := exists_bound d hd1
  have hsummable : Summable (fun u : Fin n → ℕ =>
      ∑ v ∈ sec n (∑ i, u i), (1 - R).det * gammaFock R u v * Wk ζ v u) := by
    refine Summable.of_norm ?_
    refine summable_of_sector_le _ (fun u => norm_nonneg _) _
      (summable_majorant ‖(1 - R).det‖ n r hr0 hr1) fun N => ?_
    have h := sector_sum_norm_le U hU1 hU2 d hd0 r hr0.le hr (1 - R).det ζ N
    rw [← hspec] at h
    refine le_of_eq_of_le (Finset.sum_congr rfl fun u hu => ?_) h
    rw [(mem_sec u).mp hu]
  have hG := (product_side d hd0 hd1 (Uᴴ *ᵥ ζ)).mul_left (1 - R).det
  have hsec : ∀ N, ∑ u ∈ sec n N,
      (∑ v ∈ sec n (∑ i, u i), (1 - R).det * gammaFock R u v * Wk ζ v u) =
      ∑ w ∈ sec n N, (1 - R).det * ((∏ i, (d i : ℂ) ^ w i) * Wk (Uᴴ *ᵥ ζ) w w) := by
    intro N
    have h := sector_identity U hU1 (fun i => (d i : ℂ)) ζ N
    rw [← hspec] at h
    rw [← Finset.mul_sum, ← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [(mem_sec u).mp hu, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [mul_assoc]
  have hfinal := hasSum_of_sector_eq _ _ hsummable hG hsec
  have hval : (1 - R).det * ∏ j, (((1 - d j)⁻¹ *
        Real.exp (-(Complex.normSq ((Uᴴ *ᵥ ζ) j)) * (1 + d j) / (2 * (1 - d j))) : ℝ) : ℂ) =
      ∏ j, ((Real.exp (-(Complex.normSq ((Uᴴ *ᵥ ζ) j)) * (1 + d j) / (2 * (1 - d j))) : ℝ)
        : ℂ) := by
    rw [hdet, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Complex.ofReal_mul, ← mul_assoc, mul_inv_cancel₀ (by linarith [hd1 j]), one_mul]
  rw [hval] at hfinal
  exact hfinal

/-- The complex amplitude `ζⱼ = (-ξ_{pⱼ} + i ξ_{qⱼ})/√2`. -/
private def zetaOf {n : ℕ} (ξ : Fin n × Fin 2 → ℝ) : Fin n → ℂ :=
  fun j => (-(ξ (j, 1) : ℂ) + Complex.I * (ξ (j, 0) : ℂ)) / (Real.sqrt 2 : ℂ)

theorem solution {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) :
    OscillatorCharacteristicSummable (fugacityCoeff R) ∧
    ∀ ξ : Fin n × Fin 2 → ℝ,
      oscillatorCharacteristic (fugacityCoeff R) ξ =
        Complex.exp (-(1 / 2 : ℂ) *
          ∑ j, ∑ k, star ((-(ξ (j, 1) : ℂ) + Complex.I * (ξ (j, 0) : ℂ)) / (Real.sqrt 2 : ℂ)) *
            ((1 + R) * (1 - R)⁻¹) j k *
            ((-(ξ (k, 1) : ℂ) + Complex.I * (ξ (k, 0) : ℂ)) / (Real.sqrt 2 : ℂ))) := by
  obtain ⟨U, d, hU1, hU2, hspec, hd0, hd1⟩ := spectral_data R hR hR1
  have main : ∀ ξ : Fin n × Fin 2 → ℝ,
      (∀ u : Fin n → ℕ, Summable (fun v : Fin n → ℕ =>
        fugacityCoeff R u v * Wk (zetaOf ξ) v u)) ∧
      HasSum (fun u : Fin n → ℕ => ∑' v : Fin n → ℕ, fugacityCoeff R u v * Wk (zetaOf ξ) v u)
        (Complex.exp (-(1 / 2 : ℂ) *
          ∑ j, ∑ k, star (zetaOf ξ j) * ((1 + R) * (1 - R)⁻¹) j k * zetaOf ξ k)) := by
    intro ξ
    have h := core R U d hU1 hU2 hspec hd0 hd1 (zetaOf ξ)
    rw [exponent_identity R U d hU1 hU2 hspec hd1 (zetaOf ξ)] at h
    exact h
  refine ⟨fun ξ => ⟨(main ξ).1, (main ξ).2.summable⟩, fun ξ => ?_⟩
  exact (main ξ).2.tsum_eq
