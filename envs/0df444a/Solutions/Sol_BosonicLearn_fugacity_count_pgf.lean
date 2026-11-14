-- Prove2me | solution 1 for BosonicLearn.fugacity_count_pgf
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T19:58:25.329836+00:00
-- url     : https://prove2.me/submissions/efccc60a-109c-4182-a18f-15499b0e36f3

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Theorems.Thm_BosonicLearn_gammaFock_mul
import Theorems.Thm_BosonicLearn_gammaFock_posSemidef
import Theorems.Thm_BosonicLearn_gammaFock_trace_psd

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Matrix ComplexOrder

open BosonicLearn

noncomputable section

/-! ### Sector lemmas (from `gammaFock_trace_psd`) -/

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

/-- Cyclicity of the trace of `Γ` on a photon-number sector. -/
private lemma sector_trace_comm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (N : ℕ) :
    ∑ u ∈ sec n N, gammaFock (A * B) u u = ∑ u ∈ sec n N, gammaFock (B * A) u u := by
  have h1 : ∀ (A B : Matrix (Fin n) (Fin n) ℂ), ∑ u ∈ sec n N, gammaFock (A * B) u u =
      ∑ u ∈ sec n N, ∑ w ∈ sec n N, gammaFock A u w * gammaFock B w u := by
    intro A B
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [gammaFock_mul_sec, (mem_sec u).mp hu]
  rw [h1 A B, h1 B A, Finset.sum_comm]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => mul_comm _ _

/-- Partial sums of a non-negative family are bounded by the sum of another non-negative family with the same
sector sums. -/
private lemma sum_le_of_sector {n : ℕ} (f g : (Fin n → ℕ) → ℝ) (hf : ∀ u, 0 ≤ f u)
    (hg : ∀ u, 0 ≤ g u) (h : ∀ N, ∑ u ∈ sec n N, f u = ∑ u ∈ sec n N, g u) {a : ℝ}
    (hga : HasSum g a) (s : Finset (Fin n → ℕ)) : ∑ u ∈ s, f u ≤ a := by
  set M := s.sup (fun u => ∑ i, u i) with hM
  have hdisj : ((Finset.range (M + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint (sec n) := by
    intro N _ N' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro u hu hu'
    exact hne (((mem_sec u).mp hu).symm.trans ((mem_sec u).mp hu'))
  have hsub : s ⊆ (Finset.range (M + 1)).biUnion (sec n) := by
    intro u hu
    rw [Finset.mem_biUnion]
    refine ⟨∑ i, u i, ?_, (mem_sec u).mpr rfl⟩
    rw [Finset.mem_range]
    have : ∑ i, u i ≤ M := Finset.le_sup (f := fun u : Fin n → ℕ => ∑ i, u i) hu
    omega
  calc ∑ u ∈ s, f u ≤ ∑ u ∈ (Finset.range (M + 1)).biUnion (sec n), f u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun u _ _ => hf u
    _ = ∑ N ∈ Finset.range (M + 1), ∑ u ∈ sec n N, f u := Finset.sum_biUnion hdisj
    _ = ∑ N ∈ Finset.range (M + 1), ∑ u ∈ sec n N, g u := Finset.sum_congr rfl fun N _ => h N
    _ = ∑ u ∈ (Finset.range (M + 1)).biUnion (sec n), g u := (Finset.sum_biUnion hdisj).symm
    _ ≤ a := sum_le_hasSum _ (fun u _ => hg u) hga

/-- Two non-negative families with the same sector sums have the same sum. -/
private lemma hasSum_of_sector {n : ℕ} (f g : (Fin n → ℕ) → ℝ) (hf : ∀ u, 0 ≤ f u)
    (hg : ∀ u, 0 ≤ g u) (h : ∀ N, ∑ u ∈ sec n N, f u = ∑ u ∈ sec n N, g u) {a : ℝ}
    (hga : HasSum g a) : HasSum f a := by
  have hsum : Summable f := summable_of_sum_le hf (sum_le_of_sector f g hf hg h hga)
  have h1 : ∑' u, f u ≤ a := hasSum_le_of_sum_le hsum.hasSum (sum_le_of_sector f g hf hg h hga)
  have h2 : a ≤ ∑' u, f u :=
    hasSum_le_of_sum_le hga (sum_le_of_sector g f hg hf (fun N => (h N).symm) hsum.hasSum)
  have h3 : ∑' u, f u = a := le_antisymm h1 h2
  rw [← h3]
  exact hsum.hasSum

private lemma gammaFock_diag_real {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (u : Fin n → ℕ) : (gammaFock R u u).im = 0 ∧ 0 ≤ (gammaFock R u u).re := by
  have h := gammaFock_posSemidef R hR {u} (fun _ => 1)
  simpa using h

/-! ### `Γ` of a diagonal matrix (from `fugacity_characteristic`) -/

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

/-! ### Photon counting on a subset of modes -/

/-- Regrouping a summable real family by the value of a statistic. -/
private lemma hasSum_fiberwise_ite {α : Type*} (g : α → ℝ) (c : α → ℕ) {a : ℝ} (hg : HasSum g a) :
    HasSum (fun k : ℕ => ∑' w, if c w = k then g w else 0) a := by
  have h := hg.tsum_fiberwise c
  refine h.congr_fun fun k => ?_
  rw [tsum_subtype]
  refine tsum_congr fun w => ?_
  by_cases h : c w = k
  · rw [if_pos h, Set.indicator_of_mem (by simpa using h)]
  · rw [if_neg h, Set.indicator_of_notMem (by simpa using h)]

private lemma prod_zeta_pow {n : ℕ} (A : Finset (Fin n)) (z : ℝ) (u : Fin n → ℕ) :
    ∏ i, (((if i ∈ A then z else 1 : ℝ) : ℂ)) ^ u i = ((z ^ (∑ i ∈ A, u i) : ℝ) : ℂ) := by
  rw [← Finset.prod_pow_eq_pow_sum, Complex.ofReal_prod, ← Fintype.prod_ite_mem A]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- `1 - S R S` is positive definite for a real diagonal contraction `S`. -/
private lemma posDef_one_sub_sandwich {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR1 : (1 - R).PosDef)
    (s : Fin n → ℝ) (hs : ∀ i, s i * s i ≤ 1) :
    (1 - Matrix.diagonal (fun i => (s i : ℂ)) * R * Matrix.diagonal (fun i => (s i : ℂ))).PosDef := by
  set S : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => (s i : ℂ)) with hS
  have hSH : Sᴴ = S := by
    rw [hS, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  have hdecomp : 1 - S * R * S = Sᴴ * (1 - R) * S + (1 - S * S) := by
    rw [hSH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  have hD : (1 - S * S).PosSemidef := by
    have : (1 : Matrix (Fin n) (Fin n) ℂ) - S * S =
        Matrix.diagonal (fun i => ((1 - s i * s i : ℝ) : ℂ)) := by
      rw [hS, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_sub]
      congr 1
      funext i
      simp
    rw [this]
    exact Matrix.PosSemidef.diagonal fun i => Complex.zero_le_real.mpr (by linarith [hs i])
  have h1 : (Sᴴ * (1 - R) * S).PosSemidef := hR1.posSemidef.conjTranspose_mul_mul_same S
  rw [hdecomp]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (h1.add hD).isHermitian fun x hx => ?_
  rw [Matrix.add_mulVec, dotProduct_add]
  by_cases hy : S *ᵥ x = 0
  · have h2 : (1 - S * S) *ᵥ x = x := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero,
        sub_zero]
    rw [h2]
    exact add_pos_of_nonneg_of_pos (h1.dotProduct_mulVec_nonneg x) (Matrix.dotProduct_star_self_pos_iff.mpr hx)
  · have h2 : 0 < star x ⬝ᵥ ((Sᴴ * (1 - R) * S) *ᵥ x) := by
      simpa only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul] using
        hR1.dotProduct_mulVec_pos hy
    exact add_pos_of_pos_of_nonneg h2 (hD.dotProduct_mulVec_nonneg x)

/-- `Γ(R · diag c)` on the diagonal. -/
private lemma gammaFock_mul_diagonal_self {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ)
    (u : Fin n → ℕ) :
    gammaFock (R * Matrix.diagonal c) u u = gammaFock R u u * ∏ i, c i ^ u i := by
  rw [gammaFock_mul_sec, Finset.sum_eq_single u]
  · rw [gammaFock_diagonal, if_pos rfl]
  · intro w _ hne
    rw [gammaFock_diagonal, if_neg hne, mul_zero]
  · intro h
    exact absurd ((mem_sec u).mpr rfl) h

/-- `det(1 - R)` is a positive real number. -/
private lemma det_real_pos {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) : ∃ d : ℝ, 0 < d ∧ (1 - R).det = (d : ℂ) :=
  ⟨_, (gammaFock_trace_psd R hR hR1).1,
    Complex.ext (by simp) (by simpa using (gammaFock_trace_psd R hR hR1).2.1)⟩

/-- Determinant identity `det(1 - (1 - cP)R) = det(1 + c P R(1-R)⁻¹ P) det(1 - R)` for an idempotent `P`. -/
private lemma det_one_sub_twist {n : ℕ} (R P : Matrix (Fin n) (Fin n) ℂ) (hdet : IsUnit (1 - R).det)
    (hP : P * P = P) (c : ℂ) :
    (1 - (1 - c • P) * R).det = (1 + c • (P * (R * (1 - R)⁻¹) * P)).det * (1 - R).det := by
  have h1 : 1 - (1 - c • P) * R = (1 + c • (P * (R * (1 - R)⁻¹))) * (1 - R) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
    abel
  have h2 : (1 + c • (P * (R * (1 - R)⁻¹))).det = (1 + c • (P * (R * (1 - R)⁻¹) * P)).det := by
    have h3 : c • (P * (R * (1 - R)⁻¹)) = (c • P) * (P * (R * (1 - R)⁻¹)) := by
      rw [Matrix.smul_mul, ← Matrix.mul_assoc P P, hP]
    rw [h3, Matrix.det_one_add_mul_comm, Matrix.mul_smul]
  rw [h1, Matrix.det_mul, h2]

/-- The generating function in the variables of the occupation vectors. -/
private lemma pgf_general {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) (A : Finset (Fin n)) (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < (1 + ((1 - z : ℝ) : ℂ) • (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) *
          (R * (1 - R)⁻¹) * Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0))).det.re ∧
    HasSum (fun w : Fin n → ℕ => (fugacityCoeff R w w).re * z ^ (∑ i ∈ A, w i))
      ((1 + ((1 - z : ℝ) : ℂ) • (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) *
          (R * (1 - R)⁻¹) *
          Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0))).det.re)⁻¹ := by
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ,
      P = Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) := ⟨_, rfl⟩
  rw [← hP]
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Fin n → ℝ, ζ = fun i => if i ∈ A then z else 1 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : Fin n → ℝ, s = fun i => Real.sqrt (ζ i) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin n) (Fin n) ℂ, S = Matrix.diagonal (fun i => (s i : ℂ)) :=
    ⟨_, rfl⟩
  have hζ0 : ∀ i, 0 ≤ ζ i := fun i => by
    rw [hζ]
    dsimp only
    split_ifs <;> linarith
  have hζ1 : ∀ i, ζ i ≤ 1 := fun i => by
    rw [hζ]
    dsimp only
    split_ifs <;> linarith
  have hss : ∀ i, s i * s i = ζ i := fun i => by
    rw [hs]
    exact Real.mul_self_sqrt (hζ0 i)
  have hSS : S * S = Matrix.diagonal (fun i => (ζ i : ℂ)) := by
    rw [hS, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, hss]
  have hPP : P * P = P := by
    rw [hP, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  have hZP : Matrix.diagonal (fun i => (ζ i : ℂ)) = 1 - ((1 - z : ℝ) : ℂ) • P := by
    rw [hP, hζ]
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : i ∈ A <;> simp [hi]
    · simp [hij]
  have hSH : Sᴴ = S := by
    rw [hS, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  have hMpsd : (S * R * S).PosSemidef := by
    have h := hR.conjTranspose_mul_mul_same S
    rwa [hSH] at h
  have hM1 : (1 - S * R * S).PosDef := by
    rw [hS]
    exact posDef_one_sub_sandwich R hR1 s (fun i => by rw [hss]; exact hζ1 i)
  obtain ⟨d, hd, hdet⟩ := det_real_pos R hR hR1
  obtain ⟨m, hm, hmdet⟩ := det_real_pos (S * R * S) hMpsd hM1
  have hdetid : (m : ℂ) = (1 + ((1 - z : ℝ) : ℂ) • (P * (R * (1 - R)⁻¹) * P)).det * (d : ℂ) := by
    rw [← hmdet, ← hdet, ← det_one_sub_twist R P ((Matrix.isUnit_iff_isUnit_det _).mp hR1.isUnit) hPP,
      ← hZP, ← hSS, Matrix.det_one_sub_mul_comm (S * R) S, Matrix.mul_assoc S S R]
  have hD : (1 + ((1 - z : ℝ) : ℂ) • (P * (R * (1 - R)⁻¹) * P)).det = ((m / d : ℝ) : ℂ) := by
    rw [Complex.ofReal_div]
    exact eq_div_of_mul_eq (by exact_mod_cast hd.ne') hdetid.symm
  rw [hD, Complex.ofReal_re]
  refine ⟨div_pos hm hd, ?_⟩
  have hsec : ∀ N, ∑ u ∈ sec n N, (gammaFock R u u).re * z ^ (∑ i ∈ A, u i) =
      ∑ u ∈ sec n N, (gammaFock (S * R * S) u u).re := by
    intro N
    have h := sector_trace_comm (R * S) S N
    have e1 : R * S * S = R * Matrix.diagonal (fun i => (ζ i : ℂ)) := by rw [Matrix.mul_assoc, hSS]
    have e2 : S * (R * S) = S * R * S := by rw [Matrix.mul_assoc]
    rw [e1, e2] at h
    rw [← Complex.re_sum, ← h, Complex.re_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [gammaFock_mul_diagonal_self, hζ, prod_zeta_pow, Complex.re_mul_ofReal]
  have hMre := Complex.hasSum_re (gammaFock_trace_psd (S * R * S) hMpsd hM1).2.2
  rw [hmdet, ← Complex.ofReal_inv, Complex.ofReal_re] at hMre
  have hreal := hasSum_of_sector (fun u => (gammaFock R u u).re * z ^ (∑ i ∈ A, u i))
    (fun u => (gammaFock (S * R * S) u u).re)
    (fun u => mul_nonneg (gammaFock_diag_real R hR u).2 (pow_nonneg hz0 _))
    (fun u => (gammaFock_diag_real _ hMpsd u).2) hsec hMre
  have hfin := hreal.mul_left d
  have hval : (m / d)⁻¹ = d * m⁻¹ := by rw [inv_div, div_eq_mul_inv]
  rw [hval]
  refine hfin.congr_fun fun w => ?_
  rw [fugacityCoeff, Matrix.smul_apply, smul_eq_mul, hdet, Complex.re_ofReal_mul, mul_assoc]

theorem solution {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) (A : Finset (Fin n)) :
    (∀ k : ℕ, 0 ≤ ∑' w : Occupation (Fin n),
        if ∑ i ∈ A, w i = k then (fugacityCoeff (U * R * Uᴴ) w w).re else 0) ∧
    ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      0 < (1 + ((1 - z : ℝ) : ℂ) • (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) *
          (U * (R * (1 - R)⁻¹) * Uᴴ) * Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0))).det.re ∧
      HasSum (fun k : ℕ => (∑' w : Occupation (Fin n),
            if ∑ i ∈ A, w i = k then (fugacityCoeff (U * R * Uᴴ) w w).re else 0) * z ^ k)
        ((1 + ((1 - z : ℝ) : ℂ) • (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) *
          (U * (R * (1 - R)⁻¹) * Uᴴ) *
          Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0))).det.re)⁻¹ := by
  have hU2 : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hR' : (U * R * Uᴴ).PosSemidef := hR.mul_mul_conjTranspose_same U
  have h1R' : 1 - U * R * Uᴴ = U * (1 - R) * Uᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU2]
  have hR1' : (1 - U * R * Uᴴ).PosDef := by
    rw [h1R']
    exact hR1.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_isUnit (IsUnit.of_mul_eq_one _ hU2))
  have hunit : IsUnit (1 - R).det := (Matrix.isUnit_iff_isUnit_det _).mp hR1.isUnit
  have hinv : (1 - U * R * Uᴴ)⁻¹ = U * (1 - R)⁻¹ * Uᴴ := by
    rw [h1R']
    refine Matrix.inv_eq_right_inv ?_
    calc U * (1 - R) * Uᴴ * (U * (1 - R)⁻¹ * Uᴴ)
        = U * ((1 - R) * ((Uᴴ * U) * (1 - R)⁻¹)) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, Matrix.one_mul, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one, hU2]
  have hN : U * R * Uᴴ * (1 - U * R * Uᴴ)⁻¹ = U * (R * (1 - R)⁻¹) * Uᴴ := by
    rw [hinv]
    calc U * R * Uᴴ * (U * (1 - R)⁻¹ * Uᴴ)
        = U * (R * ((Uᴴ * U) * (1 - R)⁻¹)) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * (R * (1 - R)⁻¹) * Uᴴ := by rw [hU, Matrix.one_mul]
  obtain ⟨d, hd, hdet⟩ := det_real_pos (U * R * Uᴴ) hR' hR1'
  have hf : ∀ w : Fin n → ℕ, 0 ≤ (fugacityCoeff (U * R * Uᴴ) w w).re := by
    intro w
    rw [fugacityCoeff, Matrix.smul_apply, smul_eq_mul, hdet, Complex.re_ofReal_mul]
    exact mul_nonneg hd.le (gammaFock_diag_real _ hR' w).2
  refine ⟨fun k => tsum_nonneg fun w => ?_, fun z hz0 hz1 => ?_⟩
  · split_ifs
    · exact hf w
    · exact le_rfl
  obtain ⟨hpos, hsum⟩ := pgf_general (U * R * Uᴴ) hR' hR1' A z hz0 hz1
  rw [hN] at hpos hsum
  refine ⟨hpos, ?_⟩
  have h := hasSum_fiberwise_ite _ (fun w : Fin n → ℕ => ∑ i ∈ A, w i) hsum
  refine h.congr_fun fun k => ?_
  rw [← tsum_mul_right]
  refine tsum_congr fun w => ?_
  split_ifs with hk
  · rw [hk]
  · rw [zero_mul]
