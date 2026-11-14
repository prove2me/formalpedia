-- Prove2me | solution 1 for BosonicLearn.fugacity_photon_number
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T19:32:51.58203+00:00
-- url     : https://prove2.me/submissions/45f25b42-e387-43b9-bb9c-f78ad6f6fcdf

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Theorems.Thm_BosonicLearn_gammaFock_mul
import Theorems.Thm_BosonicLearn_gammaFock_posSemidef

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

open BosonicLearn

noncomputable section

/-! ### Sectors, cyclicity and unitary diagonalization (as in `gammaFock_trace_psd`) -/

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

private lemma conj_one_sub {n : ℕ} (U D : Matrix (Fin n) (Fin n) ℂ) (hU1 : Uᴴ * U = 1) :
    Uᴴ * (1 - U * D * Uᴴ) * U = 1 - D := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU1]
  have h : Uᴴ * (U * D * Uᴴ) * U = (Uᴴ * U) * D * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
  rw [h, hU1, Matrix.one_mul, Matrix.mul_one]

private lemma one_sub_conj {n : ℕ} (U D : Matrix (Fin n) (Fin n) ℂ) (hU2 : U * Uᴴ = 1) :
    1 - U * D * Uᴴ = U * (1 - D) * Uᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU2]

private lemma one_sub_diagonal {n : ℕ} (d : Fin n → ℝ) :
    (1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.diagonal (fun i => (d i : ℂ)) =
      Matrix.diagonal (fun i => ((1 - d i : ℝ) : ℂ)) := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
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

private lemma gammaFock_diag_real {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (u : Fin n → ℕ) : (gammaFock R u u).im = 0 ∧ 0 ≤ (gammaFock R u u).re := by
  have h := gammaFock_posSemidef R hR {u} (fun _ => 1)
  simpa using h

/-! ### Diagonal entries of `Γ(diag c)` and products of series (as in `gammaFock_trace`) -/

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

/-- Diagonal entries of `Γ(diag c)`. -/
private lemma gammaFock_diagonal_self {n : ℕ} (c : Fin n → ℂ) (u : Fin n → ℕ) :
    gammaFock (Matrix.diagonal c) u u = ∏ i, c i ^ u i := by
  rw [gammaFock_eq, gSum_diagonal_self]
  have hpos : (0 : ℝ) ≤ ∏ i, (Nat.factorial (u i) : ℝ) :=
    Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
  rw [Real.sqrt_mul_self hpos]
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : ((Nat.factorial (u i) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-- A finite product of nonnegative convergent series is the series over `ℕⁿ` of the products. -/
private lemma hasSum_pi_prod_of_nonneg (n : ℕ) : ∀ (f : Fin n → ℕ → ℝ) (a : Fin n → ℝ),
    (∀ i k, 0 ≤ f i k) → (∀ i, HasSum (f i) (a i)) →
    HasSum (fun u : Fin n → ℕ => ∏ i, f i (u i)) (∏ i, a i) := by
  induction n with
  | zero =>
    intro f a _ _
    simp
  | succ n ih =>
    intro f a hf0 hf
    have ih' := ih (fun i => f i.succ) (fun i => a i.succ)
      (fun i k => hf0 i.succ k) (fun i => hf i.succ)
    have hsum : Summable (fun p : ℕ × (Fin n → ℕ) => f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i)) :=
      Summable.mul_of_nonneg (f := f 0) (g := fun u : Fin n → ℕ => ∏ i : Fin n, f i.succ (u i))
        (hf 0).summable ih'.summable (fun k => hf0 0 k)
        (fun u => Finset.prod_nonneg fun i _ => hf0 i.succ (u i))
    have hmul : HasSum (fun p : ℕ × (Fin n → ℕ) => f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i))
        (a 0 * ∏ i : Fin n, a i.succ) :=
      HasSum.mul (f := f 0) (g := fun u : Fin n → ℕ => ∏ i : Fin n, f i.succ (u i)) (hf 0) ih' hsum
    rw [Fin.prod_univ_succ]
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).hasSum_iff]
    refine hmul.congr_fun fun p => ?_
    simp [Fin.prod_univ_succ, Fin.consEquiv]

private lemma gammaFock_diagonal_re {n : ℕ} (d : Fin n → ℝ) (u : Fin n → ℕ) :
    (gammaFock (Matrix.diagonal fun i => (d i : ℂ)) u u).re = ∏ i, d i ^ u i := by
  simp only [gammaFock_diagonal_self, ← Complex.ofReal_pow, ← Complex.ofReal_prod,
    Complex.ofReal_re]

/-! ### The diagonal case and the trace side -/

/-- `∑_u |u| ∏ⱼ dⱼ^{uⱼ} = (∑ᵢ dᵢ/(1 − dᵢ)) ∏ⱼ (1 − dⱼ)⁻¹`. -/
private lemma hasSum_weighted {n : ℕ} (d : Fin n → ℝ) (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i < 1) :
    HasSum (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) * ∏ j, d j ^ u j)
      ((∑ i, d i / (1 - d i)) * ∏ j, (1 - d j)⁻¹) := by
  have hone : ∀ i : Fin n, HasSum (fun u : Fin n → ℕ => (u i : ℝ) * ∏ j, d j ^ u j)
      (d i / (1 - d i) * ∏ j, (1 - d j)⁻¹) := by
    intro i
    have h := hasSum_pi_prod_of_nonneg n
      (fun j k => (if j = i then (k : ℝ) else 1) * d j ^ k)
      (fun j => (if j = i then d i / (1 - d i) else 1) * (1 - d j)⁻¹)
      (fun j k => mul_nonneg (by split_ifs <;> positivity) (pow_nonneg (hd0 j) k))
      (fun j => by
        by_cases hji : j = i
        · subst hji
          have h := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := d j)
            (by rw [Real.norm_of_nonneg (hd0 j)]; exact hd1 j)
          have hne : 1 - d j ≠ 0 := by linarith [hd1 j]
          have hval : d j / (1 - d j) ^ 2 = d j / (1 - d j) * (1 - d j)⁻¹ := by
            field_simp
          rw [hval] at h
          simpa using h
        · simp only [if_neg hji, one_mul]
          exact hasSum_geometric_of_lt_one (hd0 j) (hd1 j))
    have e1 : ∀ u : Fin n → ℕ, ∏ j, (if j = i then (u j : ℝ) else 1) * d j ^ u j =
        (u i : ℝ) * ∏ j, d j ^ u j := by
      intro u
      rw [Finset.prod_mul_distrib]
      simp
    have e2 : ∏ j, (if j = i then d i / (1 - d i) else 1) * (1 - d j)⁻¹ =
        d i / (1 - d i) * ∏ j, (1 - d j)⁻¹ := by
      rw [Finset.prod_mul_distrib]
      simp
    rw [e2] at h
    exact h.congr_fun fun u => (e1 u).symm
  have h := hasSum_sum (s := Finset.univ) fun i _ => hone i
  rw [← Finset.sum_mul] at h
  refine h.congr_fun fun u => ?_
  rw [Finset.sum_mul]

private lemma conj_mul_conj {n : ℕ} (U A B : Matrix (Fin n) (Fin n) ℂ) (hU1 : Uᴴ * U = 1) :
    (U * A * Uᴴ) * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
  have h : (U * A * Uᴴ) * (U * B * Uᴴ) = U * (A * ((Uᴴ * U) * B)) * Uᴴ := by
    simp only [Matrix.mul_assoc]
  rw [h, hU1, Matrix.one_mul]

private lemma trace_conj {n : ℕ} (U A : Matrix (Fin n) (Fin n) ℂ) (hU1 : Uᴴ * U = 1) :
    (U * A * Uᴴ).trace = A.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul]

/-- `Tr[R(1 − R)⁻¹] = ∑ᵢ dᵢ/(1 − dᵢ)` for `R = U diag(d) Uᴴ`. -/
private lemma trace_rhs {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (hd1 : ∀ i, d i < 1) :
    (U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ *
      (1 - U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ)⁻¹).trace =
      ((∑ i, d i / (1 - d i) : ℝ) : ℂ) := by
  have hinv : (1 - U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ)⁻¹ =
      U * Matrix.diagonal (fun i => (((1 - d i)⁻¹ : ℝ) : ℂ)) * Uᴴ := by
    apply Matrix.inv_eq_right_inv
    rw [one_sub_conj U _ hU2, one_sub_diagonal, conj_mul_conj U _ _ hU1,
      Matrix.diagonal_mul_diagonal]
    have h1 : (fun i => ((1 - d i : ℝ) : ℂ) * (((1 - d i)⁻¹ : ℝ) : ℂ)) = fun _ => 1 := by
      funext i
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (by linarith [hd1 i]), Complex.ofReal_one]
    rw [h1, Matrix.diagonal_one, Matrix.mul_one, hU2]
  rw [hinv, conj_mul_conj U _ _ hU1, trace_conj U _ hU1, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_eq_mul_inv, Complex.ofReal_mul]

theorem solution {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) :
    ∑' u : Occupation (Fin n), ENNReal.ofReal (∑ i, (u i : ℝ)) * ENNReal.ofReal (fugacityCoeff R u u).re =
      ENNReal.ofReal (R * (1 - R)⁻¹).trace.re := by
  obtain ⟨U, d, hU1, hU2, hspec, hd0, hd1⟩ := spectral_data R hR hR1
  have hdet : (1 - R).det = ((∏ i, (1 - d i) : ℝ) : ℂ) := by
    rw [hspec, one_sub_conj U _ hU2, one_sub_diagonal, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal, mul_right_comm, ← Matrix.det_mul, hU2, Matrix.det_one, one_mul,
      Complex.ofReal_prod]
  have hpos : 0 < ∏ i, (1 - d i) := Finset.prod_pos fun i _ => by linarith [hd1 i]
  -- equal sector traces of `Γ(R)` and `Γ(diag d)`
  have hsec0 : ∀ N, ∑ u ∈ sec n N, (gammaFock R u u).re = ∑ u ∈ sec n N, ∏ i, d i ^ u i := by
    intro N
    have h := sector_trace_comm (U * Matrix.diagonal (fun i => (d i : ℂ))) Uᴴ N
    rw [← hspec, ← Matrix.mul_assoc, hU1, Matrix.one_mul] at h
    rw [← Complex.re_sum, h, Complex.re_sum]
    exact Finset.sum_congr rfl fun u _ => gammaFock_diagonal_re d u
  have hsec : ∀ N, ∑ u ∈ sec n N, (∑ i, (u i : ℝ)) * (gammaFock R u u).re =
      ∑ u ∈ sec n N, (∑ i, (u i : ℝ)) * ∏ i, d i ^ u i := by
    intro N
    have hc : ∀ x : (Fin n → ℕ) → ℝ,
        ∑ u ∈ sec n N, (∑ i, (u i : ℝ)) * x u = N * ∑ u ∈ sec n N, x u := by
      intro x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [← Nat.cast_sum, (mem_sec u).mp hu]
    rw [hc, hc, hsec0 N]
  have htot : ∀ u : Fin n → ℕ, 0 ≤ ∑ i, (u i : ℝ) := fun u =>
    Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have hreal := hasSum_of_sector (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) * (gammaFock R u u).re)
    (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) * ∏ i, d i ^ u i)
    (fun u => mul_nonneg (htot u) (gammaFock_diag_real R hR u).2)
    (fun u => mul_nonneg (htot u) (Finset.prod_nonneg fun i _ => pow_nonneg (hd0 i) _))
    hsec (hasSum_weighted d hd0 hd1)
  have hx : ∀ u, (fugacityCoeff R u u).re = (∏ i, (1 - d i)) * (gammaFock R u u).re := by
    intro u
    unfold fugacityCoeff
    rw [Matrix.smul_apply, smul_eq_mul, hdet, Complex.re_ofReal_mul]
  have hx0 : ∀ u, 0 ≤ (fugacityCoeff R u u).re := fun u => by
    rw [hx]
    exact mul_nonneg hpos.le (gammaFock_diag_real R hR u).2
  have hfinal : HasSum (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) * (fugacityCoeff R u u).re)
      (∑ i, d i / (1 - d i)) := by
    have h := hreal.mul_left (∏ i, (1 - d i))
    have hval : (∏ i, (1 - d i)) * ((∑ i, d i / (1 - d i)) * ∏ j, (1 - d j)⁻¹) =
        ∑ i, d i / (1 - d i) := by
      rw [Finset.prod_inv_distrib]
      field_simp
    rw [hval] at h
    refine h.congr_fun fun u => ?_
    rw [hx]
    ring
  have hlhs : ∑' u : Occupation (Fin n),
      ENNReal.ofReal (∑ i, (u i : ℝ)) * ENNReal.ofReal (fugacityCoeff R u u).re =
        ENNReal.ofReal (∑ i, d i / (1 - d i)) := by
    rw [← hfinal.tsum_eq, ENNReal.ofReal_tsum_of_nonneg
      (fun u => mul_nonneg (htot u) (hx0 u)) hfinal.summable]
    refine tsum_congr fun u => ?_
    rw [ENNReal.ofReal_mul (htot u)]
  have htrace := trace_rhs U d hU1 hU2 hd1
  rw [← hspec] at htrace
  rw [hlhs, htrace, Complex.ofReal_re]
